#!/usr/bin/env python3
"""Kernel-check inverse-search witnesses and proposed beta/eta groupings.

The Python interpreter only proposes groups. Coq checks both the surface and
the equality of the actual denotations for EVERY member. This does not prove
that inverse search covers every grammar tree, or that different groups are
semantically inequivalent under the postulates.
"""
import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

from explore_readings import Explorer, emit, sentences, tokenize

HERE = Path(__file__).resolve().parent

# Proposals only. Every mapping is checked against the revised registry AND
# the actual all-admissible-model denotations by the generated Coq proofs.
CANONICAL = [
    ['bill_walks'], ['a_man_walks'], ['every_man_walks'], ['the_man_walks'],
    ['finds_unicorn', 'finds_unicorn'],
    ['seeks_unicorn_re', 'seeks_unicorn_dicto'],
    ['tries_unicorn_re', 'tries_unicorn_dicto', 'tries_unicorn_dicto'],
    ['talks_unicorn_re', 'talks_unicorn_dicto'],
    ['bill_is_mary'], ['bill_is_man'], ['temperature_is_ninety'],
    ['temperature_rises'], ['ninety_rises'], ['a_price_rises'],
    ['woman_loves_every_man', 'woman_loves_every_man', 'every_man_loved_by_a_woman'],
    ['wish_unicorn_re', 'wish_unicorn_dicto'],
    ['belief_external_conjunction', 'belief_unicorn_re', 'belief_unicorn_dicto'],
    ['joint_seeking'], ['(joint_control try_to wish_to)'], ['(joint_control wish_to try_to)'],
]


def app(f, *args):
    for x in args:
        f = f(x) if callable(f) else ('apply', f, x)
    return f


def freeze(value, level=0):
    if callable(value):
        variable = ('bound', level)
        body = freeze(value(variable), level + 1)
        if body[0] == 'apply' and body[2] == variable and not contains(body[1], variable):
            return body[1]
        return ('lambda', level, body)
    if isinstance(value, tuple):
        return tuple(freeze(v, level) for v in value)
    return value


def contains(value, variable):
    return value == variable or isinstance(value, tuple) and any(contains(v, variable) for v in value)


def denote(tree, values, world):
    rule, *args = tree
    if rule == 'word':
        return ('word', *args, world)
    if rule == 'name':
        return lambda p: app(p, world, lambda j: ('name', args[0], j))
    if rule == 'pronoun':
        return lambda p: app(p, world, values(args[0]))
    if rule == 'be':
        return lambda q: lambda x: app(q, world, lambda j: lambda y: ('equal', app(x, j), app(y, j)))
    if rule == 'necessarily':
        return ('necessarily',)
    if rule == 's2':
        d, c = args
        return ('determiner', d, denote(c, values, world), world)
    if rule == 's3':
        c, n, p = args
        return lambda x: ('and', app(denote(c, values, world), x),
                          denote(p, lambda m: x if m == n else values(m), world))
    if rule in ('s4', 's5', 's6', 's7', 's8', 's9', 's10'):
        p, q = args
        return app(denote(p, values, world), lambda j: denote(q, values, j))
    if rule in ('s11', 's12'):
        junction, p, q = args
        op = 'and' if junction == 'conjunction' else 'or'
        if rule == 's11':
            return (op, denote(p, values, world), denote(q, values, world))
        return lambda x: (op, app(denote(p, values, world), x), app(denote(q, values, world), x))
    if rule == 's13':
        p, q = args
        return lambda prop: ('or', app(denote(p, values, world), prop), app(denote(q, values, world), prop))
    if rule in ('s14', 's15', 's16'):
        p, n, q = args
        body = lambda j: lambda x: denote(q, lambda m: x if m == n else values(m), j)
        if rule == 's14':
            return app(denote(p, values, world), body)
        return lambda y: app(denote(p, values, world), lambda j: lambda x: app(body(j)(x), y))
    if rule == 's17':
        sign, p, q = args
        return ('sign', sign, lambda j: app(denote(p, values, j), lambda k: denote(q, values, k)), world)
    raise ValueError(rule)


def signature(tree):
    return alpha_normalize(freeze(denote(tree, lambda n: ('free', n), ('world',))))


def alpha_normalize(value, bound=()):
    if not isinstance(value, tuple):
        return value
    if value[0] == 'bound':
        return ('bound', bound.index(value[1]))
    if value[0] == 'lambda':
        return ('lambda', alpha_normalize(value[2], (value[1],) + bound))
    return tuple(alpha_normalize(v, bound) for v in value)


def run(cmd, timeout=180):
    result = subprocess.run(cmd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout)
    if result.returncode:
        raise RuntimeError(result.stdout)
    return result.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--policy', choices=('literal', 'amended'), default='amended')
    parser.add_argument('--compiled-dir', type=Path, help='Reuse an existing local development build')
    reporting = parser.add_mutually_exclusive_group()
    reporting.add_argument('--output', type=Path, help='Write the reproducible JSON report')
    reporting.add_argument('--check-report', type=Path, help='Reproduce and compare an existing JSON report')
    args = parser.parse_args()
    if 'version 8.20.1' not in run(['coqc', '--version']):
        raise RuntimeError('Expected Coq 8.20.1')
    explorer = Explorer(args.policy, 100000)
    rows = []
    with tempfile.TemporaryDirectory(prefix='ptq-reading-exploration-') as directory:
        temp = Path(directory)
        if args.compiled_dir:
            compiled = args.compiled_dir.resolve()
        else:
            import check
            compiled = temp
            for unit in check.UNITS:
                shutil.copy2(HERE / (unit + '.v'), temp)
                run(['coqc', '-Q', str(temp), 'MontaguePTQ', str(temp / (unit + '.v'))])
        certificates = temp / 'certificates'
        certificates.mkdir()
        flags = ['-Q', str(compiled), 'MontaguePTQ', '-Q', str(certificates), 'ExplorationCheck']
        for number, words in enumerate(sentences(), 1):
            trees = sorted({tree for tokens in tokenize(words)
                            for tree in explorer.parse('CT', 'infinitive', tokens)}, key=repr)
            groups = defaultdict(list)
            for tree in trees:
                groups[signature(tree)].append(tree)
            source = ['From Coq Require Import List Strings.String.',
                      'From MontaguePTQ Require Import Syntax Models Grammar Meaning Postulates Examples Catalogue',
                      ' Surface SurfaceAmendment AdditionalReadings ReadingNormalization.',
                      'Import ListNotations.', 'Open Scope string_scope.']
            renderer = 'surface' if args.policy == 'literal' else 'amended_surface'
            text = ';'.join(json.dumps(w) for w in words)
            witness_index = 0
            group_rows = []
            if trees and len(groups) != len(CANONICAL[number - 1]):
                raise RuntimeError(f'Group proposal changed at sentence {number}; recheck mapping')
            for group_index, members in enumerate(groups.values()):
                rep = f'representative_{number}_{group_index}'
                canonical = CANONICAL[number - 1][group_index]
                source.append(f'Definition {rep} := {emit(members[0])}.')
                source.extend([
                    f'Example registered_{group_index} : In {canonical}',
                    f' (snd (nth {number - 1} revised_catalogue ([],[]))).',
                    'Proof. cbn; repeat (first [left; reflexivity | right]). Qed.',
                    f'Example canonical_{group_index} M (A : admissible M) r i :',
                    f' denote M {rep} r i = denote M {canonical} r i.',
                    'Proof. normalize_discovered_reading A. Qed.',
                ])
                for tree in members:
                    name = f'witness_{number}_{witness_index}'
                    source.extend([f'Definition {name} := {emit(tree)}.',
                                   f'Example surface_{witness_index} : {renderer} {name} = Some [{text}].',
                                   'Proof. reflexivity. Qed.',
                                   f'Example meaning_{witness_index} M r i : denote M {name} r i = denote M {rep} r i.',
                                   'Proof. reflexivity. Qed.'])
                    witness_index += 1
                group_rows.append(dict(group=group_index, witnesses=len(members),
                                       representative=emit(members[0]), canonical=canonical))
            generated = certificates / f'Exploration{number}.v'
            generated.write_text('\n'.join(source) + '\n')
            run(['coqc', *flags, str(generated)])
            row = dict(sentence=number, words=' '.join(words), witnesses=len(trees),
                       beta_eta_groups=len(groups), registered_classes_reached=len({g['canonical'] for g in group_rows}),
                       groups=group_rows,
                       generated_coq_sha256=hashlib.sha256(generated.read_bytes()).hexdigest())
            rows.append(row)
            print(json.dumps({k: v for k, v in row.items() if k != 'groups'}), flush=True)
        run(['coqchk', '-silent', *flags,
             *(f'ExplorationCheck.Exploration{row["sentence"]}' for row in rows)], timeout=300)
    import check
    inputs = {name: hashlib.sha256((HERE / name).read_bytes()).hexdigest()
              for name in ['explore_readings.py', 'check_reading_exploration.py',
                           *(unit + '.v' for unit in check.UNITS)]}
    result = dict(policy=args.policy, model='none', coq_version=run(['coqc', '--version']).splitlines()[0],
                  build_mode='development_cache' if args.compiled_dir else 'isolated', inputs_sha256=inputs,
                  search_completeness_proved=False, groups_proved_pairwise_inequivalent=False,
                  every_discovered_surface_kernel_checked=True,
                  every_group_member_denotation_kernel_checked=True,
                  every_group_mapped_to_registered_reading_in_all_admissible_models=True,
                  witnesses=sum(row['witnesses'] for row in rows),
                  beta_eta_groups=sum(row['beta_eta_groups'] for row in rows),
                  registered_classes_reached=sum(row['registered_classes_reached'] for row in rows), sentences=rows)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    if args.check_report and json.loads(args.check_report.read_text()) != result:
        raise RuntimeError('Reading exploration report drift; review changes before recording')
    print(f'PASS: {result["witnesses"]} witnesses, {result["registered_classes_reached"]} registered reading classes; '
          'all-model classification of the discovered set only.', flush=True)


if __name__ == '__main__':
    main()
