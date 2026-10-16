#!/usr/bin/env python3
"""Inverse derivation exploration for the registered PTQ strings.

This is discovery tooling, NOT a Coq completeness certificate. It removes
identity renaming loops and represents nontrivial renaming by splitting a
visible index class. Coq now proves redundant-wrapper normalization, local
F10 inversion and inverse-body rank decrease. The bridge covering this whole
parser, including tokenization and all grammar branches, remains unproved.
Every retained witness can be emitted as a Coq tree for independent checking.
"""
import argparse
from functools import cache
import itertools
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
IV = ('run', 'walk', 'talk', 'rise', 'change')
CN = ('man', 'woman', 'park', 'fish', 'pen', 'unicorn', 'price', 'temperature')
TV = ('find', 'lose', 'eat', 'love', 'date', 'seek', 'conceive')
ADV = ('rapidly', 'slowly', 'voluntarily', 'allegedly')
NAMES = {'John': 'john', 'Mary': 'mary', 'Bill': 'bill', 'ninety': 'ninety'}
CONTROLS = ('try_to', 'wish_to')
ATTITUDES = ('believe_that', 'assert_that')
FORM = ('infinitive', 'present', 'neg_present', 'future_form',
        'neg_future_form', 'perfect_form', 'neg_perfect_form')
SIGN = dict(zip(FORM[2:], ('negative', 'future', 'negative_future', 'perfect', 'negative_perfect')))
VERBS = tuple(('liv', v) for v in IV) + tuple(('ltv', v) for v in TV) + (
    ('be', 'be'),) + tuple(('lcontrol', v) for v in CONTROLS) + tuple(('latt', v) for v in ATTITUDES)


def verb_words(kind, word, form):
    head = word.removesuffix('_to').removesuffix('_that')
    tail = ('to',) if kind == 'lcontrol' else ('that',) if kind == 'latt' else ()
    present = {'be': 'is', 'try': 'tries', 'wish': 'wishes'}.get(head, head + 's')
    perfect = dict(run='run', walk='walked', talk='talked', rise='risen', change='changed',
                   find='found', lose='lost', eat='eaten', love='loved', date='dated',
                   seek='sought', conceive='conceived', be='been', wish='wished',
                   believe='believed', **{'try': 'tried', 'assert': 'asserted'})[head]
    prefix = {
        'infinitive': (head,), 'present': (present,),
        'neg_present': ('is', 'not') if head == 'be' else ('does', 'not', head),
        'future_form': ('will', head), 'neg_future_form': ('will', 'not', head),
        'perfect_form': ('has', perfect), 'neg_perfect_form': ('has', 'not', perfect),
    }[form]
    return prefix + tail


TOKENIZATIONS = []
for kind, word in VERBS:
    for form in FORM:
        TOKENIZATIONS.append((verb_words(kind, word, form), ('verb', kind, word, form)))
for word in CN:
    TOKENIZATIONS.append(((word,), ('noun', word)))
for word, name in NAMES.items():
    TOKENIZATIONS.append(((word,), ('name', name)))
for word in (*ADV, 'in', 'about', 'necessarily', 'a', 'every', 'the', 'such', 'that', 'and', 'or'):
    TOKENIZATIONS.append(((word,), ('literal', word)))
for gender, forms in [('masculine', ('he', 'him')), ('feminine', ('she', 'her')),
                      ('neuter', ('it', 'it'))]:
    for case, word in enumerate(forms):
        TOKENIZATIONS.append(((word,), ('plain', gender, case)))


@cache
def tokenize(words):
    if not words:
        return ((),)
    return tuple((token,) + rest for prefix, token in TOKENIZATIONS
                 if words[:len(prefix)] == prefix for rest in tokenize(words[len(prefix):]))


def first_gender(tokens):
    for token in tokens:
        if token[0] == 'noun':
            return {'man': 'masculine', 'woman': 'feminine'}.get(token[1], 'neuter')
        if token[0] == 'name':
            return {'john': 'masculine', 'bill': 'masculine', 'mary': 'feminine'}.get(token[1], 'neuter')
        if token[0] == 'index':
            return 'masculine'
    return None


def fresh_index(tokens):
    return 1 + max((t[1] for t in tokens if t[0] == 'index'), default=-1)


def object_np(tokens):
    if len(tokens) == 1 and tokens[0][0] == 'index' and tokens[0][2] == 1:
        return (('index', tokens[0][1], 0),)
    return tokens


def replaced(tokens, positions, index):
    positions = set(positions)
    return tuple(('index', index, t[2]) if k in positions else t for k, t in enumerate(tokens))


def subsets(positions, proper=False):
    low, high = (1, len(positions)) if proper else (0, len(positions) + 1)
    for n in range(low, high):
        yield from itertools.combinations(positions, n)


def rank(tokens):
    indices = [t[1] for t in tokens if t[0] == 'index']
    return (len(tokens), sum(t[0] not in ('index', 'plain') for t in tokens),
            len(indices) - len(set(indices)))


class Explorer:
    def __init__(self, policy, limit):
        self.policy, self.limit = policy, limit
        self.states = 0
        self.parse = cache(self._parse)

    def _parse(self, category, form, tokens):
        self.states += 1
        found = set()

        def add(tree):
            found.add(tree)
            if len(found) > self.limit:
                raise RuntimeError(f'Witness cap exceeded in {category}: {self.limit}; no completeness claim')

        def child(cat, mode, ts):
            if not ts:
                return ()
            if rank(ts) >= rank(tokens):
                raise AssertionError(('Nondecreasing inverse step', category, tokens, cat, ts))
            return self.parse(cat, mode, ts)

        def binary(rule, leftcat, rightcat, left, right, leftmode='infinitive', rightmode='infinitive', middle=()):
            for p in child(leftcat, leftmode, left):
                for q in child(rightcat, rightmode, right):
                    add((rule, *middle, p, q))

        if not tokens:
            return ()
        if category == 'NP':
            if len(tokens) == 1 and tokens[0][0] == 'name':
                add(('name', tokens[0][1]))
            if len(tokens) == 1 and tokens[0][0] == 'index' and tokens[0][2] == 0:
                add(('pronoun', tokens[0][1]))
            if tokens[0][0] == 'literal' and tokens[0][1] in ('a', 'every', 'the'):
                for c in child('CN', 'infinitive', tokens[1:]):
                    add(('s2', {'a': 'a_or_an'}.get(tokens[0][1], tokens[0][1]), c))
        if category == 'CN' and len(tokens) == 1 and tokens[0][0] == 'noun':
            add(('word', 'lcn', tokens[0][1]))
        if category == 'IAV' and len(tokens) == 1 and tokens[0][0] == 'literal' and tokens[0][1] in ADV:
            add(('word', 'liav', tokens[0][1]))
        if category in ('IV', 'TV', 'ATT', 'CONTROL') and len(tokens) == 1 and tokens[0][0] == 'verb':
            _, kind, word, actual = tokens[0]
            if actual == form and kind == {'IV': 'liv', 'TV': 'ltv', 'ATT': 'latt', 'CONTROL': 'lcontrol'}[category]:
                add(('word', kind, word))
            if category == 'TV' and kind == 'be' and actual == form:
                add(('be',))
        if category == 'PREP' and len(tokens) == 1 and tokens[0] in (('literal', 'in'), ('literal', 'about')):
            add(('word', 'lprep', 'in_' if tokens[0][1] == 'in' else 'about'))
        if category == 'SADV' and tokens == (('literal', 'necessarily'),):
            add(('necessarily',))

        for cut in range(1, len(tokens)):
            left, right = tokens[:cut], tokens[cut:]
            if category == 'CT':
                binary('s4', 'NP', 'IV', left, right, rightmode='present')
                binary('s9', 'SADV', 'CT', left, right)
                for mode, sign in SIGN.items():
                    binary('s17', 'NP', 'IV', left, right, rightmode=mode, middle=(sign,))
            if category == 'IV':
                binary('s5', 'TV', 'NP', left, object_np(right), leftmode=form)
                binary('s7', 'ATT', 'CT', left, right, leftmode=form)
                binary('s8', 'CONTROL', 'IV', left, right, leftmode=form)
                binary('s10', 'IAV', 'IV', right, left, rightmode=form)
            if category == 'IAV':
                binary('s6', 'PREP', 'NP', left, object_np(right))

        for pos, token in enumerate(tokens):
            if token not in (('literal', 'and'), ('literal', 'or')):
                continue
            left, right = tokens[:pos], tokens[pos + 1:]
            junction = 'conjunction' if token[1] == 'and' else 'disjunction'
            if category == 'CT':
                binary('s11', 'CT', 'CT', left, right, middle=(junction,))
            if category == 'IV':
                rightmode = form if self.policy == 'amended' and form == 'present' else 'infinitive'
                binary('s12', 'IV', 'IV', left, right, leftmode=form, rightmode=rightmode, middle=(junction,))
            if category == 'NP' and token[1] == 'or':
                binary('s13', 'NP', 'NP', left, right)

        if category == 'CN':
            for pos in range(1, len(tokens) - 2):
                if tokens[pos:pos+2] != (('literal', 'such'), ('literal', 'that')):
                    continue
                cn, sentence = tokens[:pos], tokens[pos+2:]
                gender, index = first_gender(cn), fresh_index(tokens)
                positions = [k for k, t in enumerate(sentence) if t[0] == 'plain' and t[1] == gender]
                for selected in subsets(positions):
                    for c in child('CN', 'infinitive', cn):
                        for p in child('CT', 'infinitive', replaced(sentence, selected, index)):
                            add(('s3', c, index, p))

        if category in ('CT', 'CN', 'IV'):
            rule = {'CT': 's14', 'CN': 's15', 'IV': 's16'}[category]
            index = fresh_index(tokens)
            # Non-pronominal F10: insert one NP and replace later coindexed
            # occurrences by gendered pronouns. The first case is not printed.
            for start in range(len(tokens)):
                for end in range(start + 1, len(tokens) + 1):
                    alpha = tokens[start:end]
                    if len(alpha) == 1 and alpha[0][0] == 'index':
                        continue
                    if rank(alpha) >= rank(tokens):
                        continue
                    ps = child('NP', 'infinitive', alpha)
                    if not ps:
                        continue
                    gender, suffix = first_gender(alpha), tokens[end:]
                    positions = [k for k, t in enumerate(suffix) if t[0] == 'plain' and t[1] == gender]
                    for selected in subsets(positions):
                        tail = replaced(suffix, selected, index)
                        for case in (0, 1):
                            body = tokens[:start] + (('index', index, case),) + tail
                            for q in child(category, form, body):
                                for p in ps:
                                    add((rule, p, index, q))
            # A genuine bare-pronoun merge has at least two occurrences in
            # the result. Pure relabellings and unused-name loops are omitted;
            # their semantic normalization is a separate proof obligation.
            for previous in sorted({t[1] for t in tokens if t[0] == 'index'}):
                positions = [k for k, t in enumerate(tokens) if t[0] == 'index' and t[1] == previous]
                for selected in subsets(positions, proper=True):
                    body = replaced(tokens, selected, index)
                    for q in child(category, form, body):
                        add((rule, ('pronoun', previous), index, q))
        return tuple(sorted(found, key=repr))


def emit(tree):
    rule, *args = tree
    if rule == 'word':
        return f'(s1_word ({args[0]} {args[1]}))'
    if rule == 'name':
        return f'(s1_name {args[0]})'
    if rule == 'pronoun':
        return f'(s1_pronoun {args[0]})'
    if rule in ('be', 'necessarily'):
        return 's1_' + rule
    return '(' + rule + ' ' + ' '.join(emit(a) if isinstance(a, tuple) else str(a) for a in args) + ')'


def sentences():
    source = (HERE / 'Catalogue.v').read_text()
    body = source.split('Definition catalogue :', 1)[1].split('Example catalogue_surface_checks', 1)[0]
    out = [tuple(re.findall(r'"([^"]*)"', match)) for match in re.findall(r'\(\[([^\]]+)\],', body)]
    for definition in ('printed_try_wish', 'printed_wish_try'):
        match = re.search(r'Definition ' + definition + r' :=\s*\[([^\]]+)\]', source)
        out.append(tuple(re.findall(r'"([^"]*)"', match.group(1))))
    if len(out) != 20:
        raise ValueError('Expected exactly 20 registered strings')
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sentence', type=int, choices=range(1, 21))
    parser.add_argument('--policy', choices=('literal', 'amended'), default='amended')
    parser.add_argument('--limit', type=int, default=100000)
    parser.add_argument('--emit-coq', action='store_true')
    args = parser.parse_args()
    explorer = Explorer(args.policy, args.limit)
    for number, words in enumerate(sentences(), 1):
        if args.sentence and args.sentence != number:
            continue
        trees = set()
        for tokens in tokenize(words):
            trees.update(explorer.parse('CT', 'infinitive', tokens))
        if args.emit_coq:
            for index, tree in enumerate(sorted(trees, key=repr)):
                print(f'Definition witness_{number}_{index} := {emit(tree)}.')
                renderer = 'surface' if args.policy == 'literal' else 'amended_surface'
                text = ';'.join(json.dumps(w) for w in words)
                print(f'Example check_{number}_{index} : {renderer} witness_{number}_{index} = Some [{text}].')
                print('Proof. reflexivity. Qed.')
        else:
            print(json.dumps(dict(sentence=number, words=' '.join(words),
                                  discovered_witnesses=len(trees), cached_states=explorer.states,
                                  policy=args.policy, completeness_certified=False)), flush=True)


if __name__ == '__main__':
    main()
