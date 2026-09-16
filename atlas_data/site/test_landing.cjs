// Generated-script rendering with a minimal DOM; not a browser/visual test.
const fs = require('fs');
const path = require('path');
const vm = require('vm');
const assert = require('assert/strict');
const root = path.resolve(__dirname, '../..');
const html = fs.readFileSync(path.join(__dirname, 'index.html'), 'utf8');
const blocks = [...html.matchAll(/<script\b([^>]*)>([\s\S]*?)<\/script>/gi)];
const data = JSON.parse(blocks.find(m => /application\/json/.test(m[1]))[2]);
const script = new vm.Script(blocks.filter(m => !/application\/json/.test(m[1]) && m[2].trim())[0][2]);
const app = {innerHTML: ''};
const context = vm.createContext({
  document: {
    getElementById: () => ({textContent: JSON.stringify(data)}),
    querySelector: () => app,
    querySelectorAll: () => [],
  },
  location: {hash: '#/'}, window: {scrollTo() {}}, addEventListener() {},
});
script.runInContext(context, {timeout: 5000});
const home = app.innerHTML;
assert(html.includes('<title>Formal Atlas of Semantics'));
assert(home.includes('What does formalization require?'));
assert(home.includes(`${data.papers.length}-source survey`));
assert(home.includes('P0–P5 describes intrinsic formality'));
assert(home.includes('F0–F5 records progress'));
assert(home.includes('explicitly scoped encodings'));
assert(home.includes('0 accepted source-level reviews recorded'));
assert(home.includes('href="#/reading"'));
assert(!home.includes('Every theory, on one map'));
assert(!home.includes('Every edge, machine-checked'));
assert(!home.includes('Levels of formalizability'));
assert(!home.includes('Four verdicts, not two'));

// Each featured result must lead to a record containing the named proved support.
const supports = {
  'ttr-meet': ['atlas__ttr_model', ['Countermodels.inhabited_conjuncts_empty_meet']],
  'heim-policies': ['atlas__heim1982_policies', [
    'local_global_domain_difference',
    'NegationModels.absent_king_local_true_global_false',
    'NegationModels.existing_king_same_truth_different_next_pronoun',
    'world_safe_is_strictly_more_permissive',
  ]],
  'dts-resolution': ['atlas__dts_resolution', [
    'substitution_preserves_typing', 'automatic_resolution_sound',
    'automatic_resolution_total_on_projection_contexts',
  ]],
};
for (const [id, [key, names]] of Object.entries(supports)) {
  assert(home.includes(`data-result="${id}" href="#/theory/${key}"`));
  const record = data.files.find(f => f.key === key);
  assert(record, key);
  assert(fs.existsSync(path.join(root, record.file)), record.file);
  for (const name of names) {
    assert(record.theorems.some(t => t.name === name && t.status === 'proved'), name);
  }
}

// Exercise routing, not just the standalone reading-page function.
vm.runInContext("location.hash = '#/reading'; route();", context);
const guide = app.innerHTML;
assert(guide.includes('Reading the atlas responsibly'));
assert(guide.includes('0 accepted source-level reviews are recorded'));
assert(guide.includes('LLM-assisted'));
assert(guide.includes('not independent human semantic review'));
assert(guide.includes('It is not framework equivalence'));
assert(guide.includes('without selecting a default'));
assert(guide.includes('filename/design heuristics'));
const atlasAdmissions = data.files.filter(f => f.file.startsWith('atlas/'))
  .reduce((sum, f) => sum + (f.counts?.admitted || 0), 0);
assert(guide.includes(`${data.stats.admitted - atlasAdmissions} in legacy material`));

// Counts should follow evidence rather than a hard-coded landing-page snapshot.
vm.runInContext(`D.papers.push({id: 'test-only', determination_status: 'reviewed'});
  totals.papers = D.papers.length;
  totals.sourceReviews = D.papers.filter(hasReviewedSourceOutcome).length;`, context);
assert(vm.runInContext('vHome()', context).includes(`${data.papers.length + 1}-source survey`));
assert(vm.runInContext('vReading()', context).includes('0 accepted source-level reviews'));
vm.runInContext(`Object.assign(D.papers[D.papers.length - 1], {
  citation: 'Synthetic source', determination_actual: 'as_is',
  determination_review: {status: 'reviewed', paper_id: 'test-only',
    source_citation: 'Synthetic source', determination: 'as_is'}
});
totals.sourceReviews = D.papers.filter(hasReviewedSourceOutcome).length;`, context);
assert(vm.runInContext('vReading()', context).includes('1 accepted source-level reviews'));

// Documentation links must resolve in this checkout, including retained campaign history.
for (const rel of ['README.md', 'atlas_data/READING_THE_ATLAS.md', 'CONTRIBUTING.md']) {
  const filename = path.join(root, rel);
  const markdown = fs.readFileSync(filename, 'utf8');
  for (const match of markdown.matchAll(/\[[^\]]+\]\(([^)]+)\)/g)) {
    const target = match[1];
    if (/^https?:\/\//.test(target)) continue;
    const local = target.split('#')[0];
    assert(fs.existsSync(path.resolve(path.dirname(filename), local)), `${rel}: ${target}`);
  }
}
const readme = fs.readFileSync(path.join(root, 'README.md'), 'utf8');
assert(readme.startsWith('# Formal Atlas of Semantics\n'));
assert(readme.indexOf('## Selected checked results') < readme.indexOf('## Original paper companion'));
assert(readme.includes('No accepted source-level reviews'));
assert(readme.includes('make -f Makefile.coq'));
assert(!readme.includes('8.16 or later'));
assert(fs.readFileSync(path.join(root, '.github/workflows/verify.yml'), 'utf8')
  .includes('coqorg/coq:8.20.1'));
console.log('Landing/reading routes, scoped result links, review/admission counts and documentation links checked.');
