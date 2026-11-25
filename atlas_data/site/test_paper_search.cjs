// Test the search over the built site, including citations missing from the survey.
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
const assert = require('node:assert/strict');

const html = fs.readFileSync(path.join(__dirname, 'index.html'), 'utf8');
const blocks = [...html.matchAll(/<script\b([^>]*)>([\s\S]*?)<\/script>/gi)];
const data = JSON.parse(blocks.find(m => m[1].includes('application/json'))[2]);
const source = blocks.find(m => !m[1].includes('application/json') && m[2].trim())[2];
const elements = new Map();
function element(selector) {
  if (!elements.has(selector)) elements.set(selector, {innerHTML: '', value: ''});
  return elements.get(selector);
}
const context = vm.createContext({
  document: {getElementById: () => ({textContent: JSON.stringify(data)}), querySelector: element, querySelectorAll: () => []},
  location: {hash: '#/papers?q=Sp%C3%A1thas'}, window: {scrollTo() {}}, addEventListener() {},
  history: {replaceState(_s, _t, url) { context.location.hash = url; }}, URLSearchParams,
});
vm.runInContext(source, context);
const list = query => vm.runInContext('searchWorkList(' + JSON.stringify(query) + ')', context);
const links = [
  ['Greek Focus Operators and Their Associates', '#/proof/extras__additive'],
  ['Polydefinites as Markers of Prominence', '#/proof/extras__PolydefiniteSemantics'],
  ['Bisyndetic Distributive Conjunction', '#/research/greek-double-ke'],
];
for (const query of ['Spathas', 'SPÁTHAS', 'giorgos spathas']) {
  const results = list(query);
  assert.equal((results.match(/<li /g) || []).length, 3);
  for (const [title, href] of links) {
    assert(results.includes(title));
    assert(results.includes('href="' + href + '"'));
  }
}
assert(element('#app').innerHTML.includes('value="Spáthas"'));
assert(list('prominence Spathas').includes('PolydefiniteSemantics.v'));
assert(list('Gallin Ty2').includes('#/research/gallin'));
assert(list('Retore').includes('Retoré'));
assert(list('Sutton individuation').includes('research/ttr-mtt-montague/index.html#sources'));
assert(list('xxxxnotaworkxxxx').includes('No matching works'));
element('#pq').value = 'Spathas';
vm.runInContext('pFilter()', context);
assert.equal(context.location.hash, '#/papers?q=Spathas');
assert(element('#work-results').innerHTML.includes('PolydefiniteSemantics.v'));
vm.runInContext("sourceFilter('Spathas')", context);
assert.equal(element('#registry-paper-link').href, '#/papers?q=Spathas');
assert(element('#registry-work-results').innerHTML.includes('Greek Focus Operators'));
assert(!list('<img src=x onerror=x>').includes('<img'));

for (const record of data.files) {
  for (const {citation} of record.sources) {
    if (citation.startsWith('None. Helper definitions only')) continue;
    const indexed = data.paper_index.some(work =>
      [work.citation, ...work.aliases].includes(citation.trim()) &&
      work.links.some(link => link.href === '#/proof/' + record.key));
    assert(indexed, 'Missing cited work or proof link: ' + record.key + ' / ' + citation);
  }
}
for (const supplement of data.source_registry.supplementary_sources) {
  assert(data.paper_index.some(work => [work.citation, ...work.aliases].includes(supplement.citation) &&
    work.links.some(link => link.href === '#/sources?entry=' + supplement.supplement_id)));
}
// A new standalone Rocq study must have a discoverable source before it is deployed.
const researchDir = path.resolve(__dirname, '../../research');
const studyLinks = {
  'greek-double-ke': '#/research/greek-double-ke',
  'ttr-mtt-montague': 'research/ttr-mtt-montague/index.html#sources',
  'ttr-set-types': '#/proof/ttr_mtt__TTR_types',
};
for (const entry of fs.readdirSync(researchDir, {withFileTypes: true})) {
  if (!entry.isDirectory()) continue;
  const files = fs.readdirSync(path.join(researchDir, entry.name), {recursive: true});
  if (!files.some(name => name.endsWith('.v'))) continue;
  assert(data.paper_index.some(work => work.links.some(link => link.href === studyLinks[entry.name])),
    'Missing paper search coverage for research/' + entry.name);
}
const byPath = new Map(Object.entries(data.proof_sources).map(([key, s]) => [s.path, key]));
for (const paper of data.papers) {
  assert.deepEqual(paper.coq_present, paper.coq_files.filter(f => byPath.has(f)));
}
for (const work of data.paper_index) {
  for (const {href} of work.links) {
    if (href.startsWith('#/proof/')) assert(data.proof_sources[href.slice(8)], href);
    if (href.startsWith('#/research-proof/')) assert(data.research.sources[href.slice(17)], href);
    if (!href.startsWith('#')) {
      const [filename, anchor] = href.split('#');
      const page = fs.readFileSync(path.join(__dirname, filename), 'utf8');
      assert(page.includes('id="' + anchor + '"'), href);
    }
  }
}
console.log('All implementation citations, supplements, proof links, survey paths and Spathas searches checked.');
