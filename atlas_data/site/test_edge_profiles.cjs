// Generated-script rendering, not a browser or semantic-fidelity review.
const fs = require('fs');
const path = require('path');
const vm = require('vm');
const assert = require('assert/strict');
const html = fs.readFileSync(path.join(__dirname, 'index.html'), 'utf8');
const blocks = [...html.matchAll(/<script\b([^>]*)>([\s\S]*?)<\/script>/gi)];
const data = JSON.parse(blocks.find(m => /application\/json/.test(m[1]))[2]);
const script = new vm.Script(blocks.filter(m => !/application\/json/.test(m[1]) && m[2].trim())[0][2]);
const app = {innerHTML: ''};
const context = vm.createContext({document: {
  getElementById: () => ({textContent: JSON.stringify(data)}),
  querySelector: () => app, querySelectorAll: () => [],
}, location: {hash: '#/edges'}, window: {scrollTo() {}}, addEventListener() {}});
script.runInContext(context, {timeout: 5000});
const run = s => vm.runInContext(s, context);
assert(app.innerHTML.includes('9 scoped comparison profiles'));
assert(!app.innerHTML.includes('<th class="n">Similarity</th>'));
assert(app.innerHTML.includes('No Coq bridge yet'));
for (const e of data.edges) {
  run(`location.hash = '#/edge/${e._key}'; route()`);
  const page = app.innerHTML;
  assert(page.includes('Declared comparison'));
  assert(page.includes('Theory-level relation: unassessed'));
  assert(page.includes('Theory-level comparison obligations'));
  assert(page.includes('Editorial restatement'));
  const history = page.indexOf('<details class="block" data-legacy-scores>');
  assert(history > 0);
  assert(!page.slice(0, history).includes('Historical mean:'));
  assert(page.slice(history).includes('Historical mean:'));
  for (const s of e._profile.support) {
    assert(page.includes(`href="#/proof/${s.record_key}"`));
    for (const name of Object.keys(s.theorems)) {
      const link = run(`proofLink('${s.record_key}', ${JSON.stringify(name)})`);
      assert(link.includes('?line='), name);
      assert(page.includes(link), name);
    }
  }
}
const ttr = run("vEdge('ttr__mtt')");
assert(ttr.includes('subject projection only'));
assert(ttr.includes('external-type-assignments'));
assert(run("vEdge('ptq__mtt')").includes('not a mechanized impossibility result'));
const plate = run('plateSVG()');
assert(plate.includes('Layout is not a distance measure'));
assert(!plate.includes('measured similarity'));
assert(!plate.includes('class="etag"'));
// Retired scores cannot affect graph geometry, widths, opacity or labels.
run('edges.forEach(e => {e._legacy_scores.similarity = 999; e._legacy_scores.overlap = -999;})');
assert.equal(run('plateSVG()'), plate);
const region = run("vRegion('mtt')");
assert(!region.includes('999'));
assert(!run("vTheory('atlas__mtt')").includes('999'));
context.attack = '<img src=x onerror=alert(1)>';
run("edges[0]._profile.scope = attack");
assert(!run('vEdges()').includes(context.attack));
assert(run('vEdges()').includes('&lt;img'));
run("delete edges[0]._profile");
assert(run(`vEdge('${data.edges[0]._key}')`).includes('No comparison profile recorded'));
console.log('Nine profiles, actual proof links, unassessed obligations, retired scores, unweighted graph and escaping checked.');
