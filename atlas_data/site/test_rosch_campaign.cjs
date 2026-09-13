// Actual generated page with a minimal DOM stub, not a visual browser test.
const fs = require('fs');
const path = require('path');
const vm = require('vm');
const assert = require('assert/strict');
const html = fs.readFileSync(path.join(__dirname, 'index.html'), 'utf8');
const blocks = [...html.matchAll(/<script\b([^>]*)>([\s\S]*?)<\/script>/gi)];
const data = JSON.parse(blocks.find(m => /application\/json/.test(m[1]))[2]);
const scripts = blocks.filter(m => !/application\/json/.test(m[1]) && m[2].trim());
assert.equal(scripts.length, 1);
const rec = data.files.find(f => f.key === 'atlas__pilots__rosch1978');
assert(rec);
assert.equal(rec.assessment_status, 'pilot');
assert.equal(rec.determination, 'unassessed');
assert.equal(rec.counts.proved, 25);
assert.equal(rec.probe.trivial, 5);
assert.equal(rec.probe.vacuous, 0);
assert.equal(rec.verify, null);
const paper = data.papers.find(p => String(p.id) === '122');
assert.equal(paper.level, 'F3');
assert.equal(paper.formality, 1);
assert.equal(paper.determination_actual, null);
assert(paper.coq_present.includes(rec.file));
for (const id of ['101', '196']) {
  assert.equal(data.papers.find(p => String(p.id) === id).level, 'F1');
}
const app = {innerHTML: ''};
const context = vm.createContext({
  document: {
    getElementById: () => ({textContent: JSON.stringify(data)}),
    querySelector: selector => { assert.equal(selector, '#app'); return app; },
    querySelectorAll: () => [],
  },
  location: {hash: '#/theory/atlas__pilots__rosch1978'},
  window: {scrollTo() {}},
  addEventListener() {},
});
new vm.Script(scripts[0][2]).runInContext(context, {timeout: 5000});
assert(app.innerHTML.includes('unassessed'));
assert(app.innerHTML.includes('R2-03 and R2-04 fragments only'));
assert(app.innerHTML.includes('Does not derive a basic level'));
for (const theorem of rec.theorems) assert(app.innerHTML.includes(theorem.name));
const papers = vm.runInContext("vPapers({level:'F3'})", context);
assert(papers.includes('Rosch1978.v'));
console.log('Rosch rendered as P1/F3 unassessed; 25 theorem mappings and probe flags present; Hobbs/Spivak remain F1.');
