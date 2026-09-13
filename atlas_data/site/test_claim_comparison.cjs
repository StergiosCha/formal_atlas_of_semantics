// Render the actual generated script with a minimal DOM stub. Not a browser test.
const fs = require('fs');
const path = require('path');
const vm = require('vm');
const assert = require('assert/strict');
const html = fs.readFileSync(path.join(__dirname, 'index.html'), 'utf8');
const blocks = [...html.matchAll(/<script\b([^>]*)>([\s\S]*?)<\/script>/gi)];
const data = JSON.parse(blocks.find(m => /application\/json/.test(m[1]))[2]);
const scripts = blocks.filter(m => !/application\/json/.test(m[1]) && m[2].trim());
assert.equal(scripts.length, 1);
const script = new vm.Script(scripts[0][2]);

function renderContext(payload) {
  const app = {innerHTML: ''};
  const context = vm.createContext({
    document: {
      getElementById: () => ({textContent: JSON.stringify(payload)}),
      querySelector: selector => { assert.equal(selector, '#app'); return app; },
      querySelectorAll: () => [],
    },
    location: {hash: '#/comparison'},
    window: {scrollTo() {}},
    addEventListener() {},
  });
  script.runInContext(context, {timeout: 5000});
  return {app, context};
}

const {app, context} = renderContext(data);
assert(app.innerHTML.includes('What transfers from a source into Coq?'));
assert(app.innerHTML.includes('not a success rate'));
assert(app.innerHTML.includes('not tested'));
let targets = 0;
for (const profile of data.claim_comparison.profiles) {
  assert(app.innerHTML.includes(profile.label));
  const recordHTML = vm.runInContext(`vTheory(${JSON.stringify(profile.record_key)})`, context);
  assert(recordHTML.includes('Claim-level evidence:'));
  assert(recordHTML.includes('source determination withheld'));
  for (const t of profile.targets) {
    targets++;
    assert(recordHTML.includes(`<b>${t.id}</b>`));
    for (const name of t.evidence) assert(recordHTML.includes(name));
  }
}
assert.equal(targets, 27);
const papersHTML = vm.runInContext("vPapers({level:'F3'})", context);
assert.equal((papersHTML.match(/>claim profile<\/a>/g) || []).length, 5);
assert(vm.runInContext("vTheory('atlas__ptq')", context).includes('Definitions mapped'));

const hostile = JSON.parse(JSON.stringify(data));
hostile.claim_comparison.profiles[0].targets[0].source_claim = '<img src=x onerror=alert(1)>';
const escaped = renderContext(hostile).app.innerHTML;
assert(!escaped.includes('<img src=x onerror='));
assert(escaped.includes('&lt;img src=x onerror=alert(1)&gt;'));

const absent = JSON.parse(JSON.stringify(data));
delete absent.claim_comparison;
assert(renderContext(absent).app.innerHTML.includes('No claim comparison recorded.'));
console.log('Comparison route, five theory views, F3 links, 27 targets, escaping and legacy fallback checked.');
