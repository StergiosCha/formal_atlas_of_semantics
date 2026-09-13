// Generated-script rendering with a minimal DOM; not a browser/integration test.
const fs = require('fs');
const path = require('path');
const vm = require('vm');
const assert = require('assert/strict');
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
  location: {hash: '#/papers'}, window: {scrollTo() {}}, addEventListener() {},
});
script.runInContext(context, {timeout: 5000});
const render = p => vm.runInContext(`paperOutcomeHTML(${JSON.stringify(p)})`, context);
const mismatched = 'Reviewed assessment differs from survey';
assert.equal((app.innerHTML.match(/<tr data-s=/g) || []).length, 230);
assert.equal((app.innerHTML.match(/>Source review pending</g) || []).length, 29);
assert(!app.innerHTML.includes('survey call disputed'));
assert(!app.innerHTML.includes(mismatched));
const heim = data.papers.find(p => p.id === 7);
const heimHTML = render(heim);
assert(heimHTML.includes('Source review pending'));
assert(heimHTML.includes('extras/FCS.v'));
assert(heimHTML.includes('extras/FCS2.v'));
assert(heimHTML.includes('Linked file assessments differ'));
assert(heimHTML.includes('no proved claims'));
assert(heimHTML.includes('not source verdicts'));
const discocat = render(data.papers.find(p => p.id === 159));
assert(discocat.includes('as_is'));
assert(!discocat.includes(mismatched));
assert(!render({...heim, prediction_disputed: true}).includes(mismatched));

// Synthetic reviewed state tests rendering only; not added to the registry.
const reviewed = {...heim, determination_status: 'reviewed', determination_actual: 'slight_modification',
  determination_review: {status: 'reviewed', paper_id: heim.id, source_citation: heim.citation,
    determination: 'slight_modification', scope: 'Test scope', coverage_justification: 'Test coverage',
    rationale: 'Test rationale', record_resolution: 'Test reconciliation',
    reviewer: 'Test reviewer', review_reference: 'Test reference'}};
assert(render(reviewed).includes(mismatched));
assert(render(reviewed).includes('Test scope'));
assert(!render({...reviewed, survey_determination: 'slight_modification'}).includes(mismatched));
for (const change of [{status: 'pending'}, {paper_id: 999}, {source_citation: 'Wrong source'},
                      {determination: 'unassessed'}]) {
  assert(!render({...reviewed, determination_review: {...reviewed.determination_review, ...change}}).includes(mismatched));
}
assert(!render({...reviewed, determination_actual: null}).includes(mismatched));

const attack = '<img src=x onerror=alert(1)>';
const hostile = JSON.parse(JSON.stringify(reviewed));
hostile.determination_review.scope = attack;
hostile.determination_review.reviewer = attack;
hostile.determination_candidates[0].rationale = attack;
hostile.determination_candidates[0].source_citations = [attack];
hostile.determination_candidates[0].file = attack;
hostile.determination_candidates[0].record_key = '\" onmouseover=alert(1)';
const escaped = render(hostile);
assert(!escaped.includes(attack));
assert(!escaped.includes('href="#/theory/" onmouseover'));
assert(escaped.includes('&lt;img src=x onerror=alert(1)&gt;'));

const theory = key => vm.runInContext(`vTheory(${JSON.stringify(key)})`, context);
assert(theory('atlas__discocat').includes('Recorded file assessment — not a reviewed source verdict'));
assert(theory('atlas__discocat').includes('Recorded source note — not independently confirmed here'));
assert(!theory('atlas__discocat').includes('Gap found in the published source'));
const indi = data.files.find(f => f.key === 'extras__indi');
assert.equal(typeof indi.source_gap, 'string');
assert(theory(indi.key).includes('None. The primary source is on disk in full'));
assert.equal(render({id: 999}), '');
console.log('230 papers, 29 pending reviews, retained candidates, review gating, source notes and escaping checked.');
