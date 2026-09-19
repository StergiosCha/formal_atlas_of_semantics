// Execute the generated site's real router. No browser or live Coq is claimed.
const fs = require('fs');
const path = require('path');
const vm = require('vm');
const assert = require('assert/strict');
const crypto = require('crypto');
const root = path.resolve(__dirname, '../..');
const html = fs.readFileSync(path.join(__dirname, 'index.html'), 'utf8');
const blocks = [...html.matchAll(/<script\b([^>]*)>([\s\S]*?)<\/script>/gi)];
const data = JSON.parse(blocks.find(m => /application\/json/.test(m[1]))[2]);
const script = new vm.Script(blocks.filter(m => !/application\/json/.test(m[1]) && m[2].trim())[0][2]);
const app = {innerHTML: ''};
const context = vm.createContext({
  document: {
    getElementById: () => ({textContent: JSON.stringify(data)}),
    querySelector: () => app, querySelectorAll: () => [],
  },
  location: {hash: '#/'}, window: {scrollTo() {}}, addEventListener() {},
  localStorage: {getItem() {return null;}},
});
script.runInContext(context, {timeout: 5000});
const run = s => vm.runInContext(s, context);
assert.equal(Object.keys(data.proof_sources).length, data.files.length);
for (const [key, source] of Object.entries(data.proof_sources)) {
  const raw = fs.readFileSync(path.join(root, source.path));
  assert.equal(raw.toString('utf8'), source.text);
  assert.equal(crypto.createHash('sha256').update(raw).digest('hex'), source.sha256);
  assert(run(`vTheory(${JSON.stringify(key)})`).includes(`href="#/proof/${key}"`));
}
const key = 'atlas__ttr_model';
const declaration = data.proof_sources[key].declarations.find(d => d.name === 'Countermodels.inhabited_conjuncts_empty_meet');
assert(declaration);
const url = `#/proof/${key}?line=${declaration.line}`;
assert(run(`vTheory('${key}')`).includes(`href="${url}"`));
run(`location.hash = ${JSON.stringify(url)}; route();`);
assert(app.innerHTML.includes('Full repository source'));
assert(app.innerHTML.includes('Proof.'));
assert(app.innerHTML.includes('Qed.'));
assert(app.innerHTML.includes('Recorded Print Assumptions: Closed under the global context'));
assert(app.innerHTML.includes(`id="coq-L${declaration.line}" class="proof-line selected"`));
assert(app.innerHTML.includes(/^[a-f0-9]{40}$/.test(data.revision || '')
  ? 'GitHub at this revision' : 'GitHub main (may differ)'));
assert(app.innerHTML.includes('Download .v'));

// Revision-pinned links in a CI build, explicit mismatch warning in a local build.
run("D.revision = 'working copy'");
assert(run(`vProof('${key}', ${declaration.line})`).includes('GitHub main (may differ)'));
run(`D.revision = '${'a'.repeat(40)}'`);
assert(run(`vProof('${key}', ${declaration.line})`).includes(`/blob/${'a'.repeat(40)}/atlas/ttr/TTR_Model.v#L${declaration.line}`));
assert(run(`vProof('${key}', -1)`).includes('id="coq-L1" class="proof-line selected"'));

// Every countermodel exhibit now links its actual named supporting declarations.
const exhibits = run('vExhibits()');
for (const e of run('CEX')) {
  assert(exhibits.includes(`Read full Coq proof: ${e.file}`));
  for (const name of e.thms) assert(run(`proofLink(${JSON.stringify(e.page)}, ${JSON.stringify(name)})`).includes('href='), name);
}

// Unknown and ambiguous identifiers stay text; do not manufacture a proof link.
run(`D.proof_sources.synthetic = {declarations:[{name:'A.same',line:1},{name:'B.same',line:2}]}`);
assert.equal(run("proofLink('synthetic','same')"), 'same');
assert.equal(run("proofLink('synthetic','invented')"), 'invented');
assert(run("proofLink('synthetic','A.same')").includes('?line=1'));
assert(!run(`proofAudit({audit:null}, {name:'x',status:'proved'})`).includes('Closed under'));
assert(run(`proofAudit({}, {status:'admitted'})`).includes('no completed proof'));
assert(run(`proofAudit({audit:{assumptions:{detail:{x:{raw:'Axioms: classic'}}}}}, {qualified:'x',status:'proved'})`).includes('Axioms: classic'));

// Raw source and hostile URL input remain inert markup.
context.attack = '<img src=x onerror=alert(1)>';
run(`D.proof_sources['${key}'].text = attack`);
const escaped = run(`vProof('${key}', attack)`);
assert(!escaped.includes('<img src=x'));
assert(escaped.includes('&lt;img src=x'));

// Download uses the bundled bytes, not a newly fetched or generated proof.
let blob, download;
context.Blob = class {constructor(parts) {blob = parts.join('');}};
context.URL = {createObjectURL() {return 'blob:test';}, revokeObjectURL() {}};
context.setTimeout = fn => fn();
context.document.createElement = () => ({click() {download = this.download;}, remove() {}});
context.document.body = {appendChild() {}};
run('downloadCoq()');
assert.equal(blob, context.attack);
assert.equal(download, 'TTR_Model.v');
console.log('All source hashes, proof routes, theorem links, recorded audits, escaping, revision links and .v downloads checked.');
