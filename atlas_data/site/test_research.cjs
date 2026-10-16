// Exercise the real generated router and the independently bundled research.
const fs=require('fs'), path=require('path'), vm=require('vm');
const assert=require('assert/strict'), crypto=require('crypto');
const root=path.resolve(__dirname,'../..');
const html=fs.readFileSync(path.join(__dirname,'index.html'),'utf8');
const blocks=[...html.matchAll(/<script\b([^>]*)>([\s\S]*?)<\/script>/gi)];
const data=JSON.parse(blocks.find(m=>/application\/json/.test(m[1]))[2]);
const script=new vm.Script(blocks.filter(m=>!/application\/json/.test(m[1])&&m[2].trim())[0][2]);
const app={innerHTML:''};
const context=vm.createContext({document:{getElementById:()=>({textContent:JSON.stringify(data)}),
  querySelector:()=>app,querySelectorAll:()=>[]},location:{hash:'#/'},
  window:{scrollTo(){}},addEventListener(){}});
const run=s=>vm.runInContext(s,context);
script.runInContext(context,{timeout:5000});
assert(html.includes('href="#/research" data-r="research"'));
assert(app.innerHTML.includes('New: source-first Montague research'));
const before=run('JSON.stringify([D.files,D.papers,D.edges,D.stats,D.workspace_library_sha256])');
run("location.hash='#/research';route()");
assert(app.innerHTML.includes('Montague, from source to proof.'));
assert(app.innerHTML.includes('Independent semantic review pending'));
assert(app.innerHTML.includes('Whole-search completeness is unproved'));
assert(app.innerHTML.includes('Live execution of these new packages is not enabled'));
assert(!app.innerHTML.includes('href="#/edit/research__'));
assert.equal(Object.keys(data.research.sources).length,53);
assert.equal(data.research.packages.length,3);
for(const [key,source] of Object.entries(data.research.sources)){
  assert(!data.proof_sources[key]);
  assert(app.innerHTML.includes(`href="#/research-proof/${key}"`),key);
  assert.equal(source.text,fs.readFileSync(path.join(root,source.path),'utf8'));
  assert.equal(source.sha256,crypto.createHash('sha256').update(source.text).digest('hex'));
}
for(const feature of data.research.features){
  run(`location.hash=${JSON.stringify(`#/research-proof/${feature.key}?line=${feature.line}`)};route()`);
  assert(app.innerHTML.includes(feature.name));
  assert(app.innerHTML.includes(`id="coq-L${feature.line}" class="proof-line selected"`));
  assert(app.innerHTML.includes('Proof.'));
  assert(app.innerHTML.includes('Download .v'));
  assert(app.innerHTML.includes('no global axiom dependencies for this theorem'));
  assert(app.innerHTML.includes('Explicit model and theorem premises still apply'));
  assert(!app.innerHTML.includes('Edit and run in Coq'));
  assert(!app.innerHTML.includes('href="#/theory/research__'));
}
const legacyKey='research__montague_legacy__LegacyTranslation';
const legacy=data.research.sources[legacyKey];
const decl=legacy.declarations.find(d=>d.name==='legacy_open_preservation');
assert(run(`vProof('${legacyKey}',${decl.line})`).includes('LegacyPTQ.PTQ_deep2'));
run("D.revision='"+'a'.repeat(40)+"'");
assert(run('vResearch()').includes(`/blob/${'a'.repeat(40)}/deep/montague_ptq/SOURCE_MAP.md`));
for(const key of ['missing','__proto__','constructor']){
  run(`location.hash='#/research-proof/${key}';route()`);
  assert(!app.innerHTML.includes('reader-codebar'));
}
const key=data.research.features[0].key;
run(`D.research.sources['${key}'].text='<img src=x onerror=alert(1)>'`);
const escaped=run(`vProof('${key}',1)`);
assert(escaped.includes('&lt;img src=x'));
assert(!escaped.includes('<img src=x'));
let blob,download;
context.Blob=class{constructor(parts){blob=parts.join('');}};
context.URL={createObjectURL(){return 'blob:test'},revokeObjectURL(){}};
context.setTimeout=fn=>fn();
context.document.createElement=()=>({click(){download=this.download},remove(){}});
context.document.body={appendChild(){}};
run(`location.hash='#/research-proof/${key}?line=1';downloadCoq()`);
assert.equal(blob,'<img src=x onerror=alert(1)>');
assert.equal(download,'Meaning.v');
assert.equal(run('JSON.stringify([D.files,D.papers,D.edges,D.stats,D.workspace_library_sha256])'),before);
console.log('Research routes, 53 source hashes, proof/dependency links, downloads and isolation from atlas/live library checked.');
