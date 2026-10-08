// Exercise the built router and evidence rendering. Browser checks are separate.
const fs=require('node:fs');
const vm=require('node:vm');
const assert=require('node:assert/strict');
const html=fs.readFileSync(__dirname+'/index.html','utf8');
const blocks=[...html.matchAll(/<script\b([^>]*)>([\s\S]*?)<\/script>/gi)];
const data=JSON.parse(blocks.find(m=>/application\/json/.test(m[1]))[2]);
const app={innerHTML:''};
const context=vm.createContext({
  document:{getElementById:()=>({textContent:JSON.stringify(data)}),querySelector:()=>app,querySelectorAll:()=>[]},
  location:{hash:'#/'},window:{scrollTo(){}},addEventListener(){},localStorage:{getItem(){return null;}}
});
vm.runInContext(blocks.find(m=>!/application\/json/.test(m[1])&&m[2].trim())[2],context);
const run=s=>vm.runInContext(s,context);
const route=path=>{run(`location.hash=${JSON.stringify('#/'+path)};route()`);return app.innerHTML;};
for(const path of ['explore','experiment','result/witnesses','reading','papers','theories','plate','sources','comparison','edges','exhibits']){
  assert(!route(path).includes('Not on the map.'),path);
}
assert.equal((html.match(/data-r="(?:explore|compare|experiment|about)"/g)||[]).length,4);
assert(route('explore').includes(`${data.papers.length} sources`));
assert(route('experiment').includes('No API key needed'));
const key='atlas__witness_contract', result=route('result/witnesses');
for(const name of ['independent_inhabited','shared_empty','no_total_recovery']){
  const declaration=data.proof_sources[key].declarations.find(d=>d.name===`Packages.Separation.${name}`);
  assert(declaration&&declaration.status==='proved');
  assert(result.includes(`#/proof/${key}?line=${declaration.line}`));
}
assert(result.includes('id="witness-answer" class="witness-answer" hidden'));
assert(result.includes('does <strong>not</strong> show that TTR and MTT are equivalent'));
assert(result.includes('not an independent human review'));
assert(!result.includes('sk-or-'));
assert.equal(run("declarationURL('missing','x')"),null);
assert(route('result/unknown').includes('Not on the map.'));
run("D.revision='"+'a'.repeat(40)+"'");
assert(run('vWitnessResult()').includes('/blob/'+'a'.repeat(40)+'/atlas_data/audits/'));
run("D.revision='working copy'");
assert(run('vWitnessResult()').includes('/blob/main/atlas_data/audits/'));

const line=data.proof_sources[key].declarations.find(d=>d.name==='Packages.Separation.shared_empty').line;
const reader=route(`proof/${key}?line=${line}`);
for(const text of ['Find a declaration','Claim in the record','Compilation','Assumptions','Source correspondence','Recorded pass','Closed under the global context','Original audits never transfer'])assert(reader.includes(text),text);
assert(reader.includes(`#/edit/${key}?line=${line}`));
assert(reader.includes('Source SHA256'));
assert(reader.includes('id="proof-fallback"'));
assert(reader.includes('id="proof-editor" hidden'));
assert(reader.includes('aria-current="location"'));
assert(run(`vTheory('${key}')`).includes('#/result/witnesses'));

// Never promote missing audits, failed compiles or unresolved assumption queries.
run(`D.proof_sources['${key}'].audit.compile.ok=false`);
assert(run(`vProof('${key}',${line})`).includes('Recorded failure'));
assert(!run(`vProof('${key}',${line})`).includes('Closed under the global context'));
run(`D.proof_sources['${key}'].audit.compile.ok=true;D.proof_sources['${key}'].audit.assumptions.unresolved=['missing']`);
assert(!run(`vProof('${key}',${line})`).includes('Closed under the global context'));
run(`D.proof_sources['${key}'].audit=null`);
assert(run(`vProof('${key}',${line})`).includes('Not recorded'));
run(`byKey['${key}'].summary='<img src=x onerror=alert(1)>';byKey['${key}'].theorems[10].source_claim='<script>bad()</script>'`);
assert(!run(`vProof('${key}',${line})`).includes('<img src=x'));
assert(!run(`vProof('${key}',${line})`).includes('<script>bad()'));
// Missing proof support must not produce a fabricated guided-result link.
run(`D.proof_sources['${key}'].declarations=[]`);
assert(run('vWitnessResult()').includes('Not on the map.'));
console.log('Discovery routes, exact guided-proof links, provenance, reader audits and fail-closed rendering checked.');
