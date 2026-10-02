/* Private-copy editor. Coq responses and AI explanations are separate channels. */
(function (root) {
  'use strict';
  const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
  const DEFAULT_API = 'https://formal-atlas-coq-crete.westus2.cloudapp.azure.com';
  const LEGACY_API = 'https://atlas-checker.greenrock-e642001f.westus2.azurecontainerapps.io';
  let active = null;
  const storage = {
    get(k) {try {return root.localStorage.getItem(k);} catch (_) {return null;}},
    set(k,v) {try {root.localStorage.setItem(k,v); return true;} catch (_) {return false;}}
  };
  function endpoint(value) {
    const url = new URL(value);
    if (url.username || url.password || url.search || url.hash ||
        !(url.protocol === 'https:' || (url.protocol === 'http:' && ['localhost','127.0.0.1'].includes(url.hostname)))) {
      throw new Error('Use an HTTPS backend, or localhost for development, without credentials or query parameters.');
    }
    return url.href.replace(/\/$/, '');
  }
  function keyHeaders(value) {
    const key=String(value||'').trim();
    if(!key) throw new Error('Enter your OpenRouter API key in the key field.');
    if(key.length>512 || !/^sk-or-[A-Za-z0-9_-]+$/.test(key)) throw new Error('Invalid OpenRouter API key format.');
    return {'X-OpenRouter-Key':key};
  }
  function defaultBackend() {
    const saved=storage.get('atlas_api');
    return !saved || saved.replace(/\/$/,'')===LEGACY_API ? DEFAULT_API : saved;
  }
  function sentenceEnds(code) {
    // Navigation only. Coq itself parses and validates the resulting prefix.
    const ends = []; let comment = 0, quoted = false;
    for (let i=0; i<code.length; i++) {
      if (comment) {
        if (code.slice(i,i+2)==='(*') {comment++; i++;}
        else if (code.slice(i,i+2)==='*)') {comment--; i++;}
      } else if (quoted) {
        if (code[i]==='"') {if (code[i+1]==='"') i++; else quoted=false;}
      } else if (code.slice(i,i+2)==='(*') {comment=1; i++;}
      else if (code[i]==='"') quoted=true;
      else if (code[i]==='.' && (i+1===code.length || /\s/.test(code[i+1]) || code.slice(i+1,i+3)==='(*')) ends.push(i+1);
    }
    return ends;
  }
  function lineOffset(code, line) {
    let pos=0; for (let i=1; i<line; i++) {const n=code.indexOf('\n',pos); if(n<0)return code.length; pos=n+1;} return pos;
  }
  function codepoints(code, offset) {return Array.from(code.slice(0,offset)).length;}
  function patch(path, original, edited) {
    const lines = s => s ? (s.endsWith('\n') ? s.slice(0,-1).split('\n') : s.split('\n')) : [];
    const before=lines(original), after=lines(edited);
    const body=(xs,prefix,text)=>xs.map(x=>prefix+x).join('\n')+(xs.length?'\n':'')+
      (xs.length&&!text.endsWith('\n')?'\\ No newline at end of file\n':'');
    if (original===edited) return '';
    return `--- a/${path}\n+++ b/${path}\n@@ -${before.length?1:0},${before.length} +${after.length?1:0},${after.length} @@\n`+
      body(before,'-',original)+body(after,'+',edited);
  }
  function render(source,key) {
    return `<div class="wrap live-workspace"><div class="crumb"><a href="#/proof/${encodeURIComponent(key)}">Original proof and recorded audit</a> / Editable copy</div>
      <section><h2>Work with Coq: ${esc(source.path)}</h2>
      <p>Edit the actual file, step through commands and inspect Coq's goals. Imports use the checker's precompiled atlas.
      This is your copy, not a change to the published library.</p>
      <p class="tiny dim">Drafts are saved in this browser for this source version. Check sends your code to the displayed backend.
      Explain sends the current file and question to that backend; only your selection and nearby context go to the model.</p>
      <div class="controls live-connect"><label>Checker backend <input id="live-api" type="url" value="${esc(defaultBackend())}"></label>
        <button class="btn ghost" id="live-connect">Connect</button><span id="live-connection" role="status">Not connected. No code or question has been sent.</span></div>
      <div class="live-grid"><div class="live-editor-pane">
        <div class="controls live-toolbar"><button class="btn ghost" id="live-back">Previous</button><button class="btn ghost" id="live-next">Next command</button>
        <button class="btn ghost" id="live-cursor">Check to cursor</button><button class="btn" id="live-file">Compile full copy</button></div>
        <label class="tiny" for="live-code">Editable Coq source</label>
        <textarea id="live-code" class="live-code" spellcheck="false" autocapitalize="off" autocomplete="off" aria-describedby="live-copy-status">${esc(source.text)}</textarea>
        <p id="live-copy-status" class="tiny" role="status">Original bytes loaded. This session has not checked them.</p>
        <div class="controls"><button class="btn ghost" id="live-download">Download edited .v</button>
        <button class="btn ghost" id="live-patch">Download review patch</button><button class="btn ghost" id="live-reset">Restore original</button></div>
        <p class="tiny dim">A patch is a proposal, not approval. Submit it through a <a href="https://github.com/StergiosCha/formal_atlas_of_semantics/pulls" target="_blank" rel="noopener noreferrer">GitHub pull request</a> for maintainer review. Nothing is submitted automatically.</p>
      </div><aside class="live-panels">
        <div class="block"><h3>Coq goals and diagnostics</h3><p id="live-check-status" class="small" role="status">Not checked in this session.</p>
        <pre id="live-output" class="live-output" aria-live="polite">Use Next command, Check to cursor, or Compile full copy.</pre>
        <p class="tiny dim">Each check replays in a fresh isolated Coq 8.20.1 process. Prefix checks can leave open goals.
        Compilation may accept admissions or added assumptions; it is not a source-fidelity verdict. Edited imports and downstream dependents are not rebuilt.</p></div>
        <div class="block"><h3>Explain this part</h3><p class="tiny dim">Select code in the editor, then ask a question. The assistant cannot run Coq, modify your file or approve it.</p>
        <label class="tiny">OpenRouter model <select id="live-model"><option value="gpt-6-astra">openai/gpt-6-astra (connect to check roster)</option></select></label>
        <label class="tiny" for="live-key">Your OpenRouter API key</label>
        <input id="live-key" type="password" autocomplete="off" spellcheck="false" autocapitalize="off" maxlength="512" placeholder="sk-or-...">
        <button class="btn ghost" id="live-clear-key" type="button">Clear key</button>
        <p class="tiny dim">Your OpenRouter account pays for model calls. The key is sent to the displayed backend only when you click Explain, then used to call OpenRouter. It is not saved by the app and clears on reload or navigation. Only use a backend you trust.</p>
        <p id="live-selection" class="tiny">No selection.</p><label class="tiny" for="live-question">Question about the selection</label>
        <textarea id="live-question" rows="3" placeholder="What does this theorem actually establish, and which assumptions does it need?"></textarea>
        <button class="btn ghost" id="live-explain">Explain selection</button><p id="live-explain-status" class="tiny" role="status">Optional. No model call yet.</p>
        <pre id="live-explanation" class="live-explanation" aria-live="polite"></pre>
        <p class="tiny dim">AI explanation, not a checked proof. Treat any suggested code as unverified. Coq checks do not need or receive your key.</p></div>
      </aside></div></section></div>`;
  }
  function dispose() {
    if (active) {active.requests.forEach(c=>c.abort()); active=null;}
  }
  function mount(source,key,data,line) {
    dispose();
    const el=id=>root.document.getElementById('live-'+id), editor=el('code');
    if (!editor) return;
    const state={requests:new Set(),generation:0,processed:0,ready:false,busy:false}; active=state;
    const draftKey='atlas-edit-v1:'+key+':'+source.sha256;
    const draft=storage.get(draftKey);
    editor.value=draft===null?source.text:draft;
    const valid=()=>active===state;
    const status=(id,text)=>{if(valid())el(id).textContent=text;};
    const currentAPI=()=>endpoint(el('api').value.trim());
    function changed() {
      state.generation++; state.processed=0;
      const saved=storage.set(draftKey,editor.value);
      status('copy-status',(editor.value===source.text?'Original source bytes.':'Edited private copy; original audit does not apply.')+
        (saved?' Saved in this browser.':' Browser storage unavailable; download to retain your work.'));
      status('check-status','Current copy not checked. Previous results, if shown, belong to an earlier snapshot.');
      if(el('explanation').textContent) status('explain-status','Explanation below concerns an earlier snapshot, not this edit.');
    }
    function selection() {
      const a=editor.selectionStart,b=editor.selectionEnd;
      status('selection',a===b?'No selection.':`Selected lines ${editor.value.slice(0,a).split('\n').length} to ${editor.value.slice(0,b).split('\n').length}.`);
    }
    editor.addEventListener('input',changed);
    ['select','keyup','mouseup'].forEach(event=>editor.addEventListener(event,selection));
    async function request(path,body,timeout=35000,headers={}) {
      const controller=new AbortController(); state.requests.add(controller);
      const timer=setTimeout(()=>controller.abort(),timeout);
      try {
        const response=await fetch(currentAPI()+path,{method:body?'POST':'GET',credentials:'omit',redirect:'error',signal:controller.signal,
          ...(body?{headers:{'content-type':'application/json',...headers},body:JSON.stringify(body)}:{})});
        let value; try {value=await response.json();} catch (_) {throw new Error('Backend did not return workspace JSON. It may need updating.');}
        if(!response.ok) throw new Error(typeof value.detail==='string'?value.detail:`Backend HTTP ${response.status}`);
        return value;
      } finally {clearTimeout(timer);state.requests.delete(controller);}
    }
    el('api').addEventListener('input',()=>{state.ready=false;state.generation++;status('connection','Backend changed. Connect before checking.');});
    el('connect').onclick=async()=>{
      const backend=el('api').value; state.ready=false;
      status('connection','Checking sandbox, compiler version and library snapshot...');
      try {
        const cap=await request('/workspace/capabilities');
        if(!valid() || el('api').value!==backend)return;
        if(cap.library_sha256!==data.workspace_library_sha256) throw new Error('Checker and site library snapshots differ. Backend update required.');
        storage.set('atlas_api',currentAPI());
        state.ready=cap.available===true && cap.coq_version==='8.20.1';
        status('connection',state.ready?`Connected: Coq ${cap.coq_version}, ${cap.sandbox}. Library snapshot matches.`:`Live checking unavailable: ${cap.error||'Coq 8.20.1 sandbox required'}.`);
        const roster=await request('/models');
        if(!valid() || el('api').value!==backend)return;
        const models=roster.models.filter(m=>typeof m.deployment==='string'&&!/claude/i.test(m.deployment));
        el('model').innerHTML=models.map(m=>`<option value="${esc(m.deployment)}"${m.deployment==='gpt-6-astra'?' selected':''}>${esc(m.model||m.deployment)}</option>`).join('');
      } catch(error) {if(valid() && el('api').value===backend){state.ready=false;status('connection',error.message);}}
    };
    const sourceRequest=code=>({path:source.path,source_sha256:source.sha256,library_sha256:data.workspace_library_sha256,code});
    async function check(mode,cursor) {
      if(state.busy)return;
      if(!state.ready){status('check-status','Connect to a matching, sandbox-enabled checker first.');return;}
      const code=editor.value, generation=state.generation; state.busy=true;
      ['back','next','cursor','file'].forEach(id=>el(id).disabled=true);
      status('check-status',mode==='file'?'Compiling this copy...':'Replaying the selected prefix...');
      try {
        const result=await request('/workspace/check',{...sourceRequest(code),mode,cursor:codepoints(code,cursor)});
        if(!valid())return;
        status('output',result.output||'(Coq returned no diagnostics.)');
        if(state.generation!==generation || editor.value!==code){status('check-status','Result is stale: you edited while Coq was running. Current copy is not checked.');return;}
        const hash=Array.from(new Uint8Array(await root.crypto.subtle.digest('SHA-256',new TextEncoder().encode(code)))).map(x=>x.toString(16).padStart(2,'0')).join('');
        if(!valid())return;
        if(state.generation!==generation || result.code_sha256!==hash || result.library_sha256!==data.workspace_library_sha256) {
          status('check-status','Snapshot mismatch. No check is attributed to the current copy.'); return;
        }
        if(result.ok===true) {
          state.processed=cursor;
          status('check-status',mode==='file'?'This copy compiled in Coq 8.20.1. Original audits and source approval do not transfer.':
            `Coq accepted the prefix through line ${code.slice(0,cursor).split('\n').length}. Open goals may remain.`);
          editor.setSelectionRange(cursor,cursor);
        } else status('check-status',result.timeout?'Coq timed out. This copy is not checked.':'Coq reported an error. This copy is not checked.');
        if(result.truncated) status('output','[Earlier output truncated]\n'+result.output);
      } catch(error) {status('check-status',error.name==='AbortError'?'Timed out waiting for Coq. No successful check claimed.':error.message);}
      finally {state.busy=false;if(valid())['back','next','cursor','file'].forEach(id=>el(id).disabled=false);}
    }
    el('next').onclick=()=>check('prefix',sentenceEnds(editor.value).find(n=>n>state.processed)??editor.value.length);
    el('back').onclick=()=>check('prefix',sentenceEnds(editor.value).filter(n=>n<state.processed).pop()??0);
    el('cursor').onclick=()=>check('prefix',editor.selectionEnd);
    el('file').onclick=()=>check('file',editor.value.length);
    el('key').value='';
    el('clear-key').onclick=()=>{el('key').value='';status('explain-status','Key cleared. An already-sent request may still finish.');};
    el('explain').onclick=async()=>{
      const start=editor.selectionStart,end=editor.selectionEnd,code=editor.value,generation=state.generation;
      if(start===end){status('explain-status','Select the code you want explained first.');return;}
      const question=el('question').value.trim()||'Explain this selection, its premises and what it does and does not establish.';
      const model=el('model').value;
      const selectionLines=`lines ${code.slice(0,start).split('\n').length} to ${code.slice(0,end).split('\n').length}`;
      el('explain').disabled=true;status('explain-status',`Asking ${model}. This is not a Coq check...`);
      try {
        const headers=keyHeaders(el('key').value);
        const result=await request('/workspace/explain',{...sourceRequest(code),start:codepoints(code,start),end:codepoints(code,end),question,model},100000,headers);
        if(!valid())return;
        status('explanation',result.text); // Never execute/render model-supplied HTML.
        status('explain-status',`AI explanation from ${result.model_id||result.model}${result.provider?' via '+result.provider:''} for ${selectionLines}, unverified.`+
          (state.generation!==generation?' You edited during the request; this explains the earlier snapshot.':''));
      } catch(error) {status('explain-status',error.name==='AbortError'?'Explanation timed out. No answer claimed.':error.message);}
      finally {if(valid())el('explain').disabled=false;}
    };
    function download(text,name) {
      const url=URL.createObjectURL(new Blob([text],{type:'text/plain;charset=utf-8'}));
      const a=root.document.createElement('a');a.href=url;a.download=name;root.document.body.appendChild(a);a.click();a.remove();setTimeout(()=>URL.revokeObjectURL(url),1000);
    }
    el('download').onclick=()=>download(editor.value,source.path.split('/').pop());
    el('patch').onclick=()=>{
      const proposal=patch(source.path,source.text,editor.value);
      if(!proposal){status('copy-status','No changes to export.');return;}
      download(proposal,source.path.split('/').pop()+'.patch');
    };
    el('reset').onclick=()=>{if(editor.value!==source.text&&!root.confirm('Replace this browser draft with the original? Download it first if you want to keep it.'))return;editor.value=source.text;changed();};
    if(draft!==null) status('copy-status','Restored your browser draft for this source version. Not checked in this session.');
    const pos=lineOffset(editor.value,Math.max(1,Number(line)||1));editor.setSelectionRange(pos,pos);
  }
  const api={render,mount,dispose,endpoint,keyHeaders,defaultBackend,sentenceEnds,lineOffset,codepoints,patch};
  root.AtlasWorkspace=api;
  if(typeof module!=='undefined'&&module.exports)module.exports=api;
})(typeof window!=='undefined'?window:globalThis);
