/* Editable copies, real Coq diagnostics, and explicitly unverified explanations. */
(function(root) {
  'use strict';
  const esc=s=>String(s??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
  const DEFAULT_API='https://formal-atlas-coq-crete.westus2.cloudapp.azure.com';
  const LEGACY_API='https://atlas-checker.greenrock-e642001f.westus2.azurecontainerapps.io';
  let active=null;
  const storage={get(k){try{return root.localStorage.getItem(k);}catch(_){return null;}},
    set(k,v){try{root.localStorage.setItem(k,v);return true;}catch(_){return false;}}};
  function endpoint(value) {
    const url=new URL(value);
    if(url.username||url.password||url.search||url.hash||!(url.protocol==='https:'||
      (url.protocol==='http:'&&['localhost','127.0.0.1'].includes(url.hostname))))
      throw new Error('Use an HTTPS backend, or localhost for development, without credentials or query parameters.');
    return url.href.replace(/\/$/,'');
  }
  function keyHeaders(value) {
    const key=String(value||'').trim();
    if(!key)throw new Error('Enter your OpenRouter API key in the key field.');
    if(key.length>512||!/^sk-or-[A-Za-z0-9_-]+$/.test(key))throw new Error('Invalid OpenRouter API key format.');
    return {'X-OpenRouter-Key':key};
  }
  function defaultBackend(){const saved=storage.get('atlas_api');return !saved||saved.replace(/\/$/,'')===LEGACY_API?DEFAULT_API:saved;}
  function sentenceEnds(code) {
    const ends=[];let comment=0,quoted=false;
    for(let i=0;i<code.length;i++) {
      if(comment){if(code.slice(i,i+2)==='(*'){comment++;i++;}else if(code.slice(i,i+2)==='*)'){comment--;i++;}}
      else if(quoted){if(code[i]==='"'){if(code[i+1]==='"')i++;else quoted=false;}}
      else if(code.slice(i,i+2)==='(*'){comment=1;i++;}
      else if(code[i]==='"')quoted=true;
      else if(code[i]==='.'&&(i+1===code.length||/\s/.test(code[i+1])||code.slice(i+1,i+3)==='(*'))ends.push(i+1);
    }
    return ends;
  }
  function lineOffset(code,line){let pos=0;for(let i=1;i<line;i++){const n=code.indexOf('\n',pos);if(n<0)return code.length;pos=n+1;}return pos;}
  function codepoints(code,offset){return Array.from(code.slice(0,offset)).length;}
  function patch(path,original,edited) {
    const lines=s=>s?(s.endsWith('\n')?s.slice(0,-1).split('\n'):s.split('\n')):[];
    const before=lines(original),after=lines(edited);
    const body=(xs,prefix,text)=>xs.map(x=>prefix+x).join('\n')+(xs.length?'\n':'')+(xs.length&&!text.endsWith('\n')?'\\ No newline at end of file\n':'');
    return original===edited?'':`--- a/${path}\n+++ b/${path}\n@@ -${before.length?1:0},${before.length} +${after.length?1:0},${after.length} @@\n`+body(before,'-',original)+body(after,'+',edited);
  }
  // Coq reports UTF-8 byte columns, while CodeMirror uses UTF-16 offsets.
  function byteOffset(text,bytes) {
    let used=0,offset=0;
    for(const char of text){const size=new TextEncoder().encode(char).length;if(used+size>bytes)break;used+=size;offset+=char.length;}
    return offset;
  }
  function diagnostic(output,code,path) {
    const name=path.split('/').pop();
    for(const m of output.matchAll(/File "([^"]+)", line (\d+), characters (\d+)-(\d+):/g)) {
      // Never map an imported library's error onto the edited file.
      if(m[1].split('/').pop()!==name)continue;
      const line=Number(m[2]),start=lineOffset(code,line),text=code.slice(start).split('\n')[0];
      if(line>code.split('\n').length)continue;
      const from=start+byteOffset(text,Number(m[3])),to=start+byteOffset(text,Number(m[4]));
      return {line,from,to:Math.min(code.length,Math.max(from+1,to))};
    }
    return null;
  }
  function goals(output) {
    const matches=[...output.matchAll(/(?:^|\n)(\d+) goals?(?: \(ID [^)]+\))?\s*\n/g)];
    if(!matches.length)return null;
    const m=matches[matches.length-1],body=output.slice(m.index+m[0].length);
    const divider=/^\s*={5,}\s*$/m.exec(body);
    if(!divider)return null;
    const tail=body.slice(divider.index+divider[0].length).trim();
    const parts=tail.split(/\n\s*goal \d+(?: \(ID [^)]+\))? is:\s*\n/i);
    return {count:Number(m[1]),hypotheses:body.slice(0,divider.index).trim(),conclusions:parts.map(s=>s.trim())};
  }
  function render(source,key) {
    return `<div class="live-workspace">
      <div class="live-heading"><div><a class="live-backlink" href="#/proof/${encodeURIComponent(key)}">← Original proof & audit</a>
        <h1>${esc(source.path.split('/').pop())} <span>Coq workspace</span></h1></div>
        <div class="live-heading-actions"><span id="live-badge" class="live-badge">Not connected</span><button id="live-connect" class="live-button">Connect Coq</button>
        <details class="live-settings" id="live-settings"><summary>Settings & help</summary><div class="live-settings-card">
          <label for="live-api">Checker backend</label><input id="live-api" type="url" value="${esc(defaultBackend())}">
          <p id="live-connection" role="status">Not connected. No code or question has been sent.</p>
          <p>Coq 8.20.1. Each step replays in a fresh isolated process. Imports use the precompiled atlas; edited dependents are not rebuilt.</p>
          <p>Check sends this file to the displayed backend. Explain sends your file and question there; only the selection and nearby context go to OpenRouter. Use a backend you trust.</p>
          <dl><dt>Next / previous</dt><dd>Alt + ↓ / ↑</dd><dt>Check to cursor</dt><dd>Ctrl / ⌘ + Enter</dd><dt>Compile file</dt><dd>Ctrl / ⌘ + Shift + Enter</dd><dt>Assistant</dt><dd>Alt + E</dd><dt>Search</dt><dd>Ctrl / ⌘ + F</dd></dl>
          <p>Tab indents. Escape then Tab moves focus out of the editor. <a href="https://github.com/StergiosCha/formal_atlas_of_semantics/pulls" target="_blank" rel="noopener noreferrer">Submit a review patch via pull request.</a> Nothing is submitted automatically.</p>
        </div></details></div></div>
      <div class="live-toolbar" role="toolbar" aria-label="Coq proof controls">
        <button class="live-button" id="live-back" title="Previous command (Alt+Up)">↑ Previous</button>
        <button class="live-button primary" id="live-next" title="Next command (Alt+Down)">↓ Next command</button>
        <button class="live-button" id="live-cursor" title="Check to cursor (Ctrl/Cmd+Enter)">Run to cursor</button>
        <button class="live-button" id="live-file" title="Compile full copy (Ctrl/Cmd+Shift+Enter)">Compile file</button>
        <span class="live-toolbar-spacer"></span><button class="live-button quiet" id="live-download">Download .v</button>
        <button class="live-button quiet" id="live-patch">Review patch</button><button class="live-button quiet" id="live-reset">Restore</button>
      </div>
      <div class="live-grid" id="live-grid">
        <div class="live-editor-pane"><div class="live-filebar"><span>${esc(source.path)}</span><span class="live-private">PRIVATE COPY</span></div>
          <div id="live-code" aria-label="Editable Coq source"></div>
          <div class="live-editor-footer"><span id="live-position">Ln 1, Col 1</span><span id="live-progress">Not checked</span><span class="live-legend"><i></i> Coq-accepted prefix</span></div>
        </div>
        <div id="live-divider" class="live-divider" role="separator" tabindex="0" aria-label="Resize code and proof panels" aria-orientation="vertical" aria-valuemin="35" aria-valuemax="75" aria-valuenow="62"></div>
        <aside class="live-panels"><div class="live-tabs" role="tablist" aria-label="Proof workspace panels">
          <button id="live-tab-goals" role="tab" aria-controls="live-panel-goals" aria-selected="true">Goals <span id="live-goal-count"></span></button>
          <button id="live-tab-diagnostics" role="tab" aria-controls="live-panel-diagnostics" aria-selected="false" tabindex="-1">Diagnostics</button>
          <button id="live-tab-assistant" role="tab" aria-controls="live-panel-assistant" aria-selected="false" tabindex="-1">Assistant <span class="live-ai-tag">AI</span></button>
        </div>
        <div class="live-panel" id="live-panel-goals" role="tabpanel" aria-labelledby="live-tab-goals" tabindex="0">
          <div id="live-goals"><div class="live-empty"><span class="live-empty-symbol">⊢</span><h2>One command at a time.</h2><p>Connect Coq, then step through the proof. Hypotheses and the current goal appear here.</p><kbd>Alt</kbd> + <kbd>↓</kbd><span> next command</span></div></div>
        </div>
        <div class="live-panel" id="live-panel-diagnostics" role="tabpanel" aria-labelledby="live-tab-diagnostics" tabindex="0" hidden>
          <div class="live-panel-title">Compiler output <button id="live-error-jump" class="live-button" hidden>Jump to error</button></div>
          <pre id="live-output" class="live-output">No compiler output yet.</pre>
        </div>
        <div class="live-panel" id="live-panel-assistant" role="tabpanel" aria-labelledby="live-tab-assistant" tabindex="0" hidden>
          <div class="live-assistant-intro"><h2>Explain this part</h2><p>Select code, then ask a question. The assistant explains; it cannot edit, execute or approve your proof.</p></div>
          <label for="live-model">OpenRouter model</label><select id="live-model"><option value="gpt-6-astra">openai/gpt-6-astra</option></select>
          <div class="live-key-row"><div><label for="live-key">Your OpenRouter API key</label><input id="live-key" type="password" autocomplete="off" spellcheck="false" autocapitalize="off" maxlength="512" placeholder="sk-or-..."></div><button id="live-clear-key" class="live-button">Clear</button></div>
          <p class="live-note">Your account pays. The key goes through this backend only for model calls; the app does not save it. Reloading or navigating clears it.</p>
          <div class="live-selection-head"><span id="live-selection">No selection.</span><button class="live-button quiet" id="live-select-command">Select current command</button></div>
          <pre id="live-excerpt" class="live-excerpt" hidden></pre>
          <label for="live-question">Question about this code</label><textarea id="live-question" rows="3" placeholder="What does this prove, and which assumptions does it need?"></textarea>
          <button class="live-button primary" id="live-explain">Explain selection</button><p id="live-explain-status" role="status" class="live-note">Optional. No model call yet.</p>
          <pre id="live-explanation" class="live-explanation" aria-live="polite"></pre>
          <p class="live-note">AI explanation, not a checked proof. Coq does not need or receive your key.</p>
        </div>
        <div class="live-check-footer"><span id="live-check-status" role="status">Not checked in this session.</span></div>
        </aside>
      </div>
      <div class="live-bottom"><span id="live-copy-status" role="status">Original source loaded. This session has not checked it.</span><span>Compilation is not a source-fidelity verdict. Admissions or added assumptions may compile.</span></div>
    </div>`;
  }
  function dispose() {
    if(active){active.requests.forEach(c=>c.abort());active.events.abort();active.editor?.destroy();active=null;}
    root.document?.body?.classList.remove('atlas-editing');
  }
  function mount(source,key,data,line) {
    dispose();const el=id=>root.document.getElementById('live-'+id);
    if(!el('code'))return;
    root.document.body.classList.add('atlas-editing');
    const state={requests:new Set(),events:new AbortController(),generation:0,processed:0,ready:false,busy:false,error:null,connectSeq:0,tab:'goals'};active=state;
    const valid=()=>active===state,status=(id,text)=>{if(valid())el(id).textContent=text;};
    if(!root.AtlasCodeEditor){status('check-status','Editor bundle unavailable. Reload the page.');return;}
    const draftKey='atlas-edit-v1:'+key+':'+source.sha256,draft=storage.get(draftKey);
    let editor;
    function currentRange(){const code=editor.getValue();return {from:state.processed,to:sentenceEnds(code).find(n=>n>state.processed)??code.length};}
    function progress(pending=null){editor.setProgress({accepted:state.processed,current:currentRange(),error:state.error,pending});}
    function selectTab(name,focus=false) {
      state.tab=name;
      for(const tab of ['goals','diagnostics','assistant']){const on=tab===name;el('panel-'+tab).hidden=!on;el('tab-'+tab).setAttribute('aria-selected',String(on));el('tab-'+tab).tabIndex=on?0:-1;}
      if(focus)el('tab-'+name).focus();
    }
    function changed() {
      state.generation++;state.processed=0;state.error=null;el('error-jump').hidden=true;progress();
      const code=editor.getValue(),saved=storage.set(draftKey,code);
      status('copy-status',(code===source.text?'Original source bytes.':'Edited private copy; original audit does not apply.')+(saved?' Saved in this browser.':' Storage unavailable. Download to keep your work.'));
      status('check-status','Current copy not checked. Previous output belongs to an earlier snapshot.');
      status('progress','Not checked');el('goals').classList.add('is-stale');status('goal-count','');
      if(el('explanation').textContent)status('explain-status','Explanation below concerns an earlier snapshot, not this edit.');
    }
    function selection() {
      if(!editor)return;
      const {from,to}=editor.getSelection(),code=editor.getValue(),ln=code.slice(0,to).split('\n').length;
      status('position',`Ln ${ln}, Col ${codepoints(code.slice(lineOffset(code,ln)),to-lineOffset(code,ln))+1}`);
      status('selection',from===to?'No selection.':`Selected lines ${code.slice(0,from).split('\n').length} to ${ln}`);
      el('excerpt').hidden=from===to;status('excerpt',code.slice(from,Math.min(to,from+1200))+(to-from>1200?'\n…':''));
    }
    editor=state.editor=root.AtlasCodeEditor.create(el('code'),draft===null?source.text:draft,{change:changed,selection,action:name=>{
      if(name==='assistant')selectTab('assistant');else el(name).click();
    }});
    // Browser tests use the same adapter as the UI, not a hidden textarea mirror.
    el('code').coqEditor=editor;
    const currentAPI=()=>endpoint(el('api').value.trim());
    async function request(path,body,timeout=35000,headers={}) {
      const controller=new AbortController();state.requests.add(controller);
      const timer=setTimeout(()=>controller.abort(),timeout);
      try {
        const response=await fetch(currentAPI()+path,{method:body?'POST':'GET',credentials:'omit',redirect:'error',signal:controller.signal,
          ...(body?{headers:{'content-type':'application/json',...headers},body:JSON.stringify(body)}:{})});
        let value;try{value=await response.json();}catch(_){throw new Error('Backend did not return workspace JSON. It may need updating.');}
        if(!response.ok)throw new Error(typeof value.detail==='string'?value.detail:`Backend HTTP ${response.status}`);
        return value;
      }finally{clearTimeout(timer);state.requests.delete(controller);}
    }
    el('api').addEventListener('input',()=>{state.ready=false;state.connectSeq++;state.generation++;state.processed=0;state.error=null;progress();
      el('key').value='';el('badge').classList.remove('is-ready');status('explain-status','Backend changed. Key cleared; only enter it for a backend you trust.');
      el('error-jump').hidden=true;status('badge','Not connected');status('progress','Not checked');el('goals').classList.add('is-stale');
      status('check-status','Backend changed. Connect before checking.');status('connection','Backend changed. Connect before checking.');});
    el('connect').onclick=async()=>{
      const seq=++state.connectSeq;state.ready=false;status('badge','Connecting…');status('connection','Checking sandbox, compiler version and library snapshot...');
      try {
        const cap=await request('/workspace/capabilities');if(!valid()||seq!==state.connectSeq)return;
        if(cap.library_sha256!==data.workspace_library_sha256)throw new Error('Checker and site library snapshots differ. Backend update required.');
        state.ready=cap.available===true&&cap.coq_version==='8.20.1';
        storage.set('atlas_api',currentAPI());status('badge',state.ready?'● Coq 8.20.1':'Unavailable');el('badge').classList.toggle('is-ready',state.ready);
        status('connection',state.ready?`Connected: Coq ${cap.coq_version}, ${cap.sandbox}. Library snapshot matches.`:`Live checking unavailable: ${cap.error||'Coq 8.20.1 sandbox required'}.`);
        if(state.ready){el('settings').open=false;status('connect','Reconnect');}
        const roster=await request('/models');if(!valid()||seq!==state.connectSeq)return;
        el('model').innerHTML=roster.models.filter(m=>typeof m.deployment==='string'&&!/claude/i.test(m.deployment)).map(m=>`<option value="${esc(m.deployment)}"${m.deployment==='gpt-6-astra'?' selected':''}>${esc(m.model||m.deployment)}</option>`).join('');
      }catch(error){if(valid()&&seq===state.connectSeq){status('connection',error.message);if(!state.ready)status('badge','Connection failed');else status('explain-status','Model roster unavailable. Reconnect to retry.');}}
    };
    const sourceRequest=code=>({path:source.path,source_sha256:source.sha256,library_sha256:data.workspace_library_sha256,code});
    function renderGoals(output,mode) {
      const parsed=goals(output);el('goals').classList.remove('is-stale');status('goal-count',parsed?String(parsed.count):'');
      if(parsed)el('goals').innerHTML=`<div class="live-panel-title">Hypotheses</div><pre class="live-hypotheses">${esc(parsed.hypotheses||'No local hypotheses.')}</pre>`+
        parsed.conclusions.map((goal,i)=>`<div class="live-goal-card"><div class="live-panel-title">${i?'Additional goal':'Current goal'} <span>${i+1} / ${parsed.count}</span></div><pre>${esc(goal)}</pre></div>`).join('');
      else el('goals').innerHTML=`<div class="live-empty"><span class="live-empty-symbol">${mode==='file'?'✓':'⊢'}</span><h2>${mode==='file'?'This copy compiled.':/No more goals/.test(output)?'No more goals.':'Prefix accepted.'}</h2><p>${mode==='file'?'Compilation does not transfer the original audit or establish source fidelity.':/No proof is currently open/.test(output)?'No proof is currently open. Continue to the next command.':'See Diagnostics for the complete Coq output.'}</p></div>`;
    }
    async function check(mode,cursor) {
      if(state.busy)return;
      if(!state.ready){status('check-status','Connect to a matching, sandbox-enabled checker first.');return;}
      const code=editor.getValue(),generation=state.generation;state.busy=true;state.error=null;el('error-jump').hidden=true;
      ['back','next','cursor','file'].forEach(id=>el(id).disabled=true);progress({from:Math.min(state.processed,cursor),to:cursor});
      status('check-status',mode==='file'?'Compiling this copy...':'Replaying the selected prefix...');
      try {
        const result=await request('/workspace/check',{...sourceRequest(code),mode,cursor:codepoints(code,cursor)});
        if(!valid())return;status('output',result.output||'(Coq returned no diagnostics.)');
        if(state.generation!==generation||editor.getValue()!==code){status('check-status','Result is stale: you edited while Coq was running. Current copy is not checked.');return;}
        const hash=Array.from(new Uint8Array(await root.crypto.subtle.digest('SHA-256',new TextEncoder().encode(code)))).map(x=>x.toString(16).padStart(2,'0')).join('');
        if(!valid())return;
        if(state.generation!==generation||result.code_sha256!==hash||result.library_sha256!==data.workspace_library_sha256){status('check-status','Snapshot mismatch. No check is attributed to the current copy.');return;}
        if(result.ok===true) {
          state.processed=cursor;status('progress',mode==='file'?'Full copy compiled':`Accepted through line ${code.slice(0,cursor).split('\n').length}`);
          status('check-status',mode==='file'?'This copy compiled in Coq 8.20.1. Original audits and source approval do not transfer.':`Coq accepted the prefix through line ${code.slice(0,cursor).split('\n').length}. Open goals may remain.`);
          renderGoals(result.output||'',mode);selectTab('goals');editor.select(cursor);
        }else {
          state.error=diagnostic(result.output||'',code,source.path);el('error-jump').hidden=!state.error;
          if(state.error)status('error-jump',`Jump to line ${state.error.line}`);
          status('check-status',result.timeout?'Coq timed out. This copy is not checked.':'Coq reported an error. This copy is not checked.');selectTab('diagnostics');
        }
        if(result.truncated)status('output','[Earlier output truncated]\n'+result.output);
      }catch(error){status('check-status',error.name==='AbortError'?'Timed out waiting for Coq. No successful check claimed.':error.message);}
      finally{state.busy=false;if(valid()){progress();['back','next','cursor','file'].forEach(id=>el(id).disabled=false);}}
    }
    el('next').onclick=()=>check('prefix',currentRange().to);
    el('back').onclick=()=>check('prefix',sentenceEnds(editor.getValue()).filter(n=>n<state.processed).pop()??0);
    el('cursor').onclick=()=>check('prefix',editor.getSelection().to);
    el('file').onclick=()=>check('file',editor.getValue().length);
    el('error-jump').onclick=()=>{if(state.error)editor.select(state.error.from,state.error.to);};
    const tabs=['goals','diagnostics','assistant'];
    tabs.forEach((name,i)=>{el('tab-'+name).onclick=()=>selectTab(name);el('tab-'+name).onkeydown=event=>{
      if(['ArrowLeft','ArrowRight','Home','End'].includes(event.key)){event.preventDefault();selectTab(tabs[event.key==='Home'?0:event.key==='End'?2:(i+(event.key==='ArrowRight'?1:2))%3],true);}
    };});
    el('select-command').onclick=()=>{const code=editor.getValue(),pos=editor.getSelection().to,ends=sentenceEnds(code);
      editor.select(ends.filter(n=>n<pos).pop()??0,ends.find(n=>n>=pos)??code.length,false);};
    el('key').value='';el('clear-key').onclick=()=>{el('key').value='';status('explain-status','Key cleared. An already-sent request may still finish.');};
    el('explain').onclick=async()=>{
      const {from:start,to:end}=editor.getSelection(),code=editor.getValue(),generation=state.generation;
      if(start===end){status('explain-status','Select the code you want explained first.');return;}
      const question=el('question').value.trim()||'Explain this selection, its premises and what it does and does not establish.',model=el('model').value;
      const selectionLines=`lines ${code.slice(0,start).split('\n').length} to ${code.slice(0,end).split('\n').length}`;
      el('explain').disabled=true;status('explain-status',`Asking ${model}. This is not a Coq check...`);
      try {
        const headers=keyHeaders(el('key').value);
        const result=await request('/workspace/explain',{...sourceRequest(code),start:codepoints(code,start),end:codepoints(code,end),question,model},100000,headers);
        if(!valid())return;status('explanation',result.text);
        status('explain-status',`AI explanation from ${result.model_id||result.model}${result.provider?' via '+result.provider:''} for ${selectionLines}, unverified.`+(state.generation!==generation?' You edited during the request; this explains the earlier snapshot.':''));
      }catch(error){status('explain-status',error.name==='AbortError'?'Explanation timed out. No answer claimed.':error.message);}
      finally{if(valid())el('explain').disabled=false;}
    };
    function download(text,name){const url=URL.createObjectURL(new Blob([text],{type:'text/plain;charset=utf-8'}));const a=root.document.createElement('a');a.href=url;a.download=name;root.document.body.appendChild(a);a.click();a.remove();setTimeout(()=>URL.revokeObjectURL(url),1000);}
    el('download').onclick=()=>download(editor.getValue(),source.path.split('/').pop());
    el('patch').onclick=()=>{const proposal=patch(source.path,source.text,editor.getValue());if(!proposal){status('copy-status','No changes to export.');return;}download(proposal,source.path.split('/').pop()+'.patch');};
    el('reset').onclick=()=>{if(editor.getValue()!==source.text&&!root.confirm('Restore the original source? Download your draft first to keep it.'))return;editor.setValue(source.text);};
    const divider=el('divider'),grid=el('grid');let resizing=false;
    function resize(value){value=Math.max(35,Math.min(75,value));grid.style.setProperty('--code-share',value+'%');divider.setAttribute('aria-valuenow',String(Math.round(value)));}
    divider.onpointerdown=event=>{if(event.button!==0)return;resizing=true;divider.setPointerCapture(event.pointerId);event.preventDefault();};
    divider.onpointermove=event=>{if(resizing){const rect=grid.getBoundingClientRect();resize(100*(event.clientX-rect.left)/rect.width);}};
    divider.onpointerup=divider.onpointercancel=()=>{resizing=false;};
    divider.onkeydown=event=>{if(['ArrowLeft','ArrowRight','Home'].includes(event.key)){event.preventDefault();resize(event.key==='Home'?62:Number(divider.getAttribute('aria-valuenow'))+(event.key==='ArrowRight'?2:-2));}};
    root.document.addEventListener('keydown',event=>{if(event.key==='Escape')el('settings').open=false;},{signal:state.events.signal});
    if(draft!==null)status('copy-status','Restored your browser draft for this source version. Not checked in this session.');
    editor.select(lineOffset(editor.getValue(),Math.max(1,Number(line)||1)),undefined,false);selection();progress();
  }
  const api={render,mount,dispose,endpoint,keyHeaders,defaultBackend,sentenceEnds,lineOffset,codepoints,patch,diagnostic,goals,byteOffset};
  root.AtlasWorkspace=api;if(typeof module!=='undefined'&&module.exports)module.exports=api;
})(typeof window!=='undefined'?window:globalThis);
