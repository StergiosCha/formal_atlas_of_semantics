import {EditorState, StateEffect, StateField} from '@codemirror/state';
import {EditorView, Decoration, keymap, lineNumbers, highlightActiveLine,
  highlightActiveLineGutter, drawSelection, rectangularSelection} from '@codemirror/view';
import {defaultKeymap, history, historyKeymap, indentWithTab} from '@codemirror/commands';
import {StreamLanguage, syntaxHighlighting, HighlightStyle, bracketMatching,
  indentOnInput, foldGutter, foldKeymap} from '@codemirror/language';
import {searchKeymap, highlightSelectionMatches} from '@codemirror/search';
import {tags} from '@lezer/highlight';

const keywords=new Set(('Lemma Theorem Fact Remark Corollary Proposition Definition Fixpoint CoFixpoint '
  +'Inductive CoInductive Record Class Instance Axiom Parameter Parameters Variable Variables '
  +'Hypothesis Hypotheses Context Section End Module Import Export Require From Include '
  +'Proof Qed Defined Admitted Abort Goal Let Local Global Set Unset Check Print About Search '
  +'Notation Infix Reserved Arguments Open Close Scope Type Prop Set forall exists fun match '
  +'with end as return if then else let in where struct for using').split(' '));
const tactics=new Set(('intros intro exact apply eapply refine constructor split left right exists '
  +'destruct induction inversion subst rewrite erewrite unfold fold simpl cbn cbv reflexivity '
  +'assumption symmetry transitivity auto eauto intuition firstorder congruence discriminate '
  +'tauto lia nia lra ring field now try repeat all first solve assert pose specialize clear '
  +'revert generalize dependent change replace f_equal functional_extensionality admit').split(' '));
// Lexical highlighting only. Coq remains the parser and authority.
const coq=StreamLanguage.define({
  startState:()=>({comment:0,string:false}),
  token(stream,state) {
    if(!state.comment && !state.string && stream.eatSpace())return null;
    if(!state.string && (state.comment || stream.match('(*'))) {
      if(!state.comment)state.comment=1;
      while(!stream.eol()) {
        if(stream.match('(*'))state.comment++;
        else if(stream.match('*)')){if(!--state.comment)break;}
        else stream.next();
      }
      return 'comment';
    }
    if(state.string || stream.eat('"')) {
      state.string=true;
      while(!stream.eol()) {
        if(stream.match('""'))continue;
        if(stream.next()==='"'){state.string=false;break;}
      }
      return 'string';
    }
    if(stream.match(/^[0-9]+/))return 'number';
    if(stream.match(/^[\p{L}_][\p{L}\p{N}_']*/u)) {
      return keywords.has(stream.current())?'keyword':tactics.has(stream.current())?'builtin':'variableName';
    }
    if(stream.match(/^(?:->|<-|=>|:=|\/\\|\\\/|<->|[∀∃λ→↔∧∨¬=+*/<>:;|~!&%-])/))return 'operator';
    stream.next();return null;
  },
  languageData:{commentTokens:{block:{open:'(*',close:'*)'}},indentUnit:'  '}
});
const colors=HighlightStyle.define([
  {tag:tags.keyword,color:'#8050a0',fontWeight:'600'},
  {tag:tags.standard(tags.variableName),color:'#186f8d'},
  {tag:tags.comment,color:'#748477',fontStyle:'italic'},
  {tag:tags.string,color:'#9b6027'}, {tag:tags.number,color:'#9a4e35'},
  {tag:tags.operator,color:'#526d8e'}
]);
const progress=StateEffect.define();
const marks=StateField.define({
  create:()=>Decoration.none,
  update(value,tr) {
    if(tr.docChanged)value=Decoration.none;
    for(const e of tr.effects)if(e.is(progress)) {
      const out=[], len=tr.state.doc.length;
      const add=(from,to,cls)=>{from=Math.max(0,Math.min(from,len));to=Math.max(from,Math.min(to,len));
        if(to>from)out.push(Decoration.mark({class:cls}).range(from,to));};
      const {accepted=0,current=null,error=null,pending=null}=e.value;
      add(0,accepted,'cm-coq-accepted');
      if(current)add(current.from,current.to,'cm-coq-current');
      if(pending)add(pending.from,pending.to,'cm-coq-pending');
      if(error) {
        add(error.from,error.to,'cm-coq-error');
        out.push(Decoration.line({class:'cm-coq-error-line'}).range(tr.state.doc.lineAt(Math.min(error.from,len)).from));
      }
      value=Decoration.set(out,true);
    }
    return value;
  },
  provide:f=>EditorView.decorations.from(f)
});
function create(parent,doc,callbacks) {
  const action=name=>()=>{callbacks.action(name);return true;};
  const view=new EditorView({parent,state:EditorState.create({doc,extensions:[
    lineNumbers(),highlightActiveLineGutter(),history(),drawSelection(),rectangularSelection(),
    indentOnInput(),bracketMatching(),foldGutter(),highlightActiveLine(),highlightSelectionMatches(),
    coq,syntaxHighlighting(colors),marks,
    EditorState.tabSize.of(2),
    EditorView.contentAttributes.of({'aria-label':'Editable Coq source','spellcheck':'false','autocapitalize':'off'}),
    keymap.of([{key:'Alt-ArrowDown',run:action('next')},{key:'Alt-ArrowUp',run:action('back')},
      {key:'Mod-Enter',run:action('cursor')},{key:'Mod-Shift-Enter',run:action('file')},
      {key:'Alt-e',run:action('assistant')},...defaultKeymap,...historyKeymap,...searchKeymap,...foldKeymap,indentWithTab]),
    EditorView.updateListener.of(update=>{
      if(update.docChanged)callbacks.change();
      if(update.docChanged||update.selectionSet)callbacks.selection();
    }),
    EditorView.theme({
      '&':{height:'100%',fontSize:'14px',backgroundColor:'#fcfcf9'},
      '.cm-scroller':{overflow:'auto',fontFamily:'"SFMono-Regular", Consolas, "Liberation Mono", monospace',lineHeight:'1.75'},
      '.cm-content':{padding:'16px 0',caretColor:'#293f2d'},
      '.cm-line':{padding:'0 16px'},
      '.cm-gutters':{backgroundColor:'#f4f5ef',color:'#889286',borderRight:'1px solid #e2e6db',minWidth:'48px'},
      '.cm-activeLineGutter':{backgroundColor:'#e8eddf',color:'#365837'},
      '.cm-activeLine':{backgroundColor:'#edf1e640'},
      '&.cm-focused':{outline:'none'},
      '.cm-selectionBackground, &.cm-focused .cm-selectionBackground':{backgroundColor:'#cdddc7 !important'},
      '.cm-searchMatch':{backgroundColor:'#fae5aa'},
      '.cm-panels':{backgroundColor:'#f3f5ed',fontFamily:'inherit'},
      '.cm-coq-accepted':{backgroundColor:'#dcefdc80'},
      '.cm-coq-current':{borderBottom:'2px solid #a6b68e'},
      '.cm-coq-pending':{backgroundColor:'#fae8b8a0'},
      '.cm-coq-error':{textDecoration:'underline wavy #bd4941',textUnderlineOffset:'3px'},
      '.cm-coq-error-line':{backgroundColor:'#fce8e480'}
    })
  ]})});
  return {
    getValue:()=>view.state.doc.toString(),
    getSelection:()=>({from:view.state.selection.main.from,to:view.state.selection.main.to}),
    setValue:value=>view.dispatch({changes:{from:0,to:view.state.doc.length,insert:value}}),
    select:(from,to=from,focus=true)=>{view.dispatch({selection:{anchor:from,head:to},scrollIntoView:true});if(focus)view.focus();},
    setProgress:value=>view.dispatch({effects:progress.of(value)}),
    focus:()=>view.focus(),destroy:()=>view.destroy()
  };
}
// The reader uses the same pinned lexical mode but never opens a Coq session.
function read(parent,doc,line=1) {
  const count=doc.split('\n').length, requested=Number(line);
  const selected=Number.isInteger(requested)&&requested>0&&requested<=count?requested:1;
  const view=new EditorView({parent,state:EditorState.create({doc,extensions:[
    EditorState.readOnly.of(true),EditorView.editable.of(false),
    EditorView.contentAttributes.of({'aria-label':'Read-only full Coq source','tabindex':'0'}),
    lineNumbers(),drawSelection(),bracketMatching(),highlightSelectionMatches(),
    coq,syntaxHighlighting(colors),keymap.of(searchKeymap),
    EditorView.decorations.of(Decoration.set([
      Decoration.line({class:'cm-reader-selected'}).range(EditorState.create({doc}).doc.line(selected).from)
    ])),
    EditorView.theme({
      '&':{height:'100%',fontSize:'14px',backgroundColor:'#fcfcf9'},
      '.cm-scroller':{overflow:'auto',fontFamily:'"SFMono-Regular", Consolas, monospace',lineHeight:'1.75'},
      '.cm-content':{padding:'14px 0'},'.cm-line':{padding:'0 16px'},
      '.cm-gutters':{backgroundColor:'#f3f5ee',color:'#5c6b5a',borderRight:'1px solid #d9dfd1'},
      '.cm-reader-selected':{backgroundColor:'#fff0bd'},
      '.cm-selectionBackground':{backgroundColor:'#d4e0cb !important'},
      '.cm-searchMatch':{backgroundColor:'#fae5aa'},
      '&.cm-focused':{outline:'2px solid #4e8c3b',outlineOffset:'-2px'}
    })
  ]})});
  view.dispatch({effects:EditorView.scrollIntoView(view.state.doc.line(selected).from,{y:'center'})});
  return {destroy:()=>view.destroy()};
}
window.AtlasCodeEditor={create,read};
