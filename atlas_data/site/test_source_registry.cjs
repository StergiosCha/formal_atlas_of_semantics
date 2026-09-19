// Minimal-DOM rendering tests, not browser/visual or source-fidelity checks.
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
    querySelector: () => app, querySelectorAll: () => [],
  },
  location: {hash: '#/sources'}, window: {scrollTo() {}}, addEventListener() {},
});
script.runInContext(context, {timeout: 5000});
const page = app.innerHTML;
assert.equal((page.match(/<article class="block" id="source-/g) || []).length, 231);
assert(page.includes('230 survey sources'));
assert(page.includes('138 hashed artifacts'));
assert(page.includes('7 survey sources with documented identity links'));
assert(page.includes('104 published low-tier labels'));
assert(page.includes('evidence-registration'));
assert(page.includes('candidate identity'));
assert(page.includes('not yet documented'));
assert(page.includes('2011 retypesetting'));
assert(page.includes('Date unresolved'));
assert(page.includes('Hovy 1988'));
assert(page.includes('Supplementary source — outside the frozen 230-source survey'));
assert(page.includes('No source-reading record imported'));
assert(!page.includes('href="foundations/'));
assert(!page.includes('href="dynamic/'));
assert(!html.includes('__REVISION__'));
const filterEntries = [{dataset: {sourceSearch: 'Heim 1982'}, hidden: false},
                       {dataset: {sourceSearch: 'Horn 1984'}, hidden: false}];
context.document.querySelectorAll = () => filterEntries;
vm.runInContext("sourceFilter('HEIM')", context);
assert.deepEqual(filterEntries.map(e => e.hidden), [false, true]);
vm.runInContext("sourceFilter('')", context);
assert.deepEqual(filterEntries.map(e => e.hidden), [false, false]);
const attack = '<img src=x onerror=alert(1)>';
context.attack = attack;
vm.runInContext("D.source_registry.sources[0].citation = attack", context);
assert(!vm.runInContext('vSources()', context).includes(attack));
assert(vm.runInContext('vSources()', context).includes('&lt;img'));
vm.runInContext("D.source_registry = null", context);
assert(vm.runInContext('vSources()', context).includes('Source registry unavailable'));
console.log('230 registry entries, separate Cooper supplement, candidates, missing metadata, provenance and escaping checked.');
