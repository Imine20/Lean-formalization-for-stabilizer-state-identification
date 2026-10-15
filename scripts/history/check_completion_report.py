#!/usr/bin/env python3
"""Check standalone report graph integrity and exercise its navigation code."""
from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess
import tempfile

root = Path(__file__).resolve().parents[1]
report = root / 'evidence/completion-closure-report.html'
page = report.read_text()
graphs = json.loads(re.search(r'<script id="graphs" type="application/json">(.*?)</script>', page, re.S)[1])
counts = {}
for mode, graph in graphs.items():
    ids = [n['id'] for n in graph['nodes']]
    assert len(ids) == len(set(ids)), mode
    assert all(e['from'] in ids and e['to'] in ids for e in graph['edges']), mode
    counts[mode] = {'nodes': len(ids), 'edges': len(graph['edges'])}
assert graphs['lean']['audit_count'] == 252
assert len(graphs['lean']['checked_transitive_links']) == 15
assert graphs['paper']['completion_update']['main_theorem_complete'] is False
assert not re.search(r'LEANCOMMIT|MATHLIBCOMMIT|AXCOUNT|LINKCOUNT|DETAILS|GRAPHS', page)
script = re.findall(r'<script>(.*?)</script>', page, re.S)[0]
node = shutil.which('node')
assert node, 'Node is needed to validate report navigation'
harness = r'''
const fs = require('fs'), vm = require('vm'), assert = require('assert');
const data = JSON.parse(fs.readFileSync(process.argv[2], 'utf8'));
class Element {
  constructor() { this.children = []; this.value = ''; this.textContent = ''; }
  append(...nodes) { this.children.push(...nodes); }
  replaceChildren(...nodes) { this.children = [...nodes]; this.textContent = ''; }
}
const elements = new Map();
const document = { getElementById(id) {
  if (!elements.has(id)) elements.set(id, new Element());
  return elements.get(id);
}, createElement() { return new Element(); } };
document.getElementById('graphs').textContent = JSON.stringify(data);
document.getElementById('mode').value = 'lean';
const context = vm.createContext({document});
vm.runInContext(fs.readFileSync(process.argv[3], 'utf8'), context);
let visited = 0;
for (const mode of ['lean','paper']) {
  document.getElementById('mode').value = mode;
  document.getElementById('mode').onchange();
  for (const n of data[mode].nodes) {
    vm.runInContext('show(' + JSON.stringify(n.id) + ')', context);
    assert(document.getElementById('current').children.length === 3);
    visited++;
  }
  for (const q of ['completion', 'rank', '']) {
    document.getElementById('search').oninput({target:{value:q}});
    const results = document.getElementById('results').children;
    assert(results.length <= 18);
    if (q) assert(results.length > 0);
    else assert(results.length === 0);
    if (results.length) results[0].onclick();
  }
  document.getElementById('home').onclick();
}
console.log(JSON.stringify({visited_nodes:visited, modes:2, search_cases:6, navigation:'pass'}));
'''
with tempfile.TemporaryDirectory(prefix='completion-report-check-') as tmp:
    tmp = Path(tmp)
    (tmp/'script.js').write_text(script)
    (tmp/'data.json').write_text(json.dumps(graphs))
    (tmp/'harness.js').write_text(harness)
    subprocess.run([node, '--check', str(tmp/'script.js')], check=True)
    result = subprocess.run([node, str(tmp/'harness.js'), str(tmp/'data.json'), str(tmp/'script.js')],
                            check=True, text=True, capture_output=True)
checks = {'result':'pass', 'report_sha256': hashlib.sha256(report.read_bytes()).hexdigest(),
          'graph_integrity':counts, 'interactive_navigation':json.loads(result.stdout),
          'scope':'Graph data, JavaScript syntax and mock-DOM navigation; no screenshot or browser visual inspection.'}
(root/'evidence/completion-artifact-check.json').write_text(json.dumps(checks, ensure_ascii=False, indent=2)+'\n')
print(json.dumps(checks, ensure_ascii=False))
