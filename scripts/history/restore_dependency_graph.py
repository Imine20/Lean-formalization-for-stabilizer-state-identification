#!/usr/bin/env python3
"""Restore the previously verified graph for continued planning, without copying credentials."""
from pathlib import Path
import hashlib
import importlib.util
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
support = Path.home() / 'Library/Application Support/CodexAutomation/ResultBackup'
sys.path.insert(0, str(support))
spec = importlib.util.spec_from_file_location('codex_result_backup', support / 'codex_result_backup.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
config = json.loads((support / 'config.json').read_text())
receipt = json.loads((ROOT / 'backup-receipt.json').read_text())
entry = next(e for e in receipt['files'] if e['path'].endswith('/dependency-graph.json'))
dav = module.WebDAV(config, module.credentials_for(support))
prefix = dav.url.rstrip('/') + '/'
if not entry['remote_url'].startswith(prefix):
    raise SystemExit('Receipt server mismatch')
with dav.request('GET', entry['remote_url'][len(prefix):]) as response:
    if response.status != 200:
        raise SystemExit(f'Restore HTTP status: {response.status}')
    data = response.read()
if hashlib.sha256(data).hexdigest() != entry['sha256']:
    raise SystemExit('Restored graph hash mismatch')
target = ROOT / 'planning/paper-dependency-graph.json'
if target.exists():
    raise SystemExit('Refusing to overwrite active planning graph')
target.parent.mkdir(exist_ok=True)
target.write_bytes(data)
print('Restored verified graph:', target)
