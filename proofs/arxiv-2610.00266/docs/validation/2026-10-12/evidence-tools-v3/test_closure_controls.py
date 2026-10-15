#!/usr/bin/env python3
"""Negative controls over completed preflight evidence, never a release gate."""
from pathlib import Path
import json,sys,hashlib
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
sys.path.insert(0,str(HERE))
from verify_joint_gate_strict import runtime_bundle,audit_markers,MAINS
from audit_call_inventory import declarations
source_commit=json.loads((HERE/'tool-bundle.json').read_text())['accepted_mathematical_source']
runtime_bundle(ROOT,source_commit)
assert len(MAINS)==5
known=set()
for p in (ROOT/'ExactCriticalCurve').rglob('*.lean'): known.update(declarations(p.read_text()))
logpath=ROOT/'docs/validation/2026-10-12/paper-correspondence-closure-preflight/release.log'
log=logpath.read_text()
source=(ROOT/'scripts/ReleaseAudit.lean').read_text()
stats=audit_markers(log,source,known,known,True)
tests=[]
for name in sorted(MAINS):
    marker='KERNEL_EXPECTED_TYPE_OK body '+name
    assert log.splitlines().count(marker)==1
    try: audit_markers(log.replace(marker+'\n',''),source,known,known,True)
    except ValueError as e:
        tests.append({'case':'missing main original body','target':name,'rejected':True,'reason':str(e)})
    else: raise AssertionError('Missing original body accepted: '+name)
record={'source':source_commit,'scope':'Verifier controls over completed combined ReleaseAudit preflight; not fresh full release acceptance','preflight_log_sha256':hashlib.sha256(logpath.read_bytes()).hexdigest(),'positive_constant_checks':stats['constant_checks'],'positive_original_body_checks':stats['original_body_checks'],'tests':tests,'initial_harness_attempt':'Verifier correctly rejected missing body; initial inline harness caught wrong exception class. This test catches the actual ValueError and preserves all verifier checks.'}
print(json.dumps(record,indent=2))
