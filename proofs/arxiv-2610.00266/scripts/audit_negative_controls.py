#!/usr/bin/env python3
"""Isolated adversarial controls for the exact-type/axiom gate; never formal imports."""
import datetime,json,pathlib,subprocess,sys,time
from source_policy import imports
ROOT=pathlib.Path(__file__).resolve().parents[1]
out=ROOT/'artifacts'/('negative-controls-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'))
out.mkdir(parents=True,exist_ok=False)
source=(ROOT/'scripts/PilotExpectedTypes.lean').read_text()+r'''
/- Deliberately invalid audit fixtures, confined to this generated test file. -/
namespace AuditNegativeControl
def ExpectedTrue : Prop := True
theorem good : True := True.intro
theorem extraHypothesis (h : True) : True := h
def propositionImpostor : True := True.intro
axiom forbiddenFixture : False
theorem transitiveForbidden : True := False.elim forbiddenFixture
def ExpectedUniverse.{u} : Prop := ∀ X : Type u, True
theorem monomorphic (X : Type) : True := True.intro
end AuditNegativeControl

open Lean Elab Command in
run_cmd do
  auditExactTheorem `AuditNegativeControl.good `AuditNegativeControl.ExpectedTrue
  for (bad, expected) in #[
      (`AuditNegativeControl.extraHypothesis, `AuditNegativeControl.ExpectedTrue),
      (`AuditNegativeControl.propositionImpostor, `AuditNegativeControl.ExpectedTrue),
      (`AuditNegativeControl.transitiveForbidden, `AuditNegativeControl.ExpectedTrue),
      (`AuditNegativeControl.monomorphic, `AuditNegativeControl.ExpectedUniverse)] do
    let rejected ← try
        auditExactTheorem bad expected
        pure false
      catch _ => pure true
    unless rejected do
      throwError "AUDIT_NEGATIVE_CONTROL_FAILED: {bad} was accepted"
    logInfo m!"NEGATIVE_CONTROL_REJECTED {bad}"
  logInfo "NEGATIVE_CONTROLS_OK"
'''
fixture=out/'Controls.lean';fixture.write_text(source)
records=[]
def run(label,cmd):
 start=time.monotonic()
 with (out/(label+'.log')).open('w') as log:result=subprocess.run(cmd,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
 records.append({'label':label,'command':cmd,'exit_code':result.returncode,'seconds':time.monotonic()-start})
 return result.returncode,(out/(label+'.log')).read_text()
code,log=run('type_axiom_controls',['bash','scripts/lake.sh','env','lean',str(fixture)])
passed=code==0 and 'NEGATIVE_CONTROLS_OK' in log and log.count('NEGATIVE_CONTROL_REJECTED')==4
code,log=run('missing_main',['bash','scripts/lake.sh','env','lean','scripts/ReleaseAudit.lean'])
passed=passed and code!=0 and 'MAIN_RELEASE_BLOCKED' in log
code,log=run('optimized_python',['python3','-O','scripts/source_policy.py'])
passed=passed and code!=0 and 'Optimized Python disables assertions' in log
import_controls=[]
for text in ['module\npublic import Scratch.Hidden\nimport Mathlib', 'public import Unapproved.Hidden', 'private import Scratch.Hidden', 'import\nScratch.Hidden']:
 try:
  imports(text)
  rejected=False
 except AssertionError:
  rejected=True
 import_controls.append({'source':text,'rejected':rejected})
 passed=passed and rejected
passed=passed and imports('import Mathlib\n/- ignored import Scratch.Hidden -/\nimport ExactCriticalCurve.Main')==['Mathlib','ExactCriticalCurve.Main']
record={'status':'pass' if passed else 'fail','formal_imports_contain_fixtures':False,'commands':records,'import_controls':import_controls}
(out/'result.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'status':record['status'],'record':str(out/'result.json')}))
sys.exit(0 if passed else 1)
