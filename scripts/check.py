#!/usr/bin/env python3
"""Development/merge gate; --require-main-proof is the stricter release gate."""
from pathlib import Path
import argparse, datetime, hashlib, json, subprocess, time
from check_layout import check, ROOT

p=argparse.ArgumentParser()
p.add_argument('--require-main-proof',action='store_true')
p.add_argument('--output',type=Path,default=ROOT/'artifacts/check')
a=p.parse_args(); a.output.mkdir(parents=True,exist_ok=True)
record={'scope':'main_statement_and_closed_auxiliary_proofs','layout':check(),
    'started_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'git_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
    'working_tree_status':subprocess.check_output(['git','status','--short'],cwd=ROOT,text=True),
    'main_theorem_complete':False,'steps':[],'result':'failed'}
def run(args,name):
    t=time.monotonic()
    with (a.output/name).open('w') as log:
        r=subprocess.run([str(ROOT/'scripts/lake.sh'),*args],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
    record['steps'].append({'args':args,'seconds':round(time.monotonic()-t,3),'exit_code':r.returncode,'log':name})
    return r.returncode,(a.output/name).read_text()
try:
    for cmd,name in [(['build'],'build.log'),(['env','lean','Audit.lean'],'axioms.log')]:
        code,log=run(cmd,name)
        if code: raise RuntimeError(log[-8000:])
    code,log=run(['env','lean','scripts/ReleaseAudit.lean'],'main-release-gate.log')
    if code==0 and 'MAIN_RELEASE_OK' in log:
        record['main_status']='dependencies_closed';record['main_theorem_complete']=True
        record['scope']='complete_original_main_and_all_project_declarations'
    elif code and 'MAIN_RELEASE_BLOCKED' in log:
        record['main_status']='statement_only'
        if a.require_main_proof: raise RuntimeError('Release rejected: main theorem has no proof.')
    else: raise RuntimeError('Unexpected release gate result: '+log)
    assert check()['source_sha256']==record['layout']['source_sha256'], 'Sources changed during check'
    record['result']='pass'
finally:
    record['finished_at']=datetime.datetime.now(datetime.timezone.utc).isoformat()
    (a.output/'check.json').write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'result':record['result'],'main_status':record['main_status'],'output':str(a.output)}))
