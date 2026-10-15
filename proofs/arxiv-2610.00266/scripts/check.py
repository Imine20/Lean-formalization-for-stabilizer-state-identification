#!/usr/bin/env python3
"""Build and mechanically audit. A development pass never means main-paper completion."""
import argparse,datetime,hashlib,json,pathlib,platform,subprocess,sys,time
from source_policy import check as source_check
ROOT=pathlib.Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser()
parser.add_argument('--require-main-proof',action='store_true')
parser.add_argument('--require-pilot',action='store_true')
parser.add_argument('--output',type=pathlib.Path)
args=parser.parse_args()
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
out=args.output or ROOT/'artifacts'/('check-'+stamp)
out.mkdir(parents=True,exist_ok=False)
record={'scope':'main_release' if args.require_main_proof else 'pilot' if args.require_pilot else 'development',
        'paper_main_complete':False,'started_at':stamp,'commands':[]}
def command(label,cmd):
    start=time.monotonic()
    with (out/(label+'.log')).open('w') as log:
        p=subprocess.run(cmd,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
    result={'label':label,'command':cmd,'exit_code':p.returncode,'seconds':time.monotonic()-start,
            'log':label+'.log','log_sha256':hashlib.sha256((out/(label+'.log')).read_bytes()).hexdigest()}
    record['commands'].append(result)
    print(label,p.returncode,round(result['seconds'],3),flush=True)
    if p.returncode:raise RuntimeError(label+' failed; see '+str(out/(label+'.log')))
try:
    record['layout']=source_check()
    record['git_commit']=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
    record['git_status']=subprocess.check_output(['git','status','--porcelain'],cwd=ROOT,text=True)
    record['toolchain_lock']=json.loads((ROOT/'locks/toolchain.json').read_text())
    asset=record['toolchain_lock']['compiler_assets'][platform.system()+'-'+platform.machine()]
    command('compiler',[str(ROOT/'.toolchain'/asset['directory']/'bin/lean'),'--version'])
    command('build',['bash','scripts/lake.sh','build'])
    command('axioms',['bash','scripts/lake.sh','env','lean','scripts/ProjectAudit.lean'])
    if args.require_pilot or args.require_main_proof:
        assert (ROOT/'scripts/PilotExpectedTypes.lean').is_file(),'Pilot expected types absent'
        command('pilot_types',['bash','scripts/lake.sh','env','lean','scripts/PilotExpectedTypes.lean'])
    if args.require_main_proof:
        command('release',['bash','scripts/lake.sh','env','lean','scripts/ReleaseAudit.lean'])
    final_layout=source_check()
    if record['layout'] != final_layout: raise RuntimeError('Source or audit inputs changed during checks')
    record['inputs_unchanged_through_audit']=True
    record['paper_main_complete']=bool(args.require_main_proof)
    record['status']='pass'
except Exception as error:
    record['status']='fail';record['error']=str(error)
finally:
    record['ended_at']=datetime.datetime.now(datetime.timezone.utc).isoformat()
    (out/'result.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({'status':record['status'],'scope':record['scope'],'paper_main_complete':record['paper_main_complete'],'record':str(out/'result.json')}))
sys.exit(0 if record['status']=='pass' else 1)
