#!/usr/bin/env python3
"""Rebuild an immutable commit in a new directory; never delete an existing checkout."""
import argparse,datetime,hashlib,json,pathlib,platform,shutil,subprocess,tarfile,time
ROOT=pathlib.Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser()
p.add_argument('--dest',type=pathlib.Path,required=True)
p.add_argument('--revision',default='HEAD')
p.add_argument('--compiler-dir',type=pathlib.Path,required=True)
p.add_argument('--dependency-source',type=pathlib.Path,required=True)
p.add_argument('--cached-dependencies',action='store_true',
 help='Copy verified package caches; omit to rebuild required dependency modules from source.')
p.add_argument('--require-main-proof',action='store_true',
 help='Require all original paper main types and proof bodies in addition to the full pilot gate.')
a=p.parse_args()
dest=a.dest.resolve()
if dest.exists():raise SystemExit('Fresh destination must not already exist')
compiler=a.compiler_dir.resolve()
revision=subprocess.check_output(['git','rev-parse',a.revision],cwd=ROOT,text=True).strip()
dest.mkdir(parents=True)
logs=dest/'logs';logs.mkdir()
project=dest/'project'
record={'source_revision':revision,'scope':'main_release' if a.require_main_proof else 'pilot','main_paper_complete':False,
 'dependency_mode':'verified_source_with_existing_build_cache' if a.cached_dependencies else 'required_dependency_modules_from_source',
 'commands':[],'started_at':datetime.datetime.now(datetime.timezone.utc).isoformat()}
def run(label,cmd,cwd=None):
 start=time.monotonic()
 with (logs/(label+'.log')).open('w') as log:
  result=subprocess.run(cmd,cwd=cwd,stdout=log,stderr=subprocess.STDOUT)
 record['commands'].append({'label':label,'command':cmd,'exit_code':result.returncode,
  'seconds':time.monotonic()-start,'log_sha256':hashlib.sha256((logs/(label+'.log')).read_bytes()).hexdigest()})
 (dest/'reproduction.json').write_text(json.dumps(record,indent=2)+'\n')
 print(label,result.returncode,round(time.monotonic()-start,2),flush=True)
 if result.returncode:raise RuntimeError(label+' failed')
try:
 run('clone',['git','clone','--no-hardlinks',str(ROOT),str(project)])
 run('checkout',['git','checkout','--detach',revision],project)
 lock=json.loads((project/'locks/toolchain.json').read_text())
 asset=lock['compiler_assets'][platform.system()+'-'+platform.machine()]
 version=subprocess.check_output([str(compiler/'bin/lean'),'--version'],text=True)
 if lock['lean_commit'] not in version:raise RuntimeError('Compiler commit mismatch')
 record['compiler_version']=version.strip()
 (project/'.toolchain').mkdir()
 (project/'.toolchain'/asset['directory']).symlink_to(compiler,target_is_directory=True)
 (project/'.lake/packages').mkdir(parents=True)
 manifest=json.loads((project/'lake-manifest.json').read_text())
 for pkg in manifest['packages']:
  source=a.dependency_source/pkg['name'];target=project/'.lake/packages'/pkg['name']
  actual=subprocess.check_output(['git','-C',str(source),'rev-parse','HEAD'],text=True).strip()
  if actual!=pkg['rev']:raise RuntimeError('Dependency source not at locked commit: '+pkg['name'])
  if a.cached_dependencies:
   run('copy-'+pkg['name'],['cp','-a','--reflink=auto',str(source),str(target)])
  else:
   run('clone-'+pkg['name'],['git','clone','--no-hardlinks','--no-checkout',str(source),str(target)])
   run('checkout-'+pkg['name'],['git','checkout','--detach',pkg['rev']],target)
   run('origin-'+pkg['name'],['git','remote','set-url','origin',pkg['url']],target)
 if not a.cached_dependencies:
  widget_lock=json.loads((project/'locks/proofwidgets-js.json').read_text())
  archive=project/'vendor/proofwidgets-js.tar.gz'
  if hashlib.sha256(archive.read_bytes()).hexdigest()!=widget_lock['archive_sha256']:
   raise RuntimeError('Display asset archive hash mismatch')
  target=project/'.lake/packages/proofwidgets/.lake/build'
  target.mkdir(parents=True,exist_ok=True)
  with tarfile.open(archive) as tar:
   for item in tar.getmembers():
    if item.name not in {'js/'+name for name in widget_lock['files']} or not item.isfile():
     raise RuntimeError('Unexpected display asset archive member')
    data=tar.extractfile(item).read()
    if hashlib.sha256(data).hexdigest()!=widget_lock['files'][pathlib.Path(item.name).name]:
     raise RuntimeError('Display asset hash mismatch')
    output=target/item.name;output.parent.mkdir(exist_ok=True);output.write_bytes(data)
  record['non_lean_display_assets']=widget_lock
 # Fresh project has no build files. No dependency Lean oleans are copied in source mode.
 if (project/'.lake/build').exists():raise RuntimeError('Project build cache unexpectedly present')
 acceptance_command=['python3','scripts/check.py','--require-pilot','--output',str(dest/'acceptance')]
 if a.require_main_proof:acceptance_command.append('--require-main-proof')
 run('acceptance',acceptance_command,project)
 accepted=json.loads((dest/'acceptance/result.json').read_text())
 if accepted.get('status')!='pass' or not accepted.get('inputs_unchanged_through_audit'):
  raise RuntimeError('Acceptance did not confirm an unchanged successful source-bound audit')
 if a.require_main_proof and (accepted.get('scope')!='main_release' or
   accepted.get('paper_main_complete') is not True):
  raise RuntimeError('Acceptance did not confirm all original paper main proofs')
 record['main_paper_complete']=bool(a.require_main_proof)
 record['result']='pass'
except Exception as error:
 record['result']='fail';record['error']=str(error)
finally:
 record['ended_at']=datetime.datetime.now(datetime.timezone.utc).isoformat()
 (dest/'reproduction.json').write_text(json.dumps(record,indent=2)+'\n')
 print(json.dumps({'result':record['result'],'record':str(dest/'reproduction.json')}))
raise SystemExit(0 if record['result']=='pass' else 1)
