#!/usr/bin/env python3
"""Dated independent source snapshot: Git history + current, including uncommitted, source.
No live .git/.lake sync. No toolchains, model files, credential files or private keys.
"""
from pathlib import Path
import argparse, datetime, hashlib, json, os, subprocess, tarfile, tempfile, uuid
from source_policy import EXCLUDED_DIRS, approved, content_check, forbidden
ROOT=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,default=ROOT/'artifacts/snapshots');a=p.parse_args()
a.output=a.output.resolve();a.output.mkdir(parents=True,exist_ok=True)
stamp=datetime.datetime.now(datetime.timezone(datetime.timedelta(hours=8))).strftime('%Y-%m-%d_%H%M%S_Asia-Shanghai')
target=a.output/f'StabilizerLearning-{stamp}-{uuid.uuid4().hex[:8]}.tar.gz'
# A Git bundle contains history: inspect every reachable tree, not only today's checkout.
history={}
for rev in subprocess.check_output(['git','rev-list','--all'],cwd=ROOT,text=True).splitlines():
    entries=subprocess.check_output(['git','ls-tree','-r','-z',rev],cwd=ROOT).split(b'\0')
    for entry in entries:
        if not entry:continue
        meta,name=entry.split(b'\t',1);name=name.decode();mode,kind,oid=meta.decode().split()
        if kind!='blob' or mode=='120000' or not approved(name):
            raise RuntimeError('Unapproved path in reachable Git history; snapshot refused: '+name)
        history[oid]=name
for oid,name in history.items():
    content_check(subprocess.check_output(['git','cat-file','blob',oid],cwd=ROOT),name)
files=[]
for folder,dirs,names in os.walk(ROOT):
    dirs[:]=[d for d in dirs if d not in EXCLUDED_DIRS and not (Path(folder)/d).is_symlink()
        and (Path(folder)/d).resolve()!=a.output]
    for name in names:
        f=Path(folder)/name
        rel=f.relative_to(ROOT).as_posix()
        if not f.is_symlink() and approved(rel):
            content_check(f.read_bytes(),rel);files.append(f)
with tempfile.TemporaryDirectory(prefix='stabilizer-snapshot-') as tmp:
    bundle=Path(tmp)/'history.bundle'
    subprocess.run(['git','bundle','create',str(bundle),'--all'],cwd=ROOT,check=True)
    subprocess.run(['git','bundle','verify',str(bundle)],cwd=ROOT,check=True,stdout=subprocess.DEVNULL)
    manifest={'created_at':stamp,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        'working_tree_status':subprocess.check_output(['git','status','--short'],cwd=ROOT,text=True),
        'scope':'Git bundle plus current source and documentation, including valuable uncommitted Scratch files; executable caches excluded',
        'files':{str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(files)},
        'bundle_sha256':hashlib.sha256(bundle.read_bytes()).hexdigest()}
    meta=Path(tmp)/'snapshot-manifest.json';meta.write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n')
    with tarfile.open(target,'w:gz') as t:
        t.add(bundle,arcname='history.bundle');t.add(meta,arcname='snapshot-manifest.json')
        for f in files:t.add(f,arcname='working-tree/'+str(f.relative_to(ROOT)),recursive=False)
    with tarfile.open(target,'r:gz') as t:
        for name,h in manifest['files'].items():
            assert hashlib.sha256(t.extractfile('working-tree/'+name).read()).hexdigest()==h,name
        assert hashlib.sha256(t.extractfile('history.bundle').read()).hexdigest()==manifest['bundle_sha256']
print(json.dumps({'snapshot':str(target.resolve()),'sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'readback_verified':True,'git_bundle_verified':True,'files':len(files)},ensure_ascii=False))
