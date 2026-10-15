#!/usr/bin/env python3
import pathlib,subprocess,os,json,datetime,time,fcntl,hashlib,shutil
SOURCE="a741ad2633d99a28fb4bbbe86e3a9a0ac5b7970b"
EVIDENCE="eb39f8270ea0bb736b388748c456c5b0ab7fee16"
BASE=pathlib.Path("/data/lean/acceptance/ExactCriticalCurve-independent-a741ad2")
P=BASE/"project"
OLD=pathlib.Path("/data/lean/acceptance/ExactCriticalCurve-independent-2db1594")
META=pathlib.Path("/data/lean/projects/ExactCriticalCurve-github-sync/.git/codex-exact-critical-release")
RUN=META/"runs"/SOURCE
STATE=RUN/"state.json"
env=dict(os.environ,GIT_OPTIONAL_LOCKS="0",LEAN_NUM_THREADS="2",PYTHONDONTWRITEBYTECODE="1",MATHLIB_CACHE_DIR=str(BASE/"mathlib-cache"),XDG_CACHE_HOME=str(BASE/"xdg-cache"),MATHLIB_NO_CACHE_ON_UPDATE="1")
for key in ("LEAN_PATH","LEAN_SRC_PATH","LAKE_PACKAGES_DIR"):env.pop(key,None)
for key in ("NO_PROXY","no_proxy"):env[key]=env.get(key,"")+",lakecache.blob.core.windows.net"
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(path):
 h=hashlib.sha256()
 with path.open("rb") as f:
  for block in iter(lambda:f.read(1048576),b""):h.update(block)
 return h.hexdigest()
def blob(commit,path):
 return subprocess.check_output(["git","-C","/data/lean/projects/ExactCriticalCurve","show",commit+":"+path],env=env)
lock=open(RUN/"verification.lock","a")
try:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
except BlockingIOError:raise SystemExit("This source already has a verification runner")
os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
state={"source":SOURCE,"evidence_container":EVIDENCE,"phase":"preparing_independent_environment","pid":os.getpid(),"started_at":now(),"commands":[],"cpu_affinity":sorted(os.sched_getaffinity(0)),"independent_dir":str(BASE),"dependency_mode":"Reuse of public pinned dependency sources and official caches obtained independently by this publication task; copied into separately writable directories. No research caches or project oleans reused."}
def save():
 state["updated_at"]=now();tmp=STATE.with_suffix(".tmp");tmp.write_text(json.dumps(state,indent=2)+"\n");tmp.replace(STATE)
save()
def run(label,args,cwd=P):
 state["current_step"]=label;save();tick=time.monotonic()
 file=BASE/"logs"/(label+".log")
 with file.open("wb") as log:
  p=subprocess.Popen(args,cwd=cwd,env=env,stdout=log,stderr=subprocess.STDOUT)
  state["child_pid"]=p.pid;save();rc=p.wait()
 state["commands"].append({"label":label,"command":args,"exit_code":rc,"seconds":time.monotonic()-tick,"log":str(file),"log_sha256":sha(file)})
 save()
 if rc:raise RuntimeError(label+" failed with exit "+str(rc))
try:
 if BASE.exists():raise RuntimeError("Existing per-source directory must be resumed explicitly")
 BASE.mkdir();(BASE/"logs").mkdir()
 run("clone",["git","-c","core.hooksPath=/dev/null","clone","--no-local","--no-hardlinks","--no-checkout","/data/lean/projects/ExactCriticalCurve",str(P)],BASE)
 run("checkout",["git","-c","core.hooksPath=/dev/null","checkout","--detach",SOURCE])
 if (P/".git/objects/info/alternates").exists():raise RuntimeError("Unexpected alternates")
 if (P/".lake/build").exists():raise RuntimeError("Project cache not initially empty")
 state["project_cache_initially_empty"]=True
 prefix="docs/validation/2026-10-12/main-release-correspondence-a741ad2-strict-v3/"
 ev=BASE/"upstream-evidence";ev.mkdir()
 for path in ["acceptance/result.json","source-binding.json","strict-verification-receipt.json","reproduction.json"]:
  dest=ev/path;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(blob(EVIDENCE,prefix+path))
 result=json.loads((ev/"acceptance/result.json").read_text());binding=json.loads((ev/"source-binding.json").read_text())
 if result["git_commit"]!=SOURCE or result["status"]!="pass" or not result["paper_main_complete"] or not result["inputs_unchanged_through_audit"]:raise RuntimeError("Upstream acceptance not complete")
 if sha(ev/"acceptance/result.json")!=binding["result_sha256"] or sha(ev/"reproduction.json")!=binding["reproduction_sha256"]:raise RuntimeError("Upstream evidence binding mismatch")
 hashes=result["layout"]["formal_source_sha256"]
 for name,h in hashes.items():
  if sha(P/name)!=h:raise RuntimeError("Frozen input mismatch "+name)
 (BASE/"source-inputs.json").write_text(json.dumps(hashes,indent=2)+"\n")
 state["input_count"]=len(hashes)
 for name in ["lean-toolchain","lake-manifest.json","locks/toolchain.json"]:
  if (P/name).read_bytes()!=(OLD/"project"/name).read_bytes():raise RuntimeError("Dependency environment changed; fetch independent new pins instead")
 compiler=json.loads((P/"locks/toolchain.json").read_text())["compiler_assets"]["Linux-x86_64"]
 (P/".toolchain").mkdir()
 archive=P/".toolchain"/(compiler["directory"]+".tar.zst")
 srcarchive=OLD/"project/.toolchain"/archive.name
 if sha(srcarchive)!=compiler["sha256"]:raise RuntimeError("Prior official compiler archive mismatch")
 shutil.copyfile(srcarchive,archive)
 if sha(archive)!=compiler["sha256"]:raise RuntimeError("Copied compiler archive mismatch")
 state["compiler_archive_sha256"]=sha(archive);save()
 run("compiler-bootstrap",["python3","scripts/bootstrap.py"])
 packages=P/".lake/packages";packages.mkdir(parents=True)
 manifest=json.loads((P/"lake-manifest.json").read_text())
 state["dependency_sources"]=[]
 for pkg in manifest["packages"]:
  previous=OLD/"project/.lake/packages"/pkg["name"];dest=packages/pkg["name"]
  rev=subprocess.check_output(["git","-C",str(previous),"rev-parse","HEAD"],env=env,text=True).strip()
  dirty=subprocess.check_output(["git","-C",str(previous),"status","--porcelain"],env=env,text=True).strip()
  if rev!=pkg["rev"] or dirty:raise RuntimeError("Previously independently fetched dependency is not clean/pinned "+pkg["name"])
  run("copy-independent-"+pkg["name"],["cp","-a","--reflink=auto",str(previous),str(dest)],BASE)
  if (dest/".git/objects/info/alternates").exists():raise RuntimeError("Dependency alternates")
  if (dest/".git/HEAD").stat().st_ino==(previous/".git/HEAD").stat().st_ino:raise RuntimeError("Dependency metadata hardlinked")
  if subprocess.check_output(["git","-C",str(dest),"rev-parse","HEAD"],env=env,text=True).strip()!=pkg["rev"]:raise RuntimeError("Copied pin mismatch")
  state["dependency_sources"].append({"name":pkg["name"],"url":pkg["url"],"rev":rev,"independent_fetch_receipt":str(OLD/"logs-attempt-4"/("dependency-"+pkg["name"]+".json"))})
  save()
 run("copy-independent-download-cache",["cp","-a","--reflink=auto",str(OLD/"mathlib-cache"),str(BASE/"mathlib-cache")],BASE)
 if (P/".lake/build").exists():raise RuntimeError("Project caches unexpectedly copied")
 (BASE/"cache-imports.json").write_bytes((OLD/"cache-imports.json").read_bytes())
 # Same old cache is a starting point; the official tool computes the final source's requested imports.
 imports=set()
 for f in list((P/"ExactCriticalCurve").rglob("*.lean"))+list((P/"scripts").glob("*.lean")):
  for line in f.read_text().splitlines():
   if line.startswith("import "):imports.update(x for x in line[7:].split() if x=="Mathlib" or x.startswith("Mathlib."))
 (BASE/"cache-imports.json").write_text(json.dumps(sorted(imports),indent=2)+"\n")
 heavy=open("/data/lean/.proof-slots/heavy.lock","a")
 try:fcntl.flock(heavy,fcntl.LOCK_EX|fcntl.LOCK_NB)
 except BlockingIOError:
  state["phase"]="deferred_heavy_slot_busy";save();raise SystemExit(0)
 state["heavy_lock_acquired_at"]=now();save()
 run("official-cache-completeness",["bash","scripts/lake.sh","exe","cache","get"]+sorted(imports))
 state["phase"]="independent_strict_gate_running";save()
 run("strict-main-proof",["python3","scripts/check.py","--require-main-proof","--output",str(BASE/"acceptance")])
 actual=json.loads((BASE/"acceptance/result.json").read_text())
 if actual.get("status")!="pass" or actual.get("scope")!="main_release" or actual.get("paper_main_complete") is not True or actual.get("inputs_unchanged_through_audit") is not True:raise RuntimeError("Incomplete strict result")
 if actual["git_commit"]!=SOURCE or actual["git_status"] or actual["layout"]["formal_source_sha256"]!=hashes:raise RuntimeError("Independent source binding mismatch")
 for name,h in hashes.items():
  if sha(P/name)!=h:raise RuntimeError("Post-audit input mismatch "+name)
 for cmd in actual["commands"]:
  if cmd["exit_code"]!=0 or sha(BASE/"acceptance"/cmd["log"])!=cmd["log_sha256"]:raise RuntimeError("Audit command/log mismatch")
 state["phase"]="independent_strict_gate_passed_pending_inventory_and_publication"
 state["result_sha256"]=sha(BASE/"acceptance/result.json")
except Exception as error:
 state["phase"]="independent_verification_failed";state["error"]=str(error)
finally:
 state["ended_at"]=now();state["child_pid"]=None;save()
 print(json.dumps({k:state.get(k) for k in ["phase","error","source","pid"]}),flush=True)
