#!/usr/bin/env python3
"""Seal this completed independent source run; never builds, repairs or publishes."""
import pathlib, json, hashlib, subprocess, os, sys, fcntl, datetime
SOURCE="a741ad2633d99a28fb4bbbe86e3a9a0ac5b7970b"
EVIDENCE="eb39f8270ea0bb736b388748c456c5b0ab7fee16"
BASE=pathlib.Path("/data/lean/acceptance/ExactCriticalCurve-independent-a741ad2")
PROJECT=BASE/"project"
PUBLICATION=pathlib.Path("/data/lean/projects/ExactCriticalCurve-github-sync")
META=PUBLICATION/".git/codex-exact-critical-release"
RUN=META/"runs"/SOURCE
WRAPPER_SHA="9e197f767ee685e70ccc055ef53d47c327558ef213042ff2ed6ef6ab09f63eab"
env={**os.environ,"GIT_OPTIONAL_LOCKS":"0","PYTHONDONTWRITEBYTECODE":"1"}
def require(ok,message):
    if not ok: raise RuntimeError(message)
def sha(path):
    h=hashlib.sha256()
    with pathlib.Path(path).open("rb") as stream:
        for block in iter(lambda:stream.read(1024*1024),b""): h.update(block)
    return h.hexdigest()
def git(*args): return subprocess.check_output(["git","-C",str(PROJECT),*args],env=env)
def read(path): return json.loads(pathlib.Path(path).read_text())
def main():
    # This runner and the source runner never acquire the locks in reverse order.
    operation=(META/"operation.lock").open("a")
    fcntl.flock(operation,fcntl.LOCK_EX|fcntl.LOCK_NB)
    verification=(RUN/"verification.lock").open("a")
    fcntl.flock(verification,fcntl.LOCK_EX|fcntl.LOCK_NB)
    state=read(RUN/"state.json")
    require(state["source"]==SOURCE and state["evidence_container"]==EVIDENCE,"Different source/run")
    require(state["phase"]=="independent_strict_gate_passed_pending_inventory_and_publication","Source gate has not finished successfully")
    require(state.get("project_cache_initially_empty") is True,"Missing initial empty project-cache evidence")
    require(git("rev-parse","HEAD").decode().strip()==SOURCE,"Independent HEAD changed")
    require(not git("status","--porcelain").decode().strip(),"Independent worktree is dirty")
    wrapper=PUBLICATION/"scripts/verify_arxiv_2610.py"
    require(sha(wrapper)==WRAPPER_SHA,"Reviewed sealing helper changed; review new helper before proceeding")
    sys.path.insert(0,str(PUBLICATION/"scripts"))
    import verify_arxiv_2610 as seal
    result=seal.verify_acceptance(BASE/"acceptance",PROJECT)
    require(result["git_commit"]==SOURCE and not result["git_status"],"Gate not bound to clean frozen source")
    inputs=read(BASE/"source-inputs.json")
    require(inputs==result["layout"]["formal_source_sha256"],"Initial and final input manifests differ")
    packaged=PUBLICATION/seal.PROJECT_PREFIX
    for name,digest in inputs.items():
        require(sha(PROJECT/name)==digest and sha(packaged/name)==digest,"Independent/publication source mismatch: "+name)
        require(hashlib.sha256(git("show",SOURCE+":"+name)).hexdigest()==digest,"Immutable source mismatch: "+name)
    # The two V3 sealing helpers were added in the later immutable evidence
    # container; they are not retroactively asserted to be present in SOURCE.
    def immutable_blob(name):
        revision=EVIDENCE if name.startswith(seal.V3_DIRECTORY.as_posix()+"/") else SOURCE
        return git("show",revision+":"+name)
    coverage=seal.verify_source_and_coverage(result,BASE/"acceptance",packaged,immutable_blob)
    lock=read(PROJECT/"locks/toolchain.json")
    import platform
    asset=lock["compiler_assets"][platform.system()+"-"+platform.machine()]
    archive=PROJECT/".toolchain"/(asset["directory"]+".tar.zst")
    require(sha(archive)==asset["sha256"],"Compiler archive mismatch")
    require(not (PROJECT/".toolchain"/asset["directory"]).is_symlink(),"Compiler extraction unexpectedly shared")
    require(lock["lean_commit"] in (BASE/"acceptance/compiler.log").read_text(),"Actual compiler identity mismatch")
    for pkg in read(PROJECT/"lake-manifest.json")["packages"]:
        dep=PROJECT/".lake/packages"/pkg["name"]
        def dg(*args): return subprocess.check_output(["git","-C",str(dep),*args],env=env).decode().strip()
        require(dg("rev-parse","HEAD")==pkg["rev"],"Dependency pin mismatch: "+pkg["name"])
        require(not dg("status","--porcelain","--untracked-files=no"),"Dirty dependency: "+pkg["name"])
        require(not any(f.endswith(".lean") for f in dg("ls-files","--others","--exclude-standard").splitlines()),"Extra dependency source")
        require(not (dep/".git/objects/info/alternates").exists(),"Dependency alternates")
    for command in state["commands"]:
        require(command["exit_code"]==0,"Setup/build command failed: "+command["label"])
        require(sha(command["log"])==command["log_sha256"],"Runner command-log hash mismatch")
    receipt={
      "status":"pass","scope":"independent_frozen_source_main_release",
      "source_commit":SOURCE,"source_tree":git("rev-parse",SOURCE+"^{tree}").decode().strip(),
      "evidence_container":EVIDENCE,"result_sha256":sha(BASE/"acceptance/result.json"),
      "source_input_manifest_sha256":sha(BASE/"source-inputs.json"),
      "input_count":len(inputs),"independent_project_cache_initially_empty":True,
      "dependency_mode":state["dependency_mode"],"compiler_archive_sha256":asset["sha256"],
      "independent_semantic_review_sha256":sha(BASE/"independent-semantic-review.json"),
      "all_frozen_inputs_match_git_independent_checkout_and_publication_draft":True,
      "commands":result["commands"],"strict_coverage":coverage,
      "sealing_helper_sha256":WRAPPER_SHA,"sealer_sha256":sha(__file__),
      "verified_at":datetime.datetime.now(datetime.timezone.utc).isoformat(),
      "limitations":["Independent source acceptance is not exact packaged merge-tree or GitHub acceptance.",
                    "Project rebuilt from empty cache with independently fetched public pinned dependency caches; not every dependency or compiler was rebuilt from source.",
                    "Semantic review is AI review; independent human mathematical review remains outstanding."]
    }
    target=BASE/"independent-source-binding.json"
    require(not target.exists(),"Source already sealed; inspect existing receipt instead of replacing it")
    target.write_text(json.dumps(receipt,indent=2)+"\n")
    (RUN/"independent-sealed.json").write_bytes(target.read_bytes())
    print(json.dumps({"status":"pass","scope":receipt["scope"],"input_count":len(inputs),"receipt":str(target),"receipt_sha256":sha(target)}))
if __name__=="__main__": main()
