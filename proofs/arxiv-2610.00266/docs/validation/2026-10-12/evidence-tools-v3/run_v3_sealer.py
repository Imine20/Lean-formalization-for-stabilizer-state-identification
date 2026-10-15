#!/usr/bin/env python3
"""Root-only actual V3 verifier runner. Never runs Lean or overwrites old evidence."""
from pathlib import Path
import datetime, hashlib, json, shutil, subprocess, sys, time

ROOT = Path("/data/lean/projects/ExactCriticalCurve")
SOURCE = "a741ad2633d99a28fb4bbbe86e3a9a0ac5b7970b"
DIRECTORY = "docs/validation/2026-10-12/evidence-tools-v3"
EVIDENCE = ROOT/"docs/validation/2026-10-12/main-release-correspondence-a741ad2-strict-v3"
WORK = ROOT/"artifacts/main-release-strict-sealing-a741ad2-v3"
ACCEPTANCE = Path("/data/lean/acceptance/ExactCriticalCurve-correspondence-release-20261012-a741ad2")
DRIVER = ROOT/"artifacts/main-release-correspondence-a741ad2"
TIMING = ROOT/"artifacts/proof-timing-correspondence-release-a741ad2"

def require(ok, message):
    if not ok:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

def write(path, data):
    path.write_text(json.dumps(data,ensure_ascii=False,indent=2)+"\n")

def main():
    require(Path(__file__).resolve() == ROOT/DIRECTORY/"run_v3_sealer.py",
            "Execute only the integrated committed root V3 runner")
    require(not WORK.exists() and not EVIDENCE.exists(), "Refusing to overwrite a prior attempt")
    WORK.mkdir(parents=True)
    command=["python3",DIRECTORY+"/verify_joint_gate_strict.py","--root",str(ROOT),
             "--source",SOURCE,"--acceptance",str(ACCEPTANCE),"--driver",str(DRIVER),
             "--timing",str(TIMING),"--require-main-proof","--evidence",str(EVIDENCE)]
    execution={"schema_version":1,"source_revision":SOURCE,"command":command,
               "runner_sha256":sha(Path(__file__)),"started_at_utc":utc()}
    start=time.monotonic()
    try:
        directory=ROOT/DIRECTORY
        sys.path.insert(0,str(directory))
        from verify_joint_gate_strict import runtime_bundle
        candidate=subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip()
        for name in ["audit_call_inventory.py","verify_joint_gate_strict.py",
                     "snapshot_verified_release.py","tool-bundle.json","run_v3_sealer.py"]:
            committed=subprocess.check_output(["git","show",candidate+":"+DIRECTORY+"/"+name],cwd=ROOT)
            require(committed == (directory/name).read_bytes(), "Runtime V3 file differs from candidate Git: "+name)
        execution["tool_candidate_commit"]=candidate
        before=runtime_bundle(ROOT,SOURCE)
        execution["evidence_tool_successor_before"]=before
        write(WORK/"execution.json",execution)
        with (WORK/"stdout.log").open("wb") as out, (WORK/"stderr.log").open("wb") as err:
            process=subprocess.run(command,cwd=ROOT,stdout=out,stderr=err)
        execution.update(exit_code=process.returncode,finished_at_utc=utc(),
                         elapsed_seconds=time.monotonic()-start,
                         stdout_sha256=sha(WORK/"stdout.log"),stderr_sha256=sha(WORK/"stderr.log"))
        after=runtime_bundle(ROOT,SOURCE)
        execution["evidence_tool_successor_after"]=after
        write(WORK/"execution.json",execution)
        require(process.returncode == 0, "Actual V3 strict verifier exited nonzero")
        require(before == after, "Evidence tools changed during execution")
        binding=json.loads((EVIDENCE/"source-binding.json").read_text())
        require(json.loads((WORK/"stdout.log").read_text()) == binding,
                "Actual strict stdout differs from source binding")
        require(binding["accepted_source_commit"] == SOURCE and binding["paper_main_complete"] is True,
                "Wrong source/main-release binding")
        require(binding["evidence_tool_successor"] == after, "Wrong binding tool successor")
        require(binding["verifier_sha256"] == after["tools_sha256"]["verify_joint_gate_strict.py"] and
                binding["inventory_extractor_sha256"] == after["tools_sha256"]["audit_call_inventory.py"],
                "Strict binding executable hashes differ")
        for name in ["stdout.log","stderr.log"]:
            shutil.copy2(WORK/name,EVIDENCE/name)
        receipt={"schema_version":1,"source_revision":SOURCE,"command":command,"exit_code":0,
                 "started_at_utc":execution["started_at_utc"],"finished_at_utc":execution["finished_at_utc"],
                 "elapsed_seconds":execution["elapsed_seconds"],
                 "verifier_sha256":binding["verifier_sha256"],
                 "inventory_extractor_sha256":binding["inventory_extractor_sha256"],
                 "snapshot_verifier_sha256":after["tools_sha256"]["snapshot_verified_release.py"],
                 "tool_bundle_sha256":after["manifest_sha256"],
                 "stdout_sha256":sha(EVIDENCE/"stdout.log"),"stderr_sha256":sha(EVIDENCE/"stderr.log"),
                 "source_binding_sha256":sha(EVIDENCE/"source-binding.json")}
        require(not (EVIDENCE/"strict-verification-receipt.json").exists(), "Receipt already exists")
        shutil.copy2(WORK/"execution.json",EVIDENCE/"strict-verification-execution.json")
        write(EVIDENCE/"strict-verification-receipt.json",receipt)
        print(json.dumps({"status":"actual_v3_strict_exit_zero","source":SOURCE,
                          "receipt":str(EVIDENCE/"strict-verification-receipt.json")}))
    except Exception as error:
        execution.update(failure=str(error),failed_at_utc=utc(),elapsed_seconds=time.monotonic()-start)
        write(WORK/"execution.json",execution)
        write(WORK/"failure.json",{"status":"failed","source_revision":SOURCE,"reason":str(error),
                                   "success_receipt_written":False,"finished_at_utc":utc()})
        raise

if __name__ == "__main__":
    main()
