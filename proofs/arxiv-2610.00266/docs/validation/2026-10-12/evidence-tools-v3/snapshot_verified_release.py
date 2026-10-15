#!/usr/bin/env python3
"""Validate a committed strict release receipt, then create a restorable snapshot.

The mandatory full --accepted commit is bound to actual receipt and logs. --check-only never exports.
No live worktree data, execution caches, Git config or credentials are copied.
"""
from pathlib import Path, PurePosixPath
import argparse
import collections
import datetime
import hashlib
import json
import math
import platform
import re
import subprocess
import tarfile

from audit_call_inventory import STRUCTURES, declarations, require
from verify_joint_gate_strict import ALLOWED, audit_markers, command_rows, runner_config, BUNDLE_DIRECTORY, BUNDLE_NAMES, bundle_record

DEFAULT_ROOT = Path("/data/lean/projects/ExactCriticalCurve")
NEW_TOOLS = {"scripts/verify_joint_gate_strict.py", "scripts/audit_call_inventory.py",
             "scripts/snapshot_verified_release.py"}

def run(args, cwd):
    return subprocess.check_output(args, cwd=cwd, stderr=subprocess.STDOUT)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def sha(path):
    return digest(path.read_bytes())

def write(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n")

def git(root, *args):
    return run(["git", *args], root)

def relative_path(text):
    p = PurePosixPath(text)
    require(text and not p.is_absolute() and ".." not in p.parts and "." not in p.parts,
            "Unsafe relative evidence/archive path")
    return str(p)

def tree(root, revision):
    result = {}
    for row in git(root, "ls-tree", "-r", "-z", revision).split(b"\0"):
        if not row:
            continue
        meta, path = row.split(b"\t", 1)
        mode, kind, oid = meta.decode().split()
        result[path.decode()] = (mode, kind, oid)
    return result

def mathematical_paths(entries):
    return {p for p in entries if p.endswith(".lean") and
            (p == "ExactCriticalCurve.lean" or p.startswith("ExactCriticalCurve/"))}

def check_candidate_inventory(accepted_tree, candidate_tree):
    require(mathematical_paths(accepted_tree) == mathematical_paths(candidate_tree),
            "Candidate added or removed formal Lean modules")
    for path, entry in accepted_tree.items():
        if path in mathematical_paths(accepted_tree) or path.startswith("scripts/") or path in {
            "ExactCriticalCurve.lean", "lean-toolchain", "lakefile.toml", "lake-manifest.json",
            "locks/toolchain.json", "locks/proofwidgets-js.json", "vendor/proofwidgets-js.tar.gz",
            "paper/main.tex", "paper/source.json", "docs/pgm-provenance.json"
        }:
            require(candidate_tree.get(path) == entry, "Candidate changed original audit/config input: " + path)
    for path in candidate_tree.keys() - accepted_tree.keys():
        require(not path.startswith("scripts/") or path in NEW_TOOLS,
                "Unapproved new audit/runtime script: " + path)

def forbidden_path(path):
    parts = PurePosixPath(path).parts
    secret_names = {"credentials.json", "credentials", "id_rsa", "id_ed25519", "id_dsa",
                    "authorized_keys", ".netrc", ".npmrc", ".pypirc", ".env"}
    return (any(x in {".lake", ".toolchain", ".ssh", ".aws", ".git"} for x in parts) or
            any(x in secret_names or x.endswith((".key", ".p12", ".pfx")) for x in parts))

def timestamp(s):
    value = datetime.datetime.fromisoformat(s.replace("Z", "+00:00"))
    require(value.tzinfo is not None, "Timestamp missing timezone")
    return value

def finite_nonnegative(value):
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(value) and value >= 0

def full_commit(value):
    require(isinstance(value, str) and re.fullmatch(r"[0-9a-f]{40}", value) is not None,
            "Accepted source must be a full lowercase 40-hex commit")
    return value

def scoped_directory(value, root, parent, prefix=None):
    path = (root / value).resolve()
    require(parent in path.parents and path != parent, "Evidence path escapes allowed root: " + value)
    if prefix is not None:
        require(path.parent == parent and path.name.startswith(prefix),
                "Unexpected execution directory: " + value)
    return path

def verify_receipt(receipt, binding, payloads, tool_sha, root, evidence_rel, accepted):
    full_commit(accepted)
    require(receipt.get("schema_version") == 1, "Unsupported strict receipt schema")
    require(receipt.get("source_revision") == accepted, "Wrong receipt release")
    require(type(receipt.get("exit_code")) is int and receipt["exit_code"] == 0,
            "Strict verifier did not record actual exit 0")
    require(timestamp(receipt["started_at_utc"]) <= timestamp(receipt["finished_at_utc"]),
            "Receipt timestamps reversed")
    for field, payload in [("source_binding_sha256", "source-binding.json"),
                           ("stdout_sha256", "stdout.log"), ("stderr_sha256", "stderr.log")]:
        require(receipt[field] == digest(payloads[payload]), "Strict receipt payload hash mismatch: " + field)
    require(json.loads(payloads["stdout.log"]) == binding,
            "Actual strict verifier stdout does not equal the committed binding")
    for field in ["verifier_sha256", "inventory_extractor_sha256"]:
        require(receipt[field] == binding[field] == tool_sha[field],
                "Strict executed tool differs from candidate Git: " + field)
    successor = binding["evidence_tool_successor"]
    require(receipt["tool_bundle_sha256"] == successor["manifest_sha256"] ==
            tool_sha["tool_bundle_sha256"], "Strict receipt manifest differs")
    require(receipt["snapshot_verifier_sha256"] == successor["tools_sha256"]["snapshot_verified_release.py"] ==
            tool_sha["snapshot_verifier_sha256"], "Strict receipt snapshot tool differs")
    cmd = receipt["command"]
    require(isinstance(cmd, list) and len(cmd) > 2 and all(isinstance(s, str) for s in cmd),
            "Receipt command is not literal argv")
    require(Path(cmd[0]).name in {"python3", "python3.13", "python3.12", "python3.11", "python3.10"},
            "Unexpected strict verifier interpreter")
    require((root / cmd[1]).resolve() == root / BUNDLE_DIRECTORY / "verify_joint_gate_strict.py",
            "Unexpected strict verifier script")
    args = cmd[2:]
    required = {"--source", "--acceptance", "--driver", "--timing", "--evidence"}
    if "--root" in args:
        required.add("--root")
    require(args.count("--require-main-proof") == 1, "Receipt lacks unique --require-main-proof")
    values = {}
    for flag in required:
        require(args.count(flag) == 1, "Missing/repeated receipt argument: " + flag)
        i = args.index(flag)
        require(i + 1 < len(args), "Missing receipt argument value")
        values[flag] = args[i + 1]
    require(len(args) == 1 + 2 * len(required) and
            {x for x in args if x.startswith("--")} == required | {"--require-main-proof"},
            "Unexpected strict verifier arguments")
    require(values["--source"] == accepted, "Receipt source differs from requested immutable release")
    if "--root" in values:
        require(Path(values["--root"]).resolve() == root, "Receipt root differs")
    paths = {
        "acceptance": scoped_directory(values["--acceptance"], root, Path("/data/lean/acceptance"), "ExactCriticalCurve-"),
        "driver": scoped_directory(values["--driver"], root, root/"artifacts"),
        "timing": scoped_directory(values["--timing"], root, root/"artifacts", "proof-timing-"),
        "evidence": scoped_directory(values["--evidence"], root, root/"docs/validation")}
    require(paths["evidence"] == (root/evidence_rel).resolve(), "Wrong receipt evidence path")
    return paths

def verify_closed_events(events, runner, binding, receipt, accepted):
    full_commit(accepted)
    starts = {n:json.loads(data) for n,data in events.items() if n.endswith(".start.json")}
    require(starts, "No closed gate timing evidence")
    pairs = []
    for name, start in starts.items():
        endname = name.replace(".start.json", ".end.json")
        require(endname in events, "Active timing event copied into final evidence")
        end = json.loads(events[endname])
        require(start["id"] == end["id"], "Timing identity mismatch")
        require(end["seconds"] is None or finite_nonnegative(end["seconds"]), "Invalid event duration")
        pairs.append((start, end))
    argv = runner["command"][:runner["command"].index("--")]
    def option(flag):
        require(argv.count(flag) == 1, "Bad runner timing option " + flag)
        return argv[argv.index(flag)+1]
    label, actor, package = option("--label"), option("--actor"), option("--package")
    require(option("--phase") == "release_gate" and option("--slot") == "/data/lean/.proof-slots/heavy.lock",
            "Not the final shared release gate")
    matching = [(s,e) for s,e in pairs if (s["label"],s["actor"],s["package"]) == (label,actor,package)]
    waits = [s for s,e in matching if s["phase"] == "wait_compute" and
             s["context"]["commit"] == accepted and e["outcome"] == "ok" and
             e.get("slot") == "/data/lean/.proof-slots/heavy.lock"]
    gates = [(s,e) for s,e in matching if s["phase"] == "release_gate" and
             e["outcome"] == "ok" and e.get("exit_code") == e.get("expected_exit_code") == 0 and
             e.get("slot") == "/data/lean/.proof-slots/heavy.lock" and
             any(w["process_clock_domain"] == s["process_clock_domain"] for w in waits)]
    require(len(gates) == 1, "No unique successful source-bound final release event")
    start, end = gates[0]
    claimed = binding["closed_source_bound_gate_event"]
    require(claimed["id"] == start["id"] and claimed["seconds"] == end["seconds"] and
            claimed["phase"] == "release_gate", "Binding does not match closed actual gate")
    require(set(claimed["source_bound_wait_event_ids"]) == {
            w["id"] for w in waits if w["process_clock_domain"] == start["process_clock_domain"]},
            "Binding wait identity differs")
    require(timestamp(end["utc"]) <= timestamp(receipt["finished_at_utc"]),
            "Receipt predates actual gate completion")
    return start["id"]

def verify_release_identity(result, repro, binding, accepted, acceptance):
    full_commit(accepted)
    require(result["status"] == repro["result"] == "pass", "Actual final gate has not passed")
    require(result["scope"] == repro["scope"] == "main_release", "Not main-release acceptance")
    require(result["git_commit"] == repro["source_revision"] == binding["accepted_source_commit"] == accepted,
            "Acceptance source mismatch")
    require(result["paper_main_complete"] is True and repro["main_paper_complete"] is True and
            binding["paper_main_complete"] is True, "Main proofs not verified")
    require(binding["acceptance_directory"] == str(acceptance), "Wrong acceptance directory")

def verify_runner_source(runner, accepted):
    full_commit(accepted)
    require(runner["revision"] == accepted, "Runner revision differs from requested full source")
    child = runner["command"][runner["command"].index("--")+1:]
    require(child.count("--revision") == 1 and
            child.index("--revision")+1 < len(child) and
            child[child.index("--revision")+1] == accepted,
            "Actual reproducer argv source differs")

def validate_release(root, candidate_ref, evidence_rel, accepted):
    full_commit(accepted)
    root = root.resolve()
    evidence_rel = relative_path(evidence_rel)
    candidate = git(root, "rev-parse", candidate_ref + "^{commit}").decode().strip()
    require(git(root, "rev-parse", accepted + "^{commit}").decode().strip() == accepted, "Frozen release absent")
    git(root, "merge-base", "--is-ancestor", accepted, candidate)
    accepted_tree, candidate_tree = tree(root, accepted), tree(root, candidate)
    check_candidate_inventory(accepted_tree, candidate_tree)
    for path, (mode, kind, _) in candidate_tree.items():
        require(mode in {"100644", "100755"} and kind == "blob", "Unsupported non-file tracked object: " + path)
        require(not forbidden_path(path), "Excluded cache/credential path tracked: " + path)
        if path.endswith(".start.json"):
            require(path.replace(".start.json", ".end.json") in candidate_tree,
                    "Unclosed tracked event in candidate: " + path)
    def blob(rev, path):
        return git(root, "show", rev + ":" + relative_path(path))
    def ev(path):
        return blob(candidate, evidence_rel + "/" + path)
    result_bytes, repro_bytes, binding_bytes = ev("acceptance/result.json"), ev("reproduction.json"), ev("source-binding.json")
    result, repro, binding = map(json.loads, [result_bytes, repro_bytes, binding_bytes])
    receipt = json.loads(ev("strict-verification-receipt.json"))
    payloads = {"source-binding.json":binding_bytes, "stdout.log":ev("stdout.log"), "stderr.log":ev("stderr.log")}
    manifest_path = BUNDLE_DIRECTORY + "/tool-bundle.json"
    tool_payloads = {n:blob(candidate,BUNDLE_DIRECTORY+"/"+n) for n in BUNDLE_NAMES}
    successor = bundle_record(blob(candidate,manifest_path), tool_payloads,
        {"scripts/"+n:blob(accepted,"scripts/"+n) for n in BUNDLE_NAMES}, accepted)
    require(binding["evidence_tool_successor"] == successor,
            "Strict binding tool bundle differs from committed candidate")
    tool_sha = {"verifier_sha256":digest(tool_payloads["verify_joint_gate_strict.py"]),
                "inventory_extractor_sha256":digest(tool_payloads["audit_call_inventory.py"]),
                "snapshot_verifier_sha256":digest(tool_payloads["snapshot_verified_release.py"]),
                "tool_bundle_sha256":successor["manifest_sha256"]}
    # The runtime implementation and its complete manifest must equal candidate Git.
    for name in BUNDLE_NAMES | {"tool-bundle.json"}:
        require(Path(__file__).with_name(name).read_bytes() == blob(candidate,BUNDLE_DIRECTORY+"/"+name),
                "Running versioned snapshot/checker differs from candidate: " + name)
    paths = verify_receipt(receipt, binding, payloads, tool_sha, root, evidence_rel, accepted)
    acceptance = paths["acceptance"]
    verify_release_identity(result, repro, binding, accepted, acceptance)
    require(result["inputs_unchanged_through_audit"] is True and result["git_status"] == "",
            "Acceptance inputs were dirty or changed")
    for flag in ["clean_project_build", "all_source_and_audit_hashes_match_immutable_git_and_clean_clone",
                 "inputs_unchanged_through_audit", "current_clone_HEAD_and_status_verified",
                 "required_command_inventory_argv_and_scope_verified"]:
        require(binding[flag] is True, "Missing strict verification guarantee: " + flag)
    require(binding["result_sha256"] == digest(result_bytes) and
            binding["reproduction_sha256"] == digest(repro_bytes), "Strict binding/result/reproduction hash mismatch")
    require(timestamp(result["ended_at"]) <= timestamp(receipt["finished_at_utc"]) and
            timestamp(repro["ended_at"]) <= timestamp(receipt["finished_at_utc"]), "Receipt predates acceptance")
    layout = result["layout"]
    require(json.loads(ev("preflight-layout.json")) == layout, "Preflight layout differs")
    require(layout["status"] == "pass" and layout["dependencies_pinned"] is True, "Layout policy not passed")
    formal = mathematical_paths(accepted_tree)
    mandatory = formal | {p for p in accepted_tree if p.count("/") == 1 and p.startswith("scripts/") and
                          Path(p).suffix in {".lean", ".py", ".sh"}} | {
        "docs/pgm-provenance.json", "lean-toolchain", "lakefile.toml", "lake-manifest.json",
        "locks/toolchain.json", "locks/proofwidgets-js.json", "vendor/proofwidgets-js.tar.gz", "paper/source.json"}
    require(set(layout["formal_source_sha256"]) == mandatory and
            set(layout["reachable_formal_modules"]) == formal, "Frozen source fingerprint inventory differs")
    known = set()
    for path, expected in layout["formal_source_sha256"].items():
        data = blob(accepted, path)
        require(digest(data) == expected and digest(blob(candidate, path)) == expected,
                "Candidate or accepted mathematical/audit fingerprint changed: " + path)
        if path in formal:
            known.update(declarations(data.decode()))
    provenance = json.loads(blob(accepted, "paper/source.json"))
    require(digest(blob(candidate, "paper/main.tex")) == provenance["main_tex_sha256"] ==
            digest(blob(accepted, "paper/main.tex")), "Paper provenance changed")
    runner = json.loads(ev("runner.json"))
    verify_runner_source(runner, accepted)
    ra = runner_config(root, accepted, acceptance, paths["timing"], runner, True)
    expected_mode = "verified_source_with_existing_build_cache" if ra.cached_dependencies else "required_dependency_modules_from_source"
    require(repro["dependency_mode"] == binding["dependency_mode"] == expected_mode, "Dependency mode mismatch")
    project = acceptance / "project"
    lock = json.loads(blob(accepted, "locks/toolchain.json"))
    require(result["toolchain_lock"] == lock and lock["lean_commit"] in repro["compiler_version"],
            "Compiler lock mismatch")
    asset = lock["compiler_assets"][platform.system()+"-"+platform.machine()]
    commands = {"compiler":[str(project/".toolchain"/asset["directory"]/"bin/lean"),"--version"],
        "build":["bash","scripts/lake.sh","build"],
        "axioms":["bash","scripts/lake.sh","env","lean","scripts/ProjectAudit.lean"],
        "pilot_types":["bash","scripts/lake.sh","env","lean","scripts/PilotExpectedTypes.lean"],
        "release":["bash","scripts/lake.sh","env","lean","scripts/ReleaseAudit.lean"]}
    command_rows(result["commands"], commands)
    for c in result["commands"]:
        require(c["log"] == c["label"]+".log" and
                digest(ev("acceptance/"+c["log"])) == c["log_sha256"], "Acceptance log hash mismatch")
    require(lock["lean_commit"] in ev("acceptance/compiler.log").decode(), "Compiler log lacks locked commit")
    reproduction_commands = {"clone":["git","clone","--no-hardlinks",str(root),str(project)],
        "checkout":["git","checkout","--detach",accepted]}
    for package in json.loads(blob(accepted,"lake-manifest.json"))["packages"]:
        name = package["name"]; src = Path(ra.dependency_source)/name; dst = project/".lake/packages"/name
        if ra.cached_dependencies:
            reproduction_commands["copy-"+name] = ["cp","-a","--reflink=auto",str(src),str(dst)]
        else:
            reproduction_commands["clone-"+name] = ["git","clone","--no-hardlinks","--no-checkout",str(src),str(dst)]
            reproduction_commands["checkout-"+name] = ["git","checkout","--detach",package["rev"]]
            reproduction_commands["origin-"+name] = ["git","remote","set-url","origin",package["url"]]
    reproduction_commands["acceptance"] = ["python3","scripts/check.py","--require-pilot","--output",
                                           str(acceptance/"acceptance"),"--require-main-proof"]
    command_rows(repro["commands"], reproduction_commands)
    for c in repro["commands"]:
        require(digest(ev("logs/"+c["label"]+".log")) == c["log_sha256"], "Reproduction log hash mismatch")
    ax = ev("acceptance/axioms.log").decode()
    unions = re.findall(r"^PROJECT_AXIOMS_UNION \[(.*?)\]$",ax,re.M)
    require(len(unions) == 1 and {s.strip() for s in unions[0].split(",")} == ALLOWED ==
            set(binding["allowed_axioms_union"]), "Axiom closure mismatch")
    counts = re.findall(r"^PROJECT_AUDIT_OK declarations=(\d+) theorems=(\d+)$",ax,re.M)
    require(len(counts) == 1, "Project audit completion missing or repeated")
    decls = [json.loads(s)["declaration"] for s in re.findall(r"^DECLARATION_AUDIT (.*)$",ax,re.M)]
    require(len(decls) == len(set(decls)) == int(counts[0][0]) == binding["project_declarations"],
            "All-declaration audit inventory mismatch")
    require(int(counts[0][1]) == binding["project_theorem_kind_declarations"], "Theorem count mismatch")
    stats = {}
    for label, path in [("pilot_types","scripts/PilotExpectedTypes.lean"),("release","scripts/ReleaseAudit.lean")]:
        stats[label] = audit_markers(ev("acceptance/"+label+".log").decode(), blob(accepted,path).decode(),
                                     known, set(decls), label=="release")
        require(stats[label]["constant_only_structure_checks"] ==
                ({n:1 for n in STRUCTURES} if label=="pilot_types" else {}), "Structure exception mismatch")
    require(stats == binding["executed_independent_checks"], "Executed audit inventory differs from strict binding")
    event_prefix = evidence_rel+"/timing/events/"
    events = {p[len(event_prefix):]:blob(candidate,p) for p in candidate_tree if p.startswith(event_prefix)}
    gate_id = verify_closed_events(events, runner, binding, receipt, accepted)
    # This history, not --all refs, is the complete scope of the exported Git bundle.
    history_objects = git(root,"rev-list","--objects",candidate).decode().splitlines()
    for row in history_objects:
        fields = row.split(" ",1)
        if len(fields) == 2:
            require(not forbidden_path(fields[1]), "Excluded cache/credential path in release history: "+fields[1])
    return {"candidate":candidate,"accepted":accepted,"evidence":evidence_rel,"binding":binding,
            "candidate_tree":candidate_tree,"result":result,"receipt_sha256":digest(ev("strict-verification-receipt.json")),
            "closed_gate_event":gate_id}

def create_snapshot(root, validated, snapshot):
    snapshot = snapshot.resolve(); candidate = validated["candidate"]; accepted = full_commit(validated["accepted"])
    archive_path = snapshot.with_suffix(".tar.gz")
    restore = snapshot.with_name(snapshot.name+"-restore-check.git")
    export = snapshot.with_name(snapshot.name+"-bundle-source.git")
    for path in [snapshot, archive_path, restore, export, snapshot.with_suffix(".archive-verification.json")]:
        require(not path.exists(), "Refusing to overwrite snapshot/check output: "+str(path))
    snapshot.mkdir(parents=True)
    run(["git","init","--bare",str(export)],root)
    run(["git","fetch","--no-tags",str(root),candidate+":refs/heads/verified-release"],export)
    run(["git","symbolic-ref","HEAD","refs/heads/verified-release"],export)
    bundle = snapshot/"release-history.bundle"
    run(["git","bundle","create",str(bundle),"refs/heads/verified-release"],export)
    (snapshot/"git-bundle-verify.log").write_bytes(run(["git","bundle","verify",str(bundle)],export))
    (snapshot/"git-refs.txt").write_bytes(run(["git","show-ref"],export))
    restore_log = run(["git","clone","--bare","--branch","verified-release",str(bundle),str(restore)],root)
    require(git(restore,"rev-parse","HEAD^{commit}").decode().strip() == candidate, "Restored candidate HEAD differs")
    require(git(restore,"rev-parse",accepted+"^{commit}").decode().strip() == accepted, "Accepted history missing")
    # Restore every candidate blob, not only proof inputs.
    for path, (_,_,oid) in validated["candidate_tree"].items():
        require(git(restore,"rev-parse",candidate+":"+path).decode().strip() == oid,
                "Git bundle restore missing/mismatched blob: "+path)
    source_tar = snapshot/"source-checkout.tar.gz"
    run(["git","archive","--format=tar.gz","--prefix=ExactCriticalCurve/",
         "--output="+str(source_tar),candidate],root)
    found = set()
    with tarfile.open(source_tar,"r:gz") as tar:
        for member in tar:
            relative_path(member.name)
            if member.isdir():
                continue
            require(member.isfile(), "Unexpected non-file source archive member")
            path = str(PurePosixPath(member.name).relative_to("ExactCriticalCurve"))
            require(path not in found, "Duplicate source archive member")
            found.add(path)
            require(tar.extractfile(member).read() == git(restore,"show",candidate+":"+path),
                    "Source archive differs from restored candidate: "+path)
    require(found == set(validated["candidate_tree"]), "Source archive omitted/added tracked files")
    (snapshot/"git-restore-check.log").write_bytes(restore_log+b"\nAll candidate blobs restored and archive inventory exact.\n")
    write(snapshot/"resume.json",{
        "project":"ExactCriticalCurve / arXiv:2610.00266v1",
        "snapshot_metadata_commit":candidate,"accepted_mathematical_source_commit":accepted,
        "paper_main_complete":True,"accepted_gate_evidence":validated["evidence"],
        "strict_receipt_sha256":validated["receipt_sha256"],"closed_gate_event":validated["closed_gate_event"],
        "executed_independent_checks":validated["binding"]["executed_independent_checks"],
        "allowed_axioms_union":validated["binding"]["allowed_axioms_union"],
        "limitations":validated["binding"]["limitations"],
        "bundle_scope":"Candidate commit and its complete ancestor history; unrelated refs excluded.",
        "worktree_data_included":False,"active_package_logs_included":False,
        "credential_boundary":"No Git config or untracked files copied; known credential/cache paths rejected throughout exported history. Source text is governed by the repository no-credentials policy.",
        "toolchain_and_dependency_caches_included":False,
        "created_at_utc":datetime.datetime.now(datetime.timezone.utc).isoformat()})
    files = {str(p.relative_to(snapshot)):{"bytes":p.stat().st_size,"sha256":sha(p)}
             for p in sorted(snapshot.rglob("*")) if p.is_file()}
    write(snapshot/"manifest.json",{"schema_version":1,"snapshot_metadata_commit":candidate,
          "accepted_mathematical_source_commit":accepted,"files":files})
    manifest_bytes = (snapshot/"manifest.json").read_bytes()
    with tarfile.open(archive_path,"w:gz") as tar:
        tar.add(snapshot,arcname=snapshot.name)
    with tarfile.open(archive_path,"r:gz") as tar:
        require(tar.extractfile(snapshot.name+"/manifest.json").read() == manifest_bytes, "Manifest readback differs")
        for rel, expected in files.items():
            data = tar.extractfile(snapshot.name+"/"+rel).read()
            require(len(data) == expected["bytes"] and digest(data) == expected["sha256"], "Outer archive readback mismatch")
    record = {"snapshot":str(snapshot),"archive":str(archive_path),"sha256":sha(archive_path),
        "bytes":archive_path.stat().st_size,"manifest_files_verified":len(files),
        "git_restore_verified":True,"accepted_mathematical_source_commit":accepted,
        "snapshot_metadata_commit":candidate,"strict_receipt_sha256":validated["receipt_sha256"]}
    write(snapshot.with_suffix(".archive-verification.json"),record)
    return record

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root",type=Path,default=DEFAULT_ROOT)
    parser.add_argument("--candidate",required=True)
    parser.add_argument("--accepted",required=True)
    parser.add_argument("--evidence",required=True)
    parser.add_argument("--snapshot",type=Path)
    parser.add_argument("--check-only",action="store_true")
    a = parser.parse_args()
    full_commit(a.accepted)
    require(a.root.resolve() == DEFAULT_ROOT, "Unexpected release source repository")
    require(a.check_only or a.snapshot is not None, "--snapshot required for export")
    validated = validate_release(a.root,a.candidate,a.evidence,a.accepted)
    if a.check_only:
        print(json.dumps({"status":"committed_strict_release_evidence_verified",
              "accepted":a.accepted,"candidate":validated["candidate"],"snapshot_created":False},indent=2))
    else:
        print(json.dumps(create_snapshot(a.root,validated,a.snapshot),indent=2))

if __name__ == "__main__":
    main()
