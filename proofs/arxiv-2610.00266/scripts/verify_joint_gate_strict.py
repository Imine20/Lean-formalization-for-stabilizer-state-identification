#!/usr/bin/env python3
"""Seal completed immutable acceptance evidence. Does not run or replace audits."""
from pathlib import Path
import argparse, collections, datetime, hashlib, json, platform, re, shutil, subprocess
from audit_call_inventory import STRUCTURES, declarations, extract_inventory, require

ALLOWED = {"Classical.choice", "propext", "Quot.sound"}
MAINS = {"ExactCriticalCurve.finiteSpectrum", "ExactCriticalCurve.criticalCurve",
         "ExactCriticalCurve.criticalCurveTails"}

def read(path):
    return json.loads(path.read_text())

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def git(root, *args):
    return subprocess.check_output(["git", *args], cwd=root)

def option(args, name):
    require(args.count(name)==1, "Expected exactly one option "+name)
    i=args.index(name)
    require(i+1<len(args), "Missing value for "+name)
    return args[i+1]

def command_rows(rows, expected):
    labels=[c["label"] for c in rows]
    require(labels==list(expected), "Missing, repeated or reordered required commands: "+repr(labels))
    for c in rows:
        require(c["exit_code"]==0, "Failed required command "+c["label"])
        require(c["command"]==expected[c["label"]], "Unexpected argv for "+c["label"])

def audit_markers(log, source, known, formal, main=False):
    expected, entries, dynamic=extract_inventory(source, known)
    pattern=r"^KERNEL_EXPECTED_(TYPE|DEFINITION)_OK (constant|body) (\S+)$"
    observed={"constant":collections.Counter(), "body":collections.Counter()}
    for kind, stage, name in re.findall(pattern,log,re.M):
        observed[stage][(kind,name)]+=1
    extra_structures=collections.Counter({("DEFINITION",n):v
        for (k,n),v in expected.items() if k=="DEFINITION" and n in STRUCTURES})
    expected_body=expected-extra_structures
    for stage, target in [("constant",expected),("body",expected_body)]:
        # Check every static name exactly; no counts are inferred from logs.
        require(all(observed[stage][key]==count for key,count in target.items()),
                "Missing/repeated static "+stage+" audit markers")
        require(not(target-observed[stage]), "Missing static "+stage+" audit")
        remainder=observed[stage]-target
        for d in dynamic:
            matches=[key for key,count in remainder.items() if count>0 and
                     key[0]==d["kind"] and key[1].startswith("_private.") and
                     key[1].endswith("."+d["logical_suffix"])]
            require(len(matches)==1, "Private audit suffix missing/ambiguous: "+d["logical_suffix"])
            remainder[matches[0]]-=1
        require(not +remainder, "Unexpected executed "+stage+" audit markers: "+repr(+remainder))
    require(observed["constant"]-observed["body"]==extra_structures,
            "Non-whitelisted constant-only audit check")
    require(not(observed["body"]-observed["constant"]), "Body without corresponding constant")
    if main:
        for name in MAINS:
            require(observed["body"][("TYPE",name)]>0 and name in formal,
                    "Missing actual main theorem original body: "+name)
    const=observed["constant"];body=observed["body"]
    return {"static_call_count":sum(expected.values()),"dynamic_private_call_count":len(dynamic),
        "constant_checks":sum(const.values()),"original_body_checks":sum(body.values()),
        "formal_constant_checks":sum(v for (_,n),v in const.items() if n in formal),
        "formal_original_body_checks":sum(v for (_,n),v in body.items() if n in formal),
        "distinct_formal_declarations_with_body_checks":len({n for (_,n) in body if n in formal}),
        "constant_only_structure_checks":{n:v for (_,n),v in extra_structures.items()},
        "static_source_call_inventory":entries,"dynamic_private_boundaries":dynamic}

def check_closed_gate(timing, runner, source):
    args=runner["command"]; split=args.index("--");outer=args[:split]
    label=option(outer,"--label");actor=option(outer,"--actor")
    package=option(outer,"--package");phase=option(outer,"--phase")
    require(option(outer,"--slot")=="/data/lean/.proof-slots/heavy.lock","Wrong shared heavy slot")
    events=[]
    for p in sorted((timing/"events").glob("*.start.json")):
        end=p.with_name(p.name.replace(".start.json",".end.json"))
        require(end.is_file(),"Active timing event: "+str(p))
        s,e=read(p),read(end)
        require(s["id"]==e["id"],"Timing event ID mismatch")
        require(e["seconds"] is None or e["seconds"]>=0,"Invalid duration")
        if (s["label"],s["actor"],s["package"])==(label,actor,package):
            events.append((s,e))
    waits=[s for s,e in events if s["phase"]=="wait_compute" and
           s["context"]["commit"]==source and e["outcome"]=="ok" and
           e.get("slot")=="/data/lean/.proof-slots/heavy.lock"]
    gates=[(s,e) for s,e in events if s["phase"]==phase and e["outcome"]=="ok" and
           e.get("exit_code")==0 and e.get("expected_exit_code")==0 and
           e.get("slot")=="/data/lean/.proof-slots/heavy.lock" and
           any(w["process_clock_domain"]==s["process_clock_domain"] for w in waits)]
    require(len(gates)==1,"No unique successful closed gate bound to frozen-source wait event")
    s,e=gates[0]
    return {"id":s["id"],"seconds":e["seconds"],"phase":phase,
            "source_bound_wait_event_ids":[w["id"] for w in waits if
                w["process_clock_domain"]==s["process_clock_domain"]],
            "runner_label":label,"runner_actor":actor,"runner_package":package}

def runner_config(root, source, acceptance, timing, runner, main):
    require(git(root,"rev-parse",runner["revision"]+"^{commit}").decode().strip()==source,
            "Runner revision mismatch")
    require(Path(runner["dest"]).resolve()==acceptance,"Runner destination mismatch")
    # runner.paper_main_complete records launch-time acceptance status, not the requested mode.
    if "require_main_proof" in runner:
        require(runner["require_main_proof"] is main,"Runner requested main flag mismatch")
    outer=runner["command"]
    require(outer[:2]==["python3","scripts/metrics/proof_time.py"] and "run" in outer and "--" in outer,
            "Unexpected runner wrapper")
    store=Path(option(outer[:outer.index("--")],"--store"))
    require((root/store).resolve()==timing.resolve(),"Runner timing store mismatch")
    wrapper=outer[:outer.index("--")]
    flags=["package","actor","site","phase","cache","label","slot"]
    values={flag:option(wrapper,"--"+flag) for flag in flags}
    require(wrapper==["python3","scripts/metrics/proof_time.py","--store",str(store),"run"]+
            [item for flag in flags for item in ["--"+flag,values[flag]]],
            "Unexpected wrapper argv or option order")
    require(values["site"]=="cloud" and values["phase"]==("release_gate" if main else "integration"),
            "Unexpected gate site/phase")
    require(values["slot"]=="/data/lean/.proof-slots/heavy.lock","Wrong wrapper heavy slot")
    child=outer[outer.index("--")+1:]
    require(child[:2]==["python3","scripts/reproduce.py"],"Unexpected reproduction driver")
    for flag in ["dest","revision","compiler-dir","dependency-source"]:
        option(child,"--"+flag)
    for flag in ["--cached-dependencies","--require-main-proof"]:
        require(child.count(flag)<=1,"Repeated reproducer boolean option")
    rp=argparse.ArgumentParser(add_help=False,allow_abbrev=False)
    for flag in ["dest","revision","compiler-dir","dependency-source"]:rp.add_argument("--"+flag,required=True)
    rp.add_argument("--cached-dependencies",action="store_true")
    rp.add_argument("--require-main-proof",action="store_true")
    ra=rp.parse_args(child[2:])
    require(Path(ra.dest).resolve()==acceptance,"Reproducer destination mismatch")
    require(git(root,"rev-parse",ra.revision+"^{commit}").decode().strip()==source,"Reproducer revision mismatch")
    require(ra.require_main_proof is main,"Reproducer main flag mismatch")
    return ra

def verify(a):
    root=a.root.resolve(); acceptance=a.acceptance.resolve();project=acceptance/"project"
    source=git(root,"rev-parse",a.source+"^{commit}").decode().strip()
    repro=read(acceptance/"reproduction.json");result=read(acceptance/"acceptance/result.json")
    runner=read(a.driver/"runner.json")
    mode="main_release" if a.require_main_proof else "pilot"
    require(repro["result"]=="pass" and result["status"]=="pass","Gate has not passed")
    require(repro["source_revision"]==result["git_commit"]==source,"Source revision mismatch")
    require(repro["scope"]==result["scope"]==mode,"Scope mismatch")
    require(repro["main_paper_complete"] is a.require_main_proof and
            result["paper_main_complete"] is a.require_main_proof,"Main-release flag mismatch")
    require(result["git_status"]=="" and result["inputs_unchanged_through_audit"] is True,
            "Recorded inputs were not clean and unchanged")
    require(git(project,"rev-parse","HEAD").decode().strip()==source,"Current clone HEAD mismatch")
    require(git(project,"status","--porcelain").decode()=="","Current clone is dirty")
    ra=runner_config(root,source,acceptance,a.timing,runner,a.require_main_proof)
    wanted_mode="verified_source_with_existing_build_cache" if ra.cached_dependencies else "required_dependency_modules_from_source"
    require(repro["dependency_mode"]==wanted_mode,"Dependency mode mismatch")
    gate_event=check_closed_gate(a.timing,runner,source)
    layout=result["layout"]
    require(read(a.driver/"preflight-layout.json")==layout,"Preflight input layout mismatch")
    require(layout["status"]=="pass" and layout["dependencies_pinned"] is True,"Bad source-policy result")
    paths=git(root,"ls-tree","-r","--name-only",source).decode().splitlines()
    formal_paths={p for p in paths if p.endswith(".lean") and
                  (p.startswith("ExactCriticalCurve/") or p=="ExactCriticalCurve.lean")}
    scripts={p for p in paths if p.count("/")==1 and p.startswith("scripts/") and
             Path(p).suffix in {".lean",".py",".sh"}}
    mandatory=formal_paths|scripts|{"docs/pgm-provenance.json","lean-toolchain","lakefile.toml",
        "lake-manifest.json","locks/toolchain.json","locks/proofwidgets-js.json",
        "vendor/proofwidgets-js.tar.gz","paper/source.json"}
    require(set(layout["reachable_formal_modules"])==formal_paths,"Formal module inventory mismatch")
    require(set(layout["formal_source_sha256"])==mandatory,"Frozen source/audit inventory mismatch")
    known=set()
    for name,h in layout["formal_source_sha256"].items():
        blob=git(root,"show",source+":"+name)
        require(hashlib.sha256(blob).hexdigest()==h,name+": immutable Git mismatch")
        require(sha(project/name)==h,name+": clean clone mismatch")
        if name in formal_paths:known.update(declarations(blob.decode()))
    provenance=read(project/"paper/source.json")
    require(sha(project/"paper/main.tex")==provenance["main_tex_sha256"],"Paper source mismatch")
    require(hashlib.sha256(git(root,"show",source+":paper/main.tex")).hexdigest()==provenance["main_tex_sha256"],
            "Immutable paper mismatch")
    subprocess.run(["git","merge-base","--is-ancestor",source,"HEAD"],cwd=root,check=True)
    lock=read(project/"locks/toolchain.json")
    require(result["toolchain_lock"]==lock,"Compiler lock record mismatch")
    asset=lock["compiler_assets"][platform.system()+"-"+platform.machine()]
    require(lock["lean_commit"] in repro["compiler_version"],"Recorded compiler commit mismatch")
    require((project/".toolchain"/asset["directory"]).is_symlink(),"Compiler link was not freshly provisioned")
    require((project/".toolchain"/asset["directory"]).resolve()==Path(ra.compiler_dir).resolve(),
            "Compiler link differs from runner compiler argument")
    require(lock["lean_commit"] in (acceptance/"acceptance/compiler.log").read_text(),
            "Actual compiler log lacks locked commit")
    checks={"compiler":[str(project/".toolchain"/asset["directory"]/"bin/lean"),"--version"],
        "build":["bash","scripts/lake.sh","build"],
        "axioms":["bash","scripts/lake.sh","env","lean","scripts/ProjectAudit.lean"],
        "pilot_types":["bash","scripts/lake.sh","env","lean","scripts/PilotExpectedTypes.lean"]}
    if a.require_main_proof:checks["release"]=["bash","scripts/lake.sh","env","lean","scripts/ReleaseAudit.lean"]
    command_rows(result["commands"],checks)
    for c in result["commands"]:
        require(c["log"]==c["label"]+".log","Unexpected acceptance log path")
        require(sha(acceptance/"acceptance"/c["log"])==c["log_sha256"],"Acceptance log hash mismatch")
    reprochecks={"clone":["git","clone","--no-hardlinks",str(root),str(project)],
                 "checkout":["git","checkout","--detach",source]}
    manifest=read(project/"lake-manifest.json")
    for pkg in manifest["packages"]:
        dep=Path(ra.dependency_source)/pkg["name"];target=project/".lake/packages"/pkg["name"]
        if ra.cached_dependencies:
            reprochecks["copy-"+pkg["name"]]=["cp","-a","--reflink=auto",str(dep),str(target)]
        else:
            reprochecks["clone-"+pkg["name"]]=["git","clone","--no-hardlinks","--no-checkout",str(dep),str(target)]
            reprochecks["checkout-"+pkg["name"]]=["git","checkout","--detach",pkg["rev"]]
            reprochecks["origin-"+pkg["name"]]=["git","remote","set-url","origin",pkg["url"]]
        require(git(target,"rev-parse","HEAD").decode().strip()==pkg["rev"],"Clone dependency revision mismatch")
        require(not git(target,"status","--porcelain","--untracked-files=no").decode().strip(),"Dirty cloned dependency")
        untracked=git(target,"ls-files","--others","--exclude-standard").decode().splitlines()
        require(not any(n.endswith(".lean") for n in untracked),"Untracked dependency Lean source")
    acceptance_cmd=["python3","scripts/check.py","--require-pilot","--output",str(acceptance/"acceptance")]
    if a.require_main_proof:acceptance_cmd.append("--require-main-proof")
    reprochecks["acceptance"]=acceptance_cmd
    command_rows(repro["commands"],reprochecks)
    for c in repro["commands"]:
        require(sha(acceptance/"logs"/(c["label"]+".log"))==c["log_sha256"],"Reproduction log hash mismatch")
    ax=(acceptance/"acceptance/axioms.log").read_text()
    union=re.findall(r"^PROJECT_AXIOMS_UNION \[(.*?)\]$",ax,re.M)
    require(len(union)==1 and {x.strip() for x in union[0].split(",")}==ALLOWED,"Unexpected axiom union")
    marker=re.findall(r"^PROJECT_AUDIT_OK declarations=(\d+) theorems=(\d+)$",ax,re.M)
    require(len(marker)==1,"Missing/duplicate project audit completion marker")
    rows=[json.loads(s)["declaration"] for s in re.findall(r"^DECLARATION_AUDIT (.*)$",ax,re.M)]
    require(len(rows)==len(set(rows))==int(marker[0][0]),"Project declaration inventory mismatch")
    formal=set(rows);stats={}
    for label in ["pilot_types"]+(["release"] if a.require_main_proof else []):
        path="scripts/PilotExpectedTypes.lean" if label=="pilot_types" else "scripts/ReleaseAudit.lean"
        script=git(root,"show",source+":"+path).decode()
        stats[label]=audit_markers((acceptance/"acceptance"/(label+".log")).read_text(),
                                  script,known,formal,label=="release")
        expected_exceptions={n:1 for n in STRUCTURES} if label=="pilot_types" else {}
        require(stats[label]["constant_only_structure_checks"]==expected_exceptions,
                "Required exact four structure/constructor checks differ from frozen source")
    return {"accepted_source_commit":source,"paper_main_complete":a.require_main_proof,
        "clean_project_build":True,"dependency_mode":repro["dependency_mode"],
        "all_source_and_audit_hashes_match_immutable_git_and_clean_clone":True,
        "inputs_unchanged_through_audit":True,"current_clone_HEAD_and_status_verified":True,
        "required_command_inventory_argv_and_scope_verified":True,
        "executed_independent_checks":stats,"allowed_axioms_union":sorted(ALLOWED),
        "project_declarations":int(marker[0][0]),"project_theorem_kind_declarations":int(marker[0][1]),
        "closed_source_bound_gate_event":gate_event,"acceptance_directory":str(acceptance),
        "result_sha256":sha(acceptance/"acceptance/result.json"),
        "reproduction_sha256":sha(acceptance/"reproduction.json"),
        "commands_seconds":{c["label"]:c["seconds"] for c in result["commands"]},
        "historical_unmeasured_development_seconds":None,
        "limitations":["Source-derived static audit names are checked exactly, including multiplicity.",
          "Dynamic private names are constrained by source-derived logical suffix, kind and count; compiler-generated prefixes are not independently predicted.",
          "Frozen audit-script hashes and successful actual Lean execution remain required; this verifier does not replace audits.",
          "Fresh project build with pinned dependency caches; compiler caches reused as recorded.",
          "Acceptance applies only to the immutable recorded source, not newer root work."],
        "verifier_sha256":sha(Path(__file__)),"inventory_extractor_sha256":sha(Path(__file__).with_name("audit_call_inventory.py")),
        "verified_at_utc":datetime.datetime.now(datetime.timezone.utc).isoformat()}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--root",type=Path,default=Path("/data/lean/projects/ExactCriticalCurve"))
    p.add_argument("--source",required=True)
    for name in ["acceptance","driver","evidence","timing"]:p.add_argument("--"+name,type=Path,required=True)
    p.add_argument("--require-main-proof",action="store_true")
    a=p.parse_args()
    evidence=a.evidence.resolve()
    require(not evidence.exists(),"Evidence destination already exists")
    for origin in [a.acceptance,a.driver,a.timing]:
        origin=origin.resolve()
        require(origin!=evidence and origin not in evidence.parents and evidence not in origin.parents,
                "Evidence destination overlaps read-only acceptance/driver/timing data")
    binding=verify(a)
    evidence.mkdir(parents=True)
    shutil.copytree(a.acceptance/"acceptance",evidence/"acceptance")
    shutil.copytree(a.acceptance/"logs",evidence/"logs")
    shutil.copy2(a.acceptance/"reproduction.json",evidence)
    for name in ["driver.log","runner.json","preflight-layout.json"]:shutil.copy2(a.driver/name,evidence/name)
    shutil.copytree(a.timing/"events",evidence/"timing/events")
    # Reporting alone does not establish success; matching successful event was checked above.
    subprocess.run(["python3","scripts/metrics/proof_time.py","report","--input",str(a.timing),
        "--output",str(evidence/"timing/report.json")],cwd=a.root,check=True,stdout=subprocess.DEVNULL)
    (evidence/"source-binding.json").write_text(json.dumps(binding,ensure_ascii=False,indent=2)+"\n")
    print(json.dumps(binding,ensure_ascii=False,indent=2))

if __name__=="__main__":
    main()
