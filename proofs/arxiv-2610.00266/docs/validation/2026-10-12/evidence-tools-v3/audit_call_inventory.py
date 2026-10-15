"""Static expected audit-call inventory. Never derives expectations from audit logs."""
import collections
import hashlib
import re

BT = chr(96)
QUOTED = re.compile("(" + BT + r"{1,2})([A-Za-z_][A-Za-z0-9_'.]*)")
NAME = r"[A-Za-z_][A-Za-z0-9_'.]*"
CALL = re.compile(r"\b((?:"+NAME+r"\.)?audit[A-Za-z0-9_]+)\s+")
STRUCTURES = {
    "ExactCriticalCurve.FiniteQuadratic.ModFourWuGeometry",
    "ExactCriticalCurve.FiniteQuadratic.ModFourWuGeometry.mk",
    "ExactCriticalCurve.FiniteQuadratic.ModFourQuadraticSpace",
    "ExactCriticalCurve.FiniteQuadratic.ModFourQuadraticSpace.mk",
}

def require(condition, message):
    if not condition:
        raise ValueError(message)

def uncomment(source):
    # Lean nested block comments and line comments; preserve strings and line numbers.
    out=[]; i=0; depth=0; string=False
    while i < len(source):
        pair=source[i:i+2]; c=source[i]
        if depth:
            if pair=="/-":depth+=1;out.extend("  ");i+=2
            elif pair=="-/":depth-=1;out.extend("  ");i+=2
            else:out.append("\n" if c=="\n" else " ");i+=1
        elif string:
            out.append(c);i+=1
            if c=="\\" and i<len(source):out.append(source[i]);i+=1
            elif c=='"':string=False
        elif pair=="/-":depth=1;out.extend("  ");i+=2
        elif pair=="--":
            end=source.find("\n",i)
            if end<0:end=len(source)
            out.extend(" "*(end-i));i=end
        else:
            out.append(c);i+=1
            if c=='"':string=True
    require(depth==0,"Unclosed Lean source comment")
    return "".join(out)

def contexts(source):
    stack=[{"kind":"root","name":"","opens":[]}]
    for number,line in enumerate(uncomment(source).splitlines(),1):
        t=line.strip()
        ns=".".join(x["name"] for x in stack if x["kind"]=="namespace")
        opens=[y for x in stack for y in x["opens"]]
        yield number,line,ns,opens
        m=re.fullmatch(r"namespace\s+("+NAME+r")",t)
        if m:stack.append({"kind":"namespace","name":m[1],"opens":[]});continue
        if re.fullmatch(r"(?:noncomputable\s+)?section(?:\s+"+NAME+r")?",t):
            stack.append({"kind":"section","name":"","opens":[]});continue
        if re.fullmatch(r"end(?:\s+"+NAME+r")?",t):
            require(len(stack)>1,"Unbalanced Lean end at line "+str(number))
            stack.pop();continue
        if t.startswith("open ") and " in" not in t and not t.startswith("open scoped "):
            # Parenthesized open lists require Lean name resolution; rejected if needed.
            for token in t[5:].split():
                if re.fullmatch(NAME,token):stack[-1]["opens"].append(token)

def declarations(source):
    result=set()
    for _,line,ns,_ in contexts(source):
        m=re.match(r"^\s*(?:@\[[^\]]+\]\s*)?(?:(?:protected|noncomputable|private|unsafe)\s+)*(?:def|theorem|lemma|abbrev|structure|inductive|class|opaque)\s+("+NAME+r")",line)
        if m and not re.search(r"\bprivate\b",line[:m.start(1)]):
            name=m[1]
            if name.startswith("_root_."):name=name[7:]
            elif ns:name=ns+"."+name
            result.add(name)
            if re.search(r"\b(?:structure|class)\b",line[:m.start(1)]):result.add(name+".mk")
    return result

def resolve(quote, name, ns, opens, known):
    if len(quote)==1:
        return name
    # Quoted resolved names follow local namespace, then opened namespaces.
    parts=ns.split(".") if ns else []
    for i in range(len(parts),-1,-1):
        candidate=".".join(parts[:i]+[name])
        if candidate in known:return candidate
    matches={o+"."+name for o in opens if o+"."+name in known}
    if len(matches)==1:return next(iter(matches))
    if len(matches)>1:raise ValueError("Ambiguous opened audit target "+name+": "+str(sorted(matches)))
    suffix={x for x in known if x==name or x.endswith("."+name)}
    require(len(suffix)==1,"Cannot statically resolve public audit target "+name+": "+str(sorted(suffix)))
    return next(iter(suffix))


# These anchors are derived from the frozen Pilot source, never from audit logs.
# Hash convention: comment-stripped run_cmd block joined with LF, including
# trailing blank lines up to the next top-level command, no extra terminal LF.
INLINE_CHECKS = {
    "1209df60143a347acc7537f4808a885da0bff30190a7dbcd07fed9cd51647388": {
        "name": "ExactCriticalCurve.Binary.oddWuCorrectionLinear",
        "expected": "StochasticWittExpected.CorrectionType",
        "kind": "DEFINITION",
        "axiom_block_sha256": "22df7de124d8c3e82aea0f68f275b3e6c69d5106b8d464c360c67fbb1645e93d",
        "axiom_marker": "NEW_DECLARATION_AXIOMS_OK",
    },
    "6ef4c792904e1ad3edf9b974adddfa4e343cd11b150dec0e5480ad3fe2eec89d": {
        "name": "ExactCriticalCurve.Quantum.identityStochasticLagrangian",
        "expected": "PositiveFrameExpected.IdentityType",
        "kind": "TYPE",
        "axiom_block_sha256": "6ef4c792904e1ad3edf9b974adddfa4e343cd11b150dec0e5480ad3fe2eec89d",
        "axiom_marker": "EXACT_DEFINITION_TYPE_AND_AXIOMS_OK",
    },
}

def command_blocks(lines):
    result = []
    for i, line in enumerate(lines):
        if not line.startswith("run_cmd "):
            continue
        end = i + 1
        while end < len(lines) and (not lines[end].strip() or lines[end][0].isspace()):
            end += 1
        result.append((i + 1, "\n".join(lines[i:end])))
    return result

def inline_entry(block, line, ns, opens, known, blocks):
    if "KERNEL_EXPECTED_" not in block:
        return None
    digest = hashlib.sha256(block.encode()).hexdigest()
    require(digest in INLINE_CHECKS, "Unknown or modified inline kernel audit at " + str(line))
    anchor = INLINE_CHECKS[digest]
    actual = re.search(r"let\s+actual\s*:=\s*(" + BT + r"{1,2})(" + NAME + r")", block)
    expected = re.search(r"let\s+expected\s*:=\s*mkConst\s+(" + BT + r"{1,2})(" + NAME + r")", block)
    require(actual is not None and expected is not None, "Inline audit lacks literal actual/expected")
    name = resolve(actual[1], actual[2], ns, opens, known)
    expected_name = resolve(expected[1], expected[2], ns, opens, known)
    require(name == anchor["name"] and expected_name == anchor["expected"],
            "Inline source target/expected differs")
    require(name in known and expected_name in known, "Unknown inline actual/expected declaration")
    for token in ["info.levelParams.isEmpty", "isDefEq", "Kernel.Environment.addDeclCore",
                  '.defnDecl', '"constant"', '"body"', "value := value"]:
        require(token in block, "Inline type/body check lost: " + token)
    require("KERNEL_EXPECTED_" + anchor["kind"] + "_OK {label} {actual}" in block,
            "Inline output kind differs")
    axiom_blocks = [b for _, b in blocks
                    if hashlib.sha256(b.encode()).hexdigest() == anchor["axiom_block_sha256"]]
    require(len(axiom_blocks) == 1, "Inline axiom block missing/repeated/changed")
    for token in ["collectAxioms", "propext", "Classical.choice", "Quot.sound", "throwError",
                  anchor["axiom_marker"]]:
        require(token in axiom_blocks[0], "Inline axiom guard lost: " + token)
    return {"line": line, "helper": "<inline>", "kind": anchor["kind"], "name": name,
            "expected": expected_name, "source_sha256": digest,
            "axiom_block_sha256": anchor["axiom_block_sha256"],
            "axiom_marker": anchor["axiom_marker"]}

def extract_inventory(source, known):
    source=uncomment(source)
    known=set(known)|declarations(source)
    lines=source.splitlines()
    blocks=command_blocks(lines)
    inline_seen=set()
    ctx={n:(ns,op) for n,_,ns,op in contexts(source)}
    helper={}
    # Helper kind is determined from its literal output marker, not its name alone.
    for i,l in enumerate(lines):
        m=re.match(r"^(?:private\s+)?def\s+("+NAME+r")\s",l)
        if not m:continue
        end=i+1
        while end<len(lines) and (not lines[end].strip() or lines[end][0].isspace()):end+=1
        body="\n".join(lines[i:end])
        kinds=[k for k in ["TYPE","DEFINITION"] if "KERNEL_EXPECTED_"+k+"_OK" in body]
        if len(kinds)==1:
            leaf=m[1].split(".")[-1]
            require(leaf not in helper or helper[leaf]==kinds[0],"Conflicting helper marker kinds")
            helper[leaf]=kinds[0]
    expected=collections.Counter();entries=[];dynamic=[]
    for i,line in enumerate(lines):
        if not line.startswith("run_cmd "):continue
        end=i+1
        while end<len(lines) and (not lines[end].strip() or lines[end][0].isspace()):end+=1
        block="\n".join(lines[i:end]);ns,opens=ctx[i+1]
        calls=list(CALL.finditer(block))
        if not calls:
            entry=inline_entry(block,i+1,ns,opens,known,blocks)
            if entry is not None:
                require(entry["name"] not in inline_seen, "Repeated inline kernel audit")
                inline_seen.add(entry["name"])
                expected[(entry["kind"],entry["name"])]+=1
                entries.append(entry)
            continue
        loop=re.search(r"for\s*\(\s*actual\s*,\s*expected\s*\)\s+in\s+#\[",block)
        if loop:
            require(len(calls)==1,"Unsupported mixed literal audit loop at "+str(i+1))
            helper_name=calls[0][1].split(".")[-1]
            require(helper_name in helper,"Unknown audit helper "+helper_name)
            array=re.split(r"\]\s+do",block[loop.end():],maxsplit=1)[0]
            pair=re.compile(r"\(\s*("+BT+r"{1,2})("+NAME+r")\s*,\s*"+BT+r"{1,2}"+NAME+r"\s*\)")
            found=list(pair.finditer(array))
            require(found and re.fullmatch(r"[\s,]*",pair.sub("",array)),"Nonliteral expected audit loop at "+str(i+1))
            for m in found:
                name=resolve(m[1],m[2],ns,opens,known)
                kind=helper[helper_name];expected[(kind,name)]+=1
                entries.append({"line":i+1,"helper":helper_name,"kind":kind,"name":name})
            continue
        for call in calls:
            helper_name=call[1].split(".")[-1]
            require(helper_name in helper,"Unknown audit helper "+helper_name+" at "+str(i+1))
            tail=block[call.end():]
            quoted=QUOTED.match(tail)
            if quoted:
                name=resolve(quoted[1],quoted[2],ns,opens,known)
                kind=helper[helper_name];expected[(kind,name)]+=1
                entries.append({"line":i+1,"helper":helper_name,"kind":kind,"name":name})
            else:
                # Exactly identified private expressions are a reported boundary.
                private_resolve=re.search(r'let\s+actual\s+←\s+resolve\w*Private\w*\s+"(ExactCriticalCurve\.[^"]+)"',block)
                require(("_private." in tail and "Lean.Name.mkStr" in tail) or private_resolve,
                        "Unsupported public/dynamic audit call at "+str(i+1)+": "+tail[:160])
                dynamic.append({"line":i+1,"kind":helper[helper_name],
                    "source_sha256":hashlib.sha256(block.encode()).hexdigest(),
                    "logical_suffix":private_resolve[1] if private_resolve else ".".join(re.findall(r'"([A-Za-z_][A-Za-z0-9_]*)"',tail)),
                    "reason":"Private Lean.Name construction; require paired private log markers, exact call count and successful frozen Lean audit."})
    require(expected,"No independently extracted static audit calls")
    return expected,entries,dynamic
