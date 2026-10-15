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

def extract_inventory(source, known):
    source=uncomment(source)
    known=set(known)|declarations(source)
    lines=source.splitlines()
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
        if not calls:continue
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
