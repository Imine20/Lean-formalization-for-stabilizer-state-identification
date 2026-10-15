#!/usr/bin/env python3
"""Conservative source/layout check. Kernel/type/axiom checks remain mandatory."""
import hashlib,json,pathlib,re,subprocess
if not __debug__: raise SystemExit('Optimized Python disables assertions; audit refuses to run')
ROOT=pathlib.Path(__file__).resolve().parents[1]
def code_only(text):
    out=[]; i=0; depth=0
    while i<len(text):
        if text.startswith('/-',i): depth+=1;i+=2
        elif depth and text.startswith('-/',i):depth-=1;i+=2
        elif depth:
            if text[i]=='\n':out.append('\n')
            i+=1
        elif text.startswith('--',i):
            j=text.find('\n',i);i=len(text) if j<0 else j
        elif text[i]=='"':
            out.append(' ');i+=1
            while i<len(text):
                if text[i]=='\\':i+=2
                elif text[i]=='"':i+=1;break
                else:
                    if text[i]=='\n':out.append('\n')
                    i+=1
        else:out.append(text[i]);i+=1
    assert depth==0,'Unterminated comment'
    return ''.join(out)
def imports(text):
    result=[]
    code=code_only(text)
    assert not re.search(r'^\s*module\s*$',code,re.M),'New module/import syntax needs an audited parser'
    for line in code.splitlines():
        if re.search(r'\bimport\b',line):
            assert re.fullmatch(r'\s*import(?: +[A-Za-z_][A-Za-z_0-9.]*)+\s*',line),('Unsupported import syntax',line)
            result.extend(line.strip().split()[1:])
    return result
def check():
    expected={p.relative_to(ROOT).as_posix() for p in (ROOT/'ExactCriticalCurve').rglob('*.lean')}
    expected.add('ExactCriticalCurve.lean')
    seen=set()
    def visit(name):
        if name in seen:return
        seen.add(name);source=(ROOT/name).read_text();code=code_only(source)
        assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',code),('Forbidden formal token',name)
        assert not re.search(r'\b(run_cmd|elab|macro|syntax)\b',code),('Metaprogramming belongs outside formal modules',name)
        for imp in imports(source):
            assert not imp.startswith('Scratch'),('Scratch import',name)
            if imp=='ExactCriticalCurve' or imp.startswith('ExactCriticalCurve.'):
                path=imp.replace('.','/')+'.lean'
                assert (ROOT/path).is_file(),('Missing import',path)
                visit(path)
            else:
                assert imp.split('.')[0] in {'Mathlib','Lean','Init','Std','Batteries','Aesop','Qq','Plausible'},('Unapproved import',imp)
                assert not (ROOT/(imp.replace('.','/')+'.lean')).exists(),('Local shadow',imp)
    assert 'ExactCriticalCurve.Main' in imports((ROOT/'ExactCriticalCurve.lean').read_text())
    visit('ExactCriticalCurve.lean')
    assert seen==expected,('Unreachable formal files',sorted(expected-seen))
    configs=[p.relative_to(ROOT).as_posix() for p in ROOT.rglob('lakefile.*')
             if not any(x.startswith('.') for x in p.relative_to(ROOT).parts)
             and p.relative_to(ROOT).parts[0] not in {'Scratch','artifacts'}]
    assert set(configs)=={'lakefile.toml'},('Multiple root projects',configs)
    lock=json.loads((ROOT/'locks/toolchain.json').read_text())
    manifest=json.loads((ROOT/'lake-manifest.json').read_text())
    assert (ROOT/'lean-toolchain').read_text().strip()=='leanprover/lean4:v'+lock['lean_version']
    assert next(p['rev'] for p in manifest['packages'] if p['name']=='mathlib')==lock['mathlib_commit']
    for package in manifest['packages']:
        assert re.fullmatch('[0-9a-f]{40}',package['rev'])
        path=ROOT/'.lake/packages'/package['name']
        actual=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
        assert actual==package['rev'],('Dependency revision mismatch',package['name'],actual)
        # Tracked source modifications invalidate a pinned dependency, irrespective of cache state.
        assert not subprocess.check_output(['git','-C',str(path),'status','--porcelain','--untracked-files=no'],text=True).strip(),('Dirty dependency',package['name'])
        untracked=subprocess.check_output(['git','-C',str(path),'ls-files','--others','--exclude-standard'],text=True).splitlines()
        assert not [n for n in untracked if n.endswith('.lean')],('Untracked dependency Lean source',package['name'])
    provenance=json.loads((ROOT/'paper/source.json').read_text())
    assert hashlib.sha256((ROOT/'paper/main.tex').read_bytes()).hexdigest()==provenance['main_tex_sha256']
    if (ROOT/'paper/arXiv-2610.00266v1.tar.gz').exists():
        assert hashlib.sha256((ROOT/'paper/arXiv-2610.00266v1.tar.gz').read_bytes()).hexdigest()==provenance['archive_sha256']
    migrations=json.loads((ROOT/'docs/pgm-provenance.json').read_text())
    for item in migrations['records']:
        assert hashlib.sha256((ROOT/item['destination_file']).read_bytes()).hexdigest()==item['destination_sha256'],('Migrated source changed without reviewed provenance',item['destination_file'])
    audit_files={p.relative_to(ROOT).as_posix() for p in (ROOT/'scripts').iterdir() if p.suffix in {'.lean','.py','.sh'}}
    audit_files.add('docs/pgm-provenance.json')
    audit_files|={'lean-toolchain','lakefile.toml','lake-manifest.json','locks/toolchain.json','locks/proofwidgets-js.json','vendor/proofwidgets-js.tar.gz','paper/source.json'}
    frozen={n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in sorted(seen|audit_files)}
    return {'status':'pass','reachable_formal_modules':sorted(seen),'formal_source_sha256':frozen,'dependencies_pinned':True}
if __name__=='__main__':print(json.dumps(check(),indent=2))
