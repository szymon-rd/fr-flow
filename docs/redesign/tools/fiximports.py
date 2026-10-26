import os,re,sys,json
moves = {
 'api.view': ('api.node', ['CodeView','NodeView','NodeViews','Placement','ProofView','Relation','ReviewView','Says']),
 'dsl.node': ('dsl.shape', ['Sig','Body','Defines','Elab']),
 'proof.lean.lower': ('proof.lean.statement', ['LowerProp','LowerObligation','Description']),
 'proof.obligation': ('proof.terms', ['TermTable','OpenTerms','FixedAs']),
}
# A moves file given as the first argument replaces the moves above: {"old.pkg": ["new.pkg", ["Name", ...]]}.
if len(sys.argv) > 1:
    moves = {k: tuple(v) for k, v in json.load(open(sys.argv[1])).items()}
def pkgdir(pkg):
    mod=pkg.split('.')[0]
    return f"src/{mod}/frflow/{pkg.replace('.','/')}"
def names_in(pkg):
    d=pkgdir(pkg)
    return [f[:-6] for f in os.listdir(d) if f.endswith('.scala')] if os.path.isdir(d) else []
files=[]
for root in ['src','test']:
    for d,_,fs in os.walk(root):
        if 'target' in d: continue
        files+= [os.path.join(d,f) for f in fs if f.endswith('.scala')]
def code_of(s):
    # strip comments roughly
    s=re.sub(r'/\*.*?\*/','',s,flags=re.S); s=re.sub(r'//[^\n]*','',s); return s
for p in files:
    s=open(p).read()
    m=re.match(r'package frflow\.([\w.]+)',s)
    if not m: continue
    mypkg=m.group(1)
    body=code_of(s.split('\n',1)[1])
    body_noimp='\n'.join(l for l in body.split('\n') if not l.startswith('import '))
    need=[]
    for old,(new,names) in moves.items():
        for n in names:
            if not re.search(r'\b'+n+r'\b', body_noimp): continue
            if mypkg==new: continue
            # file previously saw it if in old package or imported old.* or old.{n}
            imported = re.search(r'import frflow\.'+re.escape(old)+r'\.(\*|\{[^}]*\b'+n+r'\b[^}]*\}|'+n+r'\b)', s)
            if mypkg==old or imported:
                need.append(f"import frflow.{new}.{n}")
                # remove n from braces import
                s=re.sub(r'(import frflow\.'+re.escape(old)+r'\.\{)([^}]*)\}', lambda mm: mm.group(1)+', '.join(x.strip() for x in mm.group(2).split(',') if x.strip()!=n)+'}', s)
                s=re.sub(r'import frflow\.'+re.escape(old)+r'\.'+n+r'\n', '', s)
        # moved files now in new pkg need old names
        if mypkg==new:
            olds=[n for n in names_in(old) if re.search(r'\b'+n+r'\b', body_noimp)]
            if olds and not re.search(r'import frflow\.'+re.escape(old)+r'\.\*', s):
                need.append(f"import frflow.{old}.{{{', '.join(sorted(olds))}}}" if len(olds)>1 else f"import frflow.{old}.{olds[0]}")
    # clean empty braces / single braces
    s=re.sub(r'import frflow\.[\w.]+\.\{\}\n','',s)
    s=re.sub(r'(import frflow\.[\w.]+\.)\{(\w+)\}', r'\1\2', s)
    if need:
        lines=s.split('\n')
        imps=[i for i,l in enumerate(lines) if l.startswith('import ')]
        at = imps[-1]+1 if imps else 2
        for n in need:
            if n not in lines: lines.insert(at, n)
        s='\n'.join(lines)
    open(p,'w').write(s)
