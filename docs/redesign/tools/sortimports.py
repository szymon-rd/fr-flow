import os,re
from collections import OrderedDict
for root in ['src','test']:
  for d,_,fs in os.walk(root):
    if 'target' in d: continue
    for f in fs:
        if not f.endswith('.scala'): continue
        p=os.path.join(d,f); s=open(p).read()
        lines=s.split('\n')
        imps=[i for i,l in enumerate(lines) if l.startswith('import ')]
        if not imps: continue
        first,last=imps[0],imps[-1]
        block=[l for l in lines[first:last+1] if l.strip()]
        if not all(l.startswith('import ') for l in block): continue
        merged=OrderedDict()
        for l in block:
            m=re.match(r'import ([\w.]+)\.(\{[^}]*\}|[\w*]+(?: as \w+)?)$', l)
            if not m: merged[l]=None; continue
            pre,sel=m.group(1),m.group(2)
            items=[x.strip() for x in sel.strip('{}').split(',')] if sel.startswith('{') else [sel]
            merged.setdefault(('P',pre),[])
            for it in items:
                if it not in merged[('P',pre)]: merged[('P',pre)].append(it)
        out=[]
        for k,v in merged.items():
            if v is None: out.append(k); continue
            pre=k[1]
            if '*' in v: v=['*']+[x for x in v if x!='*' and ' as ' in x]
            v=sorted(set(v), key=lambda x:(x!='*', x.lower()))
            out.append(f"import {pre}.{v[0]}" if len(v)==1 else f"import {pre}.{{{', '.join(v)}}}")
        out=sorted(out,key=lambda l:l.replace('{','').lower())
        new=lines[:first]+out+lines[last+1:]
        if new!=lines: open(p,'w').write('\n'.join(new))
