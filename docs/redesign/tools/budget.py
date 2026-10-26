import os,re,sys,collections
root=sys.argv[1]
files=[]
for d,_,fs in os.walk(root):
    if '/target' in d: continue
    for f in fs:
        if f.endswith('.scala'): files.append(os.path.join(d,f))
tot=0; q=0; qf=0; pk=collections.Counter()
long=[];big=[];longdef=[];params=[]
for p in sorted(files):
    L=open(p).read().split('\n')
    tot+=len(L); c=sum(l.count('???') for l in L); q+=c; qf+=c>0
    if '/src/' in p: pk[os.path.dirname(p)]+=1
    if len(L)>200: big.append((p,len(L)))
    for i,l in enumerate(L):
        if len(l)>120: long.append(f"{p}:{i+1}:{len(l)}")
    # def length: from def line to next line with indent <= def indent (non-blank)
    for i,l in enumerate(L):
        m=re.match(r'(\s*)(?:(?:private|override|inline|protected|final|given|extension)[^\n]*?)?\bdef\s',l)
        if not m: continue
        ind=len(l)-len(l.lstrip()); j=i+1
        while j<len(L) and (L[j].strip()=='' or len(L[j])-len(L[j].lstrip())>ind): j+=1
        n=j-i
        while n>1 and L[i+n-1].strip()=='': n-=1
        if n>20: longdef.append(f"{p}:{i+1}:{n}")
        sig=l
        k=i
        while sig.count('(')>sig.count(')') and k+1<len(L): k+=1; sig+=L[k]
        mm=re.search(r'def\s+\S+?(\[.*?\])?\((.*?)\)',sig)
        if mm and not mm.group(2).startswith('using'):
            depth=0; cnt=1 if mm.group(2).strip() else 0
            for ch in mm.group(2):
                if ch in '([{': depth+=1
                elif ch in ')]}': depth-=1
                elif ch==',' and depth==0: cnt+=1
            if cnt>4: params.append(f"{p}:{i+1}:{cnt}")
print("files",len(files),"lines",tot,"??? occurrences",q,"files with ???",qf)
print("long lines",len(long)); [print(" ",x) for x in long]
print("big files",big)
print("long defs"); [print(" ",x) for x in longdef]
print("params>4"); [print(" ",x) for x in params]
print("packages out of 3-15:"); [print(" ",k,v) for k,v in sorted(pk.items()) if v<3 or v>15]
