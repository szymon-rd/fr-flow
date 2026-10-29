"""The size budgets over a tree of Scala (`python3 docs/redesign/tools/budget.py next`): no line over 120 columns, no
file over 200 lines, no def over 20 lines, no parameter list over four, every package of 3 to 15 files. It prints
what it measures and exits non-zero when a violation is not in the baseline (`budget-baseline.txt` beside it, one
per line, keyed without line numbers so moving code keeps its key, and counted where one file has several of a kind
and name). `--write-baseline` records today's violations.
"""
import os, re, sys, collections

HERE = os.path.dirname(os.path.abspath(__file__))


def measure(root):
    files = []
    for d, _, fs in os.walk(root):
        if '/target' in d: continue
        for f in fs:
            if f.endswith('.scala'): files.append(os.path.join(d, f))
    tot = 0; q = 0; qf = 0; pk = collections.Counter()
    long = []; big = []; longdef = []; params = []; keys = []
    for p in sorted(files):
        L = open(p).read().split('\n')
        tot += len(L); c = sum(l.count('???') for l in L); q += c; qf += c > 0
        if '/src/' in p: pk[os.path.dirname(p)] += 1
        if len(L) > 200: big.append((p, len(L))); keys.append(f"big {p}")
        for i, l in enumerate(L):
            if len(l) > 120: long.append(f"{p}:{i+1}:{len(l)}"); keys.append(f"long {p}")
        # def length: from def line to next line with indent <= def indent (non-blank)
        for i, l in enumerate(L):
            m = re.match(r'(\s*)(?:(?:private|override|inline|protected|final|given|extension)[^\n]*?)?\bdef\s', l)
            if not m: continue
            ind = len(l) - len(l.lstrip()); j = i + 1
            while j < len(L) and (L[j].strip() == '' or len(L[j]) - len(L[j].lstrip()) > ind): j += 1
            n = j - i
            while n > 1 and L[i+n-1].strip() == '': n -= 1
            name = (re.search(r'\bdef\s+([^\s(\[:]+)', l) or re.search(r'(\S+)', l)).group(1)
            if n > 20: longdef.append(f"{p}:{i+1}:{n}"); keys.append(f"longdef {p} {name}")
            sig = l
            k = i
            while sig.count('(') > sig.count(')') and k + 1 < len(L): k += 1; sig += L[k]
            mm = re.search(r'def\s+\S+?(\[.*?\])?\((.*?)\)', sig)
            if mm and not mm.group(2).startswith('using'):
                depth = 0; cnt = 1 if mm.group(2).strip() else 0
                for ch in mm.group(2):
                    if ch in '([{': depth += 1
                    elif ch in ')]}': depth -= 1
                    elif ch == ',' and depth == 0: cnt += 1
                if cnt > 4: params.append(f"{p}:{i+1}:{cnt}"); keys.append(f"params {p} {name}")
    packages = [(k, v) for k, v in sorted(pk.items()) if v < 3 or v > 15]
    keys += [f"package {k}" for k, _ in packages]
    print("files", len(files), "lines", tot, "??? occurrences", q, "files with ???", qf)
    print("long lines", len(long)); [print(" ", x) for x in long]
    print("big files", big)
    print("long defs"); [print(" ", x) for x in longdef]
    print("params>4"); [print(" ", x) for x in params]
    print("packages out of 3-15:"); [print(" ", k, v) for k, v in packages]
    counted = collections.Counter(keys)
    return sorted(k if n == 1 else f"{k} x{n}" for k, n in counted.items())


def main(args):
    write = '--write-baseline' in args
    rest = [a for a in args if a != '--write-baseline']
    baseline = os.path.join(HERE, 'budget-baseline.txt')
    if '--baseline' in rest:
        i = rest.index('--baseline'); baseline = rest[i + 1]; del rest[i:i + 2]
    keys = measure(rest[0])
    if write:
        with open(baseline, 'w') as f: f.write(''.join(k + '\n' for k in keys))
        print("baseline written:", len(keys), "violations")
        return 0
    known = set(open(baseline).read().split('\n')) if os.path.exists(baseline) else set()
    new = [k for k in keys if k not in known]
    print("new violations", len(new)); [print(" ", k) for k in new]
    return 1 if new else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
