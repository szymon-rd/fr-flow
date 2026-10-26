#!/usr/bin/env python3
"""Measure Scala sources against the size budgets in ../SKILL.md.

Usage:
  python3 -I .claude/skills/scala-fp/references/measure.py [PATH ...] [--all] [--summary]

PATH defaults to modules/*/src/main/scala. Prints one line per value over budget
(`file:line metric value > budget  name`); `--all` prints every measured value,
`--summary` only the distribution of each metric. Exit status 1 if anything is over.

The parser is approximate (it strips comments and strings, then matches
declarations by regex and balanced brackets). It is a guide for review, not a
gate: read the code it points at before reporting a finding.
"""
import glob
import os
import re
import sys
from collections import defaultdict

# Keep these in step with "Size budgets" in SKILL.md.
BUDGET = {
    "fields": 6,           # constructor parameters of a class, case class or enum case
    "optional-fields": 2,  # of those, typed Option[...] or given a default value
    "params": 4,           # explicit parameters of a def (all lists, `using` excluded)
    "def-lines": 20,       # non-blank lines of a def, signature included
    "file-lines": 200,     # non-blank lines of a file
    "line-width": 120,     # widest line of a file
    "types-per-file": 1,   # top-level types, a companion counted with its type
    "files-per-package": 15,
}

MODIFIERS = r"(?:(?:private|protected)(?:\[\w+\])?\s+|override\s+|inline\s+|final\s+|transparent\s+|implicit\s+|sealed\s+|abstract\s+|case\s+|open\s+|opaque\s+)*"


def strip(text: str) -> str:
    """Comments and string literals replaced by spaces; newlines kept so offsets map to lines."""
    out, i, n = [], 0, len(text)
    def blank(s):
        return "".join("\n" if c == "\n" else " " for c in s)
    while i < n:
        if text.startswith("//", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(blank(text[i:j])); i = j
        elif text.startswith("/*", i):
            j = text.find("*/", i + 2)
            j = n if j < 0 else j + 2
            out.append(blank(text[i:j])); i = j
        elif text.startswith('"""', i):
            j = text.find('"""', i + 3)
            j = n if j < 0 else j + 3
            while j < n and text[j] == '"':
                j += 1
            out.append('""' + blank(text[i + 2:j - 2]) + '""' if j - i >= 4 else blank(text[i:j])); i = j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] not in '"\n':
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, n)
            out.append('"' + blank(text[i + 1:j - 1]) + '"'); i = j
        elif text[i] == "'" and re.match(r"'(\\.|[^'\\\n])'", text[i:i + 4]):
            m = re.match(r"'(\\.|[^'\\\n])'", text[i:i + 4])
            out.append(" " * len(m.group(0))); i += len(m.group(0))
        else:
            out.append(text[i]); i += 1
    return "".join(out)


def balanced(text: str, i: int):
    """Index just past the bracket group opening at text[i], and its inner text."""
    pairs = {"(": ")", "[": "]", "{": "}"}
    stack, j = [pairs[text[i]]], i + 1
    while j < len(text) and stack:
        c = text[j]
        if c in pairs:
            stack.append(pairs[c])
        elif c == stack[-1]:
            stack.pop()
        j += 1
    return j, text[i + 1:j - 1]


def split_params(inner: str):
    """The explicit parameters of one list (none for a `using` or `implicit` list)."""
    s = inner.strip()
    if not s or re.match(r"(using|implicit)\b", s):
        return []
    depth, parts, cur = 0, [], []
    for c in s:
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        if c == "," and depth == 0:
            parts.append("".join(cur)); cur = []
        else:
            cur.append(c)
    parts.append("".join(cur))
    return [p for p in parts if p.strip()]


def is_optional(param: str) -> bool:
    return bool(re.search(r":\s*Option\[", param) or re.search(r"(?<![=<>!])=(?![=>])", param))


def skip_space(text: str, i: int) -> int:
    while i < len(text) and text[i] in " \t\r\n":
        i += 1
    return i


def param_lists(text: str, i: int, first_only: bool):
    """The explicit parameters in the parameter lists starting at i (type params skipped)."""
    total = []
    i = skip_space(text, i)
    if i < len(text) and text[i] == "[":
        i, _ = balanced(text, i)
    while True:
        j = skip_space(text, i)
        # skip modifiers and annotations between a class name and its constructor
        m = re.match(r"(@[\w.]+|private\[\w+\]|protected\[\w+\]|private|protected)\s*", text[j:])
        while m:
            j = skip_space(text, j + m.end())
            m = re.match(r"(@[\w.]+|private\[\w+\]|protected\[\w+\]|private|protected)\s*", text[j:])
        if j < len(text) and text[j] == "(":
            i, inner = balanced(text, j)
            total += split_params(inner)
            if first_only:
                return total
        else:
            return total


def is_pattern(text: str, i: int) -> bool:
    """Whether the `case X(...)` at i is a pattern (followed by `=>`, a guard or an alternative), not an enum case."""
    i = skip_space(text, i)
    while i < len(text) and text[i] in "[(":
        i, _ = balanced(text, i)
        i = skip_space(text, i)
    return text.startswith(("=>", "if ", "|", "@"), i)


def line_of(text: str, pos: int) -> int:
    return text.count("\n", 0, pos) + 1


def def_lines(lines, start: int) -> int:
    """Non-blank lines of the def at lines[start], by indentation (braceless and brace style)."""
    indent = len(lines[start]) - len(lines[start].lstrip())
    count, k = 1, start + 1
    while k < len(lines):
        ln = lines[k]
        if ln.strip():
            ind = len(ln) - len(ln.lstrip())
            if ind <= indent:
                if ind == indent and re.match(r"[})]|end\b", ln.strip()):
                    count += 1
                break
            count += 1
        k += 1
    return count


def measure_file(path: str):
    raw = open(path, encoding="utf-8").read()
    text = strip(raw)
    lines = text.split("\n")
    found = []
    nonblank = sum(1 for ln in raw.split("\n") if ln.strip())
    found.append(("file-lines", nonblank, path, 1, os.path.basename(path)))
    widths = [len(ln) for ln in raw.split("\n")]
    widest = max(widths) if widths else 0
    found.append(("line-width", widest, path, widths.index(widest) + 1 if widths else 1, os.path.basename(path)))

    for m in re.finditer(r"(?m)^[ \t]*" + MODIFIERS + r"(class|enum)\s+(\w+)", text):
        ps = param_lists(text, m.end(), first_only=True)
        found.append(("fields", len(ps), path, line_of(text, m.start()), m.group(2)))
        found.append(("optional-fields", sum(map(is_optional, ps)), path, line_of(text, m.start()), m.group(2)))
    for m in re.finditer(r"(?m)^[ \t]+case\s+(\w+)\s*(?=[\[(])", text):
        if is_pattern(text, m.end()):
            continue
        ps = param_lists(text, m.end(), first_only=True)
        found.append(("fields", len(ps), path, line_of(text, m.start()), m.group(1)))
        found.append(("optional-fields", sum(map(is_optional, ps)), path, line_of(text, m.start()), m.group(1)))

    for m in re.finditer(r"(?m)^[ \t]*" + MODIFIERS + r"def\s+([^\s\[(:=]+)", text):
        n = len(param_lists(text, m.end(), first_only=False))
        ln = line_of(text, m.start())
        found.append(("params", n, path, ln, m.group(1)))
        found.append(("def-lines", def_lines(lines, ln - 1), path, ln, m.group(1)))

    names = []
    for m in re.finditer(r"(?m)^" + MODIFIERS + r"(class|trait|object|enum|type)\s+(\w+)", text):
        if m.group(2) not in names:
            names.append(m.group(2))
    found.append(("types-per-file", len(names), path, 1, ",".join(names)))
    return found


def main(argv):
    flags = {a for a in argv if a.startswith("--")}
    paths = [a for a in argv if not a.startswith("--")] or glob.glob("modules/*/src/main/scala")
    files = []
    for p in paths:
        files += [p] if p.endswith(".scala") else glob.glob(os.path.join(p, "**", "*.scala"), recursive=True)
    found = []
    per_dir = defaultdict(int)
    for f in sorted(files):
        found += measure_file(f)
        per_dir[os.path.dirname(f)] += 1
    for d, n in per_dir.items():
        found.append(("files-per-package", n, d, 0, os.path.basename(d)))

    over = [x for x in found if x[1] > BUDGET[x[0]]]
    if "--summary" not in flags:
        for metric, value, path, line, name in sorted(found if "--all" in flags else over, key=lambda x: (x[0], -x[1])):
            print(f"{path}:{line}\t{metric}\t{value} > {BUDGET[metric]}\t{name}" if value > BUDGET[metric]
                  else f"{path}:{line}\t{metric}\t{value}\t{name}")
    print("\nmetric             budget  measured  over  p50  p90  max")
    for metric in BUDGET:
        vs = sorted(x[1] for x in found if x[0] == metric)
        if not vs:
            continue
        o = sum(1 for v in vs if v > BUDGET[metric])
        print(f"{metric:<18} {BUDGET[metric]:>6}  {len(vs):>8}  {o:>4}  {vs[len(vs)//2]:>3}  {vs[int(len(vs)*.9)]:>3}  {vs[-1]:>3}")
    return 1 if over else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
