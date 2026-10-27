#!/usr/bin/env python3
"""Records today's FrFlow outputs under reference/, for the rebuild's equivalence checks (step 0).

    python3 reference/capture.py rooms          # one example (or several)
    python3 reference/capture.py                # all five

Everything runs on a copy of the working tree (target/reference-copy, a git clone sharing this repository's objects,
with the working files copied over it), so the examples here are never written to. Each check starts cold: the copy
holds none of FrFlow's derived files. Output is deterministic: FRFLOW_SEED is fixed, the time zone is UTC, and paths
are relative. See reference/README.md for what is captured.
"""

import difflib
import fcntl
import json
import os
import pty
import re
import select
import shutil
import signal
import struct
import subprocess
import sys
import termios
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REF = ROOT / "reference"
COPY = ROOT / "target" / "reference-copy"
EXAMPLES = ["rooms", "auth", "keycloak", "crm", "sharing"]
SEED = "1"
# How long review may take on its terminal before the capture stops.
TERMINAL_DEADLINE = 300
OUT = COPY / "target" / "reference-out"
# Who the review runs as: a name only. No key exists where FRFLOW_KEY points, and every answer is skip: nothing is
# decided.
REVIEWER = "demo-developer"
# FrFlow's files derived from the Scala definitions or local to a run (as .gitignore lists them).
DERIVED = [".frflow/kb.json", ".frflow/checks.json", ".frflow/tests.json", ".frflow/consistency.json",
           ".frflow/running.json", "lean/FrFlowGen", "lean/FrFlowAudit"]
GENERATED_LEAN = ["lean/FrFlowGen", "lean/FrFlowAudit"]
# What the JVM or cats-effect print on stderr whatever the command.
NOISE = ("Picked up JAVA_TOOL_OPTIONS", "Your app's responsiveness to a new asynchronous event",
         "cats.effect.warnOnNonMainThreadDetected")

# The README's rooms section, steps 4 to 6, as changes to today's rooms example: (file, old, new), each `old` found
# exactly once. Steps 5 and 6 start from step 5's changes; each step starts from the example as committed.
ROOMS = "examples/rooms/src/main/scala/rooms/"
ROOMS_TEST = "examples/rooms/src/test/scala/rooms/"
FORGETS_NEXT = [(ROOMS + "Calendar.scala",
                 "byStart.lift(i - 1).forall(_.end <= request.start) && byStart.lift(i).forall(_.start >= request.end)",
                 "byStart.lift(i - 1).forall(_.end <= request.start)")]
MISREADS_OVERLAP = [
    (ROOMS + "Knowledge.scala", "a.room =!= b.room || a.end <= b.start || b.end <= a.start",
     "a.room =!= b.room || a.end < b.start || b.end < a.start"),
    (ROOMS + "Calendar.scala",
     "byStart.lift(i - 1).forall(_.end <= request.start) && byStart.lift(i).forall(_.start >= request.end)",
     "byStart.lift(i - 1).forall(_.end < request.start) && byStart.lift(i).forall(_.start > request.end)"),
    (ROOMS_TEST + "GrantedExamples.scala",
     '  example("back to back: granted"):\n'
     '    granted(RoomBookings("Oak", List(Booking("Oak", 9, 10))), Booking("Oak", 10, 11)) is true\n',
     '  example("a gap between them: granted"):\n'
     '    granted(RoomBookings("Oak", List(Booking("Oak", 9, 10))), Booking("Oak", 11, 12)) is true\n\n'
     '  example("back to back: refused"):\n'
     '    granted(RoomBookings("Oak", List(Booking("Oak", 9, 10))), Booking("Oak", 10, 11)) is false\n')]
MISREADS_COVERS = MISREADS_OVERLAP + [
    (ROOMS + "Knowledge.scala", "b.start <= t && t < b.end", "b.start <= t && t <= b.end")]
WALKTHROUGH = [
    ("4-code-forgets-the-next-booking", "README step 4: Calendar forgets the booking after the request", FORGETS_NEXT),
    ("5-misread-overlap", "README step 5: touching meetings taken to overlap, in the claim over times, the code and "
                          "the examples", MISREADS_OVERLAP),
    ("6-misread-reaches-the-claim", "README step 6: step 5, and covers includes the end moment; the proof of "
                                    "GrantWhenFree is unchanged", MISREADS_COVERS)]


def fail(message):
    sys.exit(f"capture: {message}")


def run(args, cwd, env=None, **kw):
    return subprocess.run(args, cwd=cwd, env=env, stdin=subprocess.DEVNULL, capture_output=True, text=True, **kw)


def git(*args, cwd=ROOT):
    r = run(["git", *args], cwd)
    if r.returncode != 0:
        fail(f"git {' '.join(args)}: {r.stderr.strip()}")
    return r.stdout


def write(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


# The copy.

def source_files():
    """The working tree's files as git sees them (tracked and untracked, not ignored), but reference/'s outputs."""
    names = git("ls-files", "-co", "--exclude-standard", "-z").split("\0")
    keep = lambda n: n and (not n.startswith("reference/") or n.startswith("reference/capture/"))
    return sorted(n for n in set(names) if keep(n) and (ROOT / n).is_file())


def source():
    """What the capture was taken from: the commit (`-dirty` when a file the capture reads differs from it), Lean."""
    changed = [l[3:] for l in git("status", "--porcelain", "--untracked-files=all").splitlines()]
    dirty = any(not p.startswith("reference/") or p.startswith("reference/capture") for p in changed)
    lake = run(["lake", "--version"], ROOT)
    return "\n".join([f"commit {git('rev-parse', 'HEAD').strip()}{'-dirty' if dirty else ''}",
                      f"lean-toolchain {(ROOT / 'lean' / 'lean-toolchain').read_text().strip()}",
                      f"lake {lake.stdout.strip()}", f"FRFLOW_SEED={SEED}"]) + "\n"


def sync():
    """Makes the copy's files the working tree's, at the same commit, with none of FrFlow's derived files."""
    if not (COPY / ".git").exists():
        shutil.rmtree(COPY, ignore_errors=True)
        COPY.parent.mkdir(parents=True, exist_ok=True)
        git("clone", "-q", "--shared", "--no-checkout", str(ROOT), str(COPY))
        seed_builds()
    git("reset", "-q", git("rev-parse", "HEAD").strip(), cwd=COPY)
    wanted = source_files()
    for name in wanted:
        src, dst = ROOT / name, COPY / name
        if not dst.is_file() or dst.read_bytes() != src.read_bytes():
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src, dst)
    present = set(git("ls-files", "-co", "--exclude-standard", "-z", cwd=COPY).split("\0")) - {""}
    for name in present - set(wanted):
        (COPY / name).unlink(missing_ok=True)


def cold(example):
    """None of FrFlow's derived files of `example` in the copy, and the failed cases kept only as committed."""
    for d in DERIVED:
        p = COPY / "examples" / example / d
        shutil.rmtree(p) if p.is_dir() else p.unlink(missing_ok=True)
    kept = Path("examples") / example / ".frflow" / "counterexamples.json"
    (COPY / kept).unlink(missing_ok=True)
    if (ROOT / kept).is_file():
        shutil.copy2(ROOT / kept, COPY / kept)


def seed_builds():
    """The working tree's compiled classes and Lean builds, so the copy's first build is incremental."""
    for d in [*ROOT.glob("modules/*/target"), *ROOT.glob("examples/*/target"), ROOT / "project" / "target",
              ROOT / "project" / "project", ROOT / "lean" / ".lake", *ROOT.glob("examples/*/lean/.lake")]:
        if d.is_dir():
            shutil.copytree(d, COPY / d.relative_to(ROOT), symlinks=True, dirs_exist_ok=True)


def sbt(*commands):
    env = {k: v for k, v in os.environ.items() if not k.startswith("FRFLOW_")}
    log = COPY / "target" / "capture-sbt.log"
    log.parent.mkdir(parents=True, exist_ok=True)
    print(f"capture: sbt {' '.join(commands)}", file=sys.stderr)
    r = run(["sbt", *commands], COPY, env)
    log.write_text(r.stdout + r.stderr)
    if r.returncode != 0:
        fail(f"sbt failed; its output is in {log}\n" + "\n".join((r.stdout + r.stderr).splitlines()[-30:]))


# Running a project's CLI on the copy, as bin/frflow does, with plain output.

def cli_env():
    env = {k: v for k, v in os.environ.items()
           if not k.startswith("FRFLOW_") and k not in ("COLUMNS", "JAVA_TOOL_OPTIONS", "NO_COLOR")}
    env.update(FRFLOW_SEED=SEED, FRFLOW_KEY=str(COPY / "target" / "no-signing.key"), NO_COLOR="1", TERM="dumb",
               TZ="UTC", LC_ALL="C.UTF-8")
    return env


def java(example, args):
    launch = (COPY / "examples" / example / "target" / "frflow.launch").read_text().splitlines()
    return ["java", "-Duser.timezone=UTC", *launch, "--plain", *args]


def clean(text):
    lines = [l for l in text.replace("\r\n", "\n").split("\n") if not any(n in l for n in NOISE)]
    text = "\n".join(lines)
    for path in (str(COPY), str(ROOT)):
        text = text.replace(path + "/", "").replace(path, ".")
    return text.rstrip("\n") + "\n" if text.strip() else ""


def cli(example, *args):
    print(f"capture: {example} {' '.join(args)}", file=sys.stderr)
    r = run(java(example, args), COPY, cli_env())
    return r.returncode, clean(r.stdout), clean(r.stderr)


def cli_on_terminal(example, *args, answers="s\n" * 200):
    """The command on a pseudo-terminal (review is interactive), answering `answers`; echo off, so the answers do
    not show. Returns its exit code and what it printed."""
    print(f"capture: {example} {' '.join(args)} (on a terminal)", file=sys.stderr)
    master, slave = pty.openpty()
    attrs = termios.tcgetattr(slave)
    attrs[1] &= ~termios.ONLCR
    attrs[3] &= ~termios.ECHO
    termios.tcsetattr(slave, termios.TCSANOW, attrs)
    fcntl.ioctl(slave, termios.TIOCSWINSZ, struct.pack("HHHH", 50, 200, 0, 0))
    p = subprocess.Popen(java(example, args), cwd=COPY, env=cli_env(), stdin=slave, stdout=slave, stderr=slave,
                         start_new_session=True)
    os.close(slave)
    os.write(master, answers.encode())
    out = b""
    deadline = time.monotonic() + TERMINAL_DEADLINE
    while True:
        left = deadline - time.monotonic()
        if left <= 0 or not select.select([master], [], [], left)[0]:
            os.killpg(p.pid, signal.SIGKILL)
            p.wait()
            os.close(master)
            fail(f"{example} {' '.join(args)} did not finish within {TERMINAL_DEADLINE}s on its terminal")
        try:
            chunk = os.read(master, 65536)
        except OSError:
            break
        if not chunk:
            break
        out += chunk
    os.close(master)
    return p.wait(), clean(out.decode("utf-8", "replace"))


def shown(code, out, err=""):
    """A command's output as kept: what it printed, then its stderr if any, then its exit code."""
    return out + (f"--- stderr\n{err}" if err else "") + f"--- exit {code}\n"


# What is captured of one example.

def standings(example, checked, tree, tests):
    """Each node's standing as `check` leaves it, and its review state: as text, and as fixed columns (tab-separated).
    Standing: proven, tested, assumed, failing, not proven; nothing to prove for a definition or design check has no
    result for; not checked for any other node it has none for. Tests: as check recorded them (.frflow/tests.json)."""
    nodes = {}

    def walk(entries):
        for e in entries:
            nodes.setdefault(e["node"]["id"], e["node"])
            walk(e.get("children", []))
    for part in tree.values():
        walk(part if isinstance(part, list) else [])
    by_id = {c["id"]: c for c in checked}
    lines = [f"# Standings: {example} (FRFLOW_SEED={SEED})", "",
             "node | kind | standing | review | detail", ""]
    columns = ["node", "kind", "standing", "status", "review", "causes", "cases", "against", "seed"]
    rows = ["\t".join(columns)]
    for nid in sorted(nodes):
        n, c, t = nodes[nid], by_id.get(nid), tests.get(nid, {}).get("report")
        detail = []
        if c is None:
            standing = ("assumed" if n["kind"] == "assumption" else
                        "nothing to prove" if n["kind"] in ("definition", "design") else "not checked")
        elif c.get("testFailure") or c["failing"] or c["status"] == "failed":
            standing = "failing"
        elif n["kind"] == "assumption":
            standing = "assumed"
            detail.append(f"its check: {c['status']}")
        elif not c["ok"]:
            standing = "not proven"
            detail.append(f"its check: {c['status']}")
        elif c.get("codeTested"):
            standing = "tested"
        else:
            standing = "proven"
        if c is not None and c.get("modelRuns"):
            m = c["modelRuns"]
            detail.append(f"{', '.join(m['implementations'])} run against the model on {m['runs']} runs")
        elif t:
            detail.append(f"code tested on {t['cases']} cases against {t['against']}, seed {t['seed']}")
        if c is not None:
            if c["notProven"]:
                detail.append("not proven: " + ", ".join(c["notProven"]))
            if c["failing"]:
                detail.append(f"{len(c['failing'])} example(s) failing")
            if c.get("testFailure"):
                detail.append("a generated case fails")
        causes = [str(x) for x in n.get("causes", [])]
        review = n["state"] + (f" ({', '.join(causes)})" if causes else "")
        lines.append(f"{nid} | {n['kind']} | {standing} | {review} | {'; '.join(detail)}")
        cells = [nid, n["kind"], standing, c["status"] if c else "", n["state"], ",".join(causes),
                 str(t["cases"]) if t else "", t["against"] if t else "", str(t["seed"]) if t else ""]
        rows.append("\t".join(" ".join(x.split()) for x in cells))
    return "\n".join(lines) + "\n", "\n".join(rows) + "\n", sorted(nodes)


def seeds(example, tests):
    """The seeds the reference ran with: each generated test's (as check recorded it in .frflow/tests.json), and those
    written into the example's suites."""
    lines = [f"# Seeds: {example}", "", f"FRFLOW_SEED={SEED} for every check.", "", "Generated tests (node: cases, "
             "against what, seed):"]
    for nid in sorted(tests):
        r = tests[nid]["report"]
        lines.append(f"  {nid}: {r['cases']} against {r['against']}, seed {r['seed']}")
    pattern = re.compile(r"Random\(\d+\)|seed = \d+|\(\d+ to \d+\)\.map\(s => run\(")
    fixed = [f"  {f.relative_to(ROOT)}:{i}: {line.strip()}"
             for f in sorted((ROOT / "examples" / example / "src" / "test").rglob("*.scala"))
             for i, line in enumerate(f.read_text().splitlines(), 1) if pattern.search(line)]
    lines += ["", "In the example's suites (fixed in their code):", *(fixed or ["  none"])]
    return "\n".join(lines) + "\n"


def capture_cli(example, out):
    """check --json (cold) for the standings and seeds; check (cold) as text, then status, tree, show of each node and
    review; and the Lean."""
    cold(example)
    code_json, checked_json, err = cli(example, "check", "--json")
    try:
        checked = json.loads(checked_json)["checked"]
    except (ValueError, KeyError):
        fail(f"{example}: check --json printed no report (exit {code_json})\n{err}")
    tests_file = COPY / "examples" / example / ".frflow" / "tests.json"
    tests = json.loads(tests_file.read_text()) if tests_file.is_file() else {}
    _, tree_json, _ = cli(example, "tree", "--json")
    text, tsv, ids = standings(example, checked, json.loads(tree_json), tests)
    write(out / "standings.txt", text)
    write(out / "standings.tsv", tsv)
    write(out / "seeds.txt", seeds(example, tests))
    cold(example)
    code, check_text, err = cli(example, "check")
    if code != code_json:
        fail(f"{example}: check exits {code}, check --json exited {code_json}")
    write(out / "check.txt", shown(code, check_text, err))
    write(out / "status.txt", shown(*cli(example, "status")))
    write(out / "tree.txt", shown(*cli(example, "tree")))
    for nid in ids:
        write(out / "show" / f"{nid}.txt", shown(*cli(example, "show", nid)))
    write(out / "review.txt", shown(*cli_on_terminal(example, "review", "--as", REVIEWER)))
    for d in GENERATED_LEAN:
        src = COPY / "examples" / example / d
        if src.is_dir():
            shutil.copytree(src, out / d, ignore=shutil.ignore_patterns(".lake", "*.olean", "*.ilean"))


def apply(changes):
    """Applies the changes to the copy; the diff they make, with paths relative to the repository."""
    diff = []
    for path in dict.fromkeys(f for f, _, _ in changes):
        before = (COPY / path).read_text()
        after = before
        for f, old, new in changes:
            if f != path:
                continue
            if after.count(old) != 1:
                fail(f"the walk-through's change to {path} no longer applies: {old!r} is not there exactly once")
            after = after.replace(old, new)
        (COPY / path).write_text(after)
        diff += difflib.unified_diff(before.splitlines(True), after.splitlines(True), f"a/{path}", f"b/{path}")
    return "".join(diff)


def restore(changes):
    for path in dict.fromkeys(f for f, _, _ in changes):
        shutil.copy2(ROOT / path, COPY / path)


def walkthrough(out):
    """The README's rooms steps 4 to 6, each applied to the committed example on the copy; check, status and review
    after each."""
    for name, what, changes in WALKTHROUGH:
        step = out / "walkthrough" / name
        diff = apply(changes)
        try:
            sbt("rooms/cliLauncher")
            cold("rooms")
            write(step / "change.diff", f"# {what}\n" + diff)
            write(step / "check.txt", shown(*cli("rooms", "check")))
            write(step / "status.txt", shown(*cli("rooms", "status")))
            write(step / "review.txt", shown(*cli_on_terminal("rooms", "review", "--as", REVIEWER)))
        finally:
            restore(changes)
    cold("rooms")


def main(args):
    examples = args or EXAMPLES
    unknown = [e for e in examples if e not in EXAMPLES]
    if unknown:
        fail(f"no such example: {', '.join(unknown)} (one of {', '.join(EXAMPLES)})")
    sync()
    bugs = [e for e in examples if e != "rooms"]
    bug_dir = COPY / "target" / "seeded-bugs"
    shutil.rmtree(bug_dir, ignore_errors=True)
    sbt(*[f"{e}/cliLauncher" for e in examples],
        *([f"referenceCapture/runMain frflow.reference.SeededBugs {bug_dir} {' '.join(bugs)}"] if bugs else []))
    taken_from = source()
    for example in examples:
        # Captured beside the copy; reference/EXAMPLE is replaced only once the whole example is captured.
        out = OUT / example
        shutil.rmtree(out, ignore_errors=True)
        write(out / "SOURCE", taken_from)
        capture_cli(example, out)
        if example == "rooms":
            walkthrough(out)
        else:
            shutil.copy2(bug_dir / f"{example}.txt", out / "seeded-bugs.txt")
        cold(example)
        shutil.rmtree(REF / example, ignore_errors=True)
        shutil.move(out, REF / example)


if __name__ == "__main__":
    main(sys.argv[1:])
