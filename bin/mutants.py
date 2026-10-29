#!/usr/bin/env python3
"""Mutants of FrFlow's obligation selection: each a small, plausible bug in `Required`, `Made`, `Guards`, `Scope`
or `CallingCode` that leaves Lean proving less than the statements assume. For each, the source is changed, the
example suites run (`CompletenessSuite` on rooms, auth, crm and keycloak, and the obligations' own suites), and the
mutant is killed when one of them goes red. The source is restored after each, whatever happens.

    python3 bin/mutants.py            # every mutant, then the suites unchanged (they must pass)
    python3 bin/mutants.py cover made  # only the mutants whose names start so

Run from the repository's root, with no sbt server running in it. Each mutant takes about a minute (sbt starts,
recompiles the file, runs the suites).
"""
import pathlib, re, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
OBLIGATION = "next/proof/src/main/scala/frflow/proof/obligation/"
SUITES = ["next-project/testOnly frflow.project.CompletenessSuite",
          "next-eval/testOnly whole.RulesSuite whole.CaptureSuite",
          "next-proof/testOnly frflow.proof.obligation.RequiredSuite frflow.proof.obligation.AlwaysSuite"]

# name, file, text, mutated text, the bug it stands for
MUTANTS = [
    ("cover", OBLIGATION + "Required.scala", "commutes(r, n) ++ keeps(r, n) ++ Made.of(r, n)",
     "commutes(r, n) ++ Made.of(r, n)", "Required asks no cover_: no program is held to the rules of a store"),
    ("made-op", OBLIGATION + "Made.scala", "          byModels(r, n, range, kept)",
     "          byModels(r, n, range, kept).take(0)", "Made asks no made_ of a store's operation"),
    ("made-call", OBLIGATION + "Made.scala", "case (tys, i) if tys.exists(Guards.applies(r.theory, ty, _)) =>",
     "case (tys, i) if tys.forall(Guards.applies(r.theory, ty, _)) =>",
     "Made asks made_ at a call only when every argument holds the type"),
    ("guards-fields", "next/core/src/main/scala/frflow/core/analysis/outside/Guards.scala",
     "case Ty.Data(n) if !seen(n) => data(n).exists(_.fieldTypes.exists(reaches(data, ty, seen + n)))",
     "case Ty.Data(n) if !seen(n) => false",
     "Guards.applies does not reach a record's fields: what makes a record holding a T is not held to it"),
    ("scope-writers", "next/core/src/main/scala/frflow/core/analysis/Scope.scala",
     "ops.filter(op => makes(t, r, op) || calls(t, stores, op))",
     "ops.filter(op => makes(t, r, op) || calls(t, stores, op) && op.value.isEmpty)",
     "Scope leaves out the programs calling a store's operations"),
    ("scope-stores", "next/core/src/main/scala/frflow/core/analysis/Scope.scala",
     "case Range.Made(ty)    => t.vocabulary.models.filter(m => holds(t, ty, m.state))",
     "case Range.Made(ty)    => Nil", "an always[T] is about no store, even one whose state holds a T"),
    ("calls", "next/proof/src/main/scala/frflow/proof/terms/CallingCode.scala",
     "(define).map(_.tys)", "(define).map(_.tys).take(1)", "CallingCode reads only the first call of plain Scala"),
]


def sbt(commands):
    run = subprocess.run(["sbt", *commands], cwd=ROOT, stdin=subprocess.DEVNULL, capture_output=True, text=True)
    plain = [re.sub(r"\x1b\[[0-9;]*m", "", line) for line in run.stdout.splitlines()]
    red = sorted({line.split("==> X", 1)[1].strip().split("  ")[0][:110] for line in plain if "==> X" in line})
    return run.returncode, red, run.stdout


def mutant(name, path, text, mutated, bug):
    file = ROOT / path
    source = file.read_text()
    if source.count(text) != 1:
        return f"{name}: not applied, the text is not in {path} once"
    try:
        file.write_text(source.replace(text, mutated))
        code, red, out = sbt(SUITES)
    finally:
        file.write_text(source)
    if code == 0:
        return f"{name}: SURVIVED ({bug})"
    if not red:
        tail = "\n".join(out.splitlines()[-15:])
        return f"{name}: killed by a build failure, not a suite ({bug})\n{tail}"
    return f"{name}: killed ({bug}) by\n    " + "\n    ".join(red)


def main(names):
    chosen = [m for m in MUTANTS if not names or any(m[0].startswith(n) for n in names)]
    results = [mutant(*m) for m in chosen]
    code, red, _ = sbt(SUITES)
    results.append("unchanged: the suites pass" if code == 0 else f"unchanged: RED ({', '.join(red)})")
    print("\n".join(results))
    return 0 if code == 0 and all(": killed (" in r for r in results[:-1]) else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
