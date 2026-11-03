#!/usr/bin/env python3
"""Mutants of FrFlow's obligations: each a small, plausible bug that leaves Lean proving less than the statements
assume. Of the selection (`Required`, `Made`, `Guards`, `Scope`, `CallingCode`), an obligation gone: the example
suites run (`CompletenessSuite` and `ObligationNamesSuite` on rooms, auth, crm and keycloak, and the obligations'
own suites). Of what an obligation says (`Keeping`, `Making`, `CallSites`), its statement weakened, its name kept:
the Lean suites of seeded bugs run, each expecting the bug's obligation to stay unproven. A mutant is killed when one
of its suites goes red. The source is restored after each, whatever happens.

    python3 bin/mutants.py            # every mutant, then the suites unchanged (they must pass)
    python3 bin/mutants.py cover made  # only the mutants whose names start so

Run from the repository's root, with no sbt server running in it. Each mutant takes about a minute (sbt starts,
recompiles the file, runs the suites); one checked by Lean, a few minutes.
"""
import pathlib, re, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
OBLIGATION = "next/proof/src/main/scala/frflow/proof/obligation/"
TERMS = "next/proof/src/main/scala/frflow/proof/terms/"
BROKEN = ["next-proof/Lean/testOnly frflow.proof.layout.BrokenLeanSuite"]
ASSUMED = ["next-project/testOnly frflow.project.assumed.RefusedSuite"]
SUITES = ["next-project/testOnly frflow.project.CompletenessSuite frflow.project.ObligationNamesSuite",
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
    ("keeping-before", TERMS + "Keeping.scala", "after)((_, w) =>\n            holds(s, kept, w))",
     "after)((_, _) =>\n            holds(s, kept, before))",
     "cover_ states the rule of the world a run starts from, not of the one it leaves", BROKEN),
    ("making-tautology", TERMS + "Making.scala", "kept.of[T, Any](result, s).fold(s.bool(true))(_(made(s, args)))",
     "kept.of[T, Any](result, s).fold(s.bool(true))(k => s.implies(k(made(s, args)), k(made(s, args))))",
     "made_ states that what a maker makes meets the rule if it does", BROKEN),
    ("calls-bound", TERMS + "CallSites.scala", "bound(x, made(first, written), env, written ++ writes(first))(rest)",
     "bound(x, made(first, written).orElse(guarded(x.ty, guards)), env, written ++ writes(first))(rest)",
     "made_ at a call assumes the rules of every value a step binds, not only of an operation's result",
     ["next-proof/Lean/testOnly frflow.proof.layout.calls.RowsViaBranchLeanSuite"]),
    ("atonce-pairs", "next/core/src/main/scala/frflow/core/analysis/AtOnce.scala",
     "&& models(v, ua(i)).exists(models(v, ub(j)))", "&& models(v, ua(i)).exists(models(v, ub(j))) && i < 0",
     "no two steps at once are asked to commute: the reading in turn stands for runs it does not"),
    ("atonce-whole", "next/core/src/main/scala/frflow/core/analysis/AtOnce.scala",
     "case (true, true)   => atomic(a) == atomic(b)", "case (true, true)   => true",
     "a transaction is taken as one step beside a call, which may come between its calls",
     ["next-core/testOnly frflow.core.analysis.AtOnceSuite"]),
    ("atonce-race", "next/core/src/main/scala/frflow/core/analysis/AtOnce.scala",
     "case Prog.Race(l, r, _)       => p :: of(l) ++ of(r)", "case Prog.Race(l, r, _)       => of(l) ++ of(r)",
     "a race is no concurrent step: its sides' steps are read in turn, asked nothing",
     ["next-core/testOnly frflow.core.analysis.AtOnceSuite"]),
    ("atonce-traverse-fails", "next/core/src/main/scala/frflow/core/analysis/AtOnce.scala",
     "case Prog.ParEach(_, _, b, _) => fails(v, b)", "case Prog.ParEach(_, _, b, _) => fails(v, b) && b == null",
     "a traverse at once whose body may let an error out is not refused, though the error cancels the others",
     ["next-core/testOnly frflow.core.analysis.ValidateSuite"]),
    ("model-at-once", "next/testing/src/main/scala/frflow/testing/model/ModelRuns.scala",
     "case (None, first :: second :: _) if !List(",
     "case (None, first :: second :: _) if first.op.value.isEmpty && !List(",
     "the model tests call the Scala in turn only: a call that reads, pauses and writes is taken as atomic",
     ["next-testing/testOnly frflow.testing.ModelRunsSuite"]),
    ("scheduling-call", "next/eval/src/main/scala/frflow/eval/flow/Scheduling.scala",
     "if op == Clock.sleep.name then fa else F.uncancelable(_ => fa)",
     "if op == Clock.sleep.name then fa else F.uncancelable(poll => poll(fa))",
     "the interleavings tests cancel a call part way, which production does not",
     ["next-project/testOnly sharing.InterleavingsSuite"]),
    ("running-call", "next/eval/src/main/scala/frflow/eval/Running.scala",
     "if op == Clock.sleep.name then call else F.uncancelable(_ => call)",
     "if op == Clock.sleep.name then call else F.uncancelable(poll => poll(call))",
     "production cancels an operation's call part way, which Lean reads all or nothing",
     ["next-eval/testOnly frflow.eval.RunningSuite"]),
    ("running-atomic", "next/eval/src/main/scala/frflow/eval/Running.scala",
     "F.uncancelable(_ => lock.lock.surround(of(body)))", "lock.lock.surround(of(body))",
     "production cancels a transaction part way, which Lean reads as one step",
     ["next-eval/testOnly frflow.eval.RunningSuite"]),
    ("assumed-claims", "next/core/src/main/scala/frflow/core/analysis/Resolve.scala",
     "filter(t.vocabulary.isAssumed).flatMap(Constrained.assumptions(t, _))\n    (called",
     "filter(t.vocabulary.isAssumed).flatMap(Constrained.statements(t, _))\n    (called",
     "code calling an operation known only by assumptions takes a claim about it as given (step 13c review, B3)",
     ASSUMED),
    ("assumed-hypotheses", "next/core/src/main/scala/frflow/core/analysis/Resolve.scala",
     "(reliesOn(t, id).filter(about) ++ direct)", "(Nil.filter(about) ++ direct)",
     "a step with parts over code calling an operation known only by assumptions takes nothing of it (the review's "
     "N3)", ["next-project/testOnly crm.LeanShapeSuite"]),
    ("assumed-models", OBLIGATION + "Required.scala", "Option.when(modelled && ",
     "Option.when(modelled && n.value.isEmpty && ",
     "a claim about operations on a state alone is asked nothing, so proven", ASSUMED),
    ("assumed-makes", "next/core/src/main/scala/frflow/core/analysis/refused/Assumed.scala",
     "      beside ++ made\n", "      beside ++ made.take(0)\n",
     "a claim of always covers what an operation known only by assumptions gives (the review's B2)", ASSUMED),
    ("assumed-beside", "next/core/src/main/scala/frflow/core/analysis/refused/Assumed.scala",
     "      beside ++ made\n", "      beside.take(0) ++ made\n",
     "what is assumed of an operation known only by assumptions reads another model (the review's B1)", ASSUMED),
    ("assumed-outside", TERMS + "CallSites.scala", "if o.assumed then guarded(Ty.yields(ty), outside)",
     "if o.assumed then guarded(Ty.yields(ty), guards ++ outside)",
     "a result from outside handed on carries a claim's rule (the review's R5)", ASSUMED),
    ("assumed-twice", "next/testing/src/main/scala/frflow/testing/model/AssumedCall.scala",
     "if gave.distinct.size > 1 || after != left then", "if gave.isEmpty && after != left then",
     "the model tests take an operation known only by assumptions to be a function of its state unchecked (S1)",
     ["next-testing/testOnly frflow.testing.AssumedModelSuite"]),
    ("assumed-untested", "next/core/src/main/scala/frflow/core/checking/Assumed.scala",
     ".distinct.filterNot(run.contains)", ".distinct.filterNot(run.contains).take(0)",
     "an assumption the generated runs cannot evaluate is trusted silently (S3)",
     ["next-project/testOnly frflow.project.assumed.UntestedSuite"]),
]


def sbt(commands):
    run = subprocess.run(["sbt", *commands], cwd=ROOT, stdin=subprocess.DEVNULL, capture_output=True, text=True)
    plain = [re.sub(r"\x1b\[[0-9;]*m", "", line) for line in run.stdout.splitlines()]
    red = sorted({line.split("==> X", 1)[1].strip().split("  ")[0][:110] for line in plain if "==> X" in line})
    return run.returncode, red, run.stdout


def mutant(name, path, text, mutated, bug, suites=SUITES):
    file = ROOT / path
    source = file.read_text()
    if source.count(text) != 1:
        return f"{name}: not applied, the text is not in {path} once"
    try:
        file.write_text(source.replace(text, mutated))
        code, red, out = sbt(suites)
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
    code, red, _ = sbt(SUITES + sorted({s for m in chosen if len(m) > 5 for s in m[5]}))
    results.append("unchanged: the suites pass" if code == 0 else f"unchanged: RED ({', '.join(red)})")
    print("\n".join(results))
    return 0 if code == 0 and all(": killed (" in r for r in results[:-1]) else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
