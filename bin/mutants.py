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
OBLIGATION = "modules/proof/src/main/scala/frflow/proof/obligation/"
TERMS = "modules/proof/src/main/scala/frflow/proof/terms/"
BROKEN = ["proof/Lean/testOnly frflow.proof.layout.BrokenLeanSuite"]
ASSUMED = ["project/testOnly frflow.project.assumed.RefusedSuite"]
TIME = ["project/testOnly frflow.project.TimeLeanSuite", "project/Lean/testOnly frflow.project.TimeLeanSuite"]
SUITES = ["project/testOnly frflow.project.CompletenessSuite frflow.project.ObligationNamesSuite",
          "testing/testOnly whole.RulesSuite whole.CaptureSuite",
          "proof/testOnly frflow.proof.obligation.RequiredSuite frflow.proof.obligation.AlwaysSuite"]

# name, file, text, mutated text, the bug it stands for
MUTANTS = [
    ("cover", OBLIGATION + "Required.scala", "commutes(r, n) ++ keeps(r, n) ++ Made.of(r, n)",
     "commutes(r, n) ++ Made.of(r, n)", "Required asks no cover_: no program is held to the rules of a store"),
    ("made-op", OBLIGATION + "Made.scala", "          byModels(r, n, range, kept)",
     "          byModels(r, n, range, kept).take(0)", "Made asks no made_ of a store's operation"),
    ("made-call", OBLIGATION + "Made.scala", "case (tys, i) if tys.exists(Guards.applies(r.theory, ty, _)) =>",
     "case (tys, i) if tys.forall(Guards.applies(r.theory, ty, _)) =>",
     "Made asks made_ at a call only when every argument holds the type"),
    ("guards-fields", "modules/core/src/main/scala/frflow/core/analysis/outside/Guards.scala",
     "case Ty.Data(n) if !seen(n) => data(n).exists(_.fieldTypes.exists(reaches(data, ty, seen + n)))",
     "case Ty.Data(n) if !seen(n) => false",
     "Guards.applies does not reach a record's fields: what makes a record holding a T is not held to it"),
    ("scope-writers", "modules/core/src/main/scala/frflow/core/analysis/outside/Scope.scala",
     "ops.filter(op => makes(t, r, op) || calls(t, stores, op))",
     "ops.filter(op => makes(t, r, op) || calls(t, stores, op) && op.value.isEmpty)",
     "Scope leaves out the programs calling a store's operations"),
    ("scope-stores", "modules/core/src/main/scala/frflow/core/analysis/outside/Scope.scala",
     "case Range.Made(ty)    => t.vocabulary.models.filter(m => holds(t, ty, m.state))",
     "case Range.Made(ty)    => Nil", "an always[T] is about no store, even one whose state holds a T"),
    ("calls", "modules/proof/src/main/scala/frflow/proof/terms/CallingCode.scala",
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
     ["proof/Lean/testOnly frflow.proof.layout.calls.RowsViaBranchLeanSuite"]),
    ("atonce-pairs", "modules/core/src/main/scala/frflow/core/analysis/AtOnce.scala",
     "&& models(v, ua(i)).exists(models(v, ub(j)))", "&& models(v, ua(i)).exists(models(v, ub(j))) && i < 0",
     "no two steps at once are asked to commute: the reading in turn stands for runs it does not"),
    ("atonce-whole", "modules/core/src/main/scala/frflow/core/analysis/AtOnce.scala",
     "case (true, true)   => atomic(a) == atomic(b)", "case (true, true)   => true",
     "a transaction is taken as one step beside a call, which may come between its calls",
     ["core/testOnly frflow.core.analysis.AtOnceSuite"]),
    ("atonce-race", "modules/core/src/main/scala/frflow/core/analysis/AtOnce.scala",
     "case Prog.Race(l, r, _)       => p :: of(l) ++ of(r)", "case Prog.Race(l, r, _)       => of(l) ++ of(r)",
     "a race is no concurrent step: its sides' steps are read in turn, asked nothing",
     ["core/testOnly frflow.core.analysis.AtOnceSuite"]),
    ("atonce-traverse-fails", "modules/core/src/main/scala/frflow/core/analysis/AtOnce.scala",
     "case Prog.ParEach(_, _, b, _) => fails(v, b)", "case Prog.ParEach(_, _, b, _) => fails(v, b) && b == null",
     "a traverse at once whose body may let an error out is not refused, though the error cancels the others",
     ["core/testOnly frflow.core.analysis.ValidateSuite"]),
    ("model-at-once", "modules/testing/src/main/scala/frflow/testing/model/ModelRuns.scala",
     "      case (None, first :: second :: _) =>\n",
     "      case (None, first :: second :: _) if first.op.value.isEmpty =>\n",
     "the model tests call the Scala in turn only: a call that reads, pauses and writes is taken as atomic",
     ["testing/testOnly frflow.testing.ModelRunsSuite"]),
    ("scheduling-call", "modules/eval/src/main/scala/frflow/eval/flow/Scheduling.scala",
     "if op == Clock.sleep.name then fa else F.uncancelable(_ => fa)",
     "if op == Clock.sleep.name then fa else F.uncancelable(poll => poll(fa))",
     "the interleavings tests cancel a call part way, which production does not",
     ["project/testOnly sharing.InterleavingsSuite"]),
    ("running-call", "modules/eval/src/main/scala/frflow/eval/run/Running.scala",
     "if op == Clock.sleep.name then call else F.uncancelable(_ => call)",
     "if op == Clock.sleep.name then call else F.uncancelable(poll => poll(call))",
     "production cancels an operation's call part way, which Lean reads all or nothing",
     ["evaluation/testOnly frflow.eval.RunningSuite"]),
    ("running-atomic", "modules/eval/src/main/scala/frflow/eval/run/Running.scala",
     "F.uncancelable(_ => lock.lock.surround(of(body)))", "lock.lock.surround(of(body))",
     "production cancels a transaction part way, which Lean reads as one step",
     ["evaluation/testOnly frflow.eval.RunningSuite"]),
    ("assumed-claims", "modules/core/src/main/scala/frflow/core/analysis/resolution/Resolve.scala",
     "filter(t.vocabulary.isAssumed).flatMap(Constrained.assumptions(t, _))\n    (called",
     "filter(t.vocabulary.isAssumed).flatMap(Constrained.statements(t, _))\n    (called",
     "code calling an operation known only by assumptions takes a claim about it as given (step 13c review, B3)",
     ASSUMED),
    ("assumed-hypotheses", "modules/core/src/main/scala/frflow/core/analysis/resolution/Resolve.scala",
     "(reliesOn(t, id).filter(about) ++ direct)", "(Nil.filter(about) ++ direct)",
     "a step with parts over code calling an operation known only by assumptions takes nothing of it (the review's "
     "N3)", ["project/testOnly crm.LeanShapeSuite"]),
    ("assumed-models", OBLIGATION + "Required.scala", "Option.when((modelled || worldly) && ",
     "Option.when((modelled || worldly) && n.value.isEmpty && ",
     "a claim about operations on a state alone is asked nothing, so proven", ASSUMED),
    ("assumed-makes", "modules/core/src/main/scala/frflow/core/analysis/Assumed.scala",
     "      beside ++ made\n", "      beside ++ made.take(0)\n",
     "a claim of always covers what an operation known only by assumptions gives (the review's B2)", ASSUMED),
    ("assumed-beside", "modules/core/src/main/scala/frflow/core/analysis/Assumed.scala",
     "      beside ++ made\n", "      beside.take(0) ++ made\n",
     "what is assumed of an operation known only by assumptions reads another model (the review's B1)", ASSUMED),
    ("assumed-outside", TERMS + "CallSites.scala", "if o.assumed then guarded(Ty.yields(ty), outside)",
     "if o.assumed then guarded(Ty.yields(ty), guards ++ outside)",
     "a result from outside handed on carries a claim's rule (the review's R5)", ASSUMED),
    ("assumed-twice", "modules/testing/src/main/scala/frflow/testing/model/AssumedCall.scala",
     "if gave.distinct.size > 1 || after != left then", "if gave.isEmpty && after != left then",
     "the model tests take an operation known only by assumptions to be a function of its state unchecked (S1)",
     ["testing/testOnly frflow.testing.AssumedModelSuite"]),
    ("assumed-at-once", "modules/testing/src/main/scala/frflow/testing/model/CallsAtOnce.scala",
     "if List(first, second).exists(st => check.model.isAssumed(st.op)) then againstItself(held, first, second)",
     "if List(first, second).exists(st => check.model.isAssumed(st.op)) then againstItself(held, first, second)" +
     ".map(_ => Option.empty[Difference])",
     "two calls at once of an operation known only by assumptions are not tried (R-S1)",
     ["testing/testOnly frflow.testing.ModelRunsSuite"]),
    ("cover-callees", OBLIGATION + "Required.scala", "    val callees = Callees.within(r.theory, op)\n",
     "    val callees = Callees.ofDefinition(r.theory, op).getOrElse(Callees.within(r.theory, op))\n",
     "a cover_ leaves what the program calls opaque, the code of its proven callees not put in as impl puts it",
     ["project/testOnly sharing.PortSuite"]),
    ("cover-circle", OBLIGATION + "Required.scala", ".filterNot(Reads.restsOn(r.theory, _, n))",
     ".filterNot(h => h == n)",
     "a cover_ takes a claim resting on the rule it covers, which is then kept by being assumed",
     ["project/testOnly frflow.project.CoverCircleSuite"]),
    ("schedule-inside", "modules/proof/src/main/scala/frflow/proof/layout/Lowering.scala",
     "allows(m.name), LowerFaults.free)", "allows(m.name), allows(m.name))",
     "a schedule restricts the time's moves inside a run, against the run's own view: a wait ends early (13d B1)",
     TIME),
    ("clock-writers", "modules/core/src/main/scala/frflow/core/analysis/outside/Premises.scala",
     "op => m.timed.isDefined || Progs.all", "op => false || Progs.all",
     "a run whose only clock step is now changes no clock: an isConstant is asked nothing of it (13d B2)", TIME),
    ("cover-walk", "modules/core/src/main/scala/frflow/core/analysis/outside/Reads.scala",
     "Walk.breadthFirst(List(id), identity)(Resolve.below(t, _)).exists(",
     "Walk.breadthFirst(List(id), identity)(_ => Nil).exists(",
     "a cover_ takes a claim proven from one resting on the rule it covers (the walk down)",
     ["project/testOnly frflow.project.CoverCircleSuite"]),
    ("cover-own", OBLIGATION + "Required.scala", ".filterNot(h => mentions(r, h, op))",
     ".filterNot(h => h == n && mentions(r, h, op))",
     "a cover_ takes an assumption about the covered program itself as given (13d S2)",
     ["project/testOnly frflow.project.CoverCircleSuite"]),
    ("frozen-try", "modules/proof/src/main/scala/frflow/proof/audit/Obligations.scala",
     "Option(Tries.frozen(r, n.id)).filter(_.nonEmpty)", "Option(Tries.frozen(r, n.id)).filter(_.isEmpty)",
     "a schedule freezing the clock is never tried, so every deadline holds of a still clock unwarned (13d S1)", TIME),
    ("kept-below", "modules/proof/src/main/scala/frflow/proof/audit/Obligations.scala",
     "case Cover(op)                  => Reads.coverTaken(r.theory, SymbolName(op))",
     "case Cover(op)                  => Reads.coverTaken(r.theory, SymbolName(op)).take(0)",
     "a rule kept by its cover_s from another rule still open is read as proven (the 13d re-review's R-B1)", TIME),
    ("kept-made", "modules/proof/src/main/scala/frflow/proof/audit/Obligations.scala",
     "case Made(maker)                => made(r, maker)",
     "case Made(maker)                => made(r, maker).take(0)",
     "a value rule made from another rule still open is read as proven (the 13d third pass's R3-B1)", TIME),
    ("kept-own", "modules/project/src/main/scala/frflow/project/pipeline/ReadProof.scala",
     "t.node(rule).exists(n => local(a, n, results(rule)) != (Nil, Nil))",
     "results(rule).exists(x => x.name.isInstanceOf[ObligationName.Cover] && x.status != Proven)",
     "a rule is open only for a reason listed (its cover_s), not for its whole standing (the 13d sixth pass)", TIME),
    ("kept-inhabited", "modules/project/src/main/scala/frflow/project/pipeline/ReadProof.scala",
     "vacant || t.node(rule)", "false && vacant || t.node(rule)",
     "a statement resting on a rule nothing meets is read as proven, of nothing (the 13d fifth pass's P5-B1)", TIME),
    ("kept-untried", "modules/project/src/main/scala/frflow/project/pipeline/ReadProof.scala",
     "reports.isEmpty || reports.exists(", "false && reports.isEmpty || reports.exists(",
     "a rule a tested maker no node tests is read as proven (the 13d seventh pass's S7-N1)", TIME),
    ("kept-makers", "modules/project/src/main/scala/frflow/project/pipeline/ReadProof.scala",
     "reports.exists(n => red(a.tested(n)))", "reports.exists(n => false && red(a.tested(n)))",
     "a rule a tested maker's failing test does not name is read as proven (the 13d sixth pass's P6-B1)", TIME),
    ("outside-asked", OBLIGATION + "Required.scala", "Made.atCalls(r, n) ++ Made.outside(r, n))",
     "Made.atCalls(r, n))",
     "a claimed always[T] is taken of the values from outside unasked (the 13d fourth pass's P4-B2)", TIME),
    ("late-look", "modules/core/src/main/scala/frflow/core/analysis/Waits.scala",
     "atOnce(clock, Looks.of(v, clock, d))", "atOnce(clock, d)",
     "a look at the clock after other steps reads the time the run started at (the 13d re-review's R-B2)", TIME),
    ("schedule-unwritten", "modules/core/src/main/scala/frflow/core/analysis/outside/Outsides.scala",
     "over.filter(m => t.vocabulary.model(m).forall(Premises.writers(t, _).isEmpty))", "Nil",
     "a schedule over a model no program writes freezes the time unwarned (the 13d re-review's R-N1)",
     ["api/testOnly frflow.api.ReadingSuite"]),
    ("elapse-cover", OBLIGATION + "Required.scala", "    } ++ outside(r, n)\n", "    } ++ outside(r, n).take(0)\n",
     "no rule reading the clock is asked to survive time passing (owner §47's cover_elapse)", TIME),
    ("elapse-constant", "modules/core/src/main/scala/frflow/core/analysis/outside/Constancy.scala",
     "run(t, s.name, ty).filter(_ => worldly || writers(s.name))\n",
     "run(t, s.name, ty).filter(_ => worldly && writers(s.name))\n",
     "an isConstant reading the clock is not asked to survive time passing", TIME),
    ("schedule-guard", "modules/proof/src/main/scala/frflow/proof/layout/Lowering.scala",
     "rules.reduceOption(LExpr.Infix(LOp.And, _, _)).getOrElse(Atoms.name(\"True\"))",
     "rules.take(0).reduceOption(LExpr.Infix(LOp.And, _, _)).getOrElse(Atoms.name(\"True\"))",
     "the world moves the clock wherever it likes, whatever the schedules say", TIME),
    ("schedule-premise", "modules/core/src/main/scala/frflow/core/analysis/outside/Premises.scala",
     "    Outsides.schedules(t, m.name).map((id, _) => Premise.Schedule(m.name, id))",
     "    Outsides.schedules(t, m.name).map((id, _) => Premise.Schedule(m.name, id)).take(0)",
     "a check on the clock rests on no schedule, so none is listed or reviewed",
     ["testing/testOnly whole.ExamplesSuite frflow.eval.StampsSuite"]),
    ("clock-ticks", "modules/proof/src/main/scala/frflow/proof/lean/lower/LowerFaults.scala",
     "      if op == c.timed.elapse then moved else", "      if op == c.timed.elapse || true then moved else",
     "time passes at no step of a run: a program relying on its run taking no time is proven", TIME),
    ("waits-at-once", "modules/core/src/main/scala/frflow/core/analysis/Waits.scala",
     "if AtOnce.of(ir).exists(waits(_, clock)) =>", "if AtOnce.of(ir).exists(waits(_, clock)) && d.name.value.isEmpty =>",
     "waits at once read in turn add up (the step 13 re-review's RN1)", TIME),
    ("assumed-untested", "modules/core/src/main/scala/frflow/core/checking/Assumed.scala",
     ".distinct.filterNot(run.contains)", ".distinct.filterNot(run.contains).take(0)",
     "an assumption the generated runs cannot evaluate is trusted silently (S3)",
     ["project/testOnly frflow.project.assumed.UntestedSuite"]),
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
