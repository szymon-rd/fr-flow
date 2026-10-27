package frflow.testing

import cats.syntax.all.*
import frflow.core.code.{Code, Impl}
import frflow.core.example.Example
import frflow.core.name.{NodeId, SymbolName}
import frflow.core.Theory
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType
import frflow.eval.Semantics
import frflow.eval.run.{Broken, CallCheck, Made, Wiring}
import frflow.testing.derive.ExampleCases
import frflow.testing.report.{Against, Count, Drawn, Failure, Note, TestReport}

/** Plain code tested against the claims about its Definition on generated cases: each case's inputs drawn, the
  * values its code reads made by `Wiring` (what wiring does not make drawn too), the code called through `Fn`, the
  * call judged (`Judge`). The failing cases kept are replayed first; then case `i` of `cases` is drawn from
  * `(seed, i)` at its size (`Seed.sizeOf`), so a run is a function of its seed, its count and the code. The first
  * failing case is shrunk (`Cases`). Today's run-time check of a call is this judgement, made before production.
  */
final class PropertyTests(semantics: Semantics, t: Theory):
  private val wiring = Wiring.onModels(semantics, t)
  private val made = Made.of(semantics, t)

  def of(node: NodeId, plan: Plan, draw: Draw): Option[TestReport] = of(node, plan, draw, Nil)

  /** With the cases the examples show of the call counted in its coverage first (`ExampleCases`). */
  def of(node: NodeId, plan: Plan, draw: Draw, examples: List[Example]): Option[TestReport] =
    Judge.of(semantics, t, node).map { judge =>
      val needed = givenTypes(node)
      val found = searched(node, plan, draw, judge)(needed, examples)
      val still = Option.when(judge.inputs.isEmpty && needed.isEmpty)(Note.NothingToVary).toList
      val replayed = plan.replay.collect { case f: Failure.Call => f }.size
      TestReport(Count(replayed + plan.settings.cases, found.tried), plan.settings.seed,
        Against.Claim(node), found.outcome, found.hits.unreached, draw.notes ++ still)
    }

  /** The failing cases kept, then case `i` of `cases` drawn from `(seed, i)`, judged up to the first failing. */
  private def searched(node: NodeId, plan: Plan, draw: Draw, judge: Judge)(needed: List[(SymbolName, Ty)],
      examples: List[Example]): Searched =
    val cases = Cases(semantics, judge, needed, made)
    val replayed = plan.replay.collect { case Failure.Call(ins, gs, _, from) => Case(ins, gs) -> from }
    val drawn = Iterator.range(0, plan.settings.cases).flatMap { i =>
      val from = Drawn(plan.settings.seed, i, Seed.sizeOf(i, plan.settings.cases))
      cases.drawn(draw, from).map(_ -> from)
    }
    val coverage = Coverage(semantics, t, node, judge.inputs)
    val shown = CallCheck.of(semantics, t, node).toList.flatMap(c => ExampleCases.of(examples, c.op, c.inputs))
    cases.search(replayed.iterator ++ drawn, coverage, t.vocabulary, coverage.zero |+| shown.foldMap(coverage.of))(
      NoValue.of(t, _))

  /** What one case of a call breaks, if anything (`Judge.call`). */
  def judged(check: CallCheck, code: Impl, c: Case): Option[Broken] = Judge.call(semantics, wiring)(check, code, c)

  /** The first case, in order, that breaks something, with what it broke. */
  def firstFailing(check: CallCheck, code: Impl, cases: List[Case]): Option[(Case, Broken)] =
    cases.iterator.flatMap(c => judged(check, code, c).map(c -> _)).nextOption()

  /** What a test of `node`'s code draws beside its inputs, by its declared type: what wiring does not make, and every
    * value provided where the code runs, which plain code may read without its statement mentioning it.
    */
  private def givenTypes(node: NodeId): List[(SymbolName, Ty)] =
    val provided = t.code.attached.collect { case (s, a) if a.code == Code.Provided => s }.toList.sortBy(_.value)
    (wiring.needed(node) ++ provided).distinct.flatMap(s =>
      t.vocabulary.symbol(s).map(_.ty).collect { case SymbolType.Typed(ty) => s -> ty })
