package frflow.testing

import frflow.core.code.{Impl, Values}
import frflow.core.example.Gen
import frflow.core.expr.Value
import frflow.core.name.NodeId
import frflow.core.spec.CallForms
import frflow.core.Theory
import frflow.core.name.SymbolName
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType
import frflow.eval.{Applied, Env, Fn, ScalaValue, Semantics}
import frflow.eval.run.{Broken, CallCheck, Wiring}
import frflow.testing.report.{Against, Failure, TestReport}
import scala.util.Try

/** Plain code tested against the claims about its Definition on generated cases: each case's inputs drawn, the
  * values its code reads made by `Wiring` (what wiring does not make drawn too), the code called through `Fn`, the
  * call judged by `CallCheck`; a claim that reads as no call evaluated whole on its drawn variables, every
  * Definition given its meaning (owner R14.5). The failing cases kept are replayed first. Pure given a seed, the
  * developer's code aside. Today's run-time check of a call is this judgement, made before production.
  */
final class PropertyTests(semantics: Semantics, t: Theory):
  private val wiring = Wiring(semantics, t)

  def of(node: NodeId, plan: Plan, draw: Draw): Option[TestReport] =
    val judge: Option[(List[Ty], Case => Option[Broken])] = CallCheck.of(semantics, t, node) match
      case Some(check) => code(check).map(impl => (check.inputs, c => judged(check, impl, c)))
      case None        => t.node(node).flatMap(_.statement.said).map(CallForms.whole).map { w =>
          val whole = semantics.lambda(w)
          (w.value.params.map(_.ty), c => holds(whole, w.value.params.map(_.ty), c))
        }
    judge.map { (types, judged) =>
      val replayed = plan.replay.map(f => (Case(f.inputs, Values.none), f.index, f.size))
      val drawn = (0 until plan.settings.cases).map(i => (drawnCase(node, types, draw)(plan.settings.seed, i), i,
        i % 10)).toList
      val failure = (replayed ++ drawn).iterator.flatMap((c, i, size) =>
        judged(c).map(b => Failure(c.inputs, b, plan.settings.seed, i, size))).nextOption()
      TestReport(plan.settings.cases, plan.settings.seed, Against.Claim(node), failure, Nil, Nil)
    }

  /** What one case breaks, if anything: the code's exception, the post, an `always[T]` of a value given or made. */
  def judged(check: CallCheck, code: Impl, c: Case): Option[Broken] =
    val values = wiring.values(c.drawn)
    val args = c.inputs.zip(check.inputs).map(semantics.literal)
    Try(Fn.call(code.make(values), args))
      .fold(t => Some(Broken.Threw(String.valueOf(t.getMessage))), got => check.broken(args :+ got, Env.of(values)))

  /** The first case, in order, that breaks something, with what it broke. */
  def firstFailing(check: CallCheck, code: Impl, cases: List[Case]): Option[(Case, Broken)] =
    cases.iterator.flatMap(c => judged(check, code, c).map(c -> _)).nextOption()

  /** A claim read whole, at a case's variables, each Definition given its meaning. */
  private def holds(whole: Applied, types: List[Ty], c: Case): Option[Broken] =
    Try(whole.run(Env.of(wiring.values(c.drawn)), c.inputs.zip(types).map(semantics.literal))).fold(
      e => Some(Broken.Threw(String.valueOf(e.getMessage))), {
        case Left(e)                => Some(Broken.NotEvaluated(e))
        case Right(v) if !Fn.bool(v) => Some(Broken.Post)
        case Right(_)               => None
      })

  private def code(check: CallCheck): Option[Impl] = t.code.attached.get(check.op).flatMap(_.code.scala).map(_.impl)

  /** Case `i`: its inputs drawn by their types from the case's own stream, and what wiring does not make. */
  private def drawnCase(node: NodeId, types: List[Ty], draw: Draw)(seed: Seed, i: Int): Case =
    val random = seed.forCase(i)
    val inputs = types.map(ty => value(draw, ty, i % 10, random))
    val needed = wiring.needed(node).flatMap(s => typeOf(s).map(ty => s -> semantics.literal(value(draw, ty, i % 10,
      random), ty).unwrap))
    Case(inputs, Values(needed.map((s, v) => s -> (() => v)).toMap))

  private def value(draw: Draw, ty: Ty, size: Int, random: java.util.SplittableRandom): Value =
    semantics.reflect(ScalaValue(draw(Gen.Derived[Any](ty), size, random)), ty)

  private def typeOf(s: SymbolName): Option[Ty] = t.vocabulary.symbol(s).map(_.ty).collect {
    case SymbolType.Typed(ty) => ty
  }
