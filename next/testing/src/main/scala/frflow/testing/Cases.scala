package frflow.testing

import cats.syntax.all.*
import frflow.core.code.Values
import frflow.core.example.Given
import frflow.core.name.SymbolName
import frflow.core.ty.Ty
import frflow.core.vocab.Vocabulary
import frflow.eval.{Env, EvalError, ScalaValue, Semantics}
import frflow.eval.run.{Broken, Made}
import frflow.testing.derive.Shrink
import frflow.testing.report.{Drawn, Failure, Hits, Outcome}
import scala.annotation.tailrec

/** One node's cases: each drawn by the types of its inputs and of the values its code is given (`needed`), judged
  * in turn up to the first that fails, which is then shrunk, each smaller case meeting what always holds of its
  * values (`made`).
  */
private[testing] final class Cases(semantics: Semantics, judge: Judge, needed: List[(SymbolName, Ty)],
    made: List[Made]):
  private val types = judge.inputs ++ needed.map(_._2)

  /** Case `from`: its inputs and what wiring does not make, drawn together by their types. */
  def drawn(draw: Draw, from: Drawn): Option[Case] =
    draw.all(types, from.size, from.seed.forCase(from.index)).map { vs =>
      val values = vs.zip(types).map((v, ty) => semantics.reflect(ScalaValue(v), ty))
      Case(values.take(judge.inputs.size), needed.zip(values.drop(judge.inputs.size)).map((s, v) => Given(s._1, v)))
    }

  /** The cases tried, what they reached, and what was found: the first failing case, shrunk; or, at a case the
    * statement has no Scala value at (`unchecked`), nothing more: the statement is not checked.
    */
  def search(cases: Iterator[(Case, Drawn)], coverage: Coverage, v: Vocabulary)(unchecked: EvalError => Boolean)
      : Searched =
    val shrink = Shrink(v)
    @tailrec def go(tried: Int, hits: Hits): Searched = cases.nextOption() match
      case None            => Searched(tried, hits, Outcome.Passed)
      case Some((c, from)) =>
        val reached = hits |+| coverage.of(c)
        judge.broken(c) match
          case Some(Broken.NotEvaluated(e)) if unchecked(e) => Searched(tried + 1, reached, Outcome.NotChecked(e))
          case Some(broke)                                  =>
            val (small, why) = smallest(shrink, c, broke, Shrinking.Rounds)
            Searched(tried + 1, reached, Outcome.Failed(Failure.Call(small.inputs, small.givens, why, from)))
          case None                                         => go(tried + 1, reached)
    go(0, coverage.zero)

  @tailrec private def smallest(shrink: Shrink, c: Case, broke: Broken, rounds: Int): (Case, Broken) =
    smaller(shrink, c).take(Shrinking.Tried).flatMap(s => judge.broken(s).map(s -> _)).headOption match
      case Some((s, b)) if rounds > 0 => smallest(shrink, s, b, rounds - 1)
      case _                          => (c, broke)

  /** Each input smaller, then each value given. */
  private def smaller(shrink: Shrink, c: Case): LazyList[Case] =
    val ins = LazyList.from(c.inputs.indices).flatMap(i =>
      shrink.of(c.inputs(i), judge.inputs(i)).take(Shrinking.Each).map(x => c.copy(inputs = c.inputs.updated(i, x))))
    val gs = LazyList.from(c.givens.indices).flatMap(j => needed.lift(j).fold(LazyList.empty)((_, ty) =>
      shrink.of(c.givens(j).value, ty).take(Shrinking.Each)
        .map(x => c.copy(givens = c.givens.updated(j, c.givens(j).copy(value = x))))))
    (ins #::: gs).filter(fits)

  private def fits(c: Case): Boolean =
    val values = (c.inputs ++ c.givens.map(_.value)).zip(types).map(semantics.literal)
    made.forall(_.broken(values, types, Env.of(Values.none)).isEmpty)
