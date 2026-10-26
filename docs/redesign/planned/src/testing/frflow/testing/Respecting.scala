package frflow.testing

import frflow.core.code.Values
import frflow.core.example.Gen
import frflow.eval.{Env, ScalaValue}
import frflow.eval.run.Made
import java.util.SplittableRandom

/** A `Draw` whose values meet what always holds of their types (`Made`): a value drawn by its type is drawn again
  * until every `always[T]` of its type holds of it, up to `tries` times.
  */
final class Respecting(draw: Draw, made: List[Made], tries: Int) extends Draw:
  def apply[A](g: Gen[A], size: Int, random: SplittableRandom): A = g match
    case Gen.Derived(ty) =>
      Iterator.continually(draw(g, size, random)).take(tries)
        .find(a => made.forall(_.broken(List(ScalaValue(a)), List(ty), Env.of(Values.none)).isEmpty))
        .getOrElse(throw IllegalStateException(s"no value of $ty meeting what always holds of it in $tries draws"))
    case other           => draw(other, size, random)
