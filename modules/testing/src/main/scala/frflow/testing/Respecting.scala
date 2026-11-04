package frflow.testing

import frflow.core.code.Values
import frflow.core.example.Gen
import frflow.eval.{Env, ScalaValue}
import frflow.eval.run.Made
import java.util.SplittableRandom

/** A `Draw` whose values meet what always holds of their types (`Made`, through every shape it reaches): a value
  * drawn by its type is drawn again until every `always[T]` holds of it, up to `tries` times. The derived generators
  * meet it already, value by value (`derive.Derive`); this keeps a hand-written draw to it.
  */
final class Respecting(draw: Draw, made: List[Made], tries: Int) extends Draw:
  def apply[A](g: Gen[A], size: Int, random: SplittableRandom): Option[A] = g match
    case Gen.Derived(ty) =>
      Iterator.continually(draw(g, size, random)).take(tries).flatten
        .find(a => made.forall(_.broken(List(ScalaValue(a)), List(ty), Env.of(Values.none)).isEmpty))
    case other           => draw(other, size, random)

  override def generators: List[report.Made] = draw.generators
  override def notes: List[report.Note] = draw.notes
