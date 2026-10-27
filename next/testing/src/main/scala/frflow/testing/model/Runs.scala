package frflow.testing.model

import frflow.core.vocab.BoundarySig
import frflow.eval.ScalaValue
import frflow.testing.Draw
import java.util.SplittableRandom

/** Generated runs of a boundary's operations: each call one of its signature's operations, the arguments of the
  * whole run drawn together by their types (`Draw`: meeting what always holds of each, and a room added often the
  * room asked about), kept as data.
  */
final class Runs(draw: Draw, typing: Typing):
  /** A run of 1 to `size` calls, if its arguments can be drawn. */
  def of(sig: BoundarySig, size: Int, random: SplittableRandom): Option[List[Step]] =
    Option.when(sig.ops.nonEmpty)(List.fill(1 + random.nextInt(size.max(1)))(sig.ops(random.nextInt(sig.ops.size))))
      .flatMap { ops =>
        draw.all(ops.flatMap(_.params.map(_._2)), size, random).map { args =>
          val (steps, _) = ops.foldLeft((List.empty[Step], args)) { case ((done, left), op) =>
            val (mine, rest) = left.splitAt(op.params.size)
            val values = mine.zip(op.params.map(_._2)).map((a, ty) => typing.reflect(ScalaValue(a), ty))
            (done :+ Step(sig.name, op.name, values), rest)
          }
          steps
        }
      }
