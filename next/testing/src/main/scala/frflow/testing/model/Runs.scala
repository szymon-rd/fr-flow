package frflow.testing.model

import frflow.core.vocab.StateModel
import frflow.eval.ScalaValue
import frflow.testing.Draw
import java.util.SplittableRandom

/** Generated runs of a model's operations: each call one of its operations, the arguments of the whole run drawn
  * together by their types (`Draw`: meeting what always holds of each, and a room added often the room asked about),
  * kept as data.
  */
final class Runs(draw: Draw, typing: Typing):
  /** A run of 1 to `size` calls, if its arguments can be drawn. */
  def of(model: StateModel, size: Int, random: SplittableRandom): Option[List[Step]] =
    val ops = model.sigs
    Option.when(ops.nonEmpty)(List.fill(1 + random.nextInt(size.max(1)))(ops(random.nextInt(ops.size))))
      .flatMap { chosen =>
        draw.all(chosen.flatMap(_.params.map(_._2)), size, random).map { args =>
          val (steps, _) = chosen.foldLeft((List.empty[Step], args)) { case ((done, left), op) =>
            val (mine, rest) = left.splitAt(op.params.size)
            val values = mine.zip(op.params.map(_._2)).map((a, ty) => typing.reflect(ScalaValue(a), ty))
            (done :+ Step(op.name, values), rest)
          }
          steps
        }
      }
