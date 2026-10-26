package frflow.testing

import frflow.core.example.Gen
import frflow.core.vocab.BoundarySig
import frflow.eval.ScalaValue
import java.util.SplittableRandom

/** Generated runs of a boundary's operations: each call one of its signature's operations, each argument drawn by
  * its type (`Draw`; through `Respecting`, meeting what always holds of its type).
  */
final class Runs(draw: Draw):
  /** A run of 1 to `size` calls. */
  def of(sig: BoundarySig, size: Int, random: SplittableRandom): List[Step] =
    List.fill(1 + random.nextInt(size)) {
      val op = sig.ops(random.nextInt(sig.ops.size))
      Step(sig.name, op.name, op.params.map((_, ty) => ScalaValue(draw(Gen.Derived[Any](ty), size, random))))
    }
