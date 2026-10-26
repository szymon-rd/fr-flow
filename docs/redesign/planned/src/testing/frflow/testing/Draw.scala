package frflow.testing

import frflow.core.example.Gen

/** The interpreter of `Gen`: a value drawn at a size from a random stream. Law-tested as a monad. */
trait Draw:
  def apply[A](g: Gen[A], size: Int, random: java.util.SplittableRandom): A
