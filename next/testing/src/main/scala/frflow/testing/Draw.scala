package frflow.testing

import cats.syntax.all.*
import frflow.core.example.Gen
import frflow.core.ty.Ty
import frflow.testing.report.{Made, Note}
import java.util.SplittableRandom

/** The interpreter of `Gen`: a value drawn at a size from a random stream, or none when the type has no value to
  * draw (an opaque type, a function, a world) or no draw met what always holds of it. Law-tested as a monad: the
  * same seed and size give the same value.
  */
trait Draw:
  def apply[A](g: Gen[A], size: Int, random: SplittableRandom): Option[A]

  /** A value of each type, drawn together, as one case draws its inputs and the values its code is given: a value
    * of one type may recur among them (a booking's room as the room asked about).
    */
  def all(types: List[Ty], size: Int, random: SplittableRandom): Option[List[Any]] =
    types.traverse(ty => apply(Gen.Derived[Any](ty), size, random))

  /** The generators given for the tests, each type with what the developer said it makes. */
  def generators: List[Made] = Nil

  /** What a report says of the generators: each one given, and the examples' values one never makes. */
  def notes: List[Note] = generators.map(Note.Given(_))
