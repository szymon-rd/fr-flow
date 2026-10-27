package frflow.testing.derive

import cats.syntax.all.*
import frflow.core.Elaborated
import frflow.core.example.{Example, Gen}
import frflow.core.expr.Value
import frflow.core.ty.Ty
import frflow.core.vocab.Vocabulary
import frflow.eval.Semantics
import frflow.eval.run.Made
import frflow.testing.Draw
import frflow.testing.report
import java.util.SplittableRandom

/** The derived generators (`Gen.Derived(ty)`, what `kb.generating` does not give), and the interpreter of the rest of
  * `Gen`. A value is drawn by its type through the vocabulary: numbers small and near the examples', short strings,
  * lists fewer the deeper, each constructor of a record or an enum; a type with a generator given is drawn from it
  * three times in four. Every value drawn meets each `always[T]` of every `T` it holds (`Drawing`), so a test never
  * starts from a value the covered code cannot make. Values of one type recur within a case (`Pool`). Pure given its
  * random stream.
  */
final class Derive(val semantics: Semantics, val vocabulary: Vocabulary, val rules: List[Made], hints: Hints)
    extends Draw:
  def generatorFor(ty: Ty): Option[Gen[?]] = hints.generatorFor(ty)
  def seeds: Seeds = hints.seeds

  def apply[A](g: Gen[A], size: Int, random: SplittableRandom): Option[A] =
    Drawing(this, random, size).gen(g).runA(Pool.empty)

  override def all(types: List[Ty], size: Int, random: SplittableRandom): Option[List[Any]] =
    values(types, size, random).map(_.zip(types).map((v, ty) => semantics.literal(v, ty).unwrap))

  /** A value of each type as data, drawn together. */
  def values(types: List[Ty], size: Int, random: SplittableRandom): Option[List[Value]] =
    val drawing = Drawing(this, random, size)
    types.traverse(drawing.value(_, 0)).runA(Pool.empty)

  override def generators: List[report.Made] = hints.generators.map(g => report.Made(g.ty, g.gen match
    case Gen.Described(_, says) => Some(says)
    case _                      => None))

object Derive:
  /** How many times a value is drawn again before none is found meeting what always holds of its type. */
  val Tries: Int = 50

  /** The derived generators of an elaborated knowledge base, seeded by its examples. */
  def of(e: Elaborated, examples: List[Example]): Derive =
    val semantics = Semantics(e)
    Derive(semantics, e.theory.vocabulary, Made.of(semantics, e.theory),
      Hints(e.generators, Seeds.of(e.theory.vocabulary, examples)))
