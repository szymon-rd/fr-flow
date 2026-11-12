package frflow.testing.derive

import cats.syntax.all.*
import frflow.core.code.Values
import frflow.core.Elaborated
import frflow.core.example.{Example, Gen}
import frflow.core.expr.Value
import frflow.core.ty.Ty
import frflow.core.vocab.Vocabulary
import frflow.eval.{Env, ScalaValue}
import frflow.eval.run.Made
import frflow.eval.term.Semantics
import frflow.testing.derive.Draw
import frflow.testing.report
import frflow.testing.report.Seed
import java.util.SplittableRandom

/** The derived generators (`Gen.Derived(ty)`, what `kb.withGenerator` does not give), and the interpreter of the rest
  * of `Gen`. A value is drawn by its type through the vocabulary: numbers small and near the examples', short strings,
  * lists fewer the deeper, each constructor of a record or an enum; a type with a generator given is drawn from it
  * three times in four. Every value drawn, an example's among them, meets each `always[T]` of every `T` it holds
  * (`Drawing`), so a test never starts from a value the covered code cannot make. Values of one type recur within a
  * case (`Pool`). Pure given where its stream starts (the first number of `random`).
  */
final class Derive(val semantics: Semantics, val vocabulary: Vocabulary, val made: List[Made], hints: Hints)
    extends Draw:
  def generatorFor(ty: Ty): Option[Gen[?]] = hints.generatorFor(ty)

  /** The examples' values that meet what always holds of every type they hold: the others are never drawn. */
  val seeds: Seeds = hints.seeds.keeping(meets)

  /** Whether `v` meets each `always[T]` of every `T` it holds. */
  def meets(v: Value, ty: Ty): Boolean =
    made.forall(_.broken(List(semantics.literal(v, ty)), List(ty), Env.of(Values.none)).isEmpty)

  def apply[A](g: Gen[A], size: Int, random: SplittableRandom): Option[A] =
    Rolls.run(Drawing(this, size).gen(g), start(random)).map(_._2)

  override def all(types: List[Ty], size: Int, random: SplittableRandom): Option[List[Any]] =
    values(types, size, random).map(_.zip(types).map((v, ty) => semantics.literal(v, ty).unwrap))

  /** A value of each type as data, drawn together. */
  def values(types: List[Ty], size: Int, random: SplittableRandom): Option[List[Value]] =
    val drawing = Drawing(this, size)
    Rolls.run(types.traverse(drawing.value(_, 0)), start(random)).map(_._2)

  /** The values of `ty` the first `n` cases from `seed` draw, each once, as the witness search tries them first
    * (`search.Witnesses`).
    */
  def samples(ty: Ty, seed: Seed, n: Int): List[Value] =
    (0 until n).toList.flatMap(i => values(List(ty), Seed.sizeOf(i, n), seed.forCase(i)).toList.flatten).distinct

  override def generators: List[report.Made] = hints.generators.map(g => report.Made(g.ty, g.gen match
    case Gen.Described(_, says) => Some(says)
    case _                      => None))

  /** Each generator given, then the examples' values of its type it never makes in `NeverMadeTries` draws, which
    * are drawn anyway as seeds.
    */
  override def notes: List[report.Note] =
    generators.map(report.Note.Given(_)) ++ hints.generators.flatMap { g =>
      val made = (0 until Derive.NeverMadeTries).toList.flatMap(i =>
        apply(g.gen, Seed.sizeOf(i, Derive.NeverMadeTries), Seed(7).forCase(i)))
          .map(x => semantics.reflect(ScalaValue(x), g.ty)).toSet
      Option(seeds.of(g.ty).filterNot(made).toList).filter(_.nonEmpty).map(report.Note.NeverMade(g.ty, _))
    }

  private def start(random: SplittableRandom): Draws = Draws(Pool.empty, Stream(random.nextLong()))

object Derive:
  /** How many times a value is drawn again before none is found meeting what always holds of its type. */
  val Tries: Int = 50
  /** How many values a given generator is drawn for, to say which of the examples' values it never makes. */
  val NeverMadeTries: Int = 200

  /** The derived generators of an elaborated FrModel, seeded by its examples. */
  def of(e: Elaborated, examples: List[Example]): Derive =
    val semantics = Semantics(e)
    Derive(semantics, e.theory.vocabulary, Made.of(semantics, e.theory),
      Hints(e.generators, Seeds.of(e.theory.vocabulary, examples)))
