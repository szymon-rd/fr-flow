package frflow.testing

import cats.kernel.Eq
import cats.laws.discipline.MonadTests
import cats.syntax.all.*
import frflow.core.example.Gen
import frflow.core.ty.{NumKind, Ty}
import frflow.testing.derive.Derive
import java.util.SplittableRandom
import org.scalacheck.{Arbitrary, Gen as SGen}

/** `Gen` is a monad, its laws checked on what `Draw` makes (the derived generators) for fixed seeds and sizes: two
  * generators are equal when they draw the same values from the same streams.
  */
class GenLawsSuite extends munit.DisciplineSuite:
  private val draw: Draw = Derive.of(Shelf.kb.elaborated.fold(es => throw AssertionError(es.toString), identity), Nil)
  private def samples[A](g: Gen[A]): List[Option[A]] =
    (0 until 24).toList.map(i => draw(g, 1 + i % 5, SplittableRandom(i.toLong)))

  private given [A]: Eq[Gen[A]] = Eq.instance((a, b) => samples(a) == samples(b))

  private val ints: Gen[Int] = Gen.Derived[Int](Ty.Num(NumKind.Int32))
  private def leaves[A](a: Arbitrary[A]): SGen[Gen[A]] = SGen.oneOf(
    a.arbitrary.map(Gen.Const(_)),
    SGen.zip(a.arbitrary, a.arbitrary).map((x, y) => Gen.oneOf(x, y)),
    a.arbitrary.map(x => Gen.Const(x).describedAs("one value")))

  private given [A](using a: Arbitrary[A]): Arbitrary[Gen[A]] = Arbitrary(SGen.oneOf(leaves(a),
    Arbitrary.arbitrary[Int => A].map(f => (ints: Gen[Int]).map(f)),
    leaves(a).map(g => g.flatMap(x => ints.as(x)))))

  checkAll("Gen", MonadTests[Gen].monad[Int, Int, String])

  test("describedAs changes what a generator says, not what it makes") {
    val g = ints.flatMap(n => Gen.oneOf(n, n + 1))
    assertEquals(samples(g.describedAs("near a number")), samples(g))
  }

  test("a run is a function of its seed: the same stream draws the same value, others others") {
    val g = Gen.Derived[List[Shelf.Book]](frflow.LeanType[List[Shelf.Book]].ty)
    assertEquals(samples(g), samples(g))
    assert(samples(g).distinct.size > 12)
  }
