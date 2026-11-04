package frflow.core.example

import cats.data.NonEmptyList
import cats.{Monad, StackSafeMonad}
import frflow.core.ty.Ty

/** How to make values of `A` for the tests: data, interpreted by `testing.Draw` with a seed. A monad, its laws
  * checked on what `Draw` makes for fixed seeds; `Described` changes what it says, not what it makes.
  */
enum Gen[A]:
  /** Every value of the type, as `testing.Derive` makes them (seeded by the examples' values). */
  case Derived(ty: Ty)
  case Const(value: A)
  case OneOf(values: NonEmptyList[A])
  case Bind[X, B](first: Gen[X], next: X => Gen[B]) extends Gen[B]
  case Described(gen: Gen[A], says: String)

  def describedAs(says: String): Gen[A] = Described(this, says)

object Gen:
  def oneOf[A](a: A, more: A*): Gen[A] = OneOf(NonEmptyList(a, more.toList))

  given Monad[Gen] = new StackSafeMonad[Gen]:
    def pure[A](a: A): Gen[A] = Const(a)
    def flatMap[A, B](g: Gen[A])(f: A => Gen[B]): Gen[B] = Bind(g, f)
