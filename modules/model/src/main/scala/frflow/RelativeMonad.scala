package frflow

/** A monad relative to `J` (Altenkirch, Chapman and Uustalu, "Monads Need Not Be Endofunctors"): `pure` and
  * `flatMap` go through `J` rather than the identity. `Flow` is one relative to `Term`: its steps bind symbolic
  * values, so a program can be printed as Lean as well as run.
  *
  * The laws, for every `a`, `m`, `f` and `g`:
  *   - left unit: `pure(a).flatMap(f)` ≡ `f(a)`;
  *   - right unit: `m.flatMap(pure)` ≡ `m`;
  *   - associativity: `m.flatMap(f).flatMap(g)` ≡ `m.flatMap(a => f(a).flatMap(g))`.
  * A flow is syntax (a free relative monad): ≡ is equality of what the two give when interpreted, in Lean's `do`
  * (in any lawful monad, `StateM` for the proofs) and at run time (in any lawful `cats.Monad`), not of the trees.
  * Cats' combinators follow from `pure`, `flatMap` and `map`, with Cats' names.
  */
trait RelativeMonad[F[_], J[_]]:
  def pure[A](a: J[A]): F[A]
  def flatMap[A, B](fa: F[A])(f: J[A] => F[B]): F[B]
  /** `flatMap(fa)(a => pure(f(a)))`; an instance may build it directly (Flow does, to name the bound value). */
  def map[A, B](fa: F[A])(f: J[A] => J[B]): F[B] = flatMap(fa)(a => pure(f(a)))
  /** `J`'s value of `Unit`, and its pairs: what `void` and `product` need. */
  def unitValue: J[Unit]
  def pair[A, B](a: J[A], b: J[B]): J[(A, B)]

  extension [A](fa: F[A])
    /** The result replaced by `b` (Functor's `as`). */
    def as[B](b: J[B]): F[B] = map(fa)(_ => b)
    /** The result discarded (Functor's `void`). */
    def void: F[Unit] = as(unitValue)
    /** Both results, this one's first (Apply's `product`). */
    def product[B](fb: F[B]): F[(A, B)] = flatMap(fa)(a => map(fb)(b => pair(a, b)))
    /** This, then `fb`, keeping `fb`'s result (Apply's `productR`). */
    def *>[B](fb: F[B]): F[B] = flatMap(fa)(_ => fb)
    /** This, then `fb`, keeping this one's result (Apply's `productL`). */
    def <*[B](fb: F[B]): F[A] = flatMap(fa)(a => map(fb)(_ => a))
    /** This, then `f` of its result, keeping this one's result (FlatMap's `flatTap`). */
    def flatTap[B](f: J[A] => F[B]): F[A] = flatMap(fa)(a => map(f(a))(_ => a))

  extension [A, B](p: (F[A], F[B]))
    /** Both, in order (Semigroupal's `tupled`). */
    def tupled: F[(A, B)] = p._1.product(p._2)

object RelativeMonad:
  def apply[F[_], J[_]](using m: RelativeMonad[F, J]): RelativeMonad[F, J] = m

  /** Two programs a law says are the same once interpreted (cats-laws' `IsEq`). */
  final case class IsEq[A](lhs: A, rhs: A)

  /** The laws, each as the pair of programs it equates: an interpretation is lawful when it gives the same of both. */
  final class Laws[F[_], J[_]](using M: RelativeMonad[F, J]):
    def leftUnit[A, B](a: J[A], f: J[A] => F[B]): IsEq[F[B]] = IsEq(M.flatMap(M.pure(a))(f), f(a))
    def rightUnit[A](m: F[A]): IsEq[F[A]] = IsEq(M.flatMap(m)(a => M.pure(a)), m)
    def associativity[A, B, C](m: F[A], f: J[A] => F[B], g: J[B] => F[C]): IsEq[F[C]] =
      IsEq(M.flatMap(M.flatMap(m)(f))(g), M.flatMap(m)(a => M.flatMap(f(a))(g)))
