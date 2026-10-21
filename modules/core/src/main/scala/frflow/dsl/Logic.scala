package frflow.dsl

/** Specification-only logic. These functions have a meaning in the generated
  * Lean (quantifiers over a type) but cannot be executed: calling one at run time
  * throws. They are rejected in implementation layers.
  */
final class NotExecutable(what: String)
    extends RuntimeException(s"$what is a specification construct and cannot be executed")

/** For every value of type `A`. */
def forall[A](p: A => Boolean): Boolean = throw NotExecutable("forall")

/** For all values of types `A` and `B`. */
def forall[A, B](p: (A, B) => Boolean): Boolean = throw NotExecutable("forall")

/** For all values of types `A`, `B` and `C`. */
def forall[A, B, C](p: (A, B, C) => Boolean): Boolean = throw NotExecutable("forall")

/** For some value of type `A`. */
def exists[A](p: A => Boolean): Boolean = throw NotExecutable("exists")

/** For some values of types `A` and `B`. */
def exists[A, B](p: (A, B) => Boolean): Boolean = throw NotExecutable("exists")

extension (a: Boolean)
  /** Implication. Executable. */
  infix def ==>(b: => Boolean): Boolean = !a || b
