package examples

import frflow.*

/** Words today's examples use that the term language has no operation for, written as folds over the ones it has:
  * a list's images, its first element meeting a rule, whether it holds a value, its elements' lists joined; an option empty or meeting a rule,
  * holding one meeting it, holding one at all. Each prints as its fold in Lean.
  */
object Folds:
  extension [A: LeanType](xs: Term[List[A]])
    /** Each element's image, in order (`List.map`). */
    def mapped[B: LeanType](f: Term[A] => Term[B]): Term[List[B]] =
      xs.foldLeft(Nil: Term[List[B]])((acc, x) => acc :+ f(x))
    /** The first element meeting `p`, if any (`List.find?`). */
    def firstWhere(p: Term[A] => Term[Boolean]): Term[Option[A]] =
      xs.foldLeft(none[A])((found, x) => found.fold(when(p(x))(some(x)).otherwise(none[A]))(f => some(f)))
    /** Whether `x` is an element (`List.elem`). */
    def contains(x: Term[A]): Term[Boolean] = xs.exists(y => y === x)
    /** Each element's list, joined in order (`List.flatMap`). */
    def flatMapped[B: LeanType](f: Term[A] => Term[List[B]]): Term[List[B]] =
      xs.foldLeft(Nil: Term[List[B]])((acc, x) => acc ++ f(x))

  /** The list of one element. */
  def one[A: LeanType](x: Term[A]): Term[List[A]] = x :: (Nil: Term[List[A]])

  extension [A](xs: Term[List[A]]) def isEmpty: Term[Boolean] = xs.length === 0

  extension [A: LeanType](o: Term[Option[A]])
    /** None, or one meeting `p` (`Option.all`). */
    def noneOr(p: Term[A] => Term[Boolean]): Term[Boolean] = o.fold(True)(p)
    /** One meeting `p` (`Option.any`). */
    def someWith(p: Term[A] => Term[Boolean]): Term[Boolean] = o.fold(False)(p)
    def isDefined: Term[Boolean] = o.fold(False)(_ => True)
