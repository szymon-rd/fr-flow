package frflow
package term

/** `forall` and `exists`, over one to six variables (re-exported by `frflow`). */
object Quantifiers:
  /** `x` stands for any value: specification only (Lean proves it, Scala cannot run it). */
  def forall[A](p: Term[A] => Term[Boolean])(using a: LeanType[A]): Term[Boolean] = Term.quant(all = true, p, List(a))
  def forall[A, B](p: (Term[A], Term[B]) => Term[Boolean])(using a: LeanType[A], b: LeanType[B]): Term[Boolean] = Term.quant(all = true, p, List(a, b))
  def exists[A](p: Term[A] => Term[Boolean])(using a: LeanType[A]): Term[Boolean] = Term.quant(all = false, p, List(a))
  def exists[A, B](p: (Term[A], Term[B]) => Term[Boolean])(using a: LeanType[A], b: LeanType[B]): Term[Boolean] = Term.quant(all = false, p, List(a, b))
  def forall[A, B, C](p: (Term[A], Term[B], Term[C]) => Term[Boolean])(using a: LeanType[A], b: LeanType[B], c: LeanType[C]): Term[Boolean] =
    Term.quant(all = true, p, List(a, b, c))
  def exists[A, B, C](p: (Term[A], Term[B], Term[C]) => Term[Boolean])(using a: LeanType[A], b: LeanType[B], c: LeanType[C]): Term[Boolean] =
    Term.quant(all = false, p, List(a, b, c))
  def forall[A, B, C, D](p: (Term[A], Term[B], Term[C], Term[D]) => Term[Boolean])(using a: LeanType[A], b: LeanType[B], c: LeanType[C],
      d: LeanType[D]): Term[Boolean] = Term.quant(all = true, p, List(a, b, c, d))
  def exists[A, B, C, D](p: (Term[A], Term[B], Term[C], Term[D]) => Term[Boolean])(using a: LeanType[A], b: LeanType[B], c: LeanType[C],
      d: LeanType[D]): Term[Boolean] = Term.quant(all = false, p, List(a, b, c, d))
  def forall[A, B, C, D, E](p: (Term[A], Term[B], Term[C], Term[D], Term[E]) => Term[Boolean])(using a: LeanType[A], b: LeanType[B],
      c: LeanType[C], d: LeanType[D], e: LeanType[E]): Term[Boolean] = Term.quant(all = true, p, List(a, b, c, d, e))
  def exists[A, B, C, D, E](p: (Term[A], Term[B], Term[C], Term[D], Term[E]) => Term[Boolean])(using a: LeanType[A], b: LeanType[B],
      c: LeanType[C], d: LeanType[D], e: LeanType[E]): Term[Boolean] = Term.quant(all = false, p, List(a, b, c, d, e))
  def forall[A, B, C, D, E, F](p: (Term[A], Term[B], Term[C], Term[D], Term[E], Term[F]) => Term[Boolean])(using a: LeanType[A],
      b: LeanType[B], c: LeanType[C], d: LeanType[D], e: LeanType[E], f: LeanType[F]): Term[Boolean] =
    Term.quant(all = true, p, List(a, b, c, d, e, f))
  def exists[A, B, C, D, E, F](p: (Term[A], Term[B], Term[C], Term[D], Term[E], Term[F]) => Term[Boolean])(using a: LeanType[A],
      b: LeanType[B], c: LeanType[C], d: LeanType[D], e: LeanType[E], f: LeanType[F]): Term[Boolean] =
    Term.quant(all = false, p, List(a, b, c, d, e, f))
