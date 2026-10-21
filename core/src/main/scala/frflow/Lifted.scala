package frflow

/** A Lean declaration of a domain type, produced from a Scala case class or enum. */
final case class TypeDecl(name: String, lean: String, uses: List[String])

/** A Scala lambda (or value) together with its Lean translation.
  *
  * `value` is the compiled Scala code; `lean` is the same code as a Lean term.
  * Both come from one source expression.
  *
  * @param params Lean names and types of the lambda's parameters
  * @param result Lean type of the result
  * @param types  domain types the expression refers to
  * @param defs   theory functions the expression calls
  */
final class Lifted[+F](
    val value: F,
    val params: List[(String, String)],
    val result: String,
    val body: String,
    val source: String,
    val types: List[TypeDecl],
    defsThunk: () => List[Def[?]]
):
  def defs: List[Def[?]] = defsThunk()

  /** The Lean lambda. */
  def lean: String =
    if params.isEmpty then body
    else s"fun ${params.map((n, t) => s"($n : $t)").mkString(" ")} => $body"

  /** The Lean type of the lambda. */
  def leanType: String = (params.map(_._2) :+ result).mkString(" → ")

object Lifted:
  /** Translates a Scala lambda over domain ADTs. Unsupported Scala is a compile error. */
  inline def apply[F](inline f: F): Lifted[F] = ${ Lift.lifted('f) }

/** A named function of the theory, defined once in Scala and translated to Lean.
  * It can be called from other definitions and from node predicates, and runs as Scala.
  *
  * {{{
  * val total: Def[List[Entry] => Int] = define { (l: List[Entry]) => ... }
  * }}}
  */
final class Def[F](val name: String, val lifted: Lifted[F]):
  def fn: F = lifted.value
  def lean: String = s"@[frflow_defs] def $name : ${lifted.leanType} :=\n  ${lifted.lean}"

/** Defines a theory function. Its Lean name is the name of the `val` it is assigned to. */
inline def define[F](inline f: F): Def[F] = ${ Lift.define('f) }

extension [A, R](d: Def[A => R]) def apply(a: A): R = d.fn(a)
extension [A, B, R](d: Def[(A, B) => R]) def apply(a: A, b: B): R = d.fn(a, b)
extension [A, B, C, R](d: Def[(A, B, C) => R]) def apply(a: A, b: B, c: C): R = d.fn(a, b, c)

/** Raised when specification-only logic is executed. */
final class NotExecutable(what: String) extends RuntimeException(s"$what cannot be executed")

/** For every value of type `A` (specification only). */
def forall[A](p: A => Boolean): Boolean = throw NotExecutable("forall")

/** For some value of type `A` (specification only). */
def exists[A](p: A => Boolean): Boolean = throw NotExecutable("exists")

extension (a: Boolean)
  /** Implication. */
  infix def ==>(b: => Boolean): Boolean = !a || b
