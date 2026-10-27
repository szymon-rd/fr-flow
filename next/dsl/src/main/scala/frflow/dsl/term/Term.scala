package frflow.dsl.term

import frflow.core.expr.{Binder, Expr}
import frflow.core.term.{Constructor, Final, Selector, Sym}
import frflow.core.term.interpret.ToExpr
import frflow.dsl.build.{Failure, Fault}
import scala.annotation.implicitNotFound
import scala.util.NotGiven

/** A value of the domain as a model writes it: a term in final form over FrFlow's language (`run`, the same term for
  * every interpreter: LNCS 7470 §2.1), typed by Scala as `A`. The developer never sees the representation; `==` on
  * terms does not compile, `===` says the values are equal; `b.start` selects a field. Its notes are on the term
  * itself (`noted`), gathered when elaborated (`notes`).
  */
open class Term[A](val run: Final[A])(using val leanType: LeanType[A]) extends Selectable:
  type Fields = NamedTuple.Map[NamedTuple.From[A], Term]
  def selectDynamic(name: String): Any = Term.field(this, name)
  /** `==` on terms does not compile: Scala picks this overload (its owner is the more specific) and finds no
    * `NoEquality`, whose message says what to write. As today's `Term`.
    */
  def ==(that: Any)(using Term.NoEquality): Boolean = false
  def !=(that: Any)(using Term.NoEquality): Boolean = false

  def notes: Notes = Notes.in(this)
  /** Its initial form, for the analyses (`ToExpr`), its binders numbered from `depth`. */
  def expr: Expr = ToExpr.of(run)
  def exprAt(depth: Int): Expr = ToExpr.of(run, depth)

object Term:
  @implicitNotFound("FrFlow: compare terms with === (and =!=), not == (which compares Scala objects); " +
    "in plain code, compare values (`d.fn(…)`, `env(p)`)")
  sealed trait NoEquality

  /** The DSL's implicit conversions, all of them, where Scala finds them unimported (the target's companion): a
    * value where a term is expected is the constant (Booleans are written `True` and `False`), an `Int` literal a
    * `BigInt` term.
    */
  given value[A](using t: LeanType[A], notBoolean: NotGiven[A =:= Boolean]): Conversion[A, Term[A]] = Lift.constant(_)
  given int[A <: Int]: Conversion[A, Term[BigInt]] = i => Lift.constant(BigInt(i))

  /** A term noted with what it declares (or a fault): the note on the term itself, for `Notes.in`. */
  def noted[R: LeanType](n: Notes)(run: Final[R]): Term[R] = Term([T[_]] => (s: Sym[T]) => s.noted(n, run(s)))

  /** An operation of one or two terms, the operation on their runs, for every interpreter. */
  def one[A, R: LeanType](a: Term[A])(op: [T[_]] => Sym[T] => T[A] => T[R]): Term[R] =
    Term([T[_]] => (s: Sym[T]) => op[T](s)(a.run(s)))
  def both[A, B, R: LeanType](a: Term[A], b: Term[B])(op: [T[_]] => Sym[T] => (T[A], T[B]) => T[R]): Term[R] =
    Term([T[_]] => (s: Sym[T]) => op[T](s)(a.run(s), b.run(s)))

  /** A function term applied to one argument (a define's, a Definition's or a constructor's: `Functions.app`). */
  def app[A, B: LeanType](f: Term[A => B], a: Term[A]): Term[B] = both(f, a)([T[_]] => (s: Sym[T]) => s.app[A, B])

  /** A constructor as a function term, noting the type it makes. */
  def construct[F](c: Constructor[F])(using f: LeanType[F]): Term[F] =
    noted(Notes.of(f.declares))([T[_]] => (s: Sym[T]) => s.construct(c))

  /** A variable bound outside any term: a lambda's input as the IR binds it, a recorded program's step. */
  def free[A: LeanType](x: Binder): Term[A] = Term([T[_]] => (s: Sym[T]) => s.free[A](x))

  /** A body as interpreter `s` runs it: the user's function on `s`'s own variable. */
  def body[T[_], A: LeanType, B](s: Sym[T], f: Term[A] => Term[B]): T[A] => T[B] = v => f(bound(s, v)).run(s)

  /** The variable a binder gives its body, as the body's term. A body is a host function (higher-order abstract
    * syntax, LNCS 7470 §3.2) interpreted inside its binder by the interpreter that bound it, so the term is that
    * interpreter's value: the one cast of the term language, the price of `Term[A]` not naming its representation.
    * Run by any other interpreter, it fails at once (`outside`): only a FrFlow bug can reach that.
    */
  def bound[T[_], A](owner: Sym[T], x: T[A])(using LeanType[A]): Term[A] =
    Term([U[_]] => (s: Sym[U]) => if s eq owner then x.asInstanceOf[U[A]] else outside)

  private def outside: Nothing = throw IllegalStateException("FrFlow bug: a bound variable used outside its binder")

  private def field[A](t: Term[A], name: String): Term[?] =
    t.leanType.codeOnly.foreach(scala => throw Failure(Fault.CodeOnlyInStatement(scala)))
    t.leanType.fields.find(_.selector.name == name).fold(throw Failure(Fault.NoField(name)))(f => select(t, f))

  /** A record's field, as `b.start` reads it: typed by the field's own `LeanType`. */
  def select[R, F](t: Term[R], f: LeanType.Field[R, F]): Term[F] =
    Term([T[_]] => (s: Sym[T]) => s.field(t.run(s), f.selector))(using f.leanType)

  /** The record with one field replaced (`b.updated(_.start, t)`). */
  def copy[R, F](t: Term[R], s: Selector[R, F], v: Term[F]): Term[R] =
    Term([T[_]] => (sym: Sym[T]) => sym.copy(t.run(sym), s, v.run(sym)))(using t.leanType)
