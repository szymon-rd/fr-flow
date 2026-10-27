package frflow.dsl.shape

import frflow.core.code.Code
import frflow.core.expr.{Binder, Lambda}
import frflow.core.name.{DefName, VarId}
import frflow.core.spec.Written
import frflow.core.term.{Body, Bound, Sym}
import frflow.dsl.build.Deferred
import frflow.dsl.term.{LeanType, Term}
import frflow.dsl.vocab.{Definition, OnTheSpot}

/** The shape of a define of type `F`: its lambda over its inputs' terms, the body on the inputs' variables (bound at
  * levels `0 … n-1` outside it: the written lambda, printed as its `def`), and the Definition it makes, carrying its
  * body, the same lambda in final form, one `lam` per input (LNCS 7470 §3.2), each interpreter giving its own
  * variables. One instance per arity.
  */
trait DefineShape[F]:
  type Lam <: AnyRef
  def types: List[LeanType[?]]
  def body(f: Lam, hints: List[String]): (List[Binder], Term[?])
  def made(name: DefName, f: Lam, hints: List[String], lambda: Deferred[Written[Lambda]]): Definition[F]

object DefineShape:
  given one[A, R](using a: LeanType[A], r: LeanType[R]): DefineShape[A => R] with
    type Lam = Term[A] => Term[R]
    val types: List[LeanType[?]] = List(a)
    def body(f: Lam, hints: List[String]): (List[Binder], Term[?]) =
      val x = binder(0, a, hints)
      (List(x), f(Term.free(x)))
    def made(name: DefName, f: Lam, hints: List[String], lambda: Deferred[Written[Lambda]]): Definition[A => R] =
      spot(name, lambda, Body(name, LeanType[A => R].ty,
        [T[_]] => (s: Sym[T]) => s.lam(bound(0, a, hints))(Term.body(s, f))))

  given two[A, B, R](using a: LeanType[A], b: LeanType[B], r: LeanType[R]): DefineShape[(A, B) => R] with
    type Lam = (Term[A], Term[B]) => Term[R]
    val types: List[LeanType[?]] = List(a, b)
    def body(f: Lam, hints: List[String]): (List[Binder], Term[?]) =
      val (x, y) = (binder(0, a, hints), binder(1, b, hints))
      (List(x, y), f(Term.free(x), Term.free(y)))
    def made(name: DefName, f: Lam, hints: List[String], lambda: Deferred[Written[Lambda]])
        : Definition[(A, B) => R] =
      spot(name, lambda, Body(name, LeanType[A => B => R].ty, [T[_]] => (s: Sym[T]) =>
        s.lam(bound(0, a, hints))(x => s.lam(bound(1, b, hints))(y => f(Term.bound(s, x), Term.bound(s, y)).run(s)))))
  // … for 0 to 6 inputs.

  /** A lambda's `i`th input as the IR binds it: level `i`, named as the developer named it. */
  def binder(i: Int, t: LeanType[?], hints: List[String]): Binder = Binder(VarId.level(i), hint(i, hints), t.ty)

  private def spot[F: LeanType](name: DefName, lambda: Deferred[Written[Lambda]], b: Body[?]): Definition[F] =
    Definition.onTheSpot(OnTheSpot(name, Code.Proven(name), lambda, Some(b)))

  private def bound[A](i: Int, t: LeanType[A], hints: List[String]): Bound[A] = Bound(hint(i, hints), t.ty)
  private def hint(i: Int, hints: List[String]): String = hints.lift(i).getOrElse("x")
