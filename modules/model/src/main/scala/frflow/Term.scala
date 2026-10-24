package frflow

import scala.annotation.{implicitNotFound, targetName}
import scala.compiletime.{constValue, constValueTuple}
import scala.deriving.Mirror
import scala.util.NotGiven

/** A value of the domain as FrFlow sees it: a tree that prints as Lean and compiles to Scala. Models and `define`s
  * are written with terms: `s.records` (a field), `CrmStore(a, b, c)` (with `object CrmStore extends Data[CrmStore]`),
  * `x === y`, `xs.filter(r => …)`, `forall((u: Term[User.T]) => …)`, `If(c)(a).Else(b)`, `q.on[Search.ById](id => …)`.
  */
class Term[A] private[frflow] (tree: Tree | Null, private[frflow] val termType: LeanType[A]) extends Selectable:
  type Fields = NamedTuple.Map[NamedTuple.From[A], Term]
  private[frflow] def termTree: Tree = tree.nn
  def selectDynamic(name: String): Any = Term.select(this, name)
  /** Scala's `==` would compare the tree with whatever is on the right (always false for a value): `===` says the values
    * are equal.
    */
  def ==(that: Any)(using NoEquality): Boolean = false
  def !=(that: Any)(using NoEquality): Boolean = false
  override def toString: String = s"Term($termTree)"

@implicitNotFound("FrFlow: compare terms with === (and =!=), not == (which compares the trees); in plain code, compare values (`d.fn(…)`, `p.value`)")
sealed trait NoEquality


/** A variable bound by a lambda: `hint` is the name the Scala lambda gave it (`_$1` for a wildcard). */
private[frflow] final class Binder(val hint: String, val tpe: LeanType[?]):
  /** `_` in a lambda, or `_ <-` in a for-comprehension (Scala names it `x$1`). */
  def wildcard: Boolean = hint.startsWith("_$") || hint.matches("x\\$\\d+")
  def term[A]: Term[A] = Term(Tree.Var(this), tpe.asInstanceOf[LeanType[A]])

private[frflow] enum Iter:
  case All, Some, Filter, FilterNot, Find, OptAll, OptSome

/** An operator: how it prints and runs is in `LeanPrinter` and `Eval`. */
private[frflow] enum Prim:
  case Eq, Ne, And, Or, Not, Implies
  case Add, Sub, Mul, Div, Mod, Lt, Le, Gt, Ge, Max, Min, Neg, Concat
  case Cons, Append, Contains, IsEmpty, NonEmpty, Length, MapL, FoldLeft, FlatMap, HeadOption, ToSet, Take, Drop, Zip
  case Get, HasKey, GetOrElse, Updated, Removed
  case SetHas, Incl, Excl, Union, Intersect, SubsetOf
  case OptContains, IsDefined, OptIsEmpty, OptGetOrElse

private[frflow] enum Pat:
  /** A case class or an enum case, its fields bound (a wildcard binds none). */
  case Ctor(adt: Adt, ctor: frflow.Ctor, binders: List[Binder])
  case SomeP(b: Binder)
  case NoneP
  case ConsP(h: Binder, t: Binder)
  case NilP

private[frflow] final case class Arm(pat: Pat, body: Tree, tpe: LeanType[?])

private[frflow] enum Tree:
  case Var(b: Binder)
  case Lit(v: Any, t: LeanType[?])
  case Ref(p: Param[?])
  case Call(d: Def[?], args: List[Tree])
  case Apply(f: Tree, args: List[Tree])
  case Fun(bs: List[Binder], body: Tree)
  case Quant(all: Boolean, bs: List[Binder], body: Tree)
  case If(c: Tree, a: Tree, b: Tree)
  case Match(on: Tree, cases: List[Arm])
  case Let(b: Binder, v: Tree, body: Tree)
  case Field(on: Tree, adt: Adt, index: Int)
  case Copy(on: Tree, adt: Adt, updates: List[(Int, Tree)])
  case Make(adt: Adt, ctor: frflow.Ctor, args: List[Tree])
  case Tup(es: List[Tree])
  case Proj(on: Tree, i: Int, n: Int)
  case SomeT(a: Tree)
  case ListT(es: List[Tree])
  case Over(kind: Iter, on: Tree, b: Binder, body: Tree)
  case Op(op: Prim, args: List[Tree])
  /** A flow's steps: the body of a `def` over a monad. */
  case Do(steps: Steps)
  /** A flow (a call of one) run on the models from a world: its result and the world after. */
  case RunOn(call: Tree, world: Tree)
  /** A model's state in a world. */
  case Part(world: Tree, model: StateModel[?])

/** The variables of a lambda over terms, named as the lambda names them, and its body. */
private[frflow] object Lambda:
  def binders(f: AnyRef, types: List[LeanType[?]]): List[Binder] =
    val hints = Lambdas.params(f)
    types.zipWithIndex.map((t, i) => Binder(hints.lift(i).getOrElse("x"), t))
  def body(f: AnyRef, bs: List[Binder]): Term[?] = Building {
    val ts = bs.map(_.term[Any])
    (f, ts) match
      case (g: Function0[?], Nil)                      => g().asInstanceOf[Term[?]]
      case (g: Function1[?, ?], List(a))               => g.asInstanceOf[Any => Term[?]](a)
      case (g: Function2[?, ?, ?], List(a, b))         => g.asInstanceOf[(Any, Any) => Term[?]](a, b)
      case (g: Function3[?, ?, ?, ?], List(a, b, c))   => g.asInstanceOf[(Any, Any, Any) => Term[?]](a, b, c)
      case (g: Function4[?, ?, ?, ?, ?], List(a, b, c, d)) => g.asInstanceOf[(Any, Any, Any, Any) => Term[?]](a, b, c, d)
      case (g: Function5[?, ?, ?, ?, ?, ?], List(a, b, c, d, e)) => g.asInstanceOf[(Any, Any, Any, Any, Any) => Term[?]](a, b, c, d, e)
      case _ => throw IllegalArgumentException(s"FrFlow: a lambda of ${bs.size} terms expected")
  }

/** The Lean of `t` alone: for tests and messages. */
def leanOf(t: Term[?]): String = LeanPrinter().expr(t.termTree)

/** `x` stands for any value: specification only (Lean proves it, Scala cannot run it). */
def forall[A](p: Term[A] => Term[Boolean])(using a: LeanType[A]): Term[Boolean] = Term.quant(all = true, p, List(a))
def forall[A, B](p: (Term[A], Term[B]) => Term[Boolean])(using a: LeanType[A], b: LeanType[B]): Term[Boolean] = Term.quant(all = true, p, List(a, b))
def exists[A](p: Term[A] => Term[Boolean])(using a: LeanType[A]): Term[Boolean] = Term.quant(all = false, p, List(a))
def exists[A, B](p: (Term[A], Term[B]) => Term[Boolean])(using a: LeanType[A], b: LeanType[B]): Term[Boolean] = Term.quant(all = false, p, List(a, b))

val True: Term[Boolean] = Term.lit(true)
val False: Term[Boolean] = Term.lit(false)
def some[A](a: Term[A]): Term[Option[A]] = Term(Tree.SomeT(a.termTree), LeanType.of(Shape.OptionOf(a.termType)))
def none[A](using a: LeanType[A]): Term[Option[A]] = Term(Tree.Lit(None, LeanType.of(Shape.OptionOf(a))), LeanType.of(Shape.OptionOf(a)))

/** `If(c)(a).Else(b)`: Lean's `if c then a else b`. */
def If[R](c: Term[Boolean])(a: Term[R]): Then[R] = Then(c, a)
/** `If(c)(a).Else(b)` on flows: the steps of one branch. */
def If[R](c: Term[Boolean])(a: Flow[R]): ThenFlow[R] = ThenFlow(c, a)
final class Then[R](c: Term[Boolean], a: Term[R]):
  def Else(b: Term[R]): Term[R] = Term(Tree.If(c.termTree, a.termTree, b.termTree), a.termType)

/** A shared value, named in Lean: `let(shelf.toSet)(there => picked.filter(b => there.contains(b)))`. */
def let[A, R](v: Term[A])(body: Term[A] => Term[R]): Term[R] =
  val b = Lambda.binders(body, List(v.termType)).head
  val r = body(b.term)
  Term(Tree.Let(b, v.termTree, r.termTree), r.termType)

/** Mixed into a case class's companion: `CrmStore(s.records, …)` builds a term, `CrmStore(…)` on values a value. */
trait Data[T]:
  import Tuple.Elem as E
  type F = NamedTuple.DropNames[NamedTuple.From[T]]
  private def make(t: LeanType[T], args: Term[?]*): Term[T] = Term.make(t, args.toList)
  def apply(a: Term[E[F, 0]])(using t: LeanType[T]): Term[T] = make(t, a)
  def apply(a: Term[E[F, 0]], b: Term[E[F, 1]])(using t: LeanType[T]): Term[T] = make(t, a, b)
  def apply(a: Term[E[F, 0]], b: Term[E[F, 1]], c: Term[E[F, 2]])(using t: LeanType[T]): Term[T] = make(t, a, b, c)
  def apply(a: Term[E[F, 0]], b: Term[E[F, 1]], c: Term[E[F, 2]], d: Term[E[F, 3]])(using t: LeanType[T]): Term[T] = make(t, a, b, c, d)
  def apply(a: Term[E[F, 0]], b: Term[E[F, 1]], c: Term[E[F, 2]], d: Term[E[F, 3]], e: Term[E[F, 4]])(using t: LeanType[T]): Term[T] =
    make(t, a, b, c, d, e)
  def apply(a: Term[E[F, 0]], b: Term[E[F, 1]], c: Term[E[F, 2]], d: Term[E[F, 3]], e: Term[E[F, 4]], f: Term[E[F, 5]])(using t: LeanType[T]): Term[T] =
    make(t, a, b, c, d, e, f)
  /** An enum's case built from terms, with `object Event extends Data[Event]`: `Event[Event.Wrote](w)`. (A case's
    * own companion cannot take terms: Scala gives it its `apply` and no way to add another.)
    */
  inline def apply[C <: T](using m: Mirror.ProductOf[C]): CaseOf[T, m.MirroredElemTypes] = CaseOf(constValue[m.MirroredLabel])

/** One case of an enum, given its fields as terms. */
final class CaseOf[T, F <: Tuple] @scala.annotation.publicInBinary private[frflow] (label: String):
  import Tuple.Elem as E
  private def make(t: LeanType[T], args: Term[?]*): Term[T] = Term.makeCase(t, label, args.toList)
  def apply(a: Term[E[F, 0]])(using t: LeanType[T]): Term[T] = make(t, a)
  def apply(a: Term[E[F, 0]], b: Term[E[F, 1]])(using t: LeanType[T]): Term[T] = make(t, a, b)
  def apply(a: Term[E[F, 0]], b: Term[E[F, 1]], c: Term[E[F, 2]])(using t: LeanType[T]): Term[T] = make(t, a, b, c)
  def apply(a: Term[E[F, 0]], b: Term[E[F, 1]], c: Term[E[F, 2]], d: Term[E[F, 3]])(using t: LeanType[T]): Term[T] = make(t, a, b, c, d)

/** The terms a case's lambda takes: one per field. */
type Fields[T <: Tuple, R] = T match
  case EmptyTuple => Term[R]
  case a *: EmptyTuple => Term[a] => Term[R]
  case (a, b) => (Term[a], Term[b]) => Term[R]
  case (a, b, c) => (Term[a], Term[b], Term[c]) => Term[R]
  case (a, b, c, d) => (Term[a], Term[b], Term[c], Term[d]) => Term[R]
  case (a, b, c, d, e) => (Term[a], Term[b], Term[c], Term[d], Term[e]) => Term[R]

/** The first case of a match, given its body (whose type is the match's): `.on[Search.ById](id => …)`,
  * `.on[Search.Everything.type](True)`, `.on[Some[UserId]](u => …)`, `.on[None.type](…)`.
  */
final class First[S, E <: Tuple] @scala.annotation.publicInBinary private[frflow] (scrutinee: Term[S], label: String):
  def apply[R](f: Fields[E, R]): Cases[S, R] = Cases(scrutinee, List(Term.caseOf(scrutinee, label, f.asInstanceOf[AnyRef])))

/** A further case of a match. */
final class On[S, E <: Tuple, R] @scala.annotation.publicInBinary private[frflow] (scrutinee: Term[S], before: List[Arm], label: String):
  def apply(f: Fields[E, R]): Cases[S, R] = Cases(scrutinee, before :+ Term.caseOf(scrutinee, label, f.asInstanceOf[AnyRef]))

/** A match so far: a term of its result, to which `on` adds a case. Lean refuses one that misses a case. */
final class Cases[S, R] private[frflow] (scrutinee: Term[S], cases: List[Arm])
    extends Term[R](Tree.Match(scrutinee.termTree, cases), cases.head.tpe.asInstanceOf[LeanType[R]]):
  inline def on[C <: S](using m: Mirror.ProductOf[C]): On[S, m.MirroredElemTypes, R] = On(scrutinee, cases, constValue[m.MirroredLabel])

/** Values holding terms (`List(a, b)`, `Some(u)`, `(a, b)`) are terms; a plain value (`Nil`, `None`) is one first. */
private[frflow] trait TermsOfValues:
  given someTerm[A]: Conversion[Some[Term[A]], Term[Option[A]]] = s => some(s.value)
  given listTerm[A](using a: LeanType[A]): Conversion[List[Term[A]], Term[List[A]]] =
    l => Term(Tree.ListT(l.map(_.termTree)), LeanType.of(Shape.ListOf(l.headOption.fold(a)(_.termType))))
  given pairTerm[A, B]: Conversion[(Term[A], Term[B]), Term[(A, B)]] = pair(_)
  given pairsTerm[A, B](using a: LeanType[A], b: LeanType[B]): Conversion[List[(Term[A], Term[B])], Term[List[(A, B)]]] =
    ps => Term(Tree.ListT(ps.map(pair(_).termTree)), LeanType.of(Shape.ListOf(LeanType.of(Shape.TupleOf(List(a, b))))))
  private def pair[A, B](p: (Term[A], Term[B])): Term[(A, B)] =
    Term(Tree.Tup(List(p._1.termTree, p._2.termTree)), LeanType.of(Shape.TupleOf(List(p._1.termType, p._2.termType))))

object Term extends TermsOfValues:
  private[frflow] def apply[A](t: Tree, tpe: LeanType[A]): Term[A] = new Term(t, tpe)
  private[frflow] def lit[A](v: A)(using t: LeanType[A]): Term[A] = Term(Tree.Lit(v, t), t)
  private def bool(t: Tree): Term[Boolean] = Term(t, summon[LeanType[Boolean]])
  private def op[A](p: Prim, t: LeanType[A], args: Term[?]*): Term[A] = Term(Tree.Op(p, args.toList.map(_.termTree)), t)
  private def opB(p: Prim, args: Term[?]*): Term[Boolean] = op(p, summon[LeanType[Boolean]], args*)

  /** Values are terms (Booleans are `True` and `False`: a Boolean where a term is expected is most often `==` misused). */
  given value[A](using t: LeanType[A], notBoolean: NotGiven[A =:= Boolean]): Conversion[A, Term[A]] = a => lit(a)
  /** `x + 1` with `x` a `Term[BigInt]`. */
  given int[A <: Int]: Conversion[A, Term[BigInt]] = i => lit(BigInt(i))

  private[frflow] def select(t: Term[?], name: String): Term[?] = t.termType.shape match
    case Shape.Data(adt) if !adt.isEnum =>
      val fs = adt.ctors.head.fields
      val i = fs.indexWhere(_._1 == name)
      if i < 0 then throw IllegalArgumentException(s"FrFlow: ${adt.scalaName} has no field $name")
      Term(Tree.Field(t.termTree, adt, i), fs(i)._2)
    case Shape.TupleOf(as) if name.startsWith("_") && name.drop(1).toIntOption.exists(k => k >= 1 && k <= as.size) =>
      val k = name.drop(1).toInt
      Term(Tree.Proj(t.termTree, k, as.size), as(k - 1))
    case _ => throw IllegalArgumentException(s"FrFlow: no field $name here")

  private[frflow] def make[T](t: LeanType[T], args: List[Term[?]]): Term[T] = t.shape match
    case Shape.Data(adt) if !adt.isEnum => Term(Tree.Make(adt, adt.ctors.head, args.map(_.termTree)), t)
    case _ => throw IllegalArgumentException("FrFlow: only a case class is built from its fields")

  private[frflow] def makeCase[T](t: LeanType[T], label: String, args: List[Term[?]]): Term[T] = t.shape match
    case Shape.Data(adt) if adt.isEnum => Term(Tree.Make(adt, adt.ctor(label), args.map(_.termTree)), t)
    case _ => throw IllegalArgumentException(s"FrFlow: $label is not a case of an enum")

  private[frflow] def quant(all: Boolean, p: AnyRef, types: List[LeanType[?]]): Term[Boolean] =
    val bs = Lambda.binders(p, types)
    bool(Tree.Quant(all, bs, Lambda.body(p, bs).termTree))

  private def over[A](kind: Iter, on: Term[?], elem: LeanType[?], p: Term[A] => Term[?]): (Binder, Tree) =
    val b = Lambda.binders(p, List(elem)).head
    (b, p(b.term).termTree)
  private def iter(kind: Iter, on: Term[?], elem: LeanType[?], p: Term[Any] => Term[Boolean]): Term[Boolean] =
    val (b, body) = over(kind, on, elem, p)
    bool(Tree.Over(kind, on.termTree, b, body))
  private def fun(f: AnyRef, types: List[LeanType[?]]): (Tree, LeanType[?]) =
    val bs = Lambda.binders(f, types)
    val body = Lambda.body(f, bs)
    (Tree.Fun(bs, body.termTree), body.termType)

  private def elem(t: Term[?]): LeanType[?] = t.termType.shape match
    case Shape.ListOf(a) => a
    case Shape.OptionOf(a) => a
    case Shape.SetOf(a) => a
    case _ => LeanType.unknown
  private def mapTypes(t: Term[?]): (LeanType[?], LeanType[?]) = t.termType.shape match
    case Shape.MapOf(k, v) => (k, v)
    case _ => (LeanType.unknown, LeanType.unknown)

  private[frflow] def caseOf(scrutinee: Term[?], label: String, f: AnyRef): Arm =
    def bound(types: List[LeanType[?]])(pat: List[Binder] => Pat): Arm =
      if types.isEmpty then
        val t = f.asInstanceOf[Term[?]]
        Arm(pat(Nil), t.termTree, t.termType)
      else
        val bs = Lambda.binders(f, types)
        val body = Lambda.body(f, bs)
        Arm(pat(bs), body.termTree, body.termType)
    scrutinee.termType.shape match
      case Shape.OptionOf(a) if label == "Some" => bound(List(a))(bs => Pat.SomeP(bs.head))
      case Shape.OptionOf(_) if label == "None" => bound(Nil)(_ => Pat.NoneP)
      case Shape.ListOf(a) if label == "::" => bound(List(a, scrutinee.termType))(bs => Pat.ConsP(bs(0), bs(1)))
      case Shape.ListOf(_) if label == "Nil" => bound(Nil)(_ => Pat.NilP)
      case Shape.Data(adt) =>
        val c = if adt.isEnum then adt.ctor(label) else adt.ctors.head
        bound(c.fields.map(_._2))(bs => Pat.Ctor(adt, c, bs))
      case _ => throw IllegalArgumentException(s"FrFlow: cannot match on case $label here")

  extension [S](s: Term[S])
    /** A case of a match on an enum, an Option or a List: the lambda takes the case's fields. */
    inline def on[C <: S](using m: Mirror.ProductOf[C]): First[S, m.MirroredElemTypes] = First(s, constValue[m.MirroredLabel])

  extension [A](a: Term[A])
    def ===(b: Term[A]): Term[Boolean] = opB(Prim.Eq, comparable(a), b)
    def =!=(b: Term[A]): Term[Boolean] = opB(Prim.Ne, comparable(a), b)
    /** The value with some fields changed: `a.copy((enabled = v))`. */
    inline def copy[N <: Tuple, V <: Tuple](changes: NamedTuple.NamedTuple[N, V]): Term[A] =
      copied(a, constValueTuple[N].toList.asInstanceOf[List[String]], changes.toTuple.productIterator.toList)

  /** Scala compares functions by reference, Lean by their values: an equality between two would mean one thing in each. */
  private def comparable[A](a: Term[A]): Term[A] = a.termType.shape match
    case Shape.FnOf(_, _) => throw IllegalArgumentException(
      "FrFlow: === or =!= between functions: Scala compares them by reference and Lean by their values; compare what they " +
        "give instead, as in forall((x: Term[X]) => f(x) === g(x))")
    case _ => a

  private[frflow] def copied[A](a: Term[A], labels: List[String], values: List[Any]): Term[A] = a.termType.shape match
    case Shape.Data(adt) if !adt.isEnum =>
      val fs = adt.ctors.head.fields
      val ups = labels.zip(values).map { (n, v) =>
        val i = fs.indexWhere(_._1 == n)
        if i < 0 then throw IllegalArgumentException(s"FrFlow: ${adt.scalaName} has no field $n")
        i -> (v match { case t: Term[?] => t.termTree; case x => Tree.Lit(x, fs(i)._2) })
      }
      Term(Tree.Copy(a.termTree, adt, ups.sortBy(_._1)), a.termType)
    case _ => throw IllegalArgumentException("FrFlow: only a case class is copied")

  extension (a: Term[Boolean])
    def &&(b: Term[Boolean]): Term[Boolean] = opB(Prim.And, a, b)
    def ||(b: Term[Boolean]): Term[Boolean] = opB(Prim.Or, a, b)
    def unary_! : Term[Boolean] = opB(Prim.Not, a)
    infix def ==>(b: Term[Boolean]): Term[Boolean] = opB(Prim.Implies, a, b)

  /** Int and Long compare, BigInt also computes: Scala's Int and Long wrap around, Lean's Int does not. */
  sealed trait Num[N]
  given Num[Int] = new Num[Int] {}
  given Num[Long] = new Num[Long] {}
  given Num[BigInt] = new Num[BigInt] {}

  extension [N: Num](a: Term[N])
    def <(b: Term[N]): Term[Boolean] = opB(Prim.Lt, a, b)
    def <=(b: Term[N]): Term[Boolean] = opB(Prim.Le, a, b)
    def >(b: Term[N]): Term[Boolean] = opB(Prim.Gt, a, b)
    def >=(b: Term[N]): Term[Boolean] = opB(Prim.Ge, a, b)
    def max(b: Term[N]): Term[N] = op(Prim.Max, a.termType, a, b)
    def min(b: Term[N]): Term[N] = op(Prim.Min, a.termType, a, b)

  extension (a: Term[BigInt])
    def +(b: Term[BigInt]): Term[BigInt] = op(Prim.Add, a.termType, a, b)
    def -(b: Term[BigInt]): Term[BigInt] = op(Prim.Sub, a.termType, a, b)
    def *(b: Term[BigInt]): Term[BigInt] = op(Prim.Mul, a.termType, a, b)
    def unary_- : Term[BigInt] = op(Prim.Neg, a.termType, a)
    /** By a number other than zero only: Lean divides by zero to 0, Scala throws. */
    def /(d: BigInt): Term[BigInt] = { nonZero(d); op(Prim.Div, a.termType, a, lit(d)) }
    def %(d: BigInt): Term[BigInt] = { nonZero(d); op(Prim.Mod, a.termType, a, lit(d)) }
  private def nonZero(d: BigInt): Unit =
    if d == 0 then throw IllegalArgumentException("FrFlow: `/` by zero: Lean gives 0, Scala throws")

  extension (a: Term[String])
    @targetName("concat") def +(b: Term[String]): Term[String] = op(Prim.Concat, a.termType, a, b)

  extension [A](x: Term[A])
    def ::(xs: Term[List[A]]): Term[List[A]] = op(Prim.Cons, xs.termType, x, xs)

  extension [A](xs: Term[List[A]])
    def ++(ys: Term[List[A]]): Term[List[A]] = op(Prim.Append, xs.termType, xs, ys)
    def contains(x: Term[A]): Term[Boolean] = opB(Prim.Contains, xs, x)
    def isEmpty: Term[Boolean] = opB(Prim.IsEmpty, xs)
    def nonEmpty: Term[Boolean] = opB(Prim.NonEmpty, xs)
    def length: Term[Int] = op(Prim.Length, summon[LeanType[Int]], xs)
    def size: Term[Int] = length
    def forall(p: Term[A] => Term[Boolean]): Term[Boolean] = iter(Iter.All, xs, elem(xs), p.asInstanceOf[Term[Any] => Term[Boolean]])
    def exists(p: Term[A] => Term[Boolean]): Term[Boolean] = iter(Iter.Some, xs, elem(xs), p.asInstanceOf[Term[Any] => Term[Boolean]])
    def filter(p: Term[A] => Term[Boolean]): Term[List[A]] =
      val (b, body) = over(Iter.Filter, xs, elem(xs), p)
      Term(Tree.Over(Iter.Filter, xs.termTree, b, body), xs.termType)
    def filterNot(p: Term[A] => Term[Boolean]): Term[List[A]] =
      val (b, body) = over(Iter.FilterNot, xs, elem(xs), p)
      Term(Tree.Over(Iter.FilterNot, xs.termTree, b, body), xs.termType)
    def find(p: Term[A] => Term[Boolean]): Term[Option[A]] =
      val (b, body) = over(Iter.Find, xs, elem(xs), p)
      Term(Tree.Over(Iter.Find, xs.termTree, b, body), LeanType.of(Shape.OptionOf(elem(xs))))
    def map[B](f: Term[A] => Term[B]): Term[List[B]] =
      val (t, r) = fun(f, List(elem(xs)))
      Term(Tree.Op(Prim.MapL, List(t, xs.termTree)), LeanType.of(Shape.ListOf(r)))
    def flatMap[B](f: Term[A] => Term[List[B]]): Term[List[B]] =
      val (t, r) = fun(f, List(elem(xs)))
      Term(Tree.Op(Prim.FlatMap, List(t, xs.termTree)), r.asInstanceOf[LeanType[List[B]]])
    def foldLeft[B](z: Term[B])(f: (Term[B], Term[A]) => Term[B]): Term[B] =
      val (t, _) = fun(f, List(z.termType, elem(xs)))
      Term(Tree.Op(Prim.FoldLeft, List(t, z.termTree, xs.termTree)), z.termType)
    def headOption: Term[Option[A]] = op(Prim.HeadOption, LeanType.of(Shape.OptionOf(elem(xs))), xs)
    def toSet: Term[Set[A]] = op(Prim.ToSet, LeanType.of(Shape.SetOf(elem(xs))), xs)
    def take(n: Term[Int]): Term[List[A]] = op(Prim.Take, xs.termType, n, xs)
    def drop(n: Term[Int]): Term[List[A]] = op(Prim.Drop, xs.termType, n, xs)
    /** Each element in turn, as Cats' `traverse_`: Lean's `for x in xs do`. */
    def traverse_(f: Term[A] => Flow[?]): Flow[Unit] = Flow.Each(xs, f)
    def zip[B](ys: Term[List[B]]): Term[List[(A, B)]] =
      op(Prim.Zip, LeanType.of(Shape.ListOf(LeanType.of(Shape.TupleOf(List(elem(xs), elem(ys)))))), xs, ys)

  extension [A](o: Term[Option[A]])
    @targetName("opt_forall") def forall(p: Term[A] => Term[Boolean]): Term[Boolean] = iter(Iter.OptAll, o, elem(o), p.asInstanceOf[Term[Any] => Term[Boolean]])
    @targetName("opt_exists") def exists(p: Term[A] => Term[Boolean]): Term[Boolean] = iter(Iter.OptSome, o, elem(o), p.asInstanceOf[Term[Any] => Term[Boolean]])
    @targetName("opt_contains") def contains(x: Term[A]): Term[Boolean] = opB(Prim.OptContains, o, x)
    @targetName("opt_isDefined") def isDefined: Term[Boolean] = opB(Prim.IsDefined, o)
    @targetName("opt_nonEmpty") def nonEmpty: Term[Boolean] = opB(Prim.IsDefined, o)
    @targetName("opt_isEmpty") def isEmpty: Term[Boolean] = opB(Prim.OptIsEmpty, o)
    @targetName("opt_getOrElse") def getOrElse(d: Term[A]): Term[A] = op(Prim.OptGetOrElse, d.termType, o, d)

  extension [K, V](m: Term[Map[K, V]])
    @targetName("map_get") def get(k: Term[K]): Term[Option[V]] = op(Prim.Get, LeanType.of(Shape.OptionOf(mapTypes(m)._2)), m, k)
    @targetName("map_contains") def contains(k: Term[K]): Term[Boolean] = opB(Prim.HasKey, m, k)
    @targetName("map_getOrElse") def getOrElse(k: Term[K], d: Term[V]): Term[V] = op(Prim.GetOrElse, d.termType, m, k, d)
    @targetName("map_updated") def updated(k: Term[K], v: Term[V]): Term[Map[K, V]] = op(Prim.Updated, m.termType, m, k, v)
    @targetName("map_plus") def +(kv: (Term[K], Term[V])): Term[Map[K, V]] = op(Prim.Updated, m.termType, m, kv._1, kv._2)
    @targetName("map_removed") def removed(k: Term[K]): Term[Map[K, V]] = op(Prim.Removed, m.termType, m, k)
    @targetName("map_minus") def -(k: Term[K]): Term[Map[K, V]] = op(Prim.Removed, m.termType, m, k)

  extension [A](s: Term[Set[A]])
    @targetName("set_contains") def contains(x: Term[A]): Term[Boolean] = opB(Prim.SetHas, s, x)
    @targetName("set_apply") def apply(x: Term[A]): Term[Boolean] = opB(Prim.SetHas, s, x)
    @targetName("set_incl") def incl(x: Term[A]): Term[Set[A]] = op(Prim.Incl, s.termType, s, x)
    @targetName("set_plus") def +(x: Term[A]): Term[Set[A]] = op(Prim.Incl, s.termType, s, x)
    @targetName("set_excl") def excl(x: Term[A]): Term[Set[A]] = op(Prim.Excl, s.termType, s, x)
    @targetName("set_minus") def -(x: Term[A]): Term[Set[A]] = op(Prim.Excl, s.termType, s, x)
    @targetName("set_union") def union(t: Term[Set[A]]): Term[Set[A]] = op(Prim.Union, s.termType, s, t)
    @targetName("set_concat") def ++(t: Term[Set[A]]): Term[Set[A]] = op(Prim.Union, s.termType, s, t)
    @targetName("set_or") def |(t: Term[Set[A]]): Term[Set[A]] = op(Prim.Union, s.termType, s, t)
    @targetName("set_intersect") def intersect(t: Term[Set[A]]): Term[Set[A]] = op(Prim.Intersect, s.termType, s, t)
    @targetName("set_and") def &(t: Term[Set[A]]): Term[Set[A]] = op(Prim.Intersect, s.termType, s, t)
    @targetName("set_subsetOf") def subsetOf(t: Term[Set[A]]): Term[Boolean] = opB(Prim.SubsetOf, s, t)

  private def result(f: Term[?]): LeanType[Any] = f.termType.shape match
    case Shape.FnOf(_, r) => r.asInstanceOf[LeanType[Any]]
    case _ => LeanType.unknown
  private def call(f: Term[?], args: Term[?]*): Term[Any] = Term(Tree.Apply(f.termTree, args.toList.map(_.termTree)), result(f))
  private[frflow] def applied[R](f: Term[?], args: Term[?]*): Term[R] = call(f, args*).asInstanceOf[Term[R]]

  extension [A, R](f: Term[A => R]) def apply(a: Term[A]): Term[R] = call(f, a).asInstanceOf[Term[R]]
  extension [A, B, R](f: Term[(A, B) => R]) def apply(a: Term[A], b: Term[B]): Term[R] = call(f, a, b).asInstanceOf[Term[R]]
  extension [A, B, C, R](f: Term[(A, B, C) => R]) def apply(a: Term[A], b: Term[B], c: Term[C]): Term[R] = call(f, a, b, c).asInstanceOf[Term[R]]
  extension [A, B, C, D, R](f: Term[(A, B, C, D) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C], d: Term[D]): Term[R] = call(f, a, b, c, d).asInstanceOf[Term[R]]
  extension [A, B, C, D, E, R](f: Term[(A, B, C, D, E) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C], d: Term[D], e: Term[E]): Term[R] = call(f, a, b, c, d, e).asInstanceOf[Term[R]]
