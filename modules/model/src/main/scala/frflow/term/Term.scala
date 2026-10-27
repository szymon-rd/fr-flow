package frflow
package term

import frflow.types.Shape
import scala.annotation.targetName
import scala.compiletime.{constValue, constValueTuple}
import scala.deriving.Mirror
import scala.util.NotGiven

/** A value of the domain: a tree that prints as Lean and compiles to Scala. Models and `define`s
  * are written with terms: `s.records` (a field), `CrmStore(a, b, c)` (a case class, by its name),
  * `x === y`, `xs.filter(r => …)`, `forall((u: Term[User.T]) => …)`, `c.fold(ifTrue, ifFalse)`, `o.fold(ifEmpty)(x => …)`,
  * `q.on[Search.ById](id => …)`.
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

object Term extends TermsOfValues, ListRelations, Runs:
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
  private[term] def fun(f: AnyRef, types: List[LeanType[?]]): (Tree, LeanType[?]) =
    val bs = Lambda.binders(f, types)
    val body = Lambda.body(f, bs)
    (Tree.Fun(bs, body.termTree), body.termType)

  private[term] def elem(t: Term[?]): LeanType[?] = t.termType.shape match
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
      case Shape.EitherOf(e, _) if label == "Left" => bound(List(e))(bs => Pat.InjP(true, bs.head))
      case Shape.EitherOf(_, a) if label == "Right" => bound(List(a))(bs => Pat.InjP(false, bs.head))
      case Shape.ListOf(a) if label == "::" => bound(List(a, scrutinee.termType))(bs => Pat.ConsP(bs(0), bs(1)))
      case Shape.ListOf(_) if label == "Nil" => bound(Nil)(_ => Pat.NilP)
      case Shape.Data(adt) =>
        val c = if adt.isEnum then adt.ctor(label) else adt.ctors.head
        bound(c.fields.map(_._2))(bs => Pat.Ctor(adt, c, bs))
      case _ => throw IllegalArgumentException(s"FrFlow: cannot match on case $label here")

  /** A case named by the program (`.on[C]`): an enum's or a list's. An Option is folded instead, one way to say it. */
  private[frflow] def namedCase(scrutinee: Term[?], label: String, f: AnyRef): Arm = scrutinee.termType.shape match
    case Shape.OptionOf(_) => throw IllegalArgumentException("FrFlow: an Option is folded, not matched by case: o.fold(ifEmpty)(x => …)")
    case _ => caseOf(scrutinee, label, f)

  extension [S](s: Term[S])
    /** A case of a match on an enum or a List: the lambda takes the case's fields. */
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
    /** `a implies b`: a word, so it binds after `&&` and `||`: `a && b implies c` is `(a && b) implies c`. */
    infix def implies(b: Term[Boolean]): Term[Boolean] = opB(Prim.Implies, a, b)
    /** Boolean's fold (its catamorphism): `ifTrue` when this holds, else `ifFalse`. Lean's `if … then … else …`. */
    def fold[R](ifTrue: Term[R], ifFalse: Term[R]): Term[R] = Term(Tree.If(a.termTree, ifTrue.termTree, ifFalse.termTree), ifTrue.termType)
    /** The same between two flows (Cats' `foldF`): the steps of one of them. */
    def foldF[R](ifTrue: Flow[R], ifFalse: Flow[R]): Flow[R] = Flow.Cond(a, ifTrue, ifFalse)

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
    /** The list with `x` added at its end. */
    def :+(x: Term[A]): Term[List[A]] =
      op(Prim.Append, xs.termType, xs, Term(Tree.ListT(List(x.termTree)), xs.termType))
    def contains(x: Term[A]): Term[Boolean] = opB(Prim.Contains, xs, x)
    def isEmpty: Term[Boolean] = opB(Prim.IsEmpty, xs)
    def nonEmpty: Term[Boolean] = opB(Prim.NonEmpty, xs)
    def length: Term[Int] = op(Prim.Length, summon[LeanType[Int]], xs)
    def size: Term[Int] = length
    def forall(p: Term[A] => Term[Boolean]): Term[Boolean] = iter(Iter.All, xs, elem(xs), p.asInstanceOf[Term[Any] => Term[Boolean]])
    def exists(p: Term[A] => Term[Boolean]): Term[Boolean] = iter(Iter.Some, xs, elem(xs), p.asInstanceOf[Term[Any] => Term[Boolean]])
    /** `xs.forall(endsAfterStart)`: a define of one element, as `xs.forall(x => endsAfterStart(x))`. */
    def forall(d: Def[A => Boolean]): Term[Boolean] = xs.forall(x => vocabulary.DefCalls.apply(d)(x))
    def exists(d: Def[A => Boolean]): Term[Boolean] = xs.exists(x => vocabulary.DefCalls.apply(d)(x))
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
    /** Each element in turn, the results in a list (Traverse's `traverse`): Lean's `xs.mapM fun x => do …`. */
    def traverse[B](f: Term[A] => Flow[B]): Flow[List[B]] = Flow.EachResult(xs, f)
    /** Each element in turn, the results dropped (Foldable's `traverse_`): Lean's `for x in xs do …`. */
    def traverse_(f: Term[A] => Flow[?]): Flow[Unit] = Flow.Each(xs, f)
    /** A value carried through the elements by a flow (Foldable's `foldM`): Lean's `xs.foldlM (init := z) fun acc x => do …`. */
    def foldM[B](z: Term[B])(f: (Term[B], Term[A]) => Flow[B]): Flow[B] = Flow.Fold(xs, z, f)
    /** Each element at once, the results in the list's order (Cats' `parTraverse`); structured, as `parTupled`. Lean
      * reads it as `traverse` and asks the proof that any two elements' flows commute, so every order of whole branches
      * gives the same.
      */
    def parTraverse[B](f: Term[A] => Flow[B]): Flow[List[B]] = Flow.ParEach(xs, f, None)
    /** The same, at most `n` at once (Cats Effect's `parTraverseN`). */
    def parTraverseN[B](n: Int)(f: Term[A] => Flow[B]): Flow[List[B]] =
      require(n >= 1, "FrFlow: parTraverseN runs at least one at once")
      Flow.ParEach(xs, f, Some(n))
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
    /** Option's fold (its catamorphism), as Scala's and Cats': `ifEmpty` for none, `f(x)` for `some x`. */
    @targetName("opt_fold") def fold[E](ifEmpty: E)(using e: AsTerm[E])(f: Term[A] => Term[e.R]): Term[e.R] =
      Cases(o, List(caseOf(o, "Some", f), caseOf(o, "None", e(ifEmpty))))

  extension [E, A](o: Term[Either[E, A]])
    /** Either's fold (its catamorphism): `onError(e)` for an error, `onValue(a)` for a value. Lean's `match … with
      * | .error e => … | .ok a => …`.
      */
    @targetName("either_fold") def fold[R](onError: Term[E] => Term[R], onValue: Term[A] => Term[R]): Term[R] =
      Cases(o, List(caseOf(o, "Left", onError), caseOf(o, "Right", onValue)))
    @targetName("either_isLeft") def isLeft: Term[Boolean] = o.fold(_ => True, _ => False)
    @targetName("either_isRight") def isRight: Term[Boolean] = o.fold(_ => False, _ => True)

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
