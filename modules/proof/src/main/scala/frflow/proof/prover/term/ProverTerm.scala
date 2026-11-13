package frflow.proof.prover.term

import frflow.core.expr.{Binder, Value}
import frflow.core.name.SymbolName
import frflow.core.term.*
import frflow.core.term.language.{Body, Sym}
import frflow.core.ty.Ty
import frflow.proof.prover.ast.*
import frflow.proof.prover.lower.{Atoms, LowerEnv, LowerType, LowerValue, Seen, Shape}

/** The interpreter of terms that writes them for the prover, the only one: LNCS 7470 §3.2's `S` interpreter (there
  * `S a = Int -> String`, the binder depth in, the text out), here the scope in and, out, a term of whatever syntax
  * it is given to write into (`Syntax[E]`): the tree a module is kept in, or a text. Every compound term in
  * parentheses; application flattened (`(Rooms.covers b t)`); a named definition called by name, its body printed
  * once as its `def` (`Printed.define`); a field of a constructor is its argument, so a match arm's case reads as
  * its fields' names. What it asks of a term it has written, the syntax's own `Seen[E]` tells.
  */
final class ProverTerm[E](env: LowerEnv, standing: Map[SymbolName, E] = Map.empty[SymbolName, E])(using
    protected val syntax: Syntax[E], protected val seen: Seen[E]) extends Sym[ProverTerm.S[E]], ProverFinite[E]:
  protected val atoms: Atoms[E] = new Atoms(syntax)
  import atoms.{call, const, name}
  import syntax.{dot, fun, listLit, matching, paren, prefix, tuple, typed, update}
  private type S[A] = Scope => E
  private val constants = new LowerValue[E](env)
  private val types = new LowerType(syntax)
  private lazy val byName = standing.map((n, e) => Names.ident(n.value) -> e)

  def bool(b: Boolean): S[Boolean] = _ => name(if b then "True" else "False")
  def and(a: S[Boolean], b: S[Boolean]): S[Boolean] = infix(LOp.And, a, b)
  def or(a: S[Boolean], b: S[Boolean]): S[Boolean] = infix(LOp.Or, a, b)
  def not(a: S[Boolean]): S[Boolean] = s => paren(prefix(LPrefix.Not, a(s)))
  def implies(a: S[Boolean], b: S[Boolean]): S[Boolean] = infix(LOp.Arrow, a, b)
  def cond[A](c: S[Boolean], t: S[A], e: S[A]): S[A] = s => paren(syntax.cond(c(s), t(s), e(s)))
  def eq[A](a: S[A], b: S[A]): S[Boolean] = infix(LOp.Eq, a, b)
  def add(a: S[BigInt], b: S[BigInt]): S[BigInt] = infix(LOp.Add, a, b)
  def sub(a: S[BigInt], b: S[BigInt]): S[BigInt] = infix(LOp.Sub, a, b)
  def lt(a: S[BigInt], b: S[BigInt]): S[Boolean] = infix(LOp.Lt, a, b)
  def le(a: S[BigInt], b: S[BigInt]): S[Boolean] = infix(LOp.Le, a, b)
  /** A constant, typed (`(2 : Int)`, `([1] : (List Int))`) unless its form says its type (a truth value, a string,
    * a record or a case): Lean would default a numeral to `Nat`, and an empty list to nothing.
    */
  def lit[A](a: A, value: Value, ty: Ty): S[A] = s =>
    val e = constants(value, ty).runA(s.naming).value
    value match
      case Value.Bool(_) | Value.Str(_) | Value.Unit | Value.Data(_, _) => e
      case _                                                           => typed(e, types(ty))
  /** `([] : (List T))`: typed, since nothing around an empty list need say what it holds (`([]).length`). */
  def nil[A](elem: Ty): S[List[A]] = _ => typed(listLit(Nil), types(Ty.ListOf(elem)))
  /** `x :: xs`; onto a literal list, the literal (`[x]`), the element saying what it holds. */
  def cons[A](x: S[A], xs: S[List[A]]): S[List[A]] = s =>
    val rest = xs(s)
    seen.shape(rest) match
      case Shape.Listed(es)          => listLit(x(s) :: es)
      case Shape.Typed(true)         => listLit(List(x(s)))
      case _                         => paren(syntax.infix(LOp.Cons, x(s), rest))
  def append[A](xs: S[List[A]], ys: S[List[A]]): S[List[A]] = infix(LOp.Append, xs, ys)
  def length[A](xs: S[List[A]]): S[BigInt] = s => typed(dot(paren(xs(s)), "length"), name("Int"))
  def all[A](xs: S[List[A]], x: Bound[A])(p: S[A] => S[Boolean]): S[Boolean] = member(xs, x, p)(syntax.forall(_, _))
  def any[A](xs: S[List[A]], x: Bound[A])(p: S[A] => S[Boolean]): S[Boolean] = member(xs, x, p)(syntax.exists(_, _))
  def filter[A](xs: S[List[A]], x: Bound[A])(p: S[A] => S[Boolean]): S[List[A]] =
    mapped("List.filter", xs, x, p.andThen(_.andThen(decide)))
  def map[A, B](xs: S[List[A]], x: Bound[A])(f: S[A] => S[B]): S[List[B]] = mapped("List.map", xs, x, f)
  def flatMap[A, B](xs: S[List[A]], x: Bound[A])(f: S[A] => S[List[B]]): S[List[B]] = mapped("List.flatMap", xs, x, f)
  def find[A](xs: S[List[A]], x: Bound[A])(p: S[A] => S[Boolean]): S[Option[A]] =
    mapped("List.find?", xs, x, p.andThen(_.andThen(decide)))
  def contains[A](xs: S[List[A]], x: S[A]): S[Boolean] = infix(LOp.Mem, x, xs)
  def zip[A, B](xs: S[List[A]], ys: S[List[B]]): S[List[(A, B)]] = s => call(const("List.zip"), List(xs(s), ys(s)))
  def isEmpty[A](xs: S[List[A]]): S[Boolean] = infix(LOp.Eq, xs, _ => listLit(Nil))
  def nodup[A](xs: S[List[A]]): S[Boolean] = s => call(const("List.Nodup"), List(xs(s)))
  def pairwise[A](xs: S[List[A]], x: Bound[A], y: Bound[A])(p: (S[A], S[A]) => S[Boolean]): S[Boolean] = s =>
    val (a, inner) = s.bind(x.hint, x.ty)
    val (b, body) = inner.bind(y.hint, y.ty)
    val fn = fun(List(of(a, x.ty), of(b, y.ty)), p(variable(a), variable(b))(body))
    call(const("List.Pairwise"), List(paren(fn), xs(s)))
  def foldLeft[A, B](xs: S[List[A]], z: S[B], acc: Bound[B], x: Bound[A])(f: (S[B], S[A]) => S[B]): S[B] = s =>
    val (a, inner) = s.bind(acc.hint, acc.ty)
    val (y, body) = inner.bind(x.hint, x.ty)
    val fn = fun(List(of(a, acc.ty), of(y, x.ty)), f(variable(a), variable(y))(body))
    call(const("List.foldl"), List(paren(fn), z(s), xs(s)))
  def some[A](a: S[A]): S[Option[A]] = s => call(name("some"), List(a(s)))
  /** `(none : (Option T))`, typed as the empty list is. */
  def none[A](elem: Ty): S[Option[A]] = _ => typed(name("none"), types(Ty.OptionOf(elem)))
  def foldOption[A, R](o: S[Option[A]], ifNone: S[R], x: Bound[A])(ifSome: S[A] => S[R]): S[R] = s =>
    val (n, body) = bound(x, s, ifSome)
    paren(matching(o(s), List(name("none") -> ifNone(s), syntax.app(name("some"), List(syntax.name(n))) -> body)))
  /** `(∀ (x : T), (o = (some x)) → p)`, as `optionAny` is `(∃ (x : T), (o = (some x)) ∧ p)`. */
  def optionAll[A](o: S[Option[A]], x: Bound[A])(p: S[A] => S[Boolean]): S[Boolean] =
    holding(o, x, p, LOp.Arrow)(syntax.forall(_, _))
  def optionAny[A](o: S[Option[A]], x: Bound[A])(p: S[A] => S[Boolean]): S[Boolean] =
    holding(o, x, p, LOp.And)(syntax.exists(_, _))
  def isDefined[A](o: S[Option[A]]): S[Boolean] = infix(LOp.Ne, o, _ => name("none"))
  def getOrElse[A](o: S[Option[A]], default: S[A]): S[A] = s => call(const("Option.getD"), List(o(s), default(s)))
  /** `(Except.error e : (Except E A))`: typed by the whole, which one side alone does not say. */
  def left[E, A](e: S[E], ty: Ty): S[Either[E, A]] =
    s => typed(syntax.app(const("Except.error"), List(e(s))), types(ty))
  def right[E, A](a: S[A], ty: Ty): S[Either[E, A]] =
    s => typed(syntax.app(const("Except.ok"), List(a(s))), types(ty))
  def foldEither[E, A, R](v: S[Either[E, A]], e: Bound[E], a: Bound[A])(l: S[E] => S[R], r: S[A] => S[R]): S[R] = s =>
    val ((x, onLeft), (y, onRight)) = (bound(e, s, l), bound(a, s, r))
    paren(matching(v(s), List(syntax.app(const("Except.error"), List(syntax.name(x))) -> onLeft,
      syntax.app(const("Except.ok"), List(syntax.name(y))) -> onRight)))
  def forall[A](x: Bound[A])(p: S[A] => S[Boolean]): S[Boolean] = quantified(x, p)(syntax.forall(_, _))
  def exists[A](x: Bound[A])(p: S[A] => S[Boolean]): S[Boolean] = quantified(x, p)(syntax.exists(_, _))
  /** Printed as the `∀` it narrows: Lean states an `always` only as its hypotheses (`Guarded`), what keeps it. */
  def always[A](x: Bound[A])(p: S[A] => S[Boolean]): S[Boolean] = forall(x)(p)
  def construct[F](c: Constructor[F]): S[F] = _ => atoms.ctor(c.data, c.ctor)
  /** A field of a record made on the spot (its constructor called) is its argument, typed by the field. */
  def field[R, F](r: S[R], sel: Selector[R, F]): S[F] = s =>
    val on = r(s)
    seen.shape(on) match
      case Shape.Call(fn, args) if makes(fn, Names.ident(sel.record.value)) && sel.index < args.size =>
        val arg = args(sel.index)
        seen.shape(arg) match
          case Shape.Typed(_) => arg
          case _              => typed(arg, types(sel.ty))
      case _ => dot(on, if sel.record == Selector.pair then sel.name else Names.ident(sel.name).text)
  def copy[R, F](r: S[R], sel: Selector[R, F], v: S[F]): S[R] =
    s => update(r(s), List(Names.ident(sel.name) -> v(s)))
  def pair[A, B](a: S[A], b: S[B]): S[(A, B)] = s => tuple(List(a(s), b(s)))
  def cases[V, R](v: S[V], arms: List[When[S, V, ?, R]], ty: Ty): S[R] =
    s => paren(matching(v(s), arms.map(arm(_, s))))
  def lam[A, B](x: Bound[A])(f: S[A] => S[B]): S[A => B] = s =>
    val (n, body) = bound(x, s, f)
    paren(fun(List(of(n, x.ty)), body))
  def app[A, B](f: S[A => B], a: S[A]): S[B] = s => applied(f(s), a(s))
  def let[A, B](v: S[A], x: Bound[A])(b: S[A] => S[B]): S[B] = s =>
    val (n, body) = bound(x, s, b)
    paren(syntax.let(n, types(x.ty), v(s), body))
  /** A value's name or what stands for it (a witness given before, R14.6); a define on its open terms so written. */
  def param[A](n: SymbolName, ty: Ty): S[A] = _ => standing.getOrElse(n, syntax.name(Names.ident(n.value)))
  def define[F](d: Body[F]): S[F] = _ => atoms.define(env, d.name, byName.get)
  def free[A](x: Binder): S[A] = s => syntax.name(s.named(x))
  def noted[A](n: Annotation, t: S[A]): S[A] = t

  private def decide(body: E): E = syntax.app(name("decide"), List(body))
  /** Whether `fn` is a constructor of the type named. */
  private def makes(fn: E, data: ProverName): Boolean = seen.shape(fn) match
    case Shape.Ctor(d) => d == data
    case _             => false

  /** `(List.map (fun x => body) xs)`: a list operation of a function of each element. */
  private def mapped[A, B](op: String, xs: S[List[A]], x: Bound[A], f: S[A] => S[B]): S[List[B]] = s =>
    val (n, body) = bound(x, s, f, seen.names(xs(s)))
    call(const(op), List(paren(fun(List(Binding.Of(n, types(x.ty))), body)), xs(s)))

  private def holding[A](o: S[Option[A]], x: Bound[A], p: S[A] => S[Boolean], op: LOp)(
      make: (List[Binding[E]], E) => E): S[Boolean] = s =>
    val (n, body) = bound(x, s, p, seen.names(o(s)))
    val some = paren(syntax.infix(LOp.Eq, o(s), call(name("some"), List(syntax.name(n)))))
    paren(make(List(of(n, x.ty)), syntax.infix(op, some, body)))

  private def infix[A, B, R](op: LOp, a: S[A], b: S[B]): S[R] = s => paren(syntax.infix(op, a(s), b(s)))
  private def variable[A](n: ProverName): S[A] = _ => syntax.name(n)
  private def of(n: ProverName, ty: Ty): Binding[E] = Binding.Explicit(n, types(ty))

  /** The binder's name in this scope, and the body printed in the scope one deeper, its variable that name. */
  private def bound[A, B](x: Bound[A], s: Scope, p: S[A] => S[B], avoid: Set[String] = Set.empty): (ProverName, E) =
    val (n, inner) = s.bind(x.hint, x.ty, avoid)
    (n, p(variable(n))(inner))

  private def member[A](xs: S[List[A]], x: Bound[A], p: S[A] => S[Boolean])(make: (List[Binding[E]], E) => E)
      : S[Boolean] = s =>
    val (n, body) = bound(x, s, p, seen.names(xs(s)))
    paren(make(List(Binding.Member(n, xs(s))), body))

  private def quantified[A](x: Bound[A], p: S[A] => S[Boolean])(make: (List[Binding[E]], E) => E)
      : S[Boolean] = s =>
    val (n, body) = bound(x, s, p)
    paren(make(List(of(n, x.ty)), body))

  /** `| Event.Expired at => body`: the case's fields named here, the case itself their constructor. */
  private def arm[V, C, R](w: When[S, V, C, R], s: Scope): (E, E) =
    val (names, inner) = w.c.fields.foldLeft((List.empty[ProverName], s)) { case ((ns, sc), (hint, ty)) =>
      val (n, next) = sc.bind(hint, ty)
      (ns :+ n, next)
    }
    val head = atoms.ctor(w.c.sum, w.c.ctor)
    val pattern = if names.isEmpty then head else syntax.app(head, names.map(syntax.name(_)))
    (pattern, w.body(_ => if names.isEmpty then head else paren(pattern))(inner))

object ProverTerm:
  /** What a term is to this interpreter, writing into `E`: its scope in, the term written out. */
  type S[E] = [A] =>> Scope => E
