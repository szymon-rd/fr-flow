package frflow.proof.prover.ast

/** The syntax FrFlow generates for a prover, as an algebra: one operation for each form of a term, `E` what a term
  * is to the one reading it. A printer is an interpreter of it: the notation a node's content is signed in
  * (`term.Notation`, `E` its text) and Rocq (`rocq.RocqSyntax`, `E` its text in a scope). The tree (`LExpr`) is
  * its initial form: what a term is before anyone reads it (`Tree`), read by any interpreter with `into`.
  */
trait Syntax[E]:
  def name(n: ProverName): E
  /** A qualified constant (`FrFlow.within`, `True`, `()`): each part an identifier. */
  def const(path: List[ProverName]): E
  /** A constructor of a domain type, qualified by it (`Event.Expired`, `Booking.mk`). */
  def ctor(data: ProverName, ctor: ProverName): E
  def num(n: BigInt): E
  def str(s: String): E
  def app(fn: E, args: List[E]): E
  def infix(op: LOp, left: E, right: E): E
  def prefix(op: LPrefix, arg: E): E
  def paren(inner: E): E
  /** `e.f`: a field, a projection (`.1`, `.2`), a list's length. */
  def dot(on: E, field: String): E
  def tuple(elems: List[E]): E
  def listLit(elems: List[E]): E
  /** A record with fields replaced. */
  def update(record: E, fields: List[(ProverName, E)]): E
  def fun(params: List[Binding[E]], body: E): E
  def forall(params: List[Binding[E]], body: E): E
  def exists(params: List[Binding[E]], body: E): E
  def cond(c: E, ifTrue: E, ifFalse: E): E
  def matching(on: E, arms: List[(E, E)]): E
  def let(name: ProverName, ty: E, value: E, body: E): E
  def typed(e: E, ty: E): E
  /** An anonymous constructor: the witnesses of an `exists`, then its proof. */
  def anonymous(elems: List[E]): E
  /** A proof by one of FrFlow's own tactics, named. */
  def by(tactic: ProverName): E
  /** `fn` with one input given by name. */
  def named(fn: E, name: ProverName, value: E): E

/** A binder of a `fun`, a quantifier or a declaration: explicit `(x : T)` (or several of one type), implicit
  * `{m : T}`, an instance, a bare name, a bare name whose type is known (`Of`: written as the bare name in the
  * notation a node's content is in, with its type in Rocq, which does not find it from a list given after the
  * function), a membership `x ∈ xs`. `E` is what a term is to the one reading it (`Syntax`).
  */
enum Binding[+E]:
  case Explicit(name: ProverName, ty: E)
  case Several(names: List[ProverName], ty: E)
  case Implicit(name: ProverName, ty: E)
  case Instance(cls: E)
  case Bare(name: ProverName)
  case Of(name: ProverName, ty: E)
  case Member(name: ProverName, in: E)

  /** The same binder, its terms read by `f`. */
  def map[F](f: E => F): Binding[F] = this match
    case Explicit(n, t) => Explicit(n, f(t))
    case Several(ns, t) => Several(ns, f(t))
    case Implicit(n, t) => Implicit(n, f(t))
    case Instance(c)    => Instance(f(c))
    case Bare(n)        => Bare(n)
    case Of(n, t)       => Of(n, f(t))
    case Member(n, in)  => Member(n, f(in))

  /** The names it binds. */
  def bound: List[ProverName] = this match
    case Explicit(n, _) => List(n)
    case Several(ns, _) => ns
    case Implicit(n, _) => List(n)
    case Bare(n)        => List(n)
    case Of(n, _)       => List(n)
    case Member(n, _)   => List(n)
    case Instance(_)    => Nil

/** A binder of the tree: `Binding` over `LExpr`. */
type LBinder = Binding[LExpr]
val LBinder: Binding.type = Binding
