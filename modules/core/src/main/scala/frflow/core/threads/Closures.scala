package frflow.core.threads

import cats.data.State
import cats.syntax.all.*

/** The closures a definition makes, named: each `Term.Closure` becomes a constructor of `code`,
  * `Lam_<definition>_<n>`, applied to the variables it captures, and what it runs a definition of its own,
  * `Lam_<definition>_<n>_body`, over those variables and what it is called with (`arg`).
  *
  * A definition's closures are numbered in the order they are written, one inside another after it. The captured
  * variables are listed in the order the enclosing definition's earlier statements mention them, then in the order
  * the closure's own body does.
  */
object Closures:
  /** A closure named: its constructor, and the definition of what it runs. */
  final case class Lifted(ctor: Ctor, body: Decl.Definition)

  /** The closures made so far of the definitions named `base`: how many, and each with its number. */
  private final case class Made(base: String, count: Int, lifted: List[(Int, Lifted)])
  private type Lift[A] = State[Made, A]

  /** `read`'s definition, each closure it makes replaced by its constructor, and those closures in the order of
    * their numbers, which start after `from`.
    */
  def lift(read: Draft.Read, from: Int): (Decl.Definition, List[Lifted]) =
    val (made, body) = go(read.definition.body, Nil).run(Made(read.base, from, Nil)).value
    (read.definition.copy(body = body), made.lifted.sortBy(_._1).map(_._2))

  /** `t` without closures; `used`: the names the statements before it mention. */
  private def go(t: Term, used: List[String]): Lift[Term] = t match
    case Term.Closure(captured, body) => named(captured, body, used)
    case Term.App(f, args)            => (go(f, used), args.traverse(go(_, used))).mapN(Term.App(_, _))
    case Term.Tuple(ps)               => ps.traverse(go(_, used)).map(Term.Tuple(_))
    case Term.Items(is)               => is.traverse(go(_, used)).map(Term.Items(_))
    case Term.Fun(bs, body)           => go(body, used).map(Term.Fun(bs, _))
    case Term.Let(n, v, body)         => step(v, body, used)(Term.Let(n, _, _))
    case Term.Unpack(ns, v, body)     => step(v, body, used)(Term.Unpack(ns, _, _))
    case Term.Bind(n, first, rest)    => step(first, rest, used)(Term.Bind(n, _, _))
    case Term.If(c, y, n)             => (go(c, used), go(y, used), go(n, used)).mapN(Term.If(_, _, _))
    case Term.Match(on, arms)         => (go(on, used), arms.traverse(arm(_, used))).mapN(Term.Match(_, _))
    case leaf                         => State.pure(leaf)

  private def arm(a: Arm, used: List[String]): Lift[Arm] = go(a.body, used).map(Arm(a.pattern, _))

  /** A statement and what follows it: what follows has the statement's names mentioned before it. */
  private def step(first: Term, rest: Term, used: List[String])(make: (Term, Term) => Term): Lift[Term] =
    go(first, used).flatMap(f => go(rest, used ++ f.mentions).map(make(f, _)))

  private def named(captured: List[Param], body: Term, used: List[String]): Lift[Term] =
    for
      made  <- State.get[Made]
      index  = made.count + 1
      _     <- State.set(made.copy(count = index))
      inner <- go(body, Nil)
      order  = (used ++ inner.mentions).distinct.flatMap(n => captured.find(_.name == n))
      lifted = closure(s"Lam_${made.base}_$index", order, inner)
      _     <- State.modify[Made](m => m.copy(lifted = m.lifted :+ (index -> lifted)))
    yield Term.of(lifted.ctor.name, order.map(p => Term.Ref(p.name))*)

  private def closure(name: String, captured: List[Param], body: Term): Lifted =
    Lifted(Ctor(name, captured),
      Decl.Definition(s"${name}_body", captured :+ Param(Term.Arg, Ty.Val), Decl.M(Ty.Val), body))
