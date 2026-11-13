package frflow.proof.audit

import frflow.proof.prover.ast.*
import frflow.proof.prover.ast.Tree.into
import frflow.proof.prover.term.Silent

/** What a generated module says, read off its syntax alone: a module's declarations (namespaces, documentation and
  * budgets opened), the propositions each states, and the constants applied where a statement assumes them.
  */
private[audit] object Assumed:
  /** The names of the `def`s the modules declare. */
  def defs(modules: List[ProverModule]): List[String] =
    modules.flatMap(_.decls).flatMap(flat).collect { case Decl.Def(_, n, _, _, _) => n.text }

  /** The constants the modules' statements assume, each as its dotted path. */
  def taken(modules: List[ProverModule]): List[List[ProverName]] =
    modules.flatMap(_.decls).flatMap(flat).flatMap(statements)

  private def flat(d: Decl): List[Decl] = d match
    case Decl.Documented(_, x)  => flat(x)
    case Decl.Namespace(_, ds)  => ds.flatMap(flat)
    case Decl.Budgeted(_, x)    => flat(x)
    case other                  => List(other)

  /** What a declaration states: its parameters that are hypotheses, each read as assumed (as the left of `→`),
    * then its type and body, or its statement.
    */
  private def statements(d: Decl): List[List[ProverName]] = d match
    case Decl.Def(_, _, ps, ty, body)    => hypotheses(ps) ++ List(ty, body).flatMap(_.into(Polarity)(false))
    case Decl.Theorem(_, _, ps, s, _, _) => hypotheses(ps) ++ s.into(Polarity)(false)
    case _                               => Nil

  private def hypotheses(ps: List[LBinder]): List[List[ProverName]] =
    ps.collect { case LBinder.Explicit(_, t) => t.into(Polarity)(true) }.flatten

  /** A term as the constants it applies where it assumes them, told whether it is itself assumed (`negative`):
    * left of `→`, a hypothesis binder's type, under a `¬` turned.
    */
  private type Taken = Boolean => List[List[ProverName]]
  private object Polarity extends Silent[Taken](_ => Nil):
    private def all(parts: List[Taken]): Taken = negative => parts.flatMap(_(negative))
    private def binders(ps: List[Binding[Taken]], negative: Boolean): List[List[ProverName]] = ps.flatMap {
      case Binding.Explicit(_, t) => t(negative)
      case Binding.Member(_, in)  => in(negative)
      case _                      => Nil
    }
    override def const(path: List[ProverName]): Taken = negative => if negative then List(path) else Nil
    override def app(fn: Taken, args: List[Taken]): Taken = all(fn :: args)
    override def infix(op: LOp, left: Taken, right: Taken): Taken = negative =>
      left(if op == LOp.Arrow then !negative else negative) ++ right(negative)
    override def prefix(op: LPrefix, arg: Taken): Taken = negative => arg(!negative)
    override def paren(inner: Taken): Taken = inner
    override def forall(params: List[Binding[Taken]], body: Taken): Taken =
      negative => binders(params, !negative) ++ body(negative)
    override def exists(params: List[Binding[Taken]], body: Taken): Taken =
      negative => binders(params, negative) ++ body(negative)
    override def fun(params: List[Binding[Taken]], body: Taken): Taken = body
    override def matching(on: Taken, arms: List[(Taken, Taken)]): Taken = all(on :: arms.map(_._2))
    override def cond(c: Taken, ifTrue: Taken, ifFalse: Taken): Taken =
      negative => c(true) ++ c(false) ++ ifTrue(negative) ++ ifFalse(negative)
    override def let(name: ProverName, ty: Taken, value: Taken, body: Taken): Taken = all(List(value, body))
    override def typed(e: Taken, ty: Taken): Taken = e
