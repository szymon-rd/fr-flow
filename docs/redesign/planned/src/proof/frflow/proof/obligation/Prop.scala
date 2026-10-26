package frflow.proof.obligation

import cats.data.NonEmptyList
import frflow.core.expr.{Expr, Prog}
import frflow.core.name.{NodeId, SymbolName}

/** The statement of an obligation in the logic of refinement, before any Lean syntax. Claims, conjuncts and
  * expectations stand applied to their open terms. `Forall` and `Exists` bind open terms in order: those of the
  * claims of the nodes the statement is `about`, then its conclusion's, then its hypotheses' (a statement binds the
  * terms of what it is about, not only of what it says).
  */
enum Prop:
  case ClaimOf(node: NodeId, substitute: Map[SymbolName, Substitute])
  case ConjunctOf(node: NodeId, i: Int)
  case Expected(node: NodeId, i: Int)
  case Formula(e: Expr)
  case Implies(hyps: List[Hyp], conclusion: Prop)
  case Iff(left: Prop, right: Prop)
  case Both(props: NonEmptyList[Prop])
  case Not(p: Prop)
  case False
  case Forall(about: List[NodeId], body: Prop)
  case Exists(about: List[NodeId], body: Prop)
  /** What Scala computes, stated for Lean to prove: closed, so it binds nothing. */
  case Evaluates(e: Evaluation)
  case Commutes(first: Prog, second: Prog)

object Prop:
  def claim(n: NodeId): Prop = ClaimOf(n, Map.empty)
  /** `∀` the open terms of the claims of `about` and of `body`: every obligation's statement. */
  def over(about: List[NodeId], body: Prop): Prop = Forall(about, body)
