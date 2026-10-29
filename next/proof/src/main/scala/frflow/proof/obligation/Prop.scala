package frflow.proof.obligation

import cats.data.NonEmptyList
import frflow.core.expr.Expr
import frflow.core.name.{DefName, NodeId, SymbolName}
import frflow.core.spec.Written
import frflow.core.term.Final
import frflow.core.ty.Ty
import frflow.proof.terms.Commutation

/** The statement of an obligation in the logic of refinement, before any Lean syntax. Claims and conjuncts stand
  * applied to their open terms. `Forall` and `Exists` bind open terms in order: those of the claims of the nodes the
  * statement is `about`, then its conclusion's, then its hypotheses' (a statement binds the terms of what it is
  * about, not only of what it says); `ForEvery` and `ForSome` bind exactly the symbols named.
  */
enum Prop:
  case ClaimOf(node: NodeId, substitute: Map[SymbolName, Substitute])
  /** That every run of `op` keeps an `always` (`Keeping`): its formula, declared in the statement's namespace. */
  case Keeps(always: NodeId, op: SymbolName, formula: Written[Expr], substitute: Map[SymbolName, Substitute])
  /** That every result a maker (a proven define, or a store operation on its model) gives meets an `always[T]`:
    * `always.makes_<maker>` applied to the maker's code (`made_<maker>`).
    */
  case Makes(always: NodeId, maker: SymbolName, formula: Written[Expr], substitute: Map[SymbolName, Substitute])
  case ConjunctOf(node: NodeId, i: Int)
  /** A formula as written: its term, printed, with what stands for the Definitions given there (`code`: their proven
    * code); its IR, for the open terms it mentions.
    */
  case Formula(w: Written[Expr], code: Map[SymbolName, Substitute])
  case Implies(hyps: List[Hyp], conclusion: Prop)
  case Iff(left: Prop, right: Prop)
  case Both(props: NonEmptyList[Prop])
  case Not(p: Prop)
  case False
  case Forall(about: List[NodeId], body: Prop)
  case Exists(about: List[NodeId], body: Prop)
  /** `∀` these values, each provided where code runs. */
  case ForEvery(symbols: List[SymbolName], body: Prop)
  /** `∃` these values: the open ones a witness is asked for. */
  case ForSome(symbols: List[SymbolName], body: Prop)
  /** An `always`'s rule at every state a store may start in (`initially`'s rule): an `always(stored)`'s of the
    * state; an `always[T]`'s at each `T` the state holds (`within`: the state, each element, a field's), as its
    * guard places it, over the state (level 0).
    */
  case Starts(rule: DefName, initially: DefName, state: Ty, within: Option[Final[Boolean]])
  /** Some value of `ty` meets an `always[T]`'s rule. */
  case Inhabited(rule: DefName, ty: Ty)
  /** A parallel step's two orders give the same run, for every value of the Definitions the program calls. */
  case Commutes(c: Commutation, opens: List[SymbolName])

object Prop:
  def claim(n: NodeId): Prop = ClaimOf(n, Map.empty)
  /** `∀` the open terms of the claims of `about` and of `body`: every obligation's statement. */
  def over(about: List[NodeId], body: Prop): Prop = Forall(about, body)
