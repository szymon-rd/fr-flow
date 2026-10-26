package frflow
package ledger

import frflow.protocol.*

/** Why a decision is not recorded: what the developer reads. */
enum Refusal(val message: String):
  case NoOneDecides extends Refusal("say who decides")
  case NoReason extends Refusal("give the reason for the decision in a few words: it is kept as part of the theory")
  case MovedSinceSeen(node: NodeId) extends Refusal(s"$node changed since you looked at it: look again before deciding")
  case UnknownNode(node: NodeId) extends Refusal(s"unknown node $node")
  case NotAProposal(node: NodeId, state: ReviewState) extends Refusal(s"$node is $state: only a proposal is rejected on its own")
  case AcceptFirst(waitsFor: NodeId) extends Refusal(s"accept $waitsFor first: what rests on it is decided after it")
  case AlreadyAccepted(node: NodeId) extends Refusal(s"$node is already accepted")
  case ExamplesFail(node: NodeId, failing: Int)
      extends Refusal(s"$node: $failing of its examples fail: fix the code or the contract, run check, then decide")
  case CodeFails(node: NodeId, failure: String)
      extends Refusal(s"$node: its code fails a generated case: $failure; fix the code or the contract, run check, then decide")
  case ContractChanged(node: NodeId, failure: String)
      extends Refusal(s"$node: the contract changed and its code no longer meets it: $failure; fix the code or the contract, run check, then decide")
  case NotBelow(node: NodeId, named: List[NodeId])
      extends Refusal(s"not among the decisions below $node that this decision can act on: ${named.mkString(", ")}")
  case NotDecided(node: NodeId, state: ReviewState) extends Refusal(s"$node is $state: only a decided node is revisited")
  case AlreadyRevisited(node: NodeId) extends Refusal(s"$node is already to revisit")
  case StillInModel(node: NodeId) extends Refusal(s"$node is still in the model: only a node removed from it is gone")
  case NothingToConfirm extends Refusal("nothing to confirm: no decision is mechanical")
  case NoNodes extends Refusal("name the nodes to accept")
  case NoIdea extends Refusal("there is no IDEA.md yet: write the purpose of the system in it first")
  /** No name to decide under: none given, and the developer's key is filed under none. */
  case NoDeveloper extends Refusal("say who decides: the name your key's public half is filed under (.frflow/keys/NAME.pub)")
  /** A key other than the one filed under the name: FrFlow never replaces a filed key. */
  case OtherKey(name: String) extends Refusal(s"$name's key in .frflow/keys is a different key: decisions as $name are signed " +
    s"with that key only; a new key is filed only after the developer removes .frflow/keys/$name.pub in a commit of their own")
  /** The key is filed under another name: a decision counts by the key of the name it is made under. */
  case KeyFiledAs(filed: String, name: String)
      extends Refusal(s"this key is filed as $filed (.frflow/keys/$filed.pub): decide as $filed, not as $name")
  /** One decision of several refused: none is recorded. */
  case Within(node: NodeId, refusal: Refusal)
      extends Refusal(if refusal.message.startsWith(s"$node: ") then refusal.message else s"$node: ${refusal.message}")

  override def toString: String = message
