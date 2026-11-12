package frflow.core.analysis

import frflow.core.analysis.outside.Premise
import frflow.core.name.{DefName, NodeId, SymbolName}
import frflow.core.ty.Ty

/** What keeps a theory from being checked: each case names what is wrong and where. */
enum Problem:
  // The graph
  case DuplicateId(id: NodeId)
  case NoRoot
  case AboveItself(id: NodeId)
  case ParentOutside(id: NodeId, parent: NodeId)
  case DesignWithoutParent(id: NodeId)
  case UnderDesign(id: NodeId, design: NodeId)
  /** A premise that is no assumption (2.4): `.assuming` lists what the check trusts; a claim of `always` is placed
    * below the statement it serves with `.refines`, as a rule.
    */
  case PremiseNotAssumed(id: NodeId, premise: NodeId)
  /** A premise resting, through its parents and the premises it assumes, on the node assuming it (`A.assuming(P)` with
    * `P.refines(A)`): a node is decided after what it rests on, so the two could never be decided in order.
    */
  case PremiseBelow(id: NodeId, premise: NodeId)
  /** A fact about the outside, or what values from outside meet (an assumption of `always`), refining a node: it is a
    * premise of the proofs that rest on it (`.assuming`).
    */
  case OutsideAsPart(fact: NodeId, whole: NodeId)
  // The world outside (owner §16, §17)
  /** A statement whose check rests on a fact about the outside its `.assuming` does not list (the one mechanism for a
    * premise, owner §15; `Premises` derives what each needs): an `always[T]` what values from outside meet (owner
    * §21: an assumption of `always` on `T` when the outside passes `T`s in, and each such assumption on the values
    * from outside its `T`s are made from). `by` is the assumption that says it, if one does; when none does, what to
    * say is `needs` (`Node.assumption("…")(always[T](x => …))`).
    */
  case PremiseMissing(id: NodeId, needs: Premise, by: Option[NodeId])
  /** A fact about the outside a statement's `.assuming` lists that its check does not rest on. */
  case PremiseNotNeeded(id: NodeId, premise: NodeId)
  /** An `always` whose type sits, at `at`, inside a map, a set or a function value of type `ty`: no guard reaches it
    * there yet, so the code making or storing it could not be held to it (owner §16; `Unreached`).
    */
  case AlwaysNotReached(always: NodeId, ty: Ty, at: Problem.Place)
  // The vocabulary
  case ReservedName(name: String)
  /** A name declared twice. */
  case DeclaredTwice(name: String)
  /** A statement mentioning a value only plain code reads: its Scala type (`scalaType`) has no `LeanType`; one that
    * derives it can be spoken of, and a connection stays as it is.
    */
  case CodeOnlyInStatement(id: NodeId, symbol: SymbolName, scalaType: String)
  /** A value said to exist (a `forall` under a negation or over a condition, a rule of `always`, a Declaration or a
    * Definition given plain Scala: their consistency) of a type holding a Scala `Int` or `Long`: Lean's `Int` is
    * unbounded, so it could find one Scala's cannot hold (`Bounded`).
    */
  case SaidToExist(ty: Ty, at: Problem.Place)
  // Declarations and Definitions (owner §15)
  /** A Definition nothing gives a meaning: no code, no value fixed or provided where code runs. */
  case Undefined(definition: SymbolName)
  /** A Declaration reached from code: a define that code runs mentions it. */
  case DeclarationInCode(code: DefName, declaration: SymbolName)
  /** Code for a Definition no statement mentions: there is nothing to check it against. */
  case CodeWithoutClaim(definition: SymbolName)
  /** Nodes each proven, through the others, from itself (`Resolve.circles`): a part, or a statement about what a
    * node's code calls, resting in turn on the node.
    */
  case RestsOnItself(ids: List[NodeId])
object Problem:
  /** Where a type sits that an `always` would guard (`Unreached`): a variable a statement quantifies over, a
    * Definition's value, an input or the result of a Definition (named by `of`), a field of a record or of an enum's
    * case (`of`).
    */
  enum Place:
    case Variable(of: NodeId)
    case Value(of: String)
    case Input(of: String)
    case Result(of: String)
    case Field(name: String, of: String)

    /** The place in words: `the field byRoom of Shelf`. */
    def says: String = this match
      case Variable(n) => s"a variable of ${n.value}"
      case Value(s)    => s
      case Input(s)    => s"an input of $s"
      case Result(s)   => s"the result of $s"
      case Field(f, s) => s"the field $f of $s"
