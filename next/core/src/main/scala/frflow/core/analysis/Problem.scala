package frflow.core.analysis

import frflow.core.name.{BoundaryName, DefName, ModelName, NodeId, SymbolName}
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
  /** A fact about the outside claimed: only an assumption can say one, since nothing in FrFlow proves it. */
  case OutsideClaimed(id: NodeId)
  // The world outside (owner §16, §17)
  /** A statement whose check rests on a fact about the outside its `.assuming` does not list (the one mechanism for
    * a premise, owner §15; `Premises` derives what each needs): a claim about a program's runs on a store needs
    * `store.behavesAs(stored)` and `store.atomic`; an `always(stored)` those and `stored.initially(…)`; an
    * `always[T]` what values from outside meet (owner §21:
    * an assumption of `always` on `T` when the outside passes `T`s in, and each such assumption on the values from
    * outside its `T`s are made from), the store facts of each store holding a `T`, and the model of each store
    * operation making one. `by` is the assumption that says it, if one does; when none does, what to say is
    * `needs` (for values from outside, `Node.assumption("…")(always[T](x => …))`).
    */
  case PremiseMissing(id: NodeId, needs: Premise, by: Option[NodeId])
  /** A fact about the outside a statement's `.assuming` lists that its check does not rest on. */
  case PremiseNotNeeded(id: NodeId, premise: NodeId)
  /** Two worlds said equal (`after === before`) where a boundary may fail: the faults its calls take are part of a
    * world, so a run that only read through it changes the world; that every model's state is as before is
    * `unchanged` (`.failsChangingNothing`).
    */
  case WorldsEqual(id: NodeId)
  /** A boundary covered code calls with neither a model it behaves as nor an assumption about what it gives (owner
    * §30): what the code hands it and what comes back would be checked by nothing. Say what it does with
    * `boundary.behavesAs(model)`, or what it promises with an assumption mentioning its operations.
    */
  case BoundaryUnchecked(boundary: BoundaryName)
  /** An `always` whose type sits, at `at`, inside a map, a set or a function value of type `ty`: no guard reaches it
    * there yet, so the code making or storing it could not be held to it (owner §16; `Unreached`).
    */
  case AlwaysNotReached(always: NodeId, ty: Ty, at: Problem.Place)
  // The vocabulary
  case ReservedName(name: String)
  /** A name declared twice; a model's Lean namespace (its name capitalized) counts, so one named as its boundary's
    * class is refused rather than named apart.
    */
  case DeclaredTwice(name: String)
  /** A statement mentioning a value only plain code reads: its Scala type (`scalaType`) has no `LeanType`; one that
    * derives it can be spoken of, and a connection stays as it is.
    */
  case CodeOnlyInStatement(id: NodeId, symbol: SymbolName, scalaType: String)
  // Declarations and Definitions (owner §15)
  /** A Definition nothing gives a meaning: no code, no program, no value fixed or provided where code runs. */
  case Undefined(definition: SymbolName)
  /** A Declaration reached from code: a program's steps, or a define that code runs, mentions it. */
  case DeclarationInCode(code: DefName, declaration: SymbolName)
  /** Code for a Definition no statement mentions: there is nothing to check it against. */
  case CodeWithoutClaim(definition: SymbolName)
  /** Nodes each proven, through the others, from itself (`Resolve.circles`): a part, or a statement about what a
    * node's code calls, resting in turn on the node.
    */
  case RestsOnItself(ids: List[NodeId])
  // Programs and their errors (`Failing`)
  /** A run (`p.from(before)`) of a program that is no Definition applied to inputs (a define's result, a variable):
    * what it may fail with is read off a Definition's code.
    */
  case RunOfNoDefinition(id: NodeId)
  /** A program whose steps raise, handle or meet errors of two types or more (a failing boundary's among them): its
    * run is over one error (`ExceptT E`).
    */
  case ErrorsDiffer(program: DefName, errors: List[Ty])
  /** A failing run's clause (`.failing { (error: E, after) => … }`) of another type than the program fails with. */
  case FailingDiffers(id: NodeId, program: SymbolName, clause: Ty, error: Ty)
  /** A failing run's clause on a program that cannot fail: no error escapes it (nothing it raises or meets is outside
    * a handler of its type).
    */
  case NeverFails(id: NodeId, program: SymbolName)
  /** A program with a transaction inside a transaction (`atomically` within `atomically`): production runs each
    * under one lock, which is not reentrant, so the inner one would wait on the outer for ever.
    */
  case NestedAtomic(program: DefName)

object Problem:
  /** Where a type sits that an `always` would guard (`Unreached`): a variable a statement quantifies over, a store's
    * state, a Definition's value, an input or the result of a Definition or a boundary's operation (named by `of`),
    * a field of a record or of an enum's case (`of`).
    */
  enum Place:
    case Variable(of: NodeId)
    case State(of: ModelName)
    case Value(of: String)
    case Input(of: String)
    case Result(of: String)
    case Field(name: String, of: String)

    /** The place in words: `the field byRoom of Shelf`. */
    def says: String = this match
      case Variable(n) => s"a variable of ${n.value}"
      case State(m)    => s"the state of ${m.value}"
      case Value(s)    => s
      case Input(s)    => s"an input of $s"
      case Result(s)   => s"the result of $s"
      case Field(f, s) => s"the field $f of $s"
