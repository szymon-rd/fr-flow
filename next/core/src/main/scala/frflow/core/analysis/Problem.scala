package frflow.core.analysis

import frflow.core.name.{DefName, ModelName, NodeId, SymbolName}
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
  /** A premise that is neither an assumption nor an `always`: what a proof assumes is trusted or always holds. */
  case PremiseNotAssumed(id: NodeId, premise: NodeId)
  /** A fact about the outside refining a node: it is a premise of the proofs that rest on it (`.assuming`). */
  case OutsideAsPart(fact: NodeId, whole: NodeId)
  /** A fact about the outside claimed: only an assumption can say one, since nothing in FrFlow proves it. */
  case OutsideClaimed(id: NodeId)
  // The world outside (owner §16, §17)
  /** A statement whose check rests on a fact about the outside its `.assuming` does not list (the one mechanism for
    * a premise, owner §15; `Premises` derives what each needs): a claim about a program's runs on a store needs
    * `store.behavesAs(stored)` and `stored.changedOneRunAtATime`; an `always(stored)` those and
    * `stored.initially(…)` and `stored.writtenOnlyBy(…)`; an `always[T]` what values from outside meet (owner §21:
    * an assumption of `always` on `T` when the outside passes `T`s in, and each such assumption on the values from
    * outside its `T`s are made from), the store facts of each store holding a `T`, and the model of each store
    * operation making one. `by` is the assumption that says it, if one does; when none does, what to say is
    * `needs` (for values from outside, `Node.assumption("…")(always[T](x => …))`).
    */
  case PremiseMissing(id: NodeId, needs: Premise, by: Option[NodeId])
  /** A fact about the outside a statement's `.assuming` lists that its check does not rest on. */
  case PremiseNotNeeded(id: NodeId, premise: NodeId)
  /** A program writing the store that the store's `writtenOnlyBy` does not list. */
  case WriterNotListed(model: ModelName, program: SymbolName)
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
  case CodeOnlyInStatement(id: NodeId, symbol: SymbolName)
  // Declarations and Definitions (owner §15)
  /** A Definition nothing gives a meaning: no code, no program, no value fixed or provided where code runs. */
  case Undefined(definition: SymbolName)
  /** A Declaration reached from code: a program's steps, or a define that code runs, mentions it. */
  case DeclarationInCode(code: DefName, declaration: SymbolName)
  /** Code for a Definition no statement mentions: there is nothing to check it against. */
  case CodeWithoutClaim(definition: SymbolName)
  // Programs and their errors (`Failing`)
  /** A program whose steps may end in errors of two types or more: a run fails with one. */
  case ErrorsDiffer(program: DefName, errors: List[Ty])
  /** A failing run's clause (`.failing { (error: E, after) => … }`) of another type than the program fails with. */
  case FailingDiffers(id: NodeId, program: SymbolName, clause: Ty, error: Ty)
  /** A failing run's clause on a program that cannot fail: it raises nothing and calls no failing boundary outside a
    * handler.
    */
  case NeverFails(id: NodeId, program: SymbolName)

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
