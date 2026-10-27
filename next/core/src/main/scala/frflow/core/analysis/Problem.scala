package frflow.core.analysis

import frflow.core.name.{DefName, ModelName, NodeId, SymbolName}

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
  /** A part of a node checked against proven code that is not a statement about what the code calls: the node is
    * proven by `impl` from its parts, so a part must be one.
    */
  case PartNotCalled(id: NodeId, part: NodeId)
