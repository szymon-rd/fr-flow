package frflow.dsl.build

import frflow.core.name.RelPath

/** What is wrong with a part of a model, wherever it is found: in a term being built, a constant, a path, a link. */
enum Fault:
  case DeclaredLater
  case NoType(where: String)
  case FunctionEquality
  case NotData(value: String)
  /** A field the record's type does not have (a selector the derivation did not make). */
  case NoField(name: String)
  /** A value only plain code reads, its Scala type with no `LeanType`, spoken of in a statement (its field selected):
    * the type can derive one if a statement should speak of it.
    */
  case CodeOnlyInStatement(scalaType: String)
  case BadPath(path: String, why: RelPath.Invalid)
  /** `.leftOpenAbove` on a node that is not a claim. */
  case NotAClaim(what: String)
  case OutsideStep
  /** A program's step gave a value that is not a term (nor the unit): Lean cannot read it. */
  case NotATerm(what: String)
  /** A program's step that applies no Definition (`f.step(t)` of a term of a program type that is no call): a step
    * is an operation on a state applied (`inRoom(request.room)`).
    */
  case NotAnOperation(what: String)
  /** The Scala of operations on a state given for Definitions no one model gives a meaning (`implementTested(ops*)`
    * of an operation no model's body means, or of operations of two models).
    */
  case NotOneModel(definitions: List[String])
  /** The Scala of a model's operations given for some of them only: `missing` have none. */
  case OperationsMissing(model: String, missing: List[String])
  /** An operation on a state given another meaning than its model's (`implementProven`, `implementValue`, …): its
    * Scala is given with `implementTested(ops*)(start, observe)(calls)`.
    */
  case ModelledElsewhere(definition: String)
  /** An operation on a state given a meaning by two models. */
  case MeantByTwo(definition: String, models: List[String])
  /** A program given on the spot mentioned in a statement: it is the meaning `implementProven` gives the Definition
    * the statements speak of.
    */
  case ProgramMentioned(program: String)
  /** `implementProven` given a Definition that is not a `define` or a `program`. */
  case NotProvenCode(definition: String)
  /** A meaning given to a Definition that has its own where it is written (`define`, `program`). */
  case MeantWhereWritten(definition: String)
  /** A program's run in a statement (`.result`, `.after`) of a variable bound inside the statement: a run is of the
    * statement's leading variables, from the world it holds in (owner §41).
    */
  case RunInside(program: String)
  /** The world read where nothing holds one (owner §41, §43): `where` is an `always` rule, a model's `initially`, a
    * program's step or an operation's meaning, which read state through their own values and operations.
    */
  case WorldRead(where: String)
  case Thrown(message: String)
