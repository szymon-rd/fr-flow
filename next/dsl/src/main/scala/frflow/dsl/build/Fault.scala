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
  /** A program given on the spot mentioned in a statement: it is the meaning `implementProven` gives the Definition
    * the statements speak of.
    */
  case ProgramMentioned(program: String)
  /** `implementProven` given a Definition that is not a `define` or a `program`. */
  case NotProvenCode(definition: String)
  /** A meaning given to a Definition that has its own where it is written (`define`, `program`). */
  case MeantWhereWritten(definition: String)
  case Thrown(message: String)
