package frflow.core.code

import frflow.core.name.{DefName, SymbolName}

/** The code attached to an operation: a proven define, production code beside one, a proven flow (its run on the
  * models is the vocabulary's `RunOf` define), or plain code tested against the promise.
  */
enum Code:
  case Proven(define: DefName)
  case ProvenBeside(define: DefName, runs: ScalaCode)
  case ProvenFlow(flow: DefName)
  case Tested(runs: ScalaCode, calls: List[SymbolName])

  /** The define Lean proves, if any. */
  def proven: Option[DefName] = this match
    case Proven(d)          => Some(d)
    case ProvenBeside(d, _) => Some(d)
    case ProvenFlow(f)      => Some(f)
    case Tested(_, _)       => None

  /** The Scala code the operation runs, if any: plain code, or production code beside a define. */
  def scala: Option[ScalaCode] = this match
    case Tested(r, _)       => Some(r)
    case ProvenBeside(_, r) => Some(r)
    case _                  => None
