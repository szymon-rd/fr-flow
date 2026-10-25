package frflow.api

import frflow.protocol.*
import scala.util.control.NoStackTrace

/** What fails a command (refusals a user reads are `Refusal`s instead): mapped once, at each front end. */
enum FrFlowError(val message: String) extends Exception(message) with NoStackTrace:
  /** The model does not hold together: nothing else is computed until it does. */
  case ModelProblems(problems: List[String]) extends FrFlowError(problems.mkString("\n"))
  case UnknownNode(id: NodeId) extends FrFlowError(s"unknown node $id")
  case LeanMissing extends FrFlowError("lake not found (set FRFLOW_LAKE)")
