package frflow.api.view

import cats.data.NonEmptyChain
import frflow.core.analysis.Problem
import frflow.core.name.NodeId

/** What stops an operation, raised in `F` (the front end says it and exits): the model has structural problems;
  * Lean's build tool does not run; a node named that the model does not have; a file FrFlow must read (the ledger) is
  * not JSON, has no version, a version this FrFlow does not read, or a field that does not read; the developer's
  * signing key is missing, or is not a key. What elaboration refuses is not among them: a project is opened
  * elaborated (`Project.model`), so the front end says it before.
  */
enum Stop extends scala.util.control.NoStackTrace:
  case Invalid(problems: NonEmptyChain[Problem])
  case NoLean
  case UnknownNode(id: NodeId)
  case NotJson(file: String, problem: String)
  case NoVersion(file: String)
  case UnknownVersion(file: String, version: Int, reads: Int)
  case BadField(file: String, version: Int, field: String, problem: String)
  case NoKey(file: String)
  case NotAKey(file: String, problem: String)
