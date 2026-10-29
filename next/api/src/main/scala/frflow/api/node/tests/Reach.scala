package frflow.api.node.tests

import frflow.core.name.SymbolName

/** What a test must reach of a part: an implication's premise holding, a side of an or, a condition holding and
  * not, a match's arm, a list or option not empty; in a model test, an operation called.
  */
enum Reach:
  case Premise
  case Side(index: Int)
  case Branch(held: Boolean)
  case Arm(index: Int)
  case NonEmpty
  case Called(op: SymbolName)
