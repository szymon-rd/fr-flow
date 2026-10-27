package frflow.testing.report

import frflow.core.name.OpName

/** What a test must reach of a part: an implication's premise holding, a side of an or holding, a condition
  * holding and not, a match's arm taken, a list or option a quantifier ranges over not empty; in a model test, an
  * operation called.
  */
enum Reach:
  case Premise
  case Side(index: Int)
  case Branch(held: Boolean)
  case Arm(index: Int)
  case NonEmpty
  case Called(op: OpName)
