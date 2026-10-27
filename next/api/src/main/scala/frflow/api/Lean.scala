package frflow.api

/** What Lean says in memory (`FrFlowApi.inMemory`), so front ends are tested without it: it proves every obligation
  * of the model as written but the theorems named `failing` (an error at each), and shows no try but those named
  * `shown` (`example_0`, `restates`, …); or it is not installed.
  */
enum Lean:
  case Proving(failing: Set[String], shown: Set[String])
  case Absent
