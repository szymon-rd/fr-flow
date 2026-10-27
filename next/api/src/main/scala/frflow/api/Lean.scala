package frflow.api

/** What Lean says in memory (`FrFlowApi.inMemory`), so front ends are tested without it: it proves every obligation
  * of the model as written and no try, but the theorems named `failing` (an error at each); or it is not installed.
  */
enum Lean:
  case Proving(failing: Set[String])
  case Absent
