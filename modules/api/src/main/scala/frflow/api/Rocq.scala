package frflow.api

/** What Rocq says in memory (`FrFlowApi.inMemory`), so front ends are tested without it: it proves every obligation
  * of the model as written but the lemmas named `failing` (each not accepted), and shows no try but those named
  * `shown` (`example_Examples_0`, `restates`, …); or it is not installed.
  */
enum Rocq:
  case Proving(failing: Set[String], shown: Set[String])
  case Absent
