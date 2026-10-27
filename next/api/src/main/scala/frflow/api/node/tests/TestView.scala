package frflow.api.node.tests

/** What testing a node's code before production found: the cases asked and tried, from which seed; what the code was
  * tested against; the outcome; the targets no case reached; and the notes (the generators given, the examples'
  * values one never makes, nothing to vary).
  */
final case class TestView(cases: Cases, against: Against, outcome: TestOutcome, unreached: List[Target],
    notes: List[Note])
