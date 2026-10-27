package frflow.reference

import frflow.{ContractViolation, FrModel, Node}
import frflow.example.ExampleResult

/** One seeded bug: what is seeded, where today's suites seed it, and what stops it today, as lines. */
final case class Seeded(name: String, inTable: Boolean, seeded: String, suite: String, stops: List[String]):
  def lines: List[String] =
    val where = if inTable then "in section 9's table" else "also seeded in today's suites"
    List(s"## $name ($where)", "", s"seeded: $seeded", s"suite: $suite", "") ++ stops ++ List("")

/** What stops a seeded bug: the check on a call, the examples, or the generated cases. */
object Stops:
  private def indented(text: String): List[String] = text.linesIterator.map("    " + _).toList

  /** The call of the seeded code, as a service runs it: the `ContractViolation` it throws, or its result. */
  def onCall(call: String)(run: => Any): List[String] =
    val outcome =
      try List(s"  not stopped: returned ${frflow.example.Example.show(run)}")
      catch case e: ContractViolation => "  stopped by: ContractViolation" :: indented(e.getMessage)
    s"on the call: $call" :: outcome

  /** The node's examples run against the seeded code: those whose implementation verdict is not ok. */
  def examples(kb: FrModel, n: Node[?]): List[String] =
    val results = kb.exampleResults(n)
    val failing = results.filter(_.implementation.exists(_ != "ok"))
    s"the examples of ${n.id}: ${results.size} run, ${failing.size} failing on the implementation" ::
      failing.flatMap(r => s"  ${r.example.note}" :: indented(r.verdict))

  /** The generated cases (or runs) of the node's code: the failure, shrunk, with the seed, index and size that remake
    * it.
    */
  def generated(kb: FrModel, n: Node[?]): List[String] =
    kb.test(n) match
      case None => List(s"generated cases of ${n.id}: none (not tested)")
      case Some(r) =>
        val head = s"generated cases of ${n.id}: ${r.cases} against ${r.against}, seed ${r.seed}"
        r.failure match
          case None => List(head, "  every case passes")
          case Some(f) =>
            List(head, s"  fails at seed ${f.seed}, index ${f.index}, size ${f.size}", "  case:") ++
              indented(f.shown) ++
              ("  why:" :: indented(f.why))

  /** The example runs of a node whose note says `kind` (a fault sweep, interleavings), with their verdicts. */
  def runs(kb: FrModel, n: Node[?], kind: String): List[String] =
    kb.exampleResults(n).filter(_.example.note.contains(kind)).map(r => s"  ${r.example.note}: ${verdict(r)}")

  private def verdict(r: ExampleResult): String =
    s"contract ${r.contract}, implementation ${r.implementation.getOrElse("not run")}"
