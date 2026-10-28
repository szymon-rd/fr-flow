package rooms

import cats.effect.IO
import frflow.api.Project
import frflow.core.example.Example
import frflow.dsl.example.FrFlowExamples
import frflow.dsl.kb.FrModel
import java.nio.file.{Files, Path}

/** The walk-through's steps on the port, and what each prints, against its golden (`resources/rooms/walkthrough`)
  * and against today's (`reference/rooms/walkthrough`): each node's mark in `check` and `status`, the nodes back for
  * review, and the exit code, every difference judged (`WalkthroughDifferences`).
  */
object Walkthrough:
  private def resource(path: String): String =
    scala.io.Source.fromResource(path, getClass.getClassLoader)(using scala.io.Codec.UTF8).mkString

  /** The developer's proofs, as `PortSuite` writes them. */
  val proofs: List[(String, String)] = List("Lemmas", "storeWhenFree", "answerWhenFree", "grantWhenFree",
    "neverOverlap", "roomBookingsApart").map(n => n -> resource(s"rooms/proofs/$n.lean"))

  /** Rooms as accepted, then each change on its own: the step's name in `reference/rooms/walkthrough`. */
  def steps(project: (FrModel, List[Example]) => Project[IO], examples: FrFlowExamples => List[Example])
      : List[(String, Project[IO])] =
    val granted = examples(GrantedExamples())
    List("base" -> project(rooms, granted),
      "4-code-forgets-the-next-booking" -> project(walkthrough.forgets.forgets, granted),
      "5-misread-overlap" -> project(walkthrough.misread.misread, examples(walkthrough.misread.GrantedExamples())),
      "6-misread-reaches-the-claim" -> project(walkthrough.reaches.reaches,
        examples(walkthrough.reaches.GrantedExamples())))

  /** What the port prints, its dates left out (a decision's time is the run's). */
  def normal(text: String): String = text.replaceAll("""\d{4}-\d\d-\d\d \d\d:\d\d""", "<when>")

  def golden(step: String, what: String): String = resource(s"rooms/walkthrough/$step/$what.txt")

  /** Today's text of a step: its check and status (the base's are the capture's own). */
  def today(step: String, what: String): String =
    val dir = Path.of("reference/rooms")
    Files.readString(if step == "base" then dir.resolve(s"$what.txt")
      else dir.resolve("walkthrough").resolve(step).resolve(s"$what.txt"))

  /** Where the port's step differs from today's, as `kind node: today -> now`. */
  def differences(step: String, check: String, status: String): List[String] =
    val (wasCheck, nowCheck) = (marks(today(step, "check")), marks(check))
    val ((wasTree, wasReview), (nowTree, nowReview)) = (todayTree(today(step, "status")), tree(status))
    val checked = nowCheck.keys.toList.sorted.filter(n => wasCheck.get(n) != nowCheck.get(n))
      .map(n => s"check $n: ${wasCheck.getOrElse(n, "none")} -> ${nowCheck(n)}")
    val placed = (wasTree.keySet ++ nowTree.keySet).toList.sorted.filter(n => wasTree.get(n) != nowTree.get(n))
      .map(n => s"status $n: ${wasTree.getOrElse(n, "none")} -> ${nowTree.getOrElse(n, "none")}")
    val back = (wasReview ++ nowReview).toList.sorted.filter(n => wasReview(n) != nowReview(n))
      .map(n => s"review $n: ${if wasReview(n) then "back" else "kept"} -> ${if nowReview(n) then "back" else "kept"}")
    val exits = Option.when(exit(today(step, "check")) != exit(check))(
      s"check exit: ${exit(today(step, "check"))} -> ${exit(check)}").toList
    checked ++ placed ++ back ++ exits

  private def marks(t: String): Map[String, String] =
    """(?m)^([+\-xo?!]) (\w+): """.r.findAllMatchIn(t).map(m => m.group(2) -> m.group(1)).toMap

  private def todayTree(t: String): (Map[String, String], Set[String]) =
    val line = """^[|`\- ]*?([+\-xo?!.]) (\w+)( \(assumption\))?(:| —)(.*)$""".r
    val found = t.linesIterator.toList.flatMap(l => line.findFirstMatchIn(l).filterNot(_ => l.contains("-> "))
      .map(m => (m.group(2), m.group(1), m.group(5).contains("review it"))))
    (found.map((n, k, _) => n -> k).toMap, found.collect { case (n, _, true) => n }.toSet)

  private def tree(t: String): (Map[String, String], Set[String]) =
    val line = """^\s*([+\-xo?!.]) (\w+)  (claim|assumption|design)  (accepted|to review|proposed|rejected)""".r
    val found = t.linesIterator.toList.flatMap(l => line.findFirstMatchIn(l)
      .map(m => (m.group(2), m.group(1), m.group(4) == "to review")))
    (found.map((n, k, _) => n -> k).toMap, found.collect { case (n, _, true) => n }.toSet)

  private def exit(t: String): String = """--- exit (\d+)""".r.findFirstMatchIn(t).fold("none")(_.group(1))
