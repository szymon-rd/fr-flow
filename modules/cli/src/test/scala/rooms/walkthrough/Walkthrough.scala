package rooms.walkthrough

import frflow.api.Project
import frflow.core.example.Example
import frflow.dsl.example.FrFlowExamples
import frflow.dsl.kb.FrModel

/** The walk-through's steps, and what each prints, against its golden (`resources/rooms/walkthrough`). */
object Walkthrough:
  private def resource(path: String): String =
    scala.io.Source.fromResource(path, getClass.getClassLoader)(using scala.io.Codec.UTF8).mkString

  /** The developer's proofs, as rooms' project keeps them and `PortSuite` writes them. */
  val proofs: List[(String, String)] = List("Lemmas", "storeWhenFree", "answerWhenFree", "grantWhenFree",
    "neverOverlap", "roomBookingsApart").map(n => n -> frflow.project.Ported.proof("rooms", "Rooms", n))

  /** Rooms as accepted, then each change on its own, by the step's name. */
  def steps(project: (FrModel, List[Example]) => Project, examples: FrFlowExamples => List[Example])
      : List[(String, Project)] =
    val granted = examples(rooms.GrantedExamples())
    List("base" -> project(rooms.rooms, granted),
      "4-code-forgets-the-next-booking" -> project(forgets, granted),
      "5-misread-overlap" -> project(misread.misread, examples(misread.GrantedExamples())),
      "6-misread-reaches-the-claim" -> project(reaches.reaches,
        examples(reaches.GrantedExamples())))

  /** What the port prints, its dates left out (a decision's time is the run's). */
  def normal(text: String): String = text.replaceAll("""\d{4}-\d\d-\d\d \d\d:\d\d""", "<when>")

  def golden(step: String, what: String): String = resource(s"rooms/walkthrough/$step/$what.txt")
