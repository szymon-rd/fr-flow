package frflow.reference

import _root_.sharing.knowledge
import _root_.sharing.domain.*
import _root_.sharing.service.Sharing

/** sharing's generated runs (the fault sweep and the interleavings over each flow's examples), and the seeded bug and
  * scheduler faults of `SharingSuite`.
  */
object SharingRuns:
  def all: List[Seeded] = List(sweep("fault sweep", "failing boundary failing"),
    sweep("interleavings", "its branches at once"), forgetful) ++ SchedulerFaults.all

  private def sweep(name: String, note: String): Seeded =
    val lines = knowledge.nodes.flatMap { n =>
      val runs = Stops.runs(knowledge, n, note)
      if runs.isEmpty then Nil else s"${n.id}: ${runs.size} runs" :: runs
    }
    Seeded(name, inTable = true, s"each flow's examples, run with the note \"$note\" (no bug: every run must pass)",
      "the examples' runs that check reads (ExampleRuns), also in SharingSuite: the examples pass", lines)

  private def forgetful: Seeded =
    val forgets: (Library, BigInt, PersonId, DocumentId) => Option[Level] = (lib, now, p, d) =>
      if lib.documents.exists(doc => doc.id == d && doc.trashed.isDefined) then None
      else
        val teams = lib.teams.filter(_.members.contains(p)).map(t => Grantee.Team(t.id))
        val places = Target.Doc(d) :: lib.documents.filter(_.id == d).flatMap(_.folders.map(Target.InFolder(_)))
        val mine = lib.shares.filter(s => (s.withWhom == Grantee.Person(p) || teams.contains(s.withWhom)) &&
          places.contains(s.what))
        if mine.exists(_.level == Level.Edit) then Some(Level.Edit) else mine.headOption.map(_ => Level.View)
    val kb = knowledge.implementTested(Sharing.accessContract)(forgets)
    Seeded("access that forgets the end of shares", inTable = false,
      "accessContract implemented in plain Scala that ignores when a share ends",
      "SharingSuite: a seeded bug (plain Scala access that forgets the end of shares) passes some examples; the " +
        "generated cases find it",
      Stops.examples(kb, Sharing.accessContract) ++ Stops.generated(kb, Sharing.accessContract))
