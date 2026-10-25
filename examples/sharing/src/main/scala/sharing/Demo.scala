package sharing

import sharing.domain.*

/** A small library the examples and the demo server start from.
  *  - Ann may edit the plan, and everything in the reports folder.
  *  - The engineering team (Bob) may view everything in the reports folder.
  *  - Cat has no share at all.
  *  - The Q3 report is in the q3 folder, inside reports.
  */
object Demo:
  val ann = PersonId("ann")
  val bob = PersonId("bob")
  val cat = PersonId("cat")
  val eng = TeamId("eng")
  val reports = FolderId("reports")
  val q3 = FolderId("q3")
  val plan = DocumentId("plan")
  val q3Report = DocumentId("q3-report")

  val annEditsPlan = Share(Target.Doc(plan), Grantee.Person(ann), Level.Edit)
  val annEditsReports = Share(Target.InFolder(reports), Grantee.Person(ann), Level.Edit)
  val engViewsReports = Share(Target.InFolder(reports), Grantee.Team(eng), Level.View)

  val library = Library(
    documents = List(Document(plan, "Plan", Nil), Document(q3Report, "Q3 report", List(reports, q3))),
    folders = List(Folder(reports, "Reports", Nil), Folder(q3, "Q3", List(reports))),
    teams = List(Team(eng, List(bob))),
    shares = List(annEditsPlan, annEditsReports, engViewsReports))
