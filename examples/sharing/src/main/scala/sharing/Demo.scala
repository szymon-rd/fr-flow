package sharing

import sharing.domain.*

/** A small library the examples and the demo server start from, at a moment `now` (in seconds).
  *  - Ann may edit the plan, and everything in the reports folder.
  *  - The engineering team (Bob) may view everything in the reports folder.
  *  - Cat has no share at all; nobody is invited or asking; nothing is in the trash; the log and the outbox are empty.
  *  - Ann owns both documents.
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

  /** The moment the examples are decided at, and a day in seconds. */
  val now = BigInt(1000000)
  val day = BigInt(86400)

  val annEditsPlan = Share(Target.Doc(plan), Grantee.Person(ann), Level.Edit, None)
  val annEditsReports = Share(Target.InFolder(reports), Grantee.Person(ann), Level.Edit, None)
  val engViewsReports = Share(Target.InFolder(reports), Grantee.Team(eng), Level.View, None)

  val planDoc = Document(plan, "Plan", Nil, None, ann)
  val q3ReportDoc = Document(q3Report, "Q3 report", List(reports, q3), None, ann)

  val library = Library(
    documents = List(planDoc, q3ReportDoc),
    folders = List(Folder(reports, "Reports", Nil), Folder(q3, "Q3", List(reports))),
    teams = List(Team(eng, List(bob))),
    shares = List(annEditsPlan, annEditsReports, engViewsReports),
    invitations = Nil, requests = Nil, log = Nil, outbox = Nil)

  /** Cat, invited by Ann a day before `now` to view the plan. */
  val catInvited = Invitation(cat, Target.Doc(plan), Level.View, ann, now - day)
  /** Bob may view the plan until an hour after `now`. */
  val bobViewsPlanForAnHour = Share(Target.Doc(plan), Grantee.Person(bob), Level.View, Some(now + 3600))
  /** The plan, put in the trash a day before `now`. */
  val planTrashed = planDoc.copy(trashed = Some(now - day))
