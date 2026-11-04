package sharing.examples

import frflow.*
import sharing.Demo.*
import sharing.knowledge
import sharing.domain.*
import sharing.features.Invitations
import sharing.features.Sharing

// Today's examples of who can see and change what (access, sharing, moving, invitations), one class per contract
// they were written on (owner §18), each on the demo library: given nothing, each is checked against the code in
// Scala and tried against the claims in Lean.

/** On any FrModel of sharing: the seeded bug's code is judged by them too. */
class AccessExamples(kb: FrModel = knowledge) extends FrFlowExamples(kb):
  example("Bob's team may view the reports folder, which the Q3 report is in"):
    Sharing.access(library, now, bob, q3Report) is Some(Level.View)
  example("Ann may edit the reports folder"):
    Sharing.access(library, now, ann, q3Report) is Some(Level.Edit)
  example("nothing is shared with Cat"):
    Sharing.access(library, now, cat, plan) is None
  example("Bob's share of the plan is in force"):
    Sharing.access(library.copy(shares = bobViewsPlanForAnHour :: library.shares), now, bob, plan) is Some(Level.View)
  example("Bob's share of the plan has ended"):
    Sharing.access(library.copy(shares = bobViewsPlanForAnHour :: library.shares), now + 3600, bob, plan) is None
  example("the plan is in the trash"):
    Sharing.access(library.copy(documents = List(planTrashed, q3ReportDoc)), now, ann, plan) is None
  example("nothing shares the plan with Bob or his team"):
    (Sharing.access(library, now, bob, plan) is Some(Level.View)) is false
  example("Ann's share of the plan is an edit share: her access is edit"):
    (Sharing.access(library, now, ann, plan) is Some(Level.View)) is false

class CanViewExamples extends FrFlowExamples(knowledge):
  example("Bob's team may view the reports folder"):
    Sharing.canView(library, now, bob, q3Report) is true
  example("nothing is shared with Cat"):
    Sharing.canView(library, now, cat, q3Report) is false
  example("Cat has no access to the plan"):
    (Sharing.canView(library, now, cat, plan) is true) is false

class CanEditExamples extends FrFlowExamples(knowledge):
  example("Ann may edit the reports folder, around the Q3 report"):
    Sharing.canEdit(library, now, ann, q3Report) is true
  example("Bob's team may only view it"):
    Sharing.canEdit(library, now, bob, q3Report) is false
  example("a view share never lets anyone edit"):
    (Sharing.canEdit(library, now, bob, q3Report) is true) is false

class ShareExamples extends FrFlowExamples(knowledge):
  private val bobViewsPlan = Share(Target.Doc(plan), Grantee.Person(bob), Level.View, None)
  private val catViewsReports = Share(Target.InFolder(reports), Grantee.Person(cat), Level.View, None)
  private val bobEditsPlan = Share(Target.Doc(plan), Grantee.Person(bob), Level.Edit, None)
  example("Ann may edit the plan, so she shares it with Bob"):
    Sharing.share(library, now, ann, bobViewsPlan) is library.copy(shares = bobViewsPlan :: library.shares)
  example("Ann shares the plan with Bob for an hour"):
    Sharing.share(library, now, ann, bobViewsPlanForAnHour) is
      library.copy(shares = bobViewsPlanForAnHour :: library.shares)
  example("Bob may not edit the plan: his request changes nothing"):
    Sharing.share(library, now, bob, Share(Target.Doc(plan), Grantee.Person(bob), Level.Edit, None)) is library
  example("Bob may only view the reports folder, so he cannot share it"):
    (Sharing.share(library, now, bob, catViewsReports) is
      library.copy(shares = catViewsReports :: library.shares)) is false
  example("Bob may edit the plan, but Ann owns it: her edit share stays as it is"):
    Sharing.share(library.copy(shares = bobEditsPlan :: library.shares), now, bob, Share(Target.Doc(plan),
      Grantee.Person(ann), Level.View, Some(now + 3600))) is library.copy(shares = bobEditsPlan :: library.shares)

class UnshareExamples extends FrFlowExamples(knowledge):
  private val bobEditsPlan = Share(Target.Doc(plan), Grantee.Person(bob), Level.Edit, None)
  example("Ann may edit the reports folder, so she unshares it from the engineering team"):
    Sharing.unshare(library, now, ann, Target.InFolder(reports), Grantee.Team(eng)) is
      library.copy(shares = List(annEditsPlan, annEditsReports))
  example("Bob may only view the folder: his request changes nothing"):
    Sharing.unshare(library, now, bob, Target.InFolder(reports), Grantee.Team(eng)) is library
  example("Bob may edit the plan, but Ann owns it: her share stays"):
    Sharing.unshare(library.copy(shares = bobEditsPlan :: library.shares), now, bob, Target.Doc(plan),
      Grantee.Person(ann)) is library.copy(shares = bobEditsPlan :: library.shares)
  example("Bob cannot take Ann's share of the plan away"):
    (Sharing.unshare(library, now, bob, Target.Doc(plan), Grantee.Person(ann)) is
      library.copy(shares = List(annEditsReports, engViewsReports))) is false

class MoveExamples extends FrFlowExamples(knowledge):
  example("Ann may edit the plan and the reports folder: the plan moves into it"):
    Sharing.move(library, now, ann, plan, Some(reports)) is
      library.copy(documents = List(planDoc.copy(folders = List(reports)), q3ReportDoc))
  example("Bob may only view the Q3 report: it stays where it is"):
    Sharing.move(library, now, bob, q3Report, None) is library
  example("a document never moves into a folder that does not exist"):
    (Sharing.move(library, now, ann, plan, Some(FolderId("nowhere"))) is
      library.copy(documents = List(planDoc.copy(folders = List(FolderId("nowhere"))), q3ReportDoc))) is false

class InviteExamples extends FrFlowExamples(knowledge):
  private val withCat = library.copy(invitations = List(catInvited))
  example("Ann may edit the plan: she invites Cat to view it"):
    Invitations.invite(library, now - day, ann, cat, Target.Doc(plan), Level.View) is withCat
  example("Bob may not edit the plan: nothing changes"):
    Invitations.invite(library, now, bob, cat, Target.Doc(plan), Level.View) is library
  example("Bob may only view the reports folder, so he cannot invite anyone to it"):
    (Invitations.invite(library, now, bob, cat, Target.InFolder(reports), Level.View) is
      library.copy(invitations = List(Invitation(cat, Target.InFolder(reports), Level.View, bob, now)))) is false

class AcceptExamples extends FrFlowExamples(knowledge):
  private val withCat = library.copy(invitations = List(catInvited))
  private val annInvited = library.copy(invitations = List(Invitation(ann, Target.Doc(plan), Level.View, bob,
      now - day)))
  private val catViewsPlan = Share(Target.Doc(plan), Grantee.Person(cat), Level.View, None)
  example("Cat accepts Ann's invitation, sent a day ago: she may view the plan"):
    Invitations.accept(withCat, now, cat, Target.Doc(plan)) is library.copy(shares = catViewsPlan :: library.shares)
  example("eight days after it was sent the invitation has lapsed"):
    Invitations.accept(withCat, now + 7 * day, cat, Target.Doc(plan)) is withCat
  example("Bob was not invited"):
    Invitations.accept(withCat, now, bob, Target.Doc(plan)) is withCat
  example("Ann owns the plan: accepting a view invitation to it changes nothing"):
    Invitations.accept(annInvited, now, ann, Target.Doc(plan)) is annInvited
  example("a lapsed invitation is never accepted"):
    (Invitations.accept(withCat, now + 7 * day, cat, Target.Doc(plan)) is
      library.copy(shares = catViewsPlan :: library.shares)) is false

class WithdrawExamples extends FrFlowExamples(knowledge):
  private val withCat = library.copy(invitations = List(catInvited))
  example("Ann withdraws Cat's invitation"):
    Invitations.withdraw(withCat, now, ann, cat, Target.Doc(plan)) is library
  example("Bob may not edit the plan: the invitation stays"):
    Invitations.withdraw(withCat, now, bob, cat, Target.Doc(plan)) is withCat
  example("only an editor withdraws an invitation"):
    (Invitations.withdraw(withCat, now, bob, cat, Target.Doc(plan)) is library) is false
