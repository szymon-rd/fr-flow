package sharing.examples

import frflow.*
import sharing.Demo.*
import sharing.knowledge
import sharing.features.Audit
import sharing.domain.*
import sharing.features.Ownership
import sharing.features.AccessRequests
import sharing.features.Trash

// Today's examples of the trash, access requests, ownership and the log, one class per contract they were
// written on (owner §18), each on the demo library: given nothing, each is checked against the code in Scala and
// tried against the claims in Lean.

class TrashExamples extends FrFlowExamples(knowledge):
  private val planInTrash = library.copy(documents = List(planTrashed, q3ReportDoc))
  example("Ann may edit the plan: it goes to the trash"):
    Trash.trash(library, now - day, ann, plan) is planInTrash
  example("already in the trash: it keeps its time"):
    Trash.trash(planInTrash, now, ann, plan) is planInTrash
  example("Bob may not edit the plan"):
    Trash.trash(library, now, bob, plan) is library
  example("Bob may only view the Q3 report: he cannot delete it"):
    (Trash.trash(library, now, bob, q3Report) is
      library.copy(documents = List(planDoc, q3ReportDoc.copy(trashed = Some(now))))) is false

class RestoreExamples extends FrFlowExamples(knowledge):
  private val planInTrash = library.copy(documents = List(planTrashed, q3ReportDoc))
  example("a day in the trash: Ann restores the plan"):
    Trash.restore(planInTrash, now, ann, plan) is library
  example("thirty days in the trash: it is gone"):
    Trash.restore(planInTrash, now + 29 * day, ann, plan) is planInTrash
  example("Bob may not edit the plan"):
    Trash.restore(planInTrash, now, bob, plan) is planInTrash
  example("a document gone is never restored"):
    (Trash.restore(planInTrash, now + 40 * day, ann, plan) is library) is false

class AskExamples extends FrFlowExamples(knowledge):
  private val catAsks = AccessRequest(cat, Target.Doc(plan), Level.View, now - day, false)
  private val catAsksForReports = AccessRequest(cat, Target.InFolder(reports), Level.View, now - day, false)
  private val withCatAsking = library.copy(requests = List(catAsks))
  private val catViewsPlan = Share(Target.Doc(plan), Grantee.Person(cat), Level.View, None)
  example("Cat asks to view the plan"):
    AccessRequests.ask(library, now - day, cat, Target.Doc(plan), Level.View) is withCatAsking
  example("Cat asks to view the reports folder"):
    AccessRequests.ask(library, now - day, cat, Target.InFolder(reports), Level.View) is
      library.copy(requests = List(catAsksForReports))
  example("no such document: nothing changes"):
    AccessRequests.ask(library, now, cat, Target.Doc(DocumentId("nowhere")), Level.View) is library
  example("asking gives no access"):
    (AccessRequests.ask(library, now, cat, Target.Doc(plan), Level.View) is
      library.copy(shares = catViewsPlan :: library.shares)) is false

class ApproveExamples extends FrFlowExamples(knowledge):
  private val catAsks = AccessRequest(cat, Target.Doc(plan), Level.View, now - day, false)
  private val withCatAsking = library.copy(requests = List(catAsks))
  private val catViewsPlan = Share(Target.Doc(plan), Grantee.Person(cat), Level.View, None)
  private val annAsks = library.copy(requests = List(AccessRequest(ann, Target.Doc(plan), Level.View, now - day,
      false)))
  example("Ann approves: Cat may view the plan"):
    AccessRequests.approve(withCatAsking, now, ann, cat, Target.Doc(plan)) is
      library.copy(shares = catViewsPlan :: library.shares)
  example("Bob may not edit the plan: the request stays"):
    AccessRequests.approve(withCatAsking, now, bob, cat, Target.Doc(plan)) is withCatAsking
  example("eight days on the request has lapsed"):
    AccessRequests.approve(withCatAsking, now + 7 * day, ann, cat, Target.Doc(plan)) is withCatAsking
  example("Ann owns the plan: her request for view of it changes nothing"):
    AccessRequests.approve(annAsks, now, ann, ann, Target.Doc(plan)) is annAsks
  example("only an editor approves"):
    (AccessRequests.approve(withCatAsking, now, bob, cat, Target.Doc(plan)) is
      library.copy(shares = catViewsPlan :: library.shares)) is false

class DeclineExamples extends FrFlowExamples(knowledge):
  private val catAsks = AccessRequest(cat, Target.Doc(plan), Level.View, now - day, false)
  private val withCatAsking = library.copy(requests = List(catAsks))
  example("Ann declines Cat's request"):
    AccessRequests.decline(withCatAsking, now, ann, cat, Target.Doc(plan)) is library
  example("Bob may not edit the plan: the request stays"):
    AccessRequests.decline(withCatAsking, now, bob, cat, Target.Doc(plan)) is withCatAsking
  example("only an editor declines"):
    (AccessRequests.decline(withCatAsking, now, bob, cat, Target.Doc(plan)) is library) is false

class ChaseExamples extends FrFlowExamples(knowledge):
  private val catAsks = AccessRequest(cat, Target.Doc(plan), Level.View, now - day, false)
  private val withCatAsking = library.copy(requests = List(catAsks))
  private val catAskedLongAgo = AccessRequest(cat, Target.Doc(plan), Level.View, now - 3 * day, false)
  example("asked a day ago: nothing to do"):
    AccessRequests.chase(withCatAsking, now) is withCatAsking
  example("asked three days ago: Ann, the plan's owner, is reminded"):
    AccessRequests.chase(library.copy(requests = List(catAskedLongAgo)), now) is
      library.copy(requests = List(catAskedLongAgo.copy(reminded = true)),
        outbox = List(Notice(ann, Subject.Reminder(catAskedLongAgo))))
  example("eight days on: declined, and Cat is told"):
    AccessRequests.chase(withCatAsking, now + 7 * day) is
      library.copy(outbox = List(Notice(cat, Subject.Lapsed(catAsks))))
  example("a request is reminded of once"):
    (AccessRequests.chase(library.copy(requests = List(catAskedLongAgo.copy(reminded = true))), now) is
      library.copy(requests = List(catAskedLongAgo.copy(reminded = true)),
        outbox = List(Notice(ann, Subject.Reminder(catAskedLongAgo))))) is false

class TransferExamples extends FrFlowExamples(knowledge):
  private val bobEditsPlan = Share(Target.Doc(plan), Grantee.Person(bob), Level.Edit, None)
  private val bobMayEdit = library.copy(shares = bobEditsPlan :: library.shares)
  example("Ann hands the plan on to Bob, who may edit it"):
    Ownership.transfer(bobMayEdit, now, ann, plan, bob) is
      library.copy(documents = List(planDoc.copy(owner = bob), q3ReportDoc), shares = bobEditsPlan :: library.shares)
  example("Bob may not edit the plan: Ann keeps it"):
    Ownership.transfer(library, now, ann, plan, bob) is library
  example("Bob does not own the plan"):
    Ownership.transfer(bobMayEdit, now, bob, plan, cat) is bobMayEdit
  example("only the owner hands a document on"):
    (Ownership.transfer(bobMayEdit, now, bob, plan, bob) is
      bobMayEdit.copy(documents = List(planDoc.copy(owner = bob), q3ReportDoc))) is false

class RecordExamples extends FrFlowExamples(knowledge):
  private val shared = Request.Share(ann, Target.Doc(plan), Grantee.Person(bob), Level.View, None)
  example("the first entry is number 0"):
    Audit.record(library, now, Change.Made(shared)) is library.copy(log = List(Entry(0, now, Change.Made(shared))))
  example("the next is number 1"):
    Audit.record(library.copy(log = List(Entry(0, now, Change.Made(shared)))), now + 60, Change.Housekept) is
      library.copy(log = List(Entry(0, now, Change.Made(shared)), Entry(1, now + 60, Change.Housekept)))
  example("an entry is never taken away"):
    (Audit.record(library.copy(log = List(Entry(0, now, Change.Made(shared)))), now + 60, Change.Housekept) is
      library.copy(log = List(Entry(1, now + 60, Change.Housekept)))) is false

class ForgetExamples extends FrFlowExamples(knowledge):
  private val bobViewsPlan = Share(Target.Doc(plan), Grantee.Person(bob), Level.View, None)
  private val shared = Request.Share(ann, Target.Doc(plan), Grantee.Person(bob), Level.View, None)
  private val oldShare = Entry(0, now - 400 * day, Change.Made(shared))
  private val oldUnshare = Entry(1, now - 400 * day, Change.Made(Request.Unshare(ann, Target.Doc(plan),
      Grantee.Person(bob))))
  example("over a year on: the unshare is forgotten; the share it made, still held, keeps its entry"):
    Audit.forget(library.copy(shares = bobViewsPlan :: library.shares, log = List(oldShare, oldUnshare)), now) is
      library.copy(shares = bobViewsPlan :: library.shares,
        log = List(oldShare, oldUnshare.copy(change = Change.Forgotten)))
  example("under a year: kept"):
    Audit.forget(library.copy(log = List(oldUnshare)), now - 100 * day) is library.copy(log = List(oldUnshare))
  example("an entry is never taken away"):
    (Audit.forget(library.copy(log = List(oldUnshare)), now) is library) is false
