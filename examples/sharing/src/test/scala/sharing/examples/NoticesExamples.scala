package sharing.examples

import frflow.*
import sharing.Demo.*
import sharing.knowledge
import sharing.domain.*
import sharing.features.Housekeeping
import sharing.notifications.Notifications
import sharing.time.Lifetimes

// Today's examples of notices, tidying and the lifetimes, one class per contract they were
// written on (owner §18), each on the demo library: given nothing, each is checked against the code in Scala and
// tried against the claims in Lean.

class AnnounceExamples extends FrFlowExamples(knowledge):
  private val catInvitedBy = Request.Invite(ann, cat, Target.Doc(plan), Level.View)
  private val entry = Entry(0, now, Change.Made(catInvitedBy))
  example("Cat is told of her invitation"):
    Notifications.announce(library, library, catInvitedBy, entry) is
      library.copy(outbox = List(Notice(cat, Subject.Logged(entry))))
  example("a share tells nobody"):
    Notifications.announce(library, library, Request.Share(ann, Target.Doc(plan), Grantee.Person(bob), Level.View,
      None), entry) is library
  example("an invitation is never kept from the person invited"):
    (Notifications.announce(library, library, catInvitedBy, entry) is library) is false

class WarnExamples extends FrFlowExamples(knowledge):
  private val bobsHourEndsInADay = Share(Target.Doc(plan), Grantee.Person(bob), Level.View, Some(now + day - 30))
  example("Bob's share ends in a day: he is told"):
    Notifications.warn(library.copy(shares = bobsHourEndsInADay :: library.shares), now) is
      library.copy(shares = bobsHourEndsInADay :: library.shares,
        outbox = List(Notice(bob, Subject.Ending(bobsHourEndsInADay))))
  example("a day and an hour before: not yet"):
    Notifications.warn(library.copy(shares = bobsHourEndsInADay :: library.shares), now - 3600) is
      library.copy(shares = bobsHourEndsInADay :: library.shares)
  example("a share ending is never left untold"):
    (Notifications.warn(library.copy(shares = bobsHourEndsInADay :: library.shares), now) is
      library.copy(shares = bobsHourEndsInADay :: library.shares)) is false

class TidyExamples extends FrFlowExamples(knowledge):
  private val ended = library.copy(shares = bobViewsPlanForAnHour :: library.shares, invitations = List(catInvited),
      documents = List(planTrashed, q3ReportDoc))
  example("nothing has ended yet"):
    Housekeeping.tidy(ended, now) is ended
  example("Bob's share of the plan has ended"):
    Housekeeping.tidy(ended, now + 3600) is ended.copy(shares = library.shares)
  example("a month on: the invitation has lapsed, and the plan is gone with its shares"):
    Housekeeping.tidy(ended, now + 29 * day) is
      library.copy(documents = List(q3ReportDoc), shares = List(annEditsReports, engViewsReports))
  example("nothing is removed before its time"):
    (Housekeeping.tidy(ended, now) is library) is false

class InForceExamples extends FrFlowExamples(knowledge):
  example("a share with no end"):
    Lifetimes.inForce(annEditsPlan, now) is true
  example("an hour before its end"):
    Lifetimes.inForce(bobViewsPlanForAnHour, now) is true
  example("at its end it has ended"):
    Lifetimes.inForce(bobViewsPlanForAnHour, now + 3600) is false
  example("never after its end"):
    (Lifetimes.inForce(bobViewsPlanForAnHour, now + 7200) is true) is false

class IsOpenExamples extends FrFlowExamples(knowledge):
  example("sent a day ago"):
    Lifetimes.isOpen(catInvited, now) is true
  example("a second before seven days have passed"):
    Lifetimes.isOpen(catInvited, now + 6 * day - 1) is true
  example("seven days after it was sent"):
    Lifetimes.isOpen(catInvited, now + 6 * day) is false
  example("a month later it has long lapsed"):
    (Lifetimes.isOpen(catInvited, now + 30 * day) is true) is false

class GoneExamples extends FrFlowExamples(knowledge):
  example("trashed a day ago: still restorable"):
    Lifetimes.gone(planTrashed, now) is false
  example("thirty days after it was trashed"):
    Lifetimes.gone(planTrashed, now + 29 * day) is true
  example("not in the trash"):
    Lifetimes.gone(planDoc, now + 100 * day) is false
  example("never before thirty days"):
    (Lifetimes.gone(planTrashed, now + 28 * day) is true) is false

class PendingExamples extends FrFlowExamples(knowledge):
  private val catAsks = AccessRequest(cat, Target.Doc(plan), Level.View, now - day, false)
  example("made a day ago"):
    Lifetimes.isPending(catAsks, now) is true
  example("seven days after it was made"):
    Lifetimes.isPending(catAsks, now + 6 * day) is false
  example("a month later it has long lapsed"):
    (Lifetimes.isPending(catAsks, now + 30 * day) is true) is false

class ReminderDueExamples extends FrFlowExamples(knowledge):
  private val catAsks = AccessRequest(cat, Target.Doc(plan), Level.View, now - day, false)
  example("made a day ago"):
    Lifetimes.reminderDue(catAsks, now) is false
  example("two days after it was made"):
    Lifetimes.reminderDue(catAsks, now + day) is true
  example("never before it was made"):
    (Lifetimes.reminderDue(catAsks, now - day) is true) is false
