package sharing.time

import frflow.*
import sharing.domain.*
import sharing.time.Run.*

/** What the service's run is trusted to keep to: the clock never goes back, and housekeeping runs often enough. Each
  * is a part of the deadlines resting on it, set once they are.
  */
object Schedule:
  val clockNeverGoesBack = Node.assumption("Time never goes back between the service's events: each wait is of no " +
      "time or more.")(
    forall((pre: Term[List[Event]], e: Term[Event], post: Term[List[Event]]) => (events === pre ++ (e :: post)) implies
      e.on[Event.Asked](_ => True).on[Event.Housekept.type](True).on[Event.Delivered](_ => True)
        .on[Event.Waited](d => d >= 0)))
    .refines(Deadlines.trashPurgedOnTime, Deadlines.invitationsLapseOnTime, Deadlines.endedStaysEnded,
      Deadlines.requestsAnsweredOnTime)

  val housekeepingOnTime = Node.assumption("Housekeeping runs often enough: time never moves on more than two " +
      "minutes past its last run.")(
    forall((pre: Term[List[Event]], e: Term[Event], post: Term[List[Event]]) => (events === pre ++ (e :: post)) implies
      e.on[Event.Asked](_ => True).on[Event.Housekept.type](True).on[Event.Delivered](_ => True)
        .on[Event.Waited](d => atEnd(pre).now + d <= atEnd(pre).tidied + housekeepingWithin)))
    .refines(Deadlines.trashPurgedOnTime, Deadlines.invitationsLapseOnTime, Deadlines.requestsAnsweredOnTime)
