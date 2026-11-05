package frflow.cli.say

import frflow.decision.ledger.Action
import frflow.decision.review.{Cause, Mechanical, Unproven}

/** What of a node is not proven, why a decision is not mechanical, and what moved under one, in words. */
object Unprovens:
  def text(u: Unproven): String = u match
    case Unproven.Check          => "its check is not proven"
    case Unproven.Parts          => "its parts are not proven to make it"
    case Unproven.NotNeeded(p)   => s"Lean proves it without $p: a part not needed"
    case Unproven.Clash          => "its parts clash"
    case Unproven.NothingBelow   => "nothing below it proves it: no parts, no code"
    case Unproven.Kept(id)       => s"keeping $id is not proven"
    case Unproven.Implementation => "its code is not proven"
    case Unproven.RootImpl       => "the roots of the code are not proven (root_impl)"
    case Unproven.Tests          => "its code fails a generated case"
    case Unproven.NotTested      => Tested.NotYet
    case Unproven.Idle           => "doing nothing meets it: say what users can do"
    case Unproven.Consistency    => "its consistency is not proven"

  def notMechanical(n: Mechanical.Not): String = n match
    case Mechanical.Not.HoldsAChoice              => "it holds a choice (a rival, or a rejection)"
    case Mechanical.Not.NotUnderReview(s)         => s"it is ${Refusals.state(s)}, not under review"
    case Mechanical.Not.CausesNeedTheDeveloper(cs) => s"what moved needs you: ${cs.map(cause).mkString("; ")}"
    case Mechanical.Not.MeaningMoved              => "its meaning moved"
    case Mechanical.Not.PartsNotProven            => "its new parts are not proven to make it"
    case Mechanical.Not.NotProven(us)             => s"not proven again: ${us.map(text).mkString("; ")}"
    case Mechanical.Not.WaitsFor(id)              => s"it waits for $id"

  def cause(c: Cause): String = c match
    case Cause.Self    => "it changed"
    case Cause.Above   => "the meaning of what it rests on changed"
    case Cause.Parts   => "its parts changed"
    case Cause.Code    => "the code it governs changed"
    case Cause.Revisit => "a change elsewhere may affect it"
    case Cause.Merged  => "two branches decided it and both were kept"
    case Cause.Writers(ps) => s"${ps.mkString(", ")} now ${if ps.size == 1 then "changes" else "change"} the store " +
        "it is about"

  def verb(a: Action): String = a match
    case Action.Accept  => "accepted"
    case Action.Confirm => "confirmed"
    case Action.Reject  => "rejected"
    case Action.Revisit => "asked to revisit"
    case Action.Remove  => "agreed gone"
