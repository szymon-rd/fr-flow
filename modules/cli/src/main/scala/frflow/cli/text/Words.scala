package frflow.cli
package text

import frflow.api.*
import frflow.protocol.*

/** Words shared by the views. */
object Words:
  def verb(a: Action): String = a match
    case Action.Accept  => "accepted"
    case Action.Confirm => "confirmed"
    case Action.Reject  => "rejected"
    case Action.Revisit => "asked to revisit"
    case Action.Remove  => "agreed gone"

  /** A review under `node` that moved only with it: `Decide` confirms it with the node (`Inbox.followers`). */
  def follower(f: NodeId, node: NodeId, st: Style): String = s"${st.follows} $f moved only with it: accepting $node confirms it too"

  def date(at: java.time.Instant): String = at.toString.take(16).replace('T', ' ')

  val causes: Map[Cause, String] = Map(Cause.Self -> "it changed", Cause.Above -> "the meaning of what it rests on changed",
    Cause.Parts -> "its parts changed", Cause.Code -> "the code it governs changed", Cause.Revisit -> "a change elsewhere may affect it",
    Cause.Merged -> "two branches decided it and both were kept")

  /** Why a node waits for review, in a word: `review (changed, code)`. */
  def cause(c: Cause): String = c match
    case Cause.Self    => "changed"
    case Cause.Above   => "above"
    case Cause.Parts   => "parts"
    case Cause.Code    => "code"
    case Cause.Revisit => "revisit"
    case Cause.Merged  => "two branches"

  def decided(l: Logged): String =
    val d = l.decision
    s"${d.action} ${l.node}${if d.rejected.isEmpty then "" else s", rejecting ${d.rejected.mkString(", ")}"}"
