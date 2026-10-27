package frflow.cli
package text

import frflow.api.*
import frflow.protocol.*

/** Words shared by the views. */
object Words:
  /** What Lean was asked, in words: `the step from its parts`, `the proof of its code`, `kept by book`. */
  def obligation(o: ObligationName): String = o match
    case ObligationName.Complete      => "the step from its parts"
    case ObligationName.Impl          => "the proof of its code"
    case ObligationName.RootImpl      => "the roots of the code (root_impl)"
    case ObligationName.Check         => "its run-time check"
    case ObligationName.KeptBy(p)     => s"kept by $p"
    case ObligationName.Initially     => "what the store starts with"
    case ObligationName.Expect(i)     => s"expectation ${i + 1}"
    case other                        => other.lean

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

  /** Why a node waits, in words: an assumption rests on nothing; what moves it from above is a node assuming it. */
  def cause(c: Cause, n: SnapNode): String =
    if c == Cause.Above && n.kind == NodeKind.Assumption then s"the meaning of ${assumers(n)} changed" else causes(c)

  /** What moves an assumption from above: the nodes resting on it, and what it uses, if anything. */
  private def assumers(n: SnapNode): String =
    if n.uses.isEmpty && n.relies.isEmpty then "a node assuming it" else "a node assuming it, or one it uses"

  /** Why a node waits for review, in a few words: `it and its code changed: review it`. What changed is said as
    * one subject: it; a node it rests on (a parent, or a claim or definition it uses), for an assumption a node
    * assuming it; its parts; its code. Being asked to revisit it, or kept from two branches, is a clause of its own.
    */
  def review(causes: List[Cause], n: Option[SnapNode] = None): String =
    val subjects = causes.collect {
      case Cause.Self  => "it"
      case Cause.Above => n.filter(_.kind == NodeKind.Assumption).fold("a node it rests on")(assumers)
      case Cause.Parts => "its parts"
      case Cause.Code  => "its code"
    }
    val changed = subjects match
      case Nil       => Nil
      case List(one) => List(s"$one changed")
      case more      => List(s"${more.init.mkString(", ")} and ${more.last} changed")
    val others =
      causes.collect { case Cause.Revisit => "asked to revisit it"; case Cause.Merged => "kept from two branches" }
    s"${(changed ++ others).mkString("; ")}: review it"

  def decided(l: Logged): String =
    val d = l.decision
    s"${d.action} ${l.node}${if d.rejected.isEmpty then "" else s", rejecting ${d.rejected.mkString(", ")}"}"
