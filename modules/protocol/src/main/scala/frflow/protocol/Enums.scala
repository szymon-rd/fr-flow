package frflow.protocol

import io.circe.{Codec, Decoder, Encoder}

/** An enum written as a word (its `toString`): how statuses are stored and printed. */
private[protocol] trait Words[E]:
  def values: Array[E]
  private lazy val byWord = values.map(e => e.toString -> e).toMap
  def fromWord(w: String): Option[E] = byWord.get(w)
  given Codec[E] = Codec.from(Decoder.decodeString.emap(w => fromWord(w).toRight(s"unknown value: $w")), Encoder.encodeString.contramap(_.toString))

private[protocol] def word(name: String): String =
  name.replaceAll("([a-z])([A-Z])", "$1-$2").toLowerCase

/** A node's kind, as the snapshot names it. */
enum NodeKind:
  case Claim, Contract, Assumption, Definition, Design
  override def toString: String = word(productPrefix)
  /** As people read it: an invariant is a claim with a rule. */
  def shown(rule: Boolean): String = if rule then "invariant" else toString
object NodeKind extends Words[NodeKind]

/** The outcome of checking a node: `proven`, `open`, `failed`, `model-error`, `timeout`, or `waiting`
  * (proven, but its parts are not yet, or a term it uses has two definitions and neither is chosen).
  * The snapshot adds `unchecked` (no current check) and `informal` (out of Lean: decided by reading).
  */
enum CheckStatus:
  case Proven, Open, Failed, ModelError, Waiting, Timeout, Unchecked, Informal
  override def toString: String = word(productPrefix)
object CheckStatus extends Words[CheckStatus]

/** The status of one obligation, of a try, or of a part of the snapshot.
  *
  * An obligation is `proven`, `open`, `failed`, or `unevaluated` (an example Lean did not decide). A try
  * (a statement Lean is asked whether it can prove, see `TryKind`) has a plain status instead: the second
  * of each pair when Lean proved it, the first when it found no proof within its budget (which shows
  * nothing): `needed` or `not-needed`, `not-restates` or `restates`, `no-clash` or `clash`, `not-unsat` or
  * `unsat`, `not-idle` or `idle`, `not-vacuous` or `vacuous`. The snapshot adds `unchecked`, `timeout`,
  * `informal` and, for an invariant a contract does not keep, `exempt`.
  */
enum ObligationStatus:
  case Proven, Open, Failed, Unevaluated, Unchecked, Timeout, Informal, Exempt
  case Needed, NotNeeded, Restates, NotRestates, Clash, NoClash, Unsat, NotUnsat, Idle, NotIdle, Vacuous, NotVacuous
  override def toString: String = word(productPrefix)
  /** Leaves nothing to do: an obligation proven, a try showing nothing wrong. */
  def fine: Boolean = this match
    case Proven | Needed | NotRestates | NoClash | NotUnsat | NotIdle | NotVacuous => true
    case _ => false
object ObligationStatus extends Words[ObligationStatus]

/** Where the developer stands on a node: `proposed` (not decided yet, or rejected then reworked),
  * `accepted` (decided, and nothing moved since), `review` (something moved since: see `Cause`), or
  * `rejected` (an alternative was chosen instead; the agent removes it from the model).
  */
enum ReviewState:
  case Proposed, Accepted, Review, Rejected
  override def toString: String = word(productPrefix)
object ReviewState extends Words[ReviewState]

/** What moved under a decision: `self` (what the node itself says), `above` (the meaning of what it rests
  * on), `parts` (a part added or removed), `code` (the code it governs), `revisit` (the developer asked to
  * revisit it), `merged` (two branches decided it, and a merge kept both).
  */
enum Cause:
  case Self, Above, Parts, Code, Revisit, Merged
  override def toString: String = word(productPrefix)
object Cause extends Words[Cause]

/** A decision of the developer's: `accept` (the node chosen, as seen), `confirm` (it still holds after
  * something above it moved), `reject` (an alternative not chosen), `revisit` (a change above may affect
  * it: reviewed again), `remove` (a decided node is agreed to be gone).
  */
enum Action:
  case Accept, Confirm, Reject, Revisit, Remove
  override def toString: String = word(productPrefix)
  /** What a node is bound to: an acceptance or a confirmation. */
  def binds: Boolean = this == Accept || this == Confirm
object Action extends Words[Action]

/** A request of the developer's: `open`, `answered` by the agent, or `closed`. */
enum RequestStatus:
  case Open, Answered, Closed
  override def toString: String = word(productPrefix)
object RequestStatus extends Words[RequestStatus]

/** A decision listed below a changed node: `accepted` (it may be revisited) or `moved` (under review only
  * because the node's meaning moved: it still holds, or is revisited).
  */
enum BelowKind:
  case Accepted, Moved
  override def toString: String = word(productPrefix)
object BelowKind extends Words[BelowKind]

/** A try: a statement Lean is asked whether it can prove, within a budget. Proven, it shows something
  * wrong (or, for `needed`, that the part is not needed); not proven, it shows nothing.
  */
enum TryKind:
  /** The node holds without this part (one of several). */
  case Needed(part: String)
  /** The node holds whatever its one part says. */
  case Vacuous
  /** The node's one part follows from the node: it says what its part says. */
  case Restates
  /** The parts contradict each other. */
  case Clash
  /** No world meets the node. */
  case Unsat
  /** Doing nothing meets the node (a root). */
  case Idle
  /** The expectation `i` holds whatever the node says. */
  case VacuousExpect(i: Int)

  /** The status when Lean proved it, and when it found no proof. */
  def onProven: ObligationStatus = this match
    case Needed(_) | Vacuous => ObligationStatus.NotNeeded
    case Restates            => ObligationStatus.Restates
    case Clash               => ObligationStatus.Clash
    case Unsat               => ObligationStatus.Unsat
    case Idle                => ObligationStatus.Idle
    case VacuousExpect(_)    => ObligationStatus.Vacuous
  def onNot: ObligationStatus = this match
    case Needed(_) | Vacuous => ObligationStatus.Needed
    case Restates            => ObligationStatus.NotRestates
    case Clash               => ObligationStatus.NoClash
    case Unsat               => ObligationStatus.NotUnsat
    case Idle                => ObligationStatus.NotIdle
    case VacuousExpect(_)    => ObligationStatus.NotVacuous
  /** Proven, the node fails: nothing it says can hold. */
  def fatal: Boolean = this == Clash || this == Unsat

  /** What a try Lean found no proof of leaves unshown, in plain words: `node`'s id, its one part, and
    * what doing nothing is.
    */
  def unshown(node: String, onePart: String, idle: String): String =
    val what = this match
      case Needed(_)        => s"$node holds without it"
      case Vacuous          => s"$node holds whatever $onePart says"
      case Restates         => s"$onePart follows from $node"
      case Clash            => "the parts contradict each other"
      case Unsat            => "no world meets it"
      case Idle             => s"doing nothing ($idle) meets it"
      case VacuousExpect(_) => "the expectation holds whatever the node says"
    s"Lean found no proof that $what (a try)"
