package frflow.protocol

import io.circe.{Codec, Decoder, Encoder, KeyDecoder, KeyEncoder}

/** Identifiers and hashes: strings on the wire, apart in the types. */
private[protocol] trait Id[T](using ev: T =:= String, back: String =:= T):
  def apply(s: String): T = back(s)
  extension (t: T) def value: String = ev(t)
  given Codec[T] = Codec.from(Decoder.decodeString.map(back(_)), Encoder.encodeString.contramap(ev(_)))
  given KeyEncoder[T] = KeyEncoder.encodeKeyString.contramap(ev(_))
  given KeyDecoder[T] = KeyDecoder.decodeKeyString.map(back(_))
  given Ordering[T] = Ordering.String.on(ev(_))

opaque type NodeId = String
object NodeId extends Id[NodeId]
/** A SHA-256 in hex: of a node's content, or of what its check depends on. */
opaque type Hash = String
object Hash extends Id[Hash]
/** What a node rests on, hashed: the meaning of everything above it. "" for nothing. */
opaque type Chain = String
object Chain extends Id[Chain]:
  val empty: Chain = ""
/** The hash of the source files a node governs. */
opaque type Fingerprint = String
object Fingerprint extends Id[Fingerprint]
/** A developer key's id: the first 16 hex digits of its public key's hash. */
opaque type KeyId = String
object KeyId extends Id[KeyId]
/** A short reference to one decision (see `Ledger.entry`). */
opaque type EntryRef = String
object EntryRef extends Id[EntryRef]
opaque type RequestId = String
object RequestId extends Id[RequestId]
/** A node as the developer last saw it (see the ledger's `Reading.version`): a decision sent with one is refused if it moved. */
opaque type Version = String
object Version extends Id[Version]

/** An enum written as a word (its `toString`): how statuses are stored and printed. */
trait Words[E]:
  def values: Array[E]
  private lazy val byWord = values.map(e => e.toString -> e).toMap
  given Codec[E] = Codec.from(Decoder.decodeString.emap(w => byWord.get(w).toRight(s"unknown value: $w")), Encoder.encodeString.contramap(_.toString))

def word(name: String): String = name.replaceAll("([a-z])([A-Z])", "$1-$2").toLowerCase

enum NodeKind:
  case Claim, Contract, Assumption, Definition, Design
  override def toString: String = word(productPrefix)
  /** As people read it: an invariant is a claim with a rule. */
  def shown(rule: Boolean): String = if rule then "invariant" else toString
object NodeKind extends Words[NodeKind]

/** `waiting`: proven itself, but a part is not yet, or a term it uses has two definitions and neither is
  * chosen; `unchecked`: no current check.
  */
enum CheckStatus:
  case Proven, Open, Failed, ModelError, Waiting, Timeout, Unchecked
  override def toString: String = word(productPrefix)
object CheckStatus extends Words[CheckStatus]

/** Of an obligation, or of a try: `shown` when Lean proved it, `not-shown` when it found no proof within
  * its budget. `unevaluated`: an example Lean did not decide.
  */
enum ObligationStatus:
  case Proven, Open, Failed, Unevaluated, Unchecked, Timeout, Exempt, Shown, NotShown
  override def toString: String = word(productPrefix)
  /** Leaves nothing to do: an obligation proven, a try showing nothing wrong. */
  def fine: Boolean = this == Proven || this == NotShown
object ObligationStatus extends Words[ObligationStatus]

/** Where the developer stands on a node: `proposed` (not decided yet, or rejected then reworked),
  * `accepted`, `review` (something moved since: see `Cause`), or `rejected` (an alternative was chosen).
  */
enum ReviewState:
  case Proposed, Accepted, Review, Rejected
  override def toString: String = word(productPrefix)
object ReviewState extends Words[ReviewState]

/** What moved under a decision. `merged`: two branches decided it, and a merge kept both. */
enum Cause:
  case Self, Above, Parts, Code, Revisit, Merged
  override def toString: String = word(productPrefix)
object Cause extends Words[Cause]

/** `confirm`: it still holds after something above it moved; `reject`: an alternative not chosen. */
enum Action:
  case Accept, Confirm, Reject, Revisit, Remove
  override def toString: String = word(productPrefix)
  /** What a node is bound to. */
  def binds: Boolean = this == Accept || this == Confirm
object Action extends Words[Action]

enum RequestStatus:
  case Open, Answered, Closed
  override def toString: String = word(productPrefix)
object RequestStatus extends Words[RequestStatus]

/** A decision below a changed node: `moved` is under review only because the node's meaning moved. */
enum BelowKind:
  case Accepted, Moved
  override def toString: String = word(productPrefix)
object BelowKind extends Words[BelowKind]

/** A statement Lean is asked whether it can prove, within a budget. Proven, it shows something wrong (or,
  * for `needed`, that the part is not needed); not proven, it shows nothing.
  */
enum TryKind:
  case Needed(part: String)
  case Vacuous, Restates, Clash, Unsat, Idle
  case VacuousExpect(i: Int)
  /** A part says what conjunct `i` (from 1) of its parent says, with the definitions applied. */
  case RestatesConjunct(part: String, i: Int)

  /** Proven, the node fails: nothing it says can hold. */
  def fatal: Boolean = this == Clash || this == Unsat

  /** What a try Lean found no proof of leaves unshown, in plain words. */
  def unshown(node: String, onePart: String, idle: String): String =
    val what = this match
      case Needed(_)        => s"$node holds without it"
      case Vacuous          => s"$node holds whatever $onePart says"
      case Restates         => s"$onePart follows from $node"
      case Clash            => "the parts contradict each other"
      case Unsat            => "no world meets it"
      case Idle             => s"doing nothing ($idle) meets it"
      case VacuousExpect(_) => "the expectation holds whatever the node says"
      case RestatesConjunct(p, i) => s"$p says what conjunct $i of $node says"
    s"Lean found no proof that $what (a try)"
