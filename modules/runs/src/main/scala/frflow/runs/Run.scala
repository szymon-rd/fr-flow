package frflow.runs

import frflow.*

// A run: the steps taken, one from each moment to the next, each by one actor. A moment is how many steps have been
// taken. Nothing here says what code does: that is what a model's assumptions and its code say of the run.

/** A call: what is called and what it takes, what it is called on first. */
final case class Invocation(what: String, takes: List[Thing]) derives RocqType

/** What a call completes with. */
enum Answer derives RocqType:
  case Returned(value: Thing)
  case Threw(exception: Thing)

/** A call given to an actor to run on its own. */
final case class Handed(to: Thing, call: Invocation) derives RocqType

/** The step taken from a moment.
  *   - `Makes`: a call is made, inside the pending call of its actor that makes it (`inside`, the moment that one
  *     was made), or inside none: it was handed to its actor.
  *   - `Does`: a call is made and completed at once.
  *   - `Completes`: the call made at `made` completes.
  *   - `Acts`: anything else an actor does.
  *   - `Rests`: nothing.
  * `hands` is the calls a step hands to actors to run on their own.
  */
enum Step derives RocqType:
  case Makes(by: Thing, inside: Option[BigInt], call: Invocation)
  case Does(by: Thing, inside: Option[BigInt], call: Invocation, answer: Answer, hands: List[Handed])
  case Completes(by: Thing, made: BigInt, answer: Answer, hands: List[Handed])
  case Acts(by: Thing)
  case Rests

/** The run a model's statements are about. */
val steps = Declaration[BigInt => Step]("the step taken from each moment of the run")
