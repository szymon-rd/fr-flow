package frflow.executions

import frflow.*
import frflow.values.Value

// An execution: the events of a program as it runs, one from each moment to the next, each by one actor. A moment
// is how many events there have been. Nothing here says what code does: that is what a model's assumptions and
// its code say of the execution.

/** An invocation: the method invoked and its arguments, what it is invoked on first. */
final case class Invocation(method: String, arguments: List[Value]) derives RocqType

/** What an invocation is responded to with. */
enum Response derives RocqType:
  case Returned(value: Value)
  case Threw(exception: Value)

/** An invocation given to an actor to make on its own. */
final case class Spawn(to: Value, invocation: Invocation) derives RocqType

/** What a field of an object holds. */
final case class Held(field: String, value: Value) derives RocqType

/** What happens from a moment to the next.
  *   - `Invoke`: a method is invoked, inside the pending invocation of its actor that makes it (`inside`, the
  *     moment of that one), or inside none: it was spawned.
  *   - `Atomic`: a method is invoked and responds at once.
  *   - `Respond`: the invocation of the moment `invoked` is responded to.
  *   - `Make`: an object of a class of the code is made, its fields holding what they first hold.
  *   - `Read`: a field of an object is read. `Mark`: a write of a field begins. `Write`: a field is written.
  *   - `Enter`: what is initialised once (a lazy value, an object of the code) is asked for: it is there, or the
  *     actor is to initialise it.
  *   - `Internal`: anything else an actor does.
  *   - `Stutter`: nothing.
  * `spawns` is the invocations an event gives to actors to make on their own.
  */
enum Event derives RocqType:
  case Invoke(by: Value, inside: Option[BigInt], invocation: Invocation)
  case Atomic(by: Value, inside: Option[BigInt], invocation: Invocation, response: Response, spawns: List[Spawn])
  case Respond(by: Value, invoked: BigInt, response: Response, spawns: List[Spawn])
  case Make(by: Value, inside: Option[BigInt], made: Value, cls: String, holding: List[Held])
  case Read(by: Value, inside: Option[BigInt], on: Value, field: String, value: Value)
  case Mark(by: Value, inside: Option[BigInt], on: Value, field: String)
  case Write(by: Value, inside: Option[BigInt], on: Value, field: String, value: Value)
  case Enter(by: Value, inside: Option[BigInt], on: Value, field: String, found: Option[Value])
  case Internal(by: Value)
  case Stutter

/** The execution a model's statements are about. */
val history = Declaration[BigInt => Event]("the event at each moment of the execution")
