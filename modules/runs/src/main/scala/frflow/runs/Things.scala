package frflow.runs

import frflow.*

// What code handles, as a statement about a run speaks of it: one type for every object and every piece of data,
// since a call is made with any of them and answers with any of them.

/** What code handles: an object, named by a number, or a piece of data. */
enum Thing derives RocqType:
  case NoValue
  case Truth(truth: Boolean)
  case Number(number: BigInt)
  case Text(text: String)
  case Object(place: BigInt)

/** An object of class `C`, as a statement names it: which object, not what is in it. */
opaque type Ref[C] = Thing

object Ref:
  given [C]: RocqType[Ref[C]] = summon[RocqType[Thing]].asInstanceOf[RocqType[Ref[C]]]

  extension [C](r: Term[Ref[C]])
    /** The object as what code handles. */
    def thing: Term[Thing] = r.asInstanceOf[Term[Thing]]

/** An object of class `C` in a statement. */
type Obj[C] = Term[Ref[C]]

/** A value of a statement as code handles it. */
trait AsThing[A]:
  def apply(a: Term[A]): Term[Thing]

object AsThing:
  given AsThing[Thing] = a => a
  given [C]: AsThing[Ref[C]] = a => a.thing
  given AsThing[Boolean] = a => make[Thing.Truth](a)
  given AsThing[BigInt] = a => make[Thing.Number](a)
  given AsThing[String] = a => make[Thing.Text](a)
  given AsThing[Unit] = _ => Thing.NoValue
