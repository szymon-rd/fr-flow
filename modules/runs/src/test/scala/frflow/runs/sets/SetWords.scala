package frflow.runs.sets

import frflow.{Call as _, *}
import frflow.runs.*

// A concurrent set of the JDK as a statement speaks of it: the set, what is in it, and the calls made on it.

/** A set of the JDK. */
trait KeySet

val elements = Declaration[(Ref[KeySet], BigInt) => Set[Thing]]("what is in the set at a moment")

def add(s: Obj[KeySet], x: Term[Thing]): Call[Boolean] = Call.of("KeySet.add", s.thing, x)
def remove(s: Obj[KeySet], x: Term[Thing]): Call[Boolean] = Call.of("KeySet.remove", s.thing, x)
