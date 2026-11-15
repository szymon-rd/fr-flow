package frflow.executions.sets

import frflow.{Call as _, *}
import frflow.executions.*
import frflow.values.*

// A concurrent set of the JDK as a statement speaks of it: the set, what is in it, and the calls made on it.

/** A set of the JDK. */
trait KeySet

val elements = Declaration[(Ref[KeySet], BigInt) => Set[Value]]("what is in the set at a moment")

def add(s: Obj[KeySet], x: Term[Value]): Call[Boolean] = Call.of("KeySet.add", s.asValue, x)
def remove(s: Obj[KeySet], x: Term[Value]): Call[Boolean] = Call.of("KeySet.remove", s.asValue, x)
