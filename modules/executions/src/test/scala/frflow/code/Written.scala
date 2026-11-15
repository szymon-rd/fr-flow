package frflow.code

import frflow.{Call as _, *}
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import java.util.concurrent.ConcurrentHashMap

// Calls written in statements as the code is, each read as the call it is.

type Threads = ConcurrentHashMap.KeySetView[Thread, java.lang.Boolean]

def started(t: Obj[Thread])(using Stating): Call[Unit] = t.start()
def added(s: Obj[Threads], t: Obj[Thread])(using Stating): Call[Boolean] = s.add(t)
def asked(s: Obj[Threads])(using Stating): Call[Boolean] = s.isEmpty()
def current: Call[Thread] = Thread.currentThread()

def rung(till: Obj[Till], item: Obj[Item], times: Term[BigInt])(using Stating): Call[Boolean] =
  till.ring(item, times)
def rungTwice(till: Obj[Till], item: Obj[Item])(using Stating): Call[Boolean] = till.ring(item, 2)
def made(name: Term[String])(using Stating): Call[Till] = new Till(name)
def closed(till: Obj[Till], manager: Obj[Till])(using Stating): Call[Int] = closeAll(till, true)(using manager)

/** A statement in which the code is followed by a word of a call, and one that says what each call answers. */
val aThreadIsStartedOnce = Node.assumption("A thread is started at most once.")(
  forall((t: Obj[Thread], a: Term[BigInt], b: Term[BigInt]) =>
    (t.start().called(a) && t.start().called(b)) implies (a === b)))

val addAnswersWhetherNew = Node.assumption("Adding to a set answers whether the element was not in it.")(
  forall((s: Obj[Threads], t: Obj[Thread], wasIn: Term[Boolean]) =>
    s.add(t).by(t).everyCall((_, response, _) => response === Returned(!wasIn))))

/** A statement that reads fields code outside the class may not, one assigned once and one assigned again, and
  * the words of a call that spawns code over and of one that calls another itself.
  */
val aRingIsCounted = Node.assumption("Ringing on a till calls its count, and the count is not what it was.")(
  forall((till: Obj[Till], item: Obj[Item], w: Term[BigInt]) =>
    (till.ring(item, 1).calls(till.count(), w) && till.field("drawer") =!= item) implies
      eventually(w)(later => till.field("rings").at(later) =!= till.field("rings").at(w) &&
        till.open().by(till).spawned(later))))

val noStartAfterAStart = Node.claim("A thread that was started is not started again.")(
  forall((t: Obj[Thread], w: Term[BigInt]) => t.start().calledBefore(w) implies !t.start().called(w)))

val written: FrModel = FrModel("Written")(noStartAfterAStart, aThreadIsStartedOnce.refines(noStartAfterAStart),
  addAnswersWhetherNew.refines(noStartAfterAStart), aRingIsCounted.refines(noStartAfterAStart))
