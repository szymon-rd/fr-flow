package frflow.runs.code

import frflow.{Call as _, *}
import frflow.runs.*
import frflow.runs.InCode.given
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
val startIsAtomic = Node.assumption("Starting a thread is atomic.")(
  forall((t: Obj[Thread]) => t.start().atomic))

val addAnswersWhetherNew = Node.assumption("Adding to a set answers whether the element was not in it.")(
  forall((s: Obj[Threads], t: Obj[Thread], wasIn: Term[Boolean]) =>
    s.add(t).by(t).everyCall((_, answer, _) => answer === Returned(!wasIn))))

/** A statement that reads fields code outside the class may not, one assigned once and one assigned again, and
  * the words of a call that hands code over and of one that calls another itself.
  */
val aRingIsCounted = Node.assumption("Ringing on a till calls its count, and the count is not what it was.")(
  forall((till: Obj[Till], item: Obj[Item], w: Term[BigInt]) =>
    (till.ring(item, 1).calls(till.count(), w) && till.field("drawer") =!= item) implies
      eventually(w)(later => till.field("rings").at(later) =!= till.field("rings").at(w) &&
        till.open().by(till).spawned(later))))

val aStartTakesOneStep = Node.claim("A start that completes took one step.")(
  forall((t: Obj[Thread]) => t.start().everyCall((from, _, to) => to === from + 1)))

val written: FrModel = FrModel("Written")(aStartTakesOneStep, startIsAtomic.refines(aStartTakesOneStep),
  addAnswersWhetherNew.refines(aStartTakesOneStep), aRingIsCounted.refines(aStartTakesOneStep))
