package frflow.fixtures

import frflow.*

/** Time on flows: the clock's model as an assumption, and flow contracts over it that hold for every start time and
  * every delay a sleep may add (both in the clock's state).
  */
object Timing:
  val clockKept = Node.assumption(Clock.boundary)(ClockModel)("ClockKept",
    "The clock gives the time now; a sleep moves it on by the time asked, and by a delay it may add, never less.",
    why = "Steps take no time; a sleep may wake late (a loaded machine), never early.")
    .implementedBy(c => FakeClock(c), _.state)

  /** Waits until a time, then reads the clock. */
  def waitThenRead(t: Term[BigInt]): Flow[BigInt] = Flow.waitUntil(t) *> Flow.now
  /** A sleep of some seconds, given five at most. */
  def napWithin(d: Term[BigInt]): Flow[Option[Unit]] = Flow.sleep(d).timeout(BigInt(5))
  /** Two nights: a sleep of a day, twice, then the time. */
  def twoNights(start: Term[BigInt]): Flow[BigInt] = Flow.waitUntil(start) *> Flow.sleep(BigInt(86400)) *> Flow.sleep(BigInt(86400)) *> Flow.now

  private val waited = Param[BigInt => Flow[BigInt]]("waited", "waiting until a time, then reading the clock")
  private val napped = Param[BigInt => Flow[Option[Unit]]]("napped", "a sleep of some seconds, given five at most")
  private val nights = Param[BigInt => Flow[BigInt]]("nights", "two nights after a time")

  val waitUntilContract = Node.contract(waited)("WaitUntil",
    "Waiting until a time ends at that time or later, and never before the time it started.",
    why = "waitUntil sleeps what is left; a sleep may wake late.")(
    (t, r, before, after) => r >= t && r >= before(ClockModel).now && after(ClockModel).now === r)
    .examples()(
      expect(BigInt(10), World(ClockModel -> ClockState(BigInt(4), Nil)), BigInt(10), World(ClockModel -> ClockState(BigInt(10), Nil)), "six seconds to wait"),
      expect(BigInt(10), World(ClockModel -> ClockState(BigInt(12), List[BigInt](3))), BigInt(12), World(ClockModel -> ClockState(BigInt(12), List[BigInt](3))), "already past: no sleep"),
      expect(BigInt(10), World(ClockModel -> ClockState(BigInt(4), List[BigInt](3))), BigInt(13), World(ClockModel -> ClockState(BigInt(13), Nil)), "woken three seconds late"))
  val timeoutContract = Node.contract(napped)("Timeout",
    "A sleep given five seconds gives a result exactly when the clock moved on by five seconds or less; it sleeps either way.",
    why = "timeout does not cancel: it says whether the flow took longer than its time.")(
    (d, r, before, after) => r.isDefined === (after(ClockModel).now - before(ClockModel).now <= 5) &&
      after(ClockModel).now >= before(ClockModel).now + d)
    .examples()(
      expect(BigInt(3), World(ClockModel -> ClockState(BigInt(0), Nil)), Some(()), World(ClockModel -> ClockState(BigInt(3), Nil)), "three seconds: in time"),
      expect(BigInt(3), World(ClockModel -> ClockState(BigInt(0), List[BigInt](4))), None, World(ClockModel -> ClockState(BigInt(7), Nil)), "woken late: too late"))
  val twoNightsContract = Node.contract(nights)("TwoNights",
    "Two nights after a time end two days after it, or later.",
    why = "Sleeps add up; each may wake late.")(
    (t, r, before, after) => r >= t + 2 * 86400 && after(ClockModel).now === r)

  val kb = KnowledgeBase("Timing", idea = "IDEA.md")(clockKept, waitUntilContract, timeoutContract, twoNightsContract)
    .implementProven(waitUntilContract)((t: Term[BigInt]) => waitThenRead(t))
    .implementProven(timeoutContract)((d: Term[BigInt]) => napWithin(d))
    .implementProven(twoNightsContract)((t: Term[BigInt]) => twoNights(t))
