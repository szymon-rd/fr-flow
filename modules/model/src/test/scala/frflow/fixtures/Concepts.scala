package frflow.fixtures

import frflow.*

/** The core concepts on a counter: two Definitions (a step, tested Scala; adding, a proven flow), claims about them,
  * an `always` of the counter's states kept by the one program writing it, and the facts that rests on.
  */
object Concepts:
  trait Counter:
    def read: Flow[BigInt]
    def bump(by: Term[BigInt]): Flow[Unit]

  object counted extends Counter, StateModel[BigInt]:
    def read = state.get
    def bump(by: Term[BigInt]) = state.update(c => c + by)

  val counter: Boundary[Counter] = Boundary[Counter]("counter", "the count kept")

  val step = Definition[BigInt => BigInt]("how much a request adds")
  val add = Definition[BigInt => Flow[BigInt]]("adding a request: the count after")

  val model = Node.assumption("The counter adds what it is bumped by.")(counter.behavesAs(counted))
  val writes = Node.assumption("Only adding bumps the counter.")(counted.writtenOnlyBy(add))
  val oneAtATime = Node.assumption("Requests are added one at a time.")(counted.changedOneRunAtATime)
  val startsAtNothing = Node.assumption("The counter starts at nothing.")(counted.initially(c => c === BigInt(0)))

  val grows = Node.claim("Adding a request adds its step to the count.")(
    forall((x: Term[BigInt], before: Term[World]) => counted.in(add(x).after(before)) === counted.in(before) + step(x)))
    .assuming(model)
  val neverNegative = Node.claim("The count is never negative.")(always(counted)(c => c >= BigInt(0)))
    .assuming(writes, oneAtATime, startsAtNothing)
  val stepPositive = Node.claim("A step adds one more than the request's size.")(
    forall((x: Term[BigInt]) => step(x) === when(x >= BigInt(0))(x + 1).otherwise(-x + 1))).refines(grows)

  def adding(x: Term[BigInt]): Flow[BigInt] =
    for
      _ <- counter.bump(step(x))
      c <- counter.read
    yield c

  val kb: KnowledgeBase =
    KnowledgeBase("Concepts")(grows, neverNegative, stepPositive, model, writes, oneAtATime, startsAtNothing)
      .implementProven(add)(adding)
      .implementTested(step)(x => x.abs + 1)
