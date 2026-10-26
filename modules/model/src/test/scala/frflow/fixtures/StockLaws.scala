package frflow.fixtures

import frflow.*

/** The relative monad's laws on flows over the stock: each law's two programs, and a pair of flow contracts with one
  * post for each, both proven on the model in Lean.
  */
object StockLaws:
  val laws = RelativeMonad.Laws[Flow, Term]
  /** A delivery added, then the stock counted. */
  def deliver(x: Term[BigInt]): Flow[BigInt] = stock.add(x) *> stock.count
  /** One more book, keeping the count it was given; or none, past ten. */
  def topUp(n: Term[BigInt]): Flow[BigInt] = (n > 10).foldF(Flow.pure(n), stock.add(BigInt(1)).as(n))

  def leftUnit(a: Term[BigInt]): RelativeMonad.IsEq[Flow[BigInt]] = laws.leftUnit(a, deliver)
  def rightUnit(a: Term[BigInt]): RelativeMonad.IsEq[Flow[BigInt]] = laws.rightUnit(deliver(a))
  def associativity(a: Term[BigInt]): RelativeMonad.IsEq[Flow[BigInt]] = laws.associativity(deliver(a), deliver, topUp)

  /** What a delivery gives: the stock with it added. */
  private def delivered(a: Term[BigInt], r: Term[BigInt], before: Term[World], after: Term[World]) =
    after(StockModel) === before(StockModel) + a && r === after(StockModel)
  /** Two deliveries of the stock with `a` added, then one more book unless that is past ten. */
  private def deliveredTwiceToppedUp(a: Term[BigInt], r: Term[BigInt], before: Term[World], after: Term[World]) =
    r === (before(StockModel) + a) + (before(StockModel) + a) &&
      after(StockModel) === r + (r > 10).fold(BigInt(0): Term[BigInt], BigInt(1))

  /** A law's two sides as two contracts with the one post, each proven of its side. */
  private def side(law: String, s: String, post: (Term[BigInt], Term[BigInt], Term[World], Term[World]) => Term[Boolean],
      example: Case[BigInt => Flow[BigInt]]) =
    val p = Param[BigInt => Flow[BigInt]](s"$law$s", s"the $s side of the law $law")
    Node.contract(p)(s"$law${s.capitalize}", s"The $s side of $law gives what the post says.", why = s"$law of a relative monad.")(post)
      .examples()(example)

  private val once = allows(BigInt(2), World(StockModel -> BigInt(3)), BigInt(5), World(StockModel -> BigInt(5)), "two delivered to three")
  private val twice = allows(BigInt(2), World(StockModel -> BigInt(1)), BigInt(6), World(StockModel -> BigInt(7)), "three, doubled, then one more")
  val leftLhs = side("LeftUnit", "lhs", delivered, once)
  val leftRhs = side("LeftUnit", "rhs", delivered, once)
  val rightLhs = side("RightUnit", "lhs", delivered, once)
  val rightRhs = side("RightUnit", "rhs", delivered, once)
  val assocLhs = side("Associativity", "lhs", deliveredTwiceToppedUp, twice)
  val assocRhs = side("Associativity", "rhs", deliveredTwiceToppedUp, twice)

  val kb = KnowledgeBase("Laws", idea = "IDEA.md")(neverBelowZero, clamp, countsStock, leftLhs, leftRhs, rightLhs, rightRhs, assocLhs, assocRhs)
    .implementProven(clamp)(clampAtZero)
    .implementProven(leftLhs)((a: Term[BigInt]) => leftUnit(a).lhs).implementProven(leftRhs)((a: Term[BigInt]) => leftUnit(a).rhs)
    .implementProven(rightLhs)((a: Term[BigInt]) => rightUnit(a).lhs).implementProven(rightRhs)((a: Term[BigInt]) => rightUnit(a).rhs)
    .implementProven(assocLhs)((a: Term[BigInt]) => associativity(a).lhs).implementProven(assocRhs)((a: Term[BigInt]) => associativity(a).rhs)
