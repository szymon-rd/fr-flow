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

  private val once = allows(BigInt(2), World(StockModel -> BigInt(3)), BigInt(5), World(StockModel -> BigInt(5)), "two delivered to three")
  private val twice = allows(BigInt(2), World(StockModel -> BigInt(1)), BigInt(6), World(StockModel -> BigInt(7)), "three, doubled, then one more")

  // A law's two sides: an operation each, and two contracts with the one post, each proven of its side.
  val leftUnitLhs = Param[BigInt => Flow[BigInt]]("the lhs side of the law LeftUnit")
  val leftUnitRhs = Param[BigInt => Flow[BigInt]]("the rhs side of the law LeftUnit")
  val rightUnitLhs = Param[BigInt => Flow[BigInt]]("the lhs side of the law RightUnit")
  val rightUnitRhs = Param[BigInt => Flow[BigInt]]("the rhs side of the law RightUnit")
  val associativityLhs = Param[BigInt => Flow[BigInt]]("the lhs side of the law Associativity")
  val associativityRhs = Param[BigInt => Flow[BigInt]]("the rhs side of the law Associativity")

  val leftLhs = Node.contract(leftUnitLhs)("The lhs side of LeftUnit gives what the post says.")(delivered).examples()(once)
  val leftRhs = Node.contract(leftUnitRhs)("The rhs side of LeftUnit gives what the post says.")(delivered).examples()(once)
  val rightLhs = Node.contract(rightUnitLhs)("The lhs side of RightUnit gives what the post says.")(delivered).examples()(once)
  val rightRhs = Node.contract(rightUnitRhs)("The rhs side of RightUnit gives what the post says.")(delivered).examples()(once)
  val assocLhs = Node.contract(associativityLhs)("The lhs side of Associativity gives what the post says.")(deliveredTwiceToppedUp)
    .examples()(twice)
  val assocRhs = Node.contract(associativityRhs)("The rhs side of Associativity gives what the post says.")(deliveredTwiceToppedUp)
    .examples()(twice)

  val kb = KnowledgeBase("Laws", idea = "IDEA.md")(neverBelowZero, clamp, stockModel, leftLhs, leftRhs, rightLhs, rightRhs, assocLhs, assocRhs)
    .implementProven(clamp)(clampAtZero)
    .implementProven(leftLhs)((a: Term[BigInt]) => leftUnit(a).lhs).implementProven(leftRhs)((a: Term[BigInt]) => leftUnit(a).rhs)
    .implementProven(rightLhs)((a: Term[BigInt]) => rightUnit(a).lhs).implementProven(rightRhs)((a: Term[BigInt]) => rightUnit(a).rhs)
    .implementProven(assocLhs)((a: Term[BigInt]) => associativity(a).lhs).implementProven(assocRhs)((a: Term[BigInt]) => associativity(a).rhs)
