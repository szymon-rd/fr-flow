package frflow.project.effects.samples

/** What is run on the JVM and, as the trees read from these classes, in Rocq: each method gives a number, and
  * the two must agree.
  */
final class Scenarios:
  def counters(): Int =
    val pair = Pair(Counter(10), Counter(20))
    pair.bump() + pair.left.sumTo(5) + pair.right.current

  def sharing(): Int =
    val one = Counter(1)
    val pair = Pair(one, one)
    val bumped = pair.bump()
    if pair.same then bumped + one.current else 0

  def banking(): Int =
    val a = Account(100)
    val b = Account(5)
    val bank = Bank(a, b)
    val moved = if bank.transfer(30) then 1 else 0
    val again = if bank.transfer(500) then 1 else 0
    moved + again * 10 + a.total * 100 + b.total * 10000 + a.refusals * 1000000

  def draining(): Int =
    val a = Account(50)
    val b = Account(0)
    val bank = Bank(a, b)
    val some = bank.drainAtMost(7, 3)
    val rest = bank.drain(7)
    some + rest * 100 + a.total * 10000 + b.total * 100000 + a.refusals * 10000000

  def computing(): Int =
    val n = Numbers()
    val truths = if n.either(true, false) && !n.either(true, true) then 1 else 0
    n.largest(3, 9, 4) + n.gcd(84, 36) * 10 + n.triangle(6) * 1000 + n.signOf(-5) + truths * 100000

  def wrapping(): Int =
    val n = Numbers()
    n.power(7, 20) + n.power(-3, 31)

  def edges(): Int =
    val e = Edges()
    e.first + e.receiver() * 10 + e.looping() * 1000 + e.cells() * 100000

  def naming(): Int = Edges().overloads()

  def ordering(): Int = Edges().ordering()
