package frflow.project.effects.samples

/** A number kept and added to: a field read and written, a loop over two variables. */
final class Counter(start: Int):
  private var count: Int = start

  def increment(by: Int): Int =
    count = count + by
    count

  def current: Int = count

  def sumTo(n: Int): Int =
    var i = 0
    var s = 0
    while i < n do
      s = s + i
      i = i + 1
    s

/** Two counters held: calls of another object's methods, and whether two objects are one. */
final class Pair(val left: Counter, val right: Counter):
  def bump(): Int = left.increment(1) + right.increment(2)

  def same: Boolean = left eq right
