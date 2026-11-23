package frflow.project.effects.samples

/** A number others read and write, and methods named as `eq` and `ne` are that compare what is held. */
final class Cell(start: Int):
  var held: Int = start

  def eq(other: Cell): Boolean = held == other.held

  def ne(other: Cell): Boolean = false

  def add(n: Int): Int =
    held = held + n
    held

  def add(n: Int, times: Int): Int =
    var left = times
    while left > 0 do
      held = held + n
      left = left - 1
    held

/** Where a reading must not take a shortcut: a constant used before its field is written and a field that is
  * none read before it is, a variable assigned in what a field is written on, methods that only share a name
  * with what Scala gives every object, two methods of one name.
  */
final class Edges:
  val first: Int = second + 1
  final val second = 5
  val early: Int = late + 1
  val late: Int = 7

  private def keep(c: Cell, mark: Int): Cell =
    c.held = mark
    c

  def receiver(): Int =
    val c = Cell(0)
    var i = 1
    if c.held == 0 then keep(c, { i = 5; i }).held = 2
    i + c.held * 10

  def looping(): Int =
    val c = Cell(0)
    var i = 0
    while i < 3 do keep(c, { i = i + 1; i }).held = i
    i * 10 + c.held

  def cells(): Int =
    val a = Cell(1)
    val b = Cell(1)
    a.held = 7
    b.held = 7
    (if a.eq(b) then 1 else 0) + (if a.ne(b) then 10 else 0) + a.held * 100

  def overloads(): Int =
    val c = Cell(1)
    c.add(2) + c.add(3, 4) * 100 + early * 10000 + late * 100000

  private var log: Int = 0

  private def mark(d: Int): Int =
    log = log * 10 + d
    d

  private def pick(c: Cell, d: Int): Cell =
    log = log * 10 + d
    c

  /** The order things are evaluated in, as the digits of a number: what an object is made with, what a call
    * is on before what it is given, what is given left to right, the operands of an operation.
    */
  def ordering(): Int =
    val c = Cell(mark(1))
    val added = pick(c, 2).add(mark(3), mark(4))
    c.held = mark(5) + mark(6) * mark(7)
    if added > 0 then log else 0
