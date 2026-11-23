package frflow.project.effects.samples

/** Code that only computes: choices that assign variables, loops inside loops, numbers that wrap. */
final class Numbers:
  def largest(a: Int, b: Int, c: Int): Int =
    var best = a
    if b > best then best = b
    if c > best then best = c
    best

  def power(base: Int, n: Int): Int =
    var result = 1
    var left = n
    while left > 0 do
      result = result * base
      left = left - 1
    result

  def gcd(a: Int, b: Int): Int =
    var x = a
    var y = b
    while x != y do
      if x > y then x = x - y else y = y - x
    x

  def triangle(rows: Int): Int =
    var total = 0
    var row = 1
    while row <= rows do
      var column = 0
      while column < row do
        total = total + 1
        column = column + 1
      row = row + 1
    total

  def signOf(n: Int): Int = if n < 0 then -1 else if n == 0 then 0 else 1

  def either(a: Boolean, b: Boolean): Boolean = (a || b) && !(a && b)
