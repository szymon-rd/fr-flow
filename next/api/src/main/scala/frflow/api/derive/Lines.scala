package frflow.api.derive

import frflow.api.view.diff.DiffLine

/** A line diff by longest common subsequence: kept lines, and each change as the lines removed then those added.
  * Beyond `Budget` line pairs, the whole text is shown as replaced.
  */
private[api] object Lines:
  val Budget: Int = 250000

  def diff(before: List[String], after: List[String]): List[DiffLine] =
    if before.size.toLong * after.size > Budget then before.map(DiffLine.Removed(_)) ++ after.map(DiffLine.Added(_))
    else align(before.toVector, after.toVector)

  private def align(a: Vector[String], b: Vector[String]): List[DiffLine] =
    // common(i)(j): the length of the longest common subsequence of a.drop(i) and b.drop(j).
    val common = Array.ofDim[Int](a.size + 1, b.size + 1)
    for i <- a.indices.reverse; j <- b.indices.reverse do
      common(i)(j) = if a(i) == b(j) then common(i + 1)(j + 1) + 1 else common(i + 1)(j).max(common(i)(j + 1))
    @scala.annotation.tailrec
    def walk(i: Int, j: Int, acc: List[DiffLine]): List[DiffLine] =
      if i < a.size && j < b.size && a(i) == b(j) then walk(i + 1, j + 1, DiffLine.Same(a(i)) :: acc)
      else if i < a.size && (j == b.size || common(i + 1)(j) >= common(i)(j + 1)) then
        walk(i + 1, j, DiffLine.Removed(a(i)) :: acc)
      else if j < b.size then walk(i, j + 1, DiffLine.Added(b(j)) :: acc)
      else acc.reverse
    walk(0, 0, Nil)
