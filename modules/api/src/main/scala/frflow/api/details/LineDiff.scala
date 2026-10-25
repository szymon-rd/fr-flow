package frflow.api
package details

/** A line diff by longest common subsequence; an unchanged run more than `context` lines from a change is folded. */
object LineDiff:
  /** Beyond this many line pairs the whole text is shown as replaced. */
  private val Budget = 250000

  def apply(before: String, after: String, context: Int = 1): List[DiffLine] =
    def lines(s: String) = if s.isEmpty then Vector.empty else s.split("\n", -1).toVector
    val (a, b) = (lines(before), lines(after))
    fold(if a.size.toLong * b.size > Budget then (a.map(DiffLine.Removed(_)) ++ b.map(DiffLine.Added(_))).toList else align(a, b), context)

  private def align(a: Vector[String], b: Vector[String]): List[DiffLine] =
    // common(i)(j): the length of the longest common subsequence of a.drop(i) and b.drop(j).
    val common = Array.ofDim[Int](a.size + 1, b.size + 1)
    for i <- a.indices.reverse; j <- b.indices.reverse do
      common(i)(j) = if a(i) == b(j) then common(i + 1)(j + 1) + 1 else common(i + 1)(j).max(common(i)(j + 1))
    def walk(i: Int, j: Int, acc: List[DiffLine]): List[DiffLine] =
      if i < a.size && j < b.size && a(i) == b(j) then walk(i + 1, j + 1, DiffLine.Same(a(i)) :: acc)
      else if i < a.size && (j == b.size || common(i + 1)(j) >= common(i)(j + 1)) then walk(i + 1, j, DiffLine.Removed(a(i)) :: acc)
      else if j < b.size then walk(i, j + 1, DiffLine.Added(b(j)) :: acc)
      else acc.reverse
    walk(0, 0, Nil)

  private def fold(ops: List[DiffLine], context: Int): List[DiffLine] =
    def same(l: DiffLine) = PartialFunction.cond(l) { case DiffLine.Same(_) => true }
    // The lines within `context` of a change: the change itself among them.
    val near = ops.zipWithIndex.collect { case (l, k) if !same(l) => (k - context) to (k + context) }.flatten.toSet
    ops.zipWithIndex.map((l, k) => Option.when(near(k))(l))
      .foldRight(List.empty[DiffLine]) {
        case (Some(l), acc) => l :: acc
        case (None, DiffLine.Folded(n) :: rest) => DiffLine.Folded(n + 1) :: rest
        case (None, acc) => DiffLine.Folded(1) :: acc
      }
