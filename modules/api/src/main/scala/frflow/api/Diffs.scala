package frflow.api

import frflow.protocol.{Canonical, Content}
import io.circe.Json

/** A line diff: the lines of `before` and `after` aligned by their longest common subsequence, each
  * unchanged run more than `context` lines away from a change folded into one line.
  */
object LineDiff:
  /** Beyond this many line pairs the alignment is not computed: the whole text is shown as replaced. */
  private val Budget = 250000

  def apply(before: String, after: String, context: Int = 1): List[DiffLine] =
    val (a, b) = (lines(before), lines(after))
    val ops = if a.size.toLong * b.size > Budget then (a.map(DiffLine.Removed(_)) ++ b.map(DiffLine.Added(_))).toList else align(a, b)
    fold(ops, context)

  private def lines(s: String): Vector[String] = if s.isEmpty then Vector.empty else s.split("\n", -1).toVector

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
    def same(l: DiffLine) = l match
      case DiffLine.Same(_) => true
      case _ => false
    val changed = ops.indices.filterNot(k => same(ops(k))).toVector
    def near(k: Int) = changed.exists(c => (c - k).abs <= context)
    val kept = ops.zipWithIndex.map((l, k) => Option.when(!same(l) || near(k))(l))
    // A run of lines left out becomes one `Folded` line saying how many.
    kept.foldRight(List.empty[DiffLine]) {
      case (Some(l), acc) => l :: acc
      case (None, DiffLine.Folded(n) :: rest) => DiffLine.Folded(n + 1) :: rest
      case (None, acc) => DiffLine.Folded(1) :: acc
    }

/** A node's content as fields people read, and what changed between two contents, field by field. */
object Fields:
  private val labels = Map("uses" -> "definitions used", "notModelled" -> "not modelled", "ideaSection" -> "idea section",
    "definition" -> "definition (as written)", "op" -> "operation", "keeps" -> "invariants kept")
  /** What Lean reads of a node (its `sources`): a change there and not in the statement asks whether the words still say it. */
  val formal: Set[String] = Set("formula", "post", "rule", "check")

  /** The fields, in the content's order, the source as written last (it repeats the rest). */
  def of(c: Content): List[(String, String)] =
    val flat = c.fields.flatMap((k, j) =>
      j.asObject.filter(_ => k == "sources").fold(List(labels.getOrElse(k, k) -> text(j)))(_.toList.map((s, v) => s -> text(v))))
    val (source, rest) = flat.partition(_._1 == labels("definition"))
    rest ++ source

  private def text(j: Json): String =
    j.asString.orElse(j.asArray.map(_.map(x => x.asString.getOrElse(Canonical.print(x))).mkString("\n"))).getOrElse(Canonical.print(j))

  /** The fields that differ, each as a line diff. */
  def changes(before: Content, after: Content): List[FieldChange] =
    val (a, b) = (of(before).toMap, of(after))
    val keys = (b.map(_._1) ++ of(before).map(_._1)).distinct
    keys.flatMap { k =>
      val (was, now) = (a.getOrElse(k, ""), b.toMap.getOrElse(k, ""))
      Option.when(was != now)(FieldChange(k, LineDiff(was, now)))
    }
