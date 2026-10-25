package frflow.api
package details

import frflow.protocol.*
import io.circe.Json

/** A node's content as fields people read, and what changed between two contents, field by field. */
object Fields:
  private val labels = Map("uses" -> "definitions used", "notModelled" -> "not modelled", "ideaSection" -> "idea section",
    "definition" -> "definition (as written)", "op" -> "operation", "keeps" -> "invariants kept")
  /** What Lean reads of a node (its `sources`). */
  val formal: Set[String] = Set("formula", "post", "rule", "check")

  /** The source as written comes last: it repeats the rest. */
  def of(c: Content): List[(String, String)] =
    val flat = c.fields.flatMap((k, j) =>
      j.asObject.filter(_ => k == "sources").fold(List(labels.getOrElse(k, k) -> text(j)))(_.toList.map((s, v) => s -> text(v))))
    val (source, rest) = flat.partition(_._1 == labels("definition"))
    rest ++ source

  private def text(j: Json): String =
    j.asString.orElse(j.asArray.map(_.map(x => x.asString.getOrElse(Canonical.print(x))).mkString("\n"))).getOrElse(Canonical.print(j))

  /** The source as written only when nothing else changed. */
  def changes(before: Content, after: Content): List[FieldChange] =
    val (a, b) = (of(before).toMap, of(after))
    val changed = (b.map(_._1) ++ of(before).map(_._1)).distinct.flatMap { k =>
      val (was, now) = (a.getOrElse(k, ""), b.toMap.getOrElse(k, ""))
      Option.when(was != now)(FieldChange(k, LineDiff(was, now)))
    }
    val (source, rest) = changed.partition(_.field == labels("definition"))
    if rest.isEmpty then source else rest
