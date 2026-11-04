package frflow.api.derive

import frflow.api.view.Found
import frflow.core.name.NodeId
import frflow.project.pipeline.Analysis

/** Where a change belongs: the nodes governing a path (a file, a directory holding governed files, or a file under
  * a governed directory), or, for words, the nodes whose id, statement, vocabulary or decisions' reasons mention every
  * one of them, whatever the case. A path (it has a `/`, or names a `.scala` file) mentions nothing.
  */
private[api] object Finds:
  def of(a: Analysis, query: String): Found =
    val q = query.trim.stripPrefix("./")
    val path = q.contains('/') || q.endsWith(".scala")
    Found(if path then Nil else mentioning(a, q), governing(a, q))

  private def governing(a: Analysis, q: String): List[NodeId] =
    def governs(f: String) = f == q || f.startsWith(q.stripSuffix("/") + "/") || q.startsWith(f.stripSuffix("/") + "/")
    a.subjects.inOrder.map(_.id).filter(id => a.governed.get(id).exists(_.files.exists(governs)))

  private def mentioning(a: Analysis, q: String): List[NodeId] =
    val words = q.toLowerCase.split("\\s+").filter(_.nonEmpty).toList
    a.subjects.inOrder.filter { s =>
      val text = (s.id.value :: s.content.text("statement") :: s.content.texts("vocabulary") ++
        a.inputs.ledger.counting.history(s.id).map(_.reason.text)).mkString("\n").toLowerCase
      words.nonEmpty && words.forall(text.contains)
    }.map(_.id)
