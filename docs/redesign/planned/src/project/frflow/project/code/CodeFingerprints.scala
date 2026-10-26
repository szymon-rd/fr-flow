package frflow.project.code

import frflow.core.name.RelPath
import frflow.decision.content.{CodeNow, Sha}

/** The code a node governs, fingerprinted both ways: by its tokens (what decisions are bound to) and by its raw text
  * (what decisions recorded before tokens were bound to), each file named relative to the project root.
  */
object CodeFingerprints:
  def of(files: List[(RelPath, Option[String])]): CodeNow =
    val sorted = files.sortBy(_._1)
    def joined(f: String => String) =
      sorted.map((p, t) => p.value + "\u0000" + t.fold("<missing>")(f)).mkString("\u0000")
    CodeNow(sorted.map(_._1.value), Sha(joined(ScalaTokens.significant)), Sha(joined(identity)))
