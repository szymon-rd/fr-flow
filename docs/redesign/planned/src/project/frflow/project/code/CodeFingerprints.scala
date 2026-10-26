package frflow.project.code

import frflow.core.name.RelPath
import frflow.decision.content.{CodeFingerprint, CodeNow, Sha}

/** The code a node governs, fingerprinted as the simple lexer reads it, each file named relative to the project. */
object CodeFingerprints:
  def of(files: List[(RelPath, Option[String])]): CodeNow =
    val sorted = files.sortBy(_._1)
    val joined = sorted.map((p, t) => p.value + "\u0000" + t.fold("<missing>")(ScalaTokens.significant))
    CodeNow(sorted.map(_._1.value), CodeFingerprint(Sha(joined.mkString("\u0000"))))
