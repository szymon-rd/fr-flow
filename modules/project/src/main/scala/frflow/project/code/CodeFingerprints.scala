package frflow.project.code

import frflow.decision.content.{CodeFingerprint, CodeNow, Sha}

/** The code a node governs, fingerprinted as the simple lexer reads it (a file whole, or the definitions named in it,
  * `Governed`), each file named relative to the project; a file not there is `<missing>`.
  */
object CodeFingerprints:
  def of(files: List[(Governed, Option[String])]): CodeNow =
    val sorted = files.sortBy(_._1.path)
    val joined = sorted.map((g, t) => g.path.value + "\u0000" + t.fold("<missing>")(g.of))
    CodeNow(sorted.map(_._1.path.value), CodeFingerprint(Sha(joined.mkString("\u0000"))))
