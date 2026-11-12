package frflow.proof.reading

/** What Rocq said of the files of one build, as FrFlow's prover port writes it and the judges read it: for each file
  * Rocq read to its end, the lemmas whose proofs it did not accept (each then admitted, so the rest of the file and
  * what imports it is still read), with what Rocq said, and what each audited lemma rests on (`Print Assumptions`:
  * an admitted lemma among them); or, of a file with any other error, that error (`broken`: nothing in it, or in a
  * file importing it, is proven).
  */
object RocqReport:
  final case class File(path: String, open: Map[String, String], assumes: Map[String, List[String]],
      broken: Option[String])

  def print(files: List[File]): String = files.flatMap(f =>
    s"file ${f.path}" :: f.broken.map(m => s"broken ${line(m)}").toList ++
      f.open.toList.sortBy(_._1).map((l, m) => s"open $l ${line(m)}") ++
      f.assumes.toList.sortBy(_._1).map((l, as) => s"assumes $l ${as.mkString(" ")}".trim)).mkString("", "\n", "\n")

  def read(report: String): List[File] =
    report.linesIterator.foldLeft(Vector.empty[File]) { (done, l) =>
      val (word, rest) = l.span(_ != ' ')
      (word, rest.trim, done.lastOption) match
        case ("file", path, _)          => done :+ File(path, Map.empty, Map.empty, None)
        case ("broken", m, Some(f))     => done.init :+ f.copy(broken = Some(text(m)))
        case ("open", said, Some(f))    =>
          val (lemma, m) = said.span(_ != ' ')
          done.init :+ f.copy(open = f.open + (lemma -> text(m.trim)))
        case ("assumes", said, Some(f)) =>
          val names = said.split(' ').toList.filter(_.nonEmpty)
          done.init :+ f.copy(assumes = f.assumes ++ names.headOption.map(_ -> names.drop(1)))
        case _                          => done
    }.toList

  /** A message on one line, and back. */
  private def line(message: String): String = message.trim.replace("\\", "\\\\").replace("\n", "\\n")
  private def text(l: String): String = l.replace("\\n", "\n").replace("\\\\", "\\")
