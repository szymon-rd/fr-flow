package frflow.proof.reading

import scala.annotation.tailrec

/** Rocq source with its comments and strings blanked, lines kept: what the proof rules read; and its lemmas. */
object RocqSource:
  def code(src: String): String =
    @tailrec def go(i: Int, depth: Int, inString: Boolean, out: StringBuilder): String =
      if i >= src.length then out.result()
      else
        val (c, n) = (src(i), if i + 1 < src.length then src(i + 1) else ' ')
        val blank = if c == '\n' then '\n' else ' '
        if inString then go(i + 1, depth, c != '"', out += blank)
        else if c == '(' && n == '*' then go(i + 2, depth + 1, false, out ++= "  ")
        else if depth > 0 && c == '*' && n == ')' then go(i + 2, depth - 1, false, out ++= "  ")
        else if depth > 0 then go(i + 1, depth, false, out += blank)
        else if c == '"' then go(i + 1, depth, true, out += ' ')
        else go(i + 1, depth, false, out += c)
    go(0, 0, false, StringBuilder())

  /** Each lemma the source states, with its lines: from its head to the line its proof ends on. What one with no
    * binders states is what follows its colon.
    */
  def lemmas(src: String): List[Theorem] =
    val c = code(src)
    val lineAt = c.scanLeft(1)((l, ch) => if ch == '\n' then l + 1 else l)
    Head.findAllMatchIn(c).toList.map { m =>
      val end = Ending.findFirstMatchIn(c.substring(m.end)).fold(c.length)(e => m.end + e.end)
      Theorem(m.group(1), m.group(2).trim.stripPrefix(":").trim.replaceAll("\\s+", " "), lineAt(m.start),
        lineAt(end - 1))
    }

  /** The line a place in the source is on, the place given in bytes. */
  def lineAt(src: String, byte: Int): Int =
    src.getBytes(java.nio.charset.StandardCharsets.UTF_8).take(byte).count(_ == '\n'.toByte) + 1

  /** The modules the source imports, as Rocq names them: `Require Export A.B.`, `From FrFlow Require Export Base.`
    * (`FrFlow.Base`).
    */
  def imports(src: String): List[String] = Require.findAllMatchIn(code(src)).toList.flatMap(m =>
    m.group(2).trim.split("\\s+").toList.map(n => Option(m.group(1)).fold(n)(from => s"$from.$n")))

  /** The lemmas the source audits, in order: `Print Assumptions name.`. */
  def audited(src: String): List[String] = Audit.findAllMatchIn(code(src)).map(_.group(1)).toList

  /** The source with a lemma's proof given up (`Proof. Admitted.`), its lines kept where they are; none of a lemma
    * with no proof to give up, or given up already.
    */
  def admitted(src: String, lemma: Theorem): Option[String] =
    val lines = src.split("\n", -1).toVector
    val proof = (lemma.from - 1 until lemma.to.min(lines.size)).find(i => lines(i).startsWith("Proof"))
    proof.filter(i => lines(i).trim != Given).map(i => (lines.take(i) ++ (Given +: Vector.fill(lemma.to - 1 - i)("")) ++
      lines.drop(lemma.to)).mkString("\n"))

  private val Given = "Proof. Admitted."
  private val Name = """[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*"""
  private val Gap = """[ \t]+"""
  private val Require =
    s"""(?m)^[ \\t]*(?:From$Gap(\\S+)$Gap)?Require$Gap(?:Import$Gap|Export$Gap)?($Name(?:$Gap$Name)*)\\.[ \\t]*$$""".r
  private val Audit = """(?m)^\s*Print\s+Assumptions\s+([A-Za-z_][A-Za-z0-9_']*)\.""".r
  /** A lemma's head: its name, then what it states, its binders before it if it has any, up to the period that ends
    * the sentence.
    */
  private val Head = """(?s)(?m)^(?:Lemma|Theorem)\s+([A-Za-z_][A-Za-z0-9_']*)\b(.*?)\.\s*$""".r
  private val Ending = """(?m)\b(?:Qed|Defined|Admitted|Abort)\.""".r
