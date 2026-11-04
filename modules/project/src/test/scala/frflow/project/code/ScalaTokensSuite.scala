package frflow.project.code

import frflow.core.name.RelPath

/** The simple lexer's law, in the direction that matters: an edit of what the program means moves the fingerprint;
  * edits of comments, blank lines and spacing between tokens do not; a literal is read as written.
  */
class ScalaTokensSuite extends munit.FunSuite:
  private val src = """package shop
    |
    |/** Prices. */
    |object Prices:
    |  // the total, in cents
    |  def total(xs: List[Int]): Int = xs.sum  /* nested /* comment */ still */
    |  val greeting = "hello // not a comment"
    |""".stripMargin

  private def same(a: String, b: String)(using munit.Location) =
    assertEquals(ScalaTokens.significant(a), ScalaTokens.significant(b))
  private def moved(a: String, b: String)(using munit.Location) =
    assertNotEquals(ScalaTokens.significant(a), ScalaTokens.significant(b))

  test("comments are blanked, blank lines and trailing spaces dropped, indentation kept, runs of spaces one") {
    assertEquals(ScalaTokens.significant(src), """package shop
      |object Prices:
      |  def total(xs: List[Int]): Int = xs.sum
      |  val greeting = "hello // not a comment"""".stripMargin)
  }

  test("editing a comment, a blank line or the spacing between tokens moves nothing") {
    same(src, src.replace("// the total, in cents", "// in cents").replace("\n\n", "\n\n\n"))
    same(src, src.replace("Int = xs.sum", "Int  =   xs.sum   "))
    same(src, src.replace("/* nested /* comment */ still */", "/* other */"))
    same("val x = a  /* plus */  + b", "val x = a + b")
  }

  test("an edit of code, of a literal, or of indentation moves it") {
    moved(src, src.replace("xs.sum", "xs.max"))
    moved(src, src.replace("hello // not", "hello  // not"))
    moved(src, src.replace("  def total", "    def total"))
  }

  test("a multi-line string keeps its lines, blank and spaced, as written") {
    val text = "val q = \"\"\"select *\n\n  from   t\"\"\"\n"
    assertEquals(ScalaTokens.significant(text), text.stripTrailing)
    moved(text, text.replace("\n\n", "\n"))
  }

  test("an interpolation's hole is read through to its closing brace, a brace in its strings included") {
    val text = "val s = s\"a ${ m(\"}\") } // b\" // tail\nval t = 1\n"
    assertEquals(ScalaTokens.significant(text), "val s = s\"a ${ m(\"}\") } // b\"\nval t = 1")
  }

  test("characters are literals; a quote starting none is code") {
    val text = "val c = '\"' // q\nval d = '\\'' ; val e = '\\u0041' // e\ntype T = 'x\n"
    assertEquals(ScalaTokens.significant(text), "val c = '\"'\nval d = '\\'' ; val e = '\\u0041'\ntype T = 'x")
  }

  test("the fingerprint names each file, a missing one too, in the order of their paths") {
    val (a, b) = (Governed.Whole(RelPath.fromIdentifiers("src", "A.scala")),
      Governed.Whole(RelPath.fromIdentifiers("src", "B.scala")))
    val now = CodeFingerprints.of(List(b -> None, a -> Some(src)))
    assertEquals(now.files, List("src/A.scala", "src/B.scala"))
    assertEquals(now, CodeFingerprints.of(List(a -> Some(src.replace("// the total, in cents", "")), b -> None)))
    assertNotEquals(now, CodeFingerprints.of(List(a -> Some(src), b -> Some(""))))
  }
