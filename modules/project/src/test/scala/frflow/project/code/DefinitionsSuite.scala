package frflow.project.code

import frflow.core.name.RelPath

/** The definitions a fingerprint reads in a file that holds nodes (owner §38): each named one to the next line at its
  * indentation or less, with the same file's definitions those name; a node beside them is no part of it.
  */
class DefinitionsSuite extends munit.FunSuite:
  private val src = """package shop
    |
    |val total = Node.claim("The total is the sum of the lines.")(
    |  forall((b: Term[Basket]) => priced(b) === sum(b)))
    |
    |/** The sum of a basket's lines. */
    |def sum(b: Basket): BigInt =
    |  b.lines.map(line).sum
    |
    |private def line(l: Line): BigInt = l.price * l.count
    |
    |object Store:
    |  def open(): Store = Store()
    |  val unused = 1
    |
    |val tax = 2
    |""".stripMargin

  private def read(names: String*): String = Definitions.of(ScalaTokens.significant(src), names.toList)

  test("a definition runs from its line to the next at its indentation or less, with what it names in the file") {
    assertEquals(read("sum"), "def sum(b: Basket): BigInt =\n  b.lines.map(line).sum\n" +
      "private def line(l: Line): BigInt = l.price * l.count")
  }

  test("an object is read whole; a name the file does not define, nothing") {
    assertEquals(read("Store", "Basket"), "object Store:\n  def open(): Store = Store()\n  val unused = 1")
  }

  private val path = RelPath.fromIdentifiers("src", "Shop.scala")
  private def printed(text: String) = CodeFingerprints.of(List(Governed.Named(path, List("sum")) -> Some(text)))

  test("editing a node beside the definitions named leaves their fingerprint; editing one of them moves it") {
    val node = src.replace("The total is the sum of the lines.", "The total is what the lines add up to.")
    assertEquals(printed(node), printed(src))
    assertNotEquals(printed(src.replace("l.price * l.count", "l.price * l.count + 1")), printed(src))
    assertNotEquals(printed(src), CodeFingerprints.of(List(Governed.Whole(path) -> Some(src))))
  }
