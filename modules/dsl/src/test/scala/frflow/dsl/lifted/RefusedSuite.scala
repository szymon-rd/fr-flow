package frflow.dsl.lifted

import frflow.dsl.lifted.LiftSyntax.lifted
import scala.compiletime.testing.typeCheckErrors

/** The Scala the reader does not read is a compile error at the construct, saying what to write: nothing whose
  * value in Scala could differ from its term's is read (state, effects, partial calls, numbers that wrap around,
  * equality that is not data's, a value from outside the function), nor what the term language cannot say yet
  * (recursion).
  */
class RefusedSuite extends munit.FunSuite:
  val limit: BigInt = BigInt(3)

  private def refused(errors: List[String], says: String): Unit =
    assert(errors.exists(_.contains(says)), s"expected an error saying `$says`, found: ${errors.mkString(" | ")}")

  test("state and effects") {
    refused(typeCheckErrors("lifted { (x: BigInt) => { var y = x; y } }").map(_.message), "not an immutable value")
    refused(typeCheckErrors("lifted { (x: BigInt) => { println(x); x } }").map(_.message), "not an immutable value")
    refused(typeCheckErrors("lifted { (x: BigInt) => { lazy val y = x; y } }").map(_.message),
      "not an immutable value")
  }

  test("calls that are not total, and what throws") {
    refused(typeCheckErrors("lifted { (xs: List[BigInt]) => xs.head }").map(_.message), "`head` of a")
    refused(typeCheckErrors("lifted { (o: Option[BigInt]) => o.get }").map(_.message), "`get` of a")
    refused(typeCheckErrors("lifted { (a: BigInt, b: BigInt) => a / b }").map(_.message), "`/` of a")
    refused(typeCheckErrors("lifted { (x: BigInt) => if x < BigInt(0) then throw new Exception(\"no\") else x }")
      .map(_.message), "lifted code cannot hold")
  }

  test("numbers that wrap around") {
    refused(typeCheckErrors("lifted { (x: Int) => x }").map(_.message), "has no FrSpec")
    refused(typeCheckErrors("lifted { (xs: List[BigInt]) => BigInt(xs.length + 1) }").map(_.message),
      "Scala's Int wraps around")
  }

  test("a value of a type with no FrSpec") {
    refused(typeCheckErrors("lifted { (u: Unspecified) => u.x }").map(_.message), "has no FrSpec")
    refused(typeCheckErrors("lifted { (x: BigInt) => Unspecified(x).x }").map(_.message), "no LeanType")
    refused(typeCheckErrors("lifted { (x: Double) => x }").map(_.message), "has no FrSpec")
  }

  test("a value from outside the function, and an operation the term language has none for") {
    refused(typeCheckErrors("lifted { (x: BigInt) => x < limit }").map(_.message), "a value from outside the function")
    refused(typeCheckErrors("lifted { (a: String, b: String) => a + b }").map(_.message), "`+` of a")
  }

  test("a type whose equality is its own has no spec") {
    refused(typeCheckErrors("FrSpec.derived[Loose]").map(_.message), "declares its own `equals`")
  }

  test("equality of two types") {
    refused(typeCheckErrors("lifted { (b: Booking, s: Shape) => b == s }").map(_.message),
      "two values of one type are compared")
    // Scala itself refuses to compare most pairs of standard types
    refused(typeCheckErrors("lifted { (x: BigInt, s: String) => x == s }").map(_.message), "cannot be compared")
  }

  test("a match with a guard, a pattern inside a pattern, a missing case") {
    refused(typeCheckErrors("""lifted { (s: Shape) => s match
      case Shape.Circle(r) if r < BigInt(1) => r
      case _ => BigInt(0) }""").map(_.message), "a case with a guard")
    refused(typeCheckErrors("""lifted { (o: Option[Shape]) => o match
      case Some(Shape.Circle(r)) => r
      case _ => BigInt(0) }""").map(_.message), "lifted code cannot hold")
    refused(typeCheckErrors("""lifted { (s: Shape) => (s: @unchecked) match
      case Shape.Circle(r) => r }""").map(_.message), "misses the case")
  }

  test("a call of itself") {
    refused(typeCheckErrors("""{
      lazy val down: Lifted.Of1[BigInt, BigInt] = lifted { (x: BigInt) => down(x - BigInt(1)) }
      down }""").map(_.message), "recursion is not read yet")
  }
