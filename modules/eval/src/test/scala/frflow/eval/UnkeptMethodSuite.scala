package frflow.eval

import frflow.*
import scala.compiletime.testing.typeCheckErrors

/** A call of an ordinary method from lifted code where the compiler did not keep the method's body (this module
  * compiles without `-Yretain-trees`): refused, the error saying what to do.
  */
class UnkeptMethodSuite extends munit.FunSuite:
  test("an ordinary method whose body the compiler did not keep is not read, and the error says so") {
    val errors = typeCheckErrors("lifted { (s: UnkeptMethodSuite.Stretch) => s.twice }").map(_.message)
    assert(errors.exists(_.contains("whose body the compiler did not keep: make it `inline` or a lifted `val`, " +
      "or compile with -Yretain-trees")), errors.mkString(" | "))
  }

object UnkeptMethodSuite:
  final case class Stretch(length: BigInt) derives FrSpec:
    def twice: BigInt = length + length
