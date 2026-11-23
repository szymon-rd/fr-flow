package frflow.project.effects

import frflow.dsl.compiled.effect.EmitEffects
import frflow.dsl.lifted.NotRead

/** Scala the emitter does not read yet is refused where it stands, and never passed over: each class of
  * `refused` holds one such thing.
  */
class EmitRefusalsSuite extends munit.FunSuite:
  private def refusal(file: String): String =
    intercept[NotRead](EmitEffects(classOf[refused.Wide], _.endsWith(s"/effects/refused/$file.tasty"))).getMessage

  test("a trait is refused: it is no class with a body of its own") {
    assert(refusal("Shape").contains("what is no class with a body of its own"), refusal("Shape"))
  }

  test("a value of a type a tree has no value of is refused, with its file and line") {
    assert(refusal("Wide").contains("a value of type scala.Long"), refusal("Wide"))
    assert(refusal("Wide").contains("Wide.scala:5"), refusal("Wide"))
  }

  test("a function made where it is used is refused") {
    assert(refusal("Applies").contains("is not read into a tree of effects"), refusal("Applies"))
    assert(refusal("Applies").contains("Applies.scala"), refusal("Applies"))
  }

  test("an exception thrown is refused") {
    assert(refusal("Throws").contains("is not read into a tree of effects"), refusal("Throws"))
    assert(refusal("Throws").contains("Throws.scala:5"), refusal("Throws"))
  }
