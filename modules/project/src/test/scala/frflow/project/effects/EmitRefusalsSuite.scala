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

  test("what is passed by name, and a method put in place where it is called, are refused") {
    assert(refusal("ByName").contains("what is passed by name"), refusal("ByName"))
    assert(refusal("Inlines").contains("a method Scala puts in place where it is called"), refusal("Inlines"))
  }

  test("a field evaluated when it is first read is refused") {
    assert(refusal("Later").contains("a field evaluated when or where it is read"), refusal("Later"))
  }

  test("a class another may extend is refused: a call of its method may run another's") {
    assert(refusal("Open").contains("a class another may extend"), refusal("Open"))
  }

  test("a call outside the code on no written object is refused, and not given the method's own") {
    assert(refusal("Bare").contains("on no object that is written"), refusal("Bare"))
    assert(refusal("Bare").contains("Bare.scala:6"), refusal("Bare"))
  }

  test("a choice between values of two types is refused when its value is used") {
    assert(refusal("Mixed").contains("a choice between values of two types"), refusal("Mixed"))
  }
