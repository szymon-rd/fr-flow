package whole

import frflow.core.checking.Checking

class ScratchSuite extends munit.FunSuite:
  test("scratch") {
    List(crm.knowledge).foreach { kb =>
      println(Theories.errors(kb).mkString("\n"))
      println(Theories.problems(kb).mkString("\n"))
      val t = Theories.theory(kb)
      t.nodes.foreach(n => println(s"${n.node.id.value}: ${Checking.of(t, n.node.id).mkString("\n    ")}"))
    }
  }
