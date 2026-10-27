package frflow
package cli

import java.nio.file.{Files, Path}

class InitSuite extends munit.FunSuite:
  private val temp = FunFixture[Path](_ => Files.createTempDirectory("frflow-init"), d =>
    Files.walk(d).sorted(java.util.Comparator.reverseOrder()).forEach(Files.delete))

  temp.test("a new project: an empty FrModel and its line in build.sbt; nothing twice") { d =>
    Files.writeString(d.resolve("build.sbt"), "lazy val auth = example(\"auth\")\n")
    val made = Init.write(d, "toy")
    assertEquals(made.map(_.size), Right(2))
    val kb = Files.readString(d.resolve("examples/toy/src/main/scala/toy/Knowledge.scala"))
    assert(kb.contains("""val knowledge = FrModel("Toy", idea = "IDEA.md")()"""), kb)
    assert(kb.contains("""object toyCli extends frflow.cli.FrFlowApp(knowledge, root = "examples/toy")"""), kb)
    // a core project: no layer on top on its classpath
    assert(Files.readString(d.resolve("build.sbt")).linesIterator.contains("""lazy val toy = example("toy", layers = Nil)"""))
    // no IDEA.md: the developer writes what the system is for
    assert(!Files.exists(d.resolve("examples/toy/IDEA.md")))
    assertEquals(Init.write(d, "toy"), Left("examples/toy exists already"))
    assert(Init.write(d, "Toy").isLeft && Init.write(d, "auth").isLeft && Init.write(d.resolve("nowhere"), "x").isLeft)
  }

  test("an empty FrModel is valid: IDEA.md comes before the root") {
    assertEquals(FrModel("Toy", idea = "IDEA.md")().problems, Nil)
  }
