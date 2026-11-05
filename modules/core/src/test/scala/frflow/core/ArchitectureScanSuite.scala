package frflow.core

/** `ArchitectureSuite`'s scan, on files seeded with each way round a rule the review found: it reads names in braces,
  * wildcards, relative names and split package clauses, and not a comment or a string.
  */
class ArchitectureScanSuite extends munit.FunSuite:
  private def at(module: String, pkg: String, name: String = "A") =
    s"modules/$module/src/main/scala/${pkg.replace('.', '/')}/$name.scala"
  private def one(text: String, module: String = "core", pkg: String = "frflow.core") =
    Sources(List(at(module, pkg) -> text)).main.head

  test("names: a path, names in braces and the facade; not a comment or a string") {
    def named(text: String) = Source.Named.findAllMatchIn(Source.code(text)).map(_.matched).toList
    assertEquals(named("import frflow.core.spec.{NodeKind, Statement}"), List("frflow.core.spec"))
    assertEquals(named("import frflow.{api as a, Node}\nimport frflow.*"), List("frflow.{api as a, Node}", "frflow.*"))
    assertEquals(named("// frflow.project\n/* frflow.wire */ val s = \"frflow.proof\""), Nil)
    assert(Ref("frflow.core.spec.x").within("core.spec") && Ref("frflow.core.spec").within("core"))
    assert(!Ref("frflow.core.specs").within("core.spec") && Ref("frflow").within("eval"))
  }

  test("the environment, randomness and files, however imported, are impure; a word in a string is not") {
    val seeded = List("val e = sys.env(\"HOME\")", "val p = sys.props(\"x\")", "val p = System.getProperty(\"x\")",
      "import scala.util.{Random, Try}\nval n = Random.nextInt()", "val r = new java.util.Random()",
      "import java.nio.file.*\nval b = Files.exists(Paths.get(\"\"))", "import cats.effect.IO")
    assertEquals(seeded.filter(s => Architecture.impure(one(s)).isEmpty), Nil)
    val quiet = List("val s = \"sys.env\"", "// Random", "val r = java.security.SecureRandom()")
    assertEquals(quiet.filter(s => Architecture.impure(one(s)).nonEmpty), Nil)
  }

  test("a lock of the JDK's, a semaphore, a monitor or an atomic is a lock") {
    val seeded = List("import java.util.concurrent.locks.ReentrantLock", "val s = Semaphore[IO](1)",
      "def f = synchronized(1)", "import java.util.concurrent.atomic.AtomicLong", "val m = Mutex[IO]")
    assertEquals(seeded.filter(s => Architecture.locks(one(s)).isEmpty), Nil)
  }

  test("an example's model may name the facade only, its app the front ends' entry points too") {
    val model = "examples/x/src/main/scala/x/K.scala"
    val app = "examples/x/app/src/main/scala/x/XCli.scala"
    val files = Sources(List(model -> "package x\n\nimport frflow.*\nimport frflow.eval.flow.Wall\n",
      app -> "package x\n\nimport frflow.*\nobject XCli extends frflow.cli.FrFlowApp(k)\nval c = frflow.cli.text.X\n"))
    val allowed = Map("model" -> List("frflow"), "app" -> List("frflow", "frflow.cli", "frflow.agent"))
    assertEquals(Architecture.outsideFacade(files.all, allowed),
      List(s"$model: frflow.eval.flow", s"$app: frflow.cli.text"))
  }

  test("a split package clause is seen, and the relative names it makes visible are read as the packages they are") {
    val files = Sources(List(
      at("decision", "frflow.decision.ledger") -> "package frflow.decision\npackage ledger\n\nimport rules.Refusal\n",
      at("decision", "frflow.decision.rules") -> "package frflow.decision.rules\n\nimport frflow.decision.ledger.L\n"))
    assertEquals(files.main.map(_.clauses.size), List(2, 1))
    assertEquals(Cycles.of(files.main), List(List("frflow.decision.ledger", "frflow.decision.rules")))
  }

  test("a subpackage named relatively, and another module named through a split clause, are edges") {
    val cli = at("cli", "frflow.cli")
    val files = Sources(List(
      at("core", "frflow.core.analysis") -> "package frflow.core.analysis\n\nval g = outside.Guards.of\n",
      at("core", "frflow.core.analysis.outside", "Guards") ->
        "package frflow.core.analysis.outside\n\nimport frflow.core.analysis.A\n",
      cli -> "package frflow\npackage cli\n\nimport project.Live\n",
      at("project", "frflow.project", "Live") -> "package frflow.project\n"))
    assertEquals(Cycles.of(files.main.filter(_.module == "core")),
      List(List("frflow.core.analysis", "frflow.core.analysis.outside")))
    assertEquals(Architecture.crossing(files.main, Map("cli" -> List("api"))),
      List(cli + ": frflow.project"))
  }
