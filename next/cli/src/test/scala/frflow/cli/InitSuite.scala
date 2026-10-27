package frflow.cli

import cats.effect.{ExitCode, IO, Resource}
import frflow.api.Opened
import frflow.cli.command.Command
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.Files
import java.security.KeyPairGenerator
import java.util.Base64

/** A new project: its files and its line in build.sbt, written once; the first deciders' list, from the developer's
  * key; and an empty FrModel says what comes next.
  */
class InitSuite extends munit.CatsEffectSuite:
  private val temp = ResourceFunFixture(Resource.make(IO.blocking(Files.createTempDirectory("frflow-init")))(d =>
    IO.blocking(Files.walk(d).sorted(java.util.Comparator.reverseOrder()).forEach(p => Files.delete(p)))))

  temp.test("a new project: an empty FrModel, its examples' class and its line in build.sbt; nothing twice") { d =>
    for
      _     <- IO.blocking(Files.writeString(d.resolve("build.sbt"), "lazy val other = project\n", UTF_8))
      first <- Init.write(d, "toy", None)
      again <- Init.write(d, "toy", None)
      upper <- Init.write(d, "Toy", None)
      build <- IO.blocking(Files.readString(d.resolve("build.sbt"), UTF_8))
      model <- IO.blocking(Files.readString(d.resolve("examples/toy/src/main/scala/toy/Model.scala"), UTF_8))
    yield
      assertEquals(first.map(_.size), Right(3))
      assertEquals(again, Left("examples/toy exists already"))
      assert(build.contains("lazy val toy = nextExample(\"toy\", layers = Nil).dependsOn(nextTesting % Test)"), build)
      assert(build.contains("testFrameworks += TestFramework(\"frflow.testing.examples.ExamplesFramework\")"), build)
      assert(model.contains("object toyCli extends frflow.cli.FrFlowApp(frModel, root = \"examples/toy\")"), model)
      assert(upper.left.exists(_.startsWith("Toy is not a lowercase name")), upper)
  }

  temp.test("deciders --as NAME lists the developer's key as the first decider, signed by it; once") { d =>
    val key = d.resolve("signing.key")
    val p = TestProject(d, Map("FRFLOW_KEY" -> key.toString))
    for
      _      <- IO.blocking(Files.writeString(key, throwaway, UTF_8))
      term   <- Scripted(Nil, interactive = false)
      codes  <- new Launch(p, p.env, Nil).run(Command.Deciders("ann"), term, Cli.plain).flatMap(a =>
                    new Launch(p, p.env, Nil).run(Command.Deciders("bob"), term, Cli.plain).map(List(a, _)))
      text   <- term.text
      listed <- IO.blocking(Files.readString(d.resolve(".frflow/deciders"), UTF_8))
    yield
      assertEquals(codes, List(ExitCode(0), ExitCode(0)))
      assert(text.contains("wrote .frflow/deciders, listing you as the first decider: commit it"), text)
      assert(text.contains(".frflow/deciders is there already"), text)
      assert(listed.contains("\"name\": \"ann\"") && !listed.contains("bob") && listed.contains("\"seal\""), listed)
  }

  test("an empty FrModel says its root statements come first, and is not complete") {
    Opened.api(Opened.project(Shelves.Empty.kb)).flatMap(Cli.all(_, Command.Status(json = false))).map { (codes, t) =>
      assertEquals(codes, List(ExitCode(1)))
      assert(t.contains("FrModel: no nodes yet: propose the root statements first"), t)
    }
  }

  test("a project under examples/NAME requires FrFlow's Lean library, the one the proof suites build") {
    val library = frflow.proof.layout.LeanWorkspace.library
    val root = library.getParent.getParent.getParent
    assertEquals(root.resolve("examples/toy/lean").resolve(FrFlowApp.Library).normalize, library.normalize)
  }

  /** A key made for this test only, in its own directory. */
  private def throwaway: String =
    val pair = KeyPairGenerator.getInstance("Ed25519").generateKeyPair()
    val b64 = Base64.getEncoder
    s"${b64.encodeToString(pair.getPrivate.getEncoded)}\n${b64.encodeToString(pair.getPublic.getEncoded)}\n"
