package frflow.project.port

import cats.effect.IO
import cats.syntax.all.*
import frflow.core.name.RelPath
import frflow.project.Live
import frflow.project.port.memory.MemoryFiles
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.Files

/** The laws of the project's files, on each interpreter: a read after a write gives what was written; writing what a
  * file holds writes nothing and says so; a directory lists every file under it, sorted, and a missing one none; a
  * deleted file reads as none. The disk writes UTF-8 whatever the platform's default.
  */
class ProjectFilesSuite extends munit.CatsEffectSuite:
  private def path(s: String) = RelPath.parse(s).fold(e => fail(e.toString), identity)
  private val (a, b, c) = (path("lean/FrFlowGen/A.lean"), path("lean/FrFlowGen/Sub/B.lean"), path("src/C.scala"))

  private def laws(name: String, files: IO[ProjectFiles[IO]], tags: Set[munit.Tag]): Unit =
    written(name, files, tags)
    listed(name, files, tags)

  private def written(name: String, files: IO[ProjectFiles[IO]], tags: Set[munit.Tag]): Unit =
    test(munit.TestOptions(s"$name: a read after a write gives it; the same text again writes nothing")
      .withTags(tags)) {
      for
        f       <- files
        first   <- f.writeIfChanged(a, "théorème α\n")
        again   <- f.writeIfChanged(a, "théorème α\n")
        read    <- f.read(a)
        missing <- f.read(c)
      yield assertEquals((first, again, read, missing), (true, false, Some("théorème α\n"), None))
    }

  private def listed(name: String, files: IO[ProjectFiles[IO]], tags: Set[munit.Tag]): Unit =
    test(munit.TestOptions(s"$name: a directory lists each file under it, sorted; a deleted file reads as none")
      .withTags(tags)) {
      for
        f      <- files
        _      <- List(b -> "b", a -> "a", c -> "c").traverse_((p, t) => f.writeIfChanged(p, t))
        listed <- f.list(path("lean"))
        none   <- f.list(path("nowhere"))
        _      <- f.delete(b)
        gone   <- f.read(b)
        after  <- f.list(path("lean"))
      yield assertEquals((listed, none, gone, after), (List(a, b), Nil, None, List(a)))
    }

  laws("memory", MemoryFiles[IO](Map.empty).widen, Set.empty)
  laws("disk", IO(Files.createTempDirectory("frflow-files")).map(ProjectFiles.make[IO](_)), Set(Live))

  test("the disk writes UTF-8 bytes".tag(Live)) {
    for
      dir <- IO(Files.createTempDirectory("frflow-utf8"))
      _   <- ProjectFiles.make[IO](dir).writeIfChanged(a, "∀ α")
    yield assertEquals(Files.readAllBytes(dir.resolve(a.value)).toList, "∀ α".getBytes(UTF_8).toList)
  }
