package frflow.project.port

import cats.effect.IO
import cats.syntax.all.*
import frflow.core.name.RelPath
import frflow.project.Live
import java.nio.file.{Files, Path}

/** The laws of the repository, on each interpreter: `committed(p)` is the last of `versions(p)`, oldest first, a
  * commit leaving the file as it was not counted again; before a first commit there is no head and nothing
  * committed. The live one runs `git` in a repository made for the test.
  */
class GitSuite extends munit.CatsEffectSuite:
  private val file = RelPath.fromIdentifiers(".frflow", "deciders")
  private val other = RelPath.fromIdentifiers("src", "Other.scala")

  /** Commits `files` over the last commit; the commit's hash. */
  private trait Committing:
    def git: Git[IO]
    def commit(files: Map[RelPath, String]): IO[String]

  private def laws(name: String, make: IO[Committing], tags: Set[munit.Tag]): Unit =
    test(munit.TestOptions(s"$name: committed is the last version; versions are oldest first, each once")
      .withTags(tags)) {
      for
        r      <- make
        before <- (r.git.head, r.git.committed(file), r.git.versions(file)).tupled
        _      <- r.commit(Map(file -> "one"))
        _      <- r.commit(Map(other -> "x"))
        last   <- r.commit(Map(file -> "two"))
        after  <- (r.git.head, r.git.committed(file), r.git.versions(file)).tupled
      yield
        assertEquals(before, (None, None, Nil))
        assertEquals(after, (Some(last), Some("two"), List("one", "two")))
    }

  laws("memory", MemoryGit[IO].map(g => new Committing:
    def git: Git[IO] = g
    def commit(files: Map[RelPath, String]): IO[String] = g.commit(files)), Set.empty)

  laws("git", IO(Files.createTempDirectory("frflow-git")).flatTap(d => run(d, "init", "-q")).map(d => new Committing:
    def git: Git[IO] = Git.make[IO](d)
    def commit(files: Map[RelPath, String]): IO[String] = IO.blocking {
      files.keys.foreach(p => Files.createDirectories(d.resolve(p.value).getParent): Unit)
      files.foreach((p, t) => Files.writeString(d.resolve(p.value), t): Unit)
    } >> run(d, "add", "-A") >> run(d, "-c", "user.name=FrFlow test", "-c", "user.email=test@frflow.invalid",
      "commit", "-q", "-m", "test") >> run(d, "rev-parse", "HEAD").map(_.trim)), Set(Live))

  /** `git` in `d`: its standard output. */
  private def run(d: Path, args: String*): IO[String] = IO.blocking {
    val p = ProcessBuilder(("git" +: args)*).directory(d.toFile).redirectErrorStream(false).start()
    val out = String(p.getInputStream.readAllBytes())
    val _ = p.waitFor()
    out
  }
