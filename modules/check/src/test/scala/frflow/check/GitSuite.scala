package frflow
package check

import cats.effect.IO
import java.nio.file.{Files, Path}

/** How code changed since a commit, as git says, in a temporary repository. */
class GitSuite extends munit.CatsEffectSuite:

  private def git(repo: Path, args: String*): IO[Unit] = IO.blocking {
    val p = ProcessBuilder(("git" +: args)*).directory(repo.toFile).redirectErrorStream(true).start()
    p.getInputStream.readAllBytes()
    assertEquals(p.waitFor(), 0, args)
  }
  private def write(f: Path, text: String) = IO.blocking(Files.writeString(f, text)).void

  test("the code diffed against a commit: a file git does not track is compared as it is, not shown as deleted") {
    for
      repo <- IO.blocking(Files.createTempDirectory("frflow-git"))
      _    <- git(repo, "init", "-q") *> git(repo, "config", "user.email", "t@example.com") *> git(repo, "config", "user.name", "t")
      dir  <- IO.blocking(Files.createDirectories(repo.resolve("project")))
      _    <- write(dir.resolve("Desk.scala"), "val desk = 1\n") *> git(dir, "add", "Desk.scala") *> git(repo, "commit", "-q", "-m", "first")
      g     = Git.at(dir)
      head <- g.head.map(_.getOrElse(""))
      _    <- write(dir.resolve("Desk.scala"), "val desk = 1\nval members = 2\n") *> write(dir.resolve("New.scala"), "val added = 3\n")
      d    <- g.diff(head, List("Desk.scala", "New.scala"))
      // Removed from the working tree: shown as deleted.
      _    <- IO.blocking(Files.delete(dir.resolve("Desk.scala")))
      gone <- g.diff(head, List("Desk.scala"))
      // Nothing changed: no diff; and the repository's own index is untouched.
      _    <- write(dir.resolve("Desk.scala"), "val desk = 1\n")
      same <- g.diff(head, List("Desk.scala"))
      listed <- IO.blocking(String(ProcessBuilder("git", "ls-files", "New.scala").directory(dir.toFile).start().getInputStream.readAllBytes()))
    yield
      assert(head.nonEmpty)
      assert(d.contains("+val members = 2") && !d.contains("-val desk = 1"), d)
      assert(d.contains("new file") && d.contains("+val added = 3"), d)
      assert(gone.contains("-val desk = 1"), gone)
      assertEquals(same, "")
      assert(listed.trim.isEmpty, listed)
  }

  test("outside git: no commit, no diff") {
    for
      dir  <- IO.blocking(Files.createTempDirectory("frflow-nogit"))
      g     = Git.at(dir)
      head <- g.head
      d    <- g.diff("abc", List("A.scala"))
    yield assertEquals((head, d), (None, ""))
  }
