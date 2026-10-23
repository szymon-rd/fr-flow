package frflow
package ledger

import cats.effect.IO
import java.nio.file.{Files, Path}

/** The code a decision saw, as git keeps it, in a temporary repository. */
class GitSuite extends munit.CatsEffectSuite:

  private def git(repo: Path, args: String*): IO[Unit] = IO.blocking {
    val p = ProcessBuilder(("git" +: args)*).directory(repo.toFile).redirectErrorStream(true).start()
    p.getInputStream.readAllBytes()
    assertEquals(p.waitFor(), 0, args)
  }
  private def write(f: Path, text: String) = IO.blocking(Files.writeString(f, text)).void

  test("the code a decision saw, diffed: a file git does not track is compared as it is, not shown as deleted") {
    for
      repo <- IO.blocking(Files.createTempDirectory("frflow-git"))
      _    <- git(repo, "init", "-q") *> git(repo, "config", "user.email", "t@example.com") *> git(repo, "config", "user.name", "t")
      dir  <- IO.blocking(Files.createDirectories(repo.resolve("project")))
      _    <- write(repo.resolve("README"), "x\n") *> git(repo, "add", "README") *> git(repo, "commit", "-q", "-m", "first")
      g     = Git.at(dir)
      head <- g.head
      // Untracked: the project's files, before its first commit.
      _    <- write(dir.resolve("Desk.scala"), "val desk = 1\n")
      tree <- g.snapshot(List("Desk.scala", "New.scala")).map(_.getOrElse(""))
      has  <- g.has(tree)
      _    <- write(dir.resolve("Desk.scala"), "val desk = 1\nval members = 2\n") *> write(dir.resolve("New.scala"), "val added = 3\n")
      d    <- g.diff(tree, List("Desk.scala", "New.scala"))
      // Removed from the working tree: shown as deleted.
      _    <- IO.blocking(Files.delete(dir.resolve("Desk.scala")))
      gone <- g.diff(tree, List("Desk.scala"))
      // Nothing changed: no diff; and the repository's own index is untouched.
      _    <- write(dir.resolve("Desk.scala"), "val desk = 1\n")
      same <- g.diff(tree, List("Desk.scala"))
      listed <- IO.blocking(String(ProcessBuilder("git", "ls-files", "Desk.scala").directory(dir.toFile).start().getInputStream.readAllBytes()))
    yield
      assert(head.isDefined && has, (head, tree))
      assert(!d.contains("deleted file"), d)
      assert(d.contains("+val members = 2") && !d.contains("-val desk = 1"), d)
      assert(d.contains("new file") && d.contains("+val added = 3"), d)
      assert(gone.contains("-val desk = 1"), gone)
      assertEquals(same, "")
      assert(listed.trim.isEmpty, listed)
  }

  test("outside git: no commit, no tree, no diff") {
    for
      dir  <- IO.blocking(Files.createTempDirectory("frflow-nogit"))
      g     = Git.at(dir)
      head <- g.head
      tree <- g.snapshot(List("A.scala"))
      has  <- g.has("abc")
    yield assertEquals((head, tree, has), (None, None, false))
  }
