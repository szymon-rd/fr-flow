package frflow
package check

import cats.effect.IO
import cats.syntax.all.*
import frflow.ledger.*
import frflow.fixtures.*
import frflow.protocol.*
import java.nio.file.{Files, Path}

/** What the checker reads of a workspace on disk, what deciding writes there, and what git says of it. */
class WorkspaceSuite extends munit.CatsEffectSuite with TempDirs:

  private def workspace: IO[Workspace] = IO.blocking {
    val ws = Workspace(tempDir("frflow"), "../lean")
    Files.writeString(ws.root.resolve("IDEA.md"), Desk.idea)
    ws
  }
  private def write(p: Path, text: String): IO[Unit] = IO.blocking(Files.writeString(p, text)).void
  private def git(repo: Path, args: String*): IO[Unit] = IO.blocking {
    val p = ProcessBuilder(("git" +: args)*).directory(repo.toFile).redirectErrorStream(true).start()
    p.getInputStream.readAllBytes()
    assertEquals(p.waitFor(), 0, args)
  }
  private def accept(w: OnDisk, n: Node[?], reason: String): IO[Unit] =
    w.decide(Decide.Accept(List(NodeId(n.id)), reason)).flatMap(r => IO.fromEither(r.leftMap(e => AssertionError(e.message))))
  /** IDEA.md first: the root is decided after it. */
  private def acceptAll(w: OnDisk): IO[Unit] =
    w.decide(Decide.Accept(List(IdeaDecision.Id), "it says what the shelf is for")).flatMap(r => IO.fromEither(r.leftMap(e => AssertionError(e.message)))) *>
      w.kb.ordered.traverse_(n => accept(w, n, s"${n.id} is right"))
  private def state(a: Analysis, n: Node[?]) = a.annotated.byId(NodeId(n.id)).state
  private def causes(w: OnDisk, id: String): IO[List[String]] =
    w.analysis.map(_.annotated.byId(NodeId(id)).review.causes.map(_.toString))

  test("a change to the implementation's code shows on its contract") {
    for
      ws <- workspace
      impl = ws.root.resolve("Impl.scala")
      _ <- write(impl, "class Impl")
      kb = shelfKb.withImplementation(Implementation("Pick", () => (s: List[Book], n: Int) => s.filter(_.pages >= 100), List(impl.toString, "Model.scala")))
      w <- OnDisk(kb, ws)
      _ <- acceptAll(w)
      // all accepted, and status still fails with no developer key: an agent could have written the decisions
      _ <- w.analysis.map(a => assert(state(a, pick) == ReviewState.Accepted && a.warnings.exists(_.startsWith("no developer key")), a.warnings))
      _ <- write(impl, "class Impl // faster")
      _ <- causes(w, "Pick").assertEquals(List("code"))
      _ <- w.analysis.map(a => assert(!OnDisk.ok(a)))
      _ <- accept(w, pick, "Same behaviour; examples pass.")
      _ <- w.analysis.map(a => assertEquals(state(a, pick), ReviewState.Accepted))
    yield ()
  }

  test("a design decision governs files and has nothing to prove; a file it governs changing reviews it") {
    val cache = Node.design("Shelves are cached in memory.", why = "They change once a day.")("Store.scala").refines(pick)
    def governing(fingerprint: String)(d: Desk) = d.copy(inputs = d.inputs.copy(code = Map("Cache" -> CodeRef(List("Store.scala"), Fingerprint(fingerprint)))))
    val d = governing("a")(Desk(shelfWith(pick, cache))).acceptAll
    assertEquals(d.kb.problems, Nil)
    assertEquals((d.node("Cache").node.split, d.node("Cache").node.status, d.node("Cache").node.code.map(_.files)), (None, None, Some(List("Store.scala"))))
    assertEquals(governing("b")(d).causes("Cache"), List("code"))
  }

  test("a node governing a file that does not exist, a file governed by two nodes, and a proof file of no node are warned of") {
    val one = Node.design("The store is kept in one file.", why = "Simple.")("Store.scala").refines(pick)
    val two = Node.design("The store and the cache are kept apart.", why = "Clear.")("Store.scala", "Cache.scala").refines(pick)
    val d = Desk(shelfWith(pick, one, two))
    val warnings = Governance.warnings(Desk(d.kb, d.inputs.copy(missing = Set("Cache.scala"), proofs = Map("Gone" -> "-- a node renamed\n"),
      code = Map("One" -> CodeRef(List("Store.scala"), Fingerprint("f")), "Two" -> CodeRef(List("Store.scala", "Cache.scala"), Fingerprint("g"))))).analysis)
    assert(warnings.contains("Two governs Cache.scala, which does not exist"), warnings)
    assert(warnings.contains("Store.scala is governed by One and Two: give it one owner"), warnings)
    assert(warnings.exists(_.startsWith("lean/Proofs/Shelf/Gone.lean is the proof file of no node")), warnings)
  }

  test("a statement whose Lean takes what an assumption says of what comes from outside lists that assumption") {
    val warnings = Governance.warnings(Desk(Refunds.kb).analysis)
    // both take an amount as given, its rule a hypothesis of their Lean; neither lists the assumption
    assert(warnings.exists(_.startsWith("Refunded rests on NoNegativeAmounts:")), warnings)
    assert(warnings.exists(_.startsWith("Costs rests on NoNegativeAmounts:")), warnings)
    val listed = Refunds.costs.assuming(Refunds.noNegativeAmounts)
    val kb =
      FrModel("Refunds", idea = "IDEA.md")(Refunds.refunded, listed, Refunds.tillAdds, Refunds.noNegativeAmounts)
    assert(!Governance.warnings(Desk(kb).analysis).exists(_.startsWith("Costs rests on")))
  }

  test("what is proven or tested lists the assumption it rests on; a leaf with nothing to prove and no code need not") {
    import Concepts.*
    val sent = Node.assumption("Requests are sizes.")(always[BigInt](x => x >= BigInt(0)))
    val level = Declaration[World => BigInt]("how far the count has come, as the world stands")
    val levelIsCount = Node.claim("The level is the count.")(forall((now: Term[World]) => level(now) === counted.in(now)))
    val kb = FrModel("Concepts", idea = "IDEA.md")(grows, neverNegative, stepPositive, levelIsCount, model, writes,
      oneAtATime, startsAtNothing, sent).implementProven(add)(adding).implementTested(step)(x => x.abs + 1)
    val warnings = Governance.warnings(Desk(kb).analysis).filter(_.contains(" rests on Sent:"))
    // proven by kept_by_add, tested, proven of its code: each takes the rule; what the Declaration is only carries it
    assertEquals(warnings.map(_.takeWhile(_ != ' ')).sorted, List("Grows", "NeverNegative", "StepPositive"))
  }

  test("source files no node governs are found under src/main and in what the build compiles; tests are not production code") {
    for
      ws <- workspace
      _ <- IO.blocking(Files.createDirectories(ws.root.resolve("src/main/scala")))
      _ <- write(ws.root.resolve("src/main/scala/Leak.scala"), "object Leak")
      _ <- IO.blocking(Files.createDirectories(ws.root.resolve("src/fast/scala")))
      _ <- write(ws.root.resolve("src/fast/scala/Fast.scala"), "object Fast")
      _ <- IO.blocking(Files.createDirectories(ws.root.resolve("src/test/scala")))
      _ <- write(ws.root.resolve("src/test/scala/T.scala"), "object T")
      cfg <- Config.load.map(_.copy(sources = List(ws.root.resolve("src/fast/scala/Fast.scala"))))
      u <- Inputs.read(shelfKb, ws, cfg, IO.pure(Ledger.empty)).map(in => Governance.ungoverned(Analysis(shelfKb, ws, in)))
    yield assertEquals(u, List("src/fast/scala/Fast.scala", "src/main/scala/Leak.scala"))
  }

  test("a FrModel without an idea reads none, though the project has an IDEA.md") {
    val noIdea = FrModel("Shelf")(shelfKb.nodes*)
    for
      ws <- workspace
      _ <- write(ws.root.resolve("IDEA.md"), "# Shelf\n\nReaders find books.\n")
      cfg <- Config.load
      without <- Inputs.read(noIdea, ws, cfg, IO.pure(Ledger.empty))
      withIdea <- Inputs.read(shelfKb, ws, cfg, IO.pure(Ledger.empty))
    yield
      assertEquals((noIdea.idea, without.idea), ("", ""))
      assert(withIdea.idea.contains("Readers find books."), withIdea.idea)
      assertEquals(Governance.warnings(Analysis(noIdea, ws, without)).filter(_.contains("IDEA")), Nil)
  }

  test("the code diffed against a commit: a file git does not track is compared as it is, not shown as deleted") {
    for
      repo <- IO.blocking(tempDir("frflow-git"))
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
      dir  <- IO.blocking(tempDir("frflow-nogit"))
      g     = Git.at(dir)
      head <- g.head
      d    <- g.diff("abc", List("A.scala"))
    yield assertEquals((head, d), (None, ""))
  }
