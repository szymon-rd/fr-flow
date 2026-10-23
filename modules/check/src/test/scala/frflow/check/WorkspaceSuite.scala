package frflow
package check

import cats.effect.IO
import cats.syntax.all.*
import frflow.ledger.*
import frflow.fixtures.*
import frflow.protocol.*
import java.nio.file.{Files, Path}

/** What the checker reads of a workspace on disk, and what deciding writes there. */
class WorkspaceSuite extends munit.CatsEffectSuite:

  private def workspace: IO[Workspace] = IO.blocking {
    val ws = Workspace(Files.createTempDirectory("frflow"), "../lean")
    Files.writeString(ws.root.resolve("IDEA.md"), Desk.idea)
    ws
  }
  private def write(p: Path, text: String): IO[Unit] = IO.blocking(Files.writeString(p, text)).void
  private def accept(w: OnDisk, n: Node[?], reason: String): IO[Unit] =
    w.decide(Decide.Accept(List(NodeId(n.id)), reason)).flatMap(r => IO.fromEither(r.leftMap(e => AssertionError(e.message))))
  private def acceptAll(w: OnDisk): IO[Unit] = w.kb.ordered.traverse_(n => accept(w, n, s"${n.id} is right"))
  private def state(a: Analysis, n: Node[?]) = a.annotated.byId(NodeId(n.id)).state
  private def causes(w: OnDisk, id: String): IO[List[String]] =
    w.analysis.map(_.annotated.byId(NodeId(id)).review.causes.map(_.toString))

  test("a change to the implementation's code shows on its contract") {
    for
      ws <- workspace
      impl <- IO.blocking(Files.createTempDirectory("impl").resolve("Impl.scala"))
      _ <- write(impl, "class Impl")
      kb = shelfKb.withImplementation(Implementation("Pick", () => (s: List[Book], n: Int) => s.filter(_.pages >= 100), List(impl.toString, "Model.scala")))
      w <- OnDisk(kb, ws)
      _ <- acceptAll(w)
      _ <- w.analysis.map(a => assertEquals(state(a, pick), ReviewState.Accepted))
      _ <- write(impl, "class Impl // faster")
      _ <- causes(w, "Pick").assertEquals(List("code"))
      _ <- w.analysis.map(a => assert(!OnDisk.ok(a)))
      _ <- accept(w, pick, "Same behaviour; examples pass.")
      _ <- w.analysis.map(a => assertEquals(state(a, pick), ReviewState.Accepted))
    yield ()
  }

  test("a design decision governs files, sits under what it serves, and has nothing to prove") {
    val cache = Node.design("Cache", "Shelves are cached in memory.", why = "They change once a day.")("Store.scala").under(pick)
    for
      ws <- workspace
      _ <- write(ws.root.resolve("Store.scala"), "object Store")
      w <- OnDisk(shelfWith(pick, cache), ws)
      _ = assertEquals(w.kb.problems, Nil)
      _ <- acceptAll(w)
      node <- w.analysis.map(_.annotated.byId(NodeId("Cache")).node)
      _ = assertEquals((node.split, node.status), (None, None))
      _ = assertEquals(node.code.map(_.files), Some(List("Store.scala")))
      _ <- write(ws.root.resolve("Store.scala"), "object Store // redis")
      _ <- causes(w, "Cache").assertEquals(List("code"))
    yield ()
  }

  test("a node governing a file that does not exist, and a file governed by two nodes, are warned of") {
    val one = Node.design("One", "The store is kept in one file.", why = "Simple.")("Store.scala").under(pick)
    val two = Node.design("Two", "The store and the cache are kept apart.", why = "Clear.")("Store.scala", "Cache.scala").under(pick)
    for
      ws <- workspace
      _ <- write(ws.root.resolve("Store.scala"), "object Store")
      w <- OnDisk(shelfWith(pick, one, two), ws)
      warnings <- w.analysis.map(Governance.codeWarnings)
    yield
      assert(warnings.contains("Two governs Cache.scala, which does not exist"), warnings)
      assert(warnings.contains("Store.scala is governed by One and Two: give it one owner"), warnings)
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

  test("a proof file of no node is warned of") {
    for
      ws <- workspace
      _ <- IO.blocking(Files.createDirectories(ws.lean.resolve("Proofs/Shelf")))
      _ <- write(ws.lean.resolve("Proofs/Shelf/Gone.lean"), "-- proofs of a node renamed\n")
      warnings <- OnDisk(shelfKb, ws).flatMap(_.analysis).map(Governance.codeWarnings)
    yield assert(warnings.exists(_.startsWith("lean/Proofs/Shelf/Gone.lean is the proof file of no node")), warnings)
  }

  test("decisions are written to the ledger, compactly; with no developer key, status fails whatever the ledger says") {
    for
      ws <- workspace
      w <- OnDisk(shelfKb, ws)
      _ <- acceptAll(w)
      a <- w.analysis
      text <- IO.blocking(Files.readString(ws.ledgerFile))
    yield
      assertEquals(io.circe.parser.decode[Ledger](text), Right(a.ledger))
      assert(a.kb.nodes.forall(state(a, _) == ReviewState.Accepted))
      assert(a.warnings.exists(_.startsWith("no developer key")), a.warnings)
      assert(!OnDisk.ok(a))
  }

  test("the snapshot written is the analysis's") {
    for
      ws <- workspace
      w <- OnDisk(callsKb, ws)
      a <- w.analysis
      file <- CheckRunner.writeSnapshot(a)
      text <- IO.blocking(Files.readString(file))
    yield assertEquals(io.circe.parser.decode[Snapshot](text).map(_.nodes.map(_.id)), Right(a.snapshot.nodes.map(_.id)))
  }
