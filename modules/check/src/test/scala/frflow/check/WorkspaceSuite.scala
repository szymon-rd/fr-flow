package frflow
package check

import cats.effect.IO
import cats.syntax.all.*
import frflow.ledger.*
import frflow.fixtures.*
import frflow.protocol.{NodeKind as _, *}
import java.nio.file.{Files, Path}

/** What the checker reads of a workspace on disk, and what deciding writes there. */
class WorkspaceSuite extends munit.CatsEffectSuite:

  private def workspace: IO[Workspace] = IO.blocking {
    val ws = Workspace(Files.createTempDirectory("frflow"), "../lean")
    Files.writeString(ws.root.resolve("IDEA.md"), Desk.idea)
    ws
  }
  private def write(p: Path, text: String): IO[Unit] = IO.blocking(Files.writeString(p, text)).void
  private def accept(w: Workflow, n: Node[?], reason: String): IO[Unit] =
    w.decide(Desk.req(n.id, reason)).flatMap(r => IO.fromEither(r.leftMap(e => AssertionError(e.message))))
  private def acceptAll(w: Workflow): IO[Unit] = w.kb.ordered.traverse_(n => accept(w, n, s"${n.id} is right"))
  private def causes(w: Workflow, id: String): IO[List[String]] =
    w.analysis.map(_.annotated.byId(NodeId(id)).review.causes.map(_.toString))

  test("a change to the implementation's code shows on its contract") {
    for
      ws <- workspace
      impl <- IO.blocking(Files.createTempDirectory("impl").resolve("Impl.scala"))
      _ <- write(impl, "class Impl")
      kb = shelfKb.withImplementation(Implementation("Pick", () => (s: List[Book], n: Int) => s.filter(_.pages >= 100), List(impl.toString, "Model.scala")))
      w <- Workflow(kb, ws)
      _ <- acceptAll(w)
      _ <- w.analysis.map(a => assertEquals(a.state(pick), ReviewState.Accepted))
      _ <- write(impl, "class Impl // faster")
      _ <- causes(w, "Pick").assertEquals(List("code"))
      _ <- w.status.map(s => assert(!s.ok))
      _ <- accept(w, pick, "Same behaviour; examples pass.")
      _ <- w.analysis.map(a => assertEquals(a.state(pick), ReviewState.Accepted))
    yield ()
  }

  test("a design decision governs files, sits under what it serves, and has nothing to prove") {
    val cache = Node.design("Cache", "Shelves are cached in memory.", why = "They change once a day.")("Store.scala").under(pick)
    for
      ws <- workspace
      _ <- write(ws.root.resolve("Store.scala"), "object Store")
      w <- Workflow(shelfWith(pick, cache), ws)
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
      w <- Workflow(shelfWith(pick, one, two), ws)
      warnings <- w.analysis.map(Governance.codeWarnings)
    yield
      assert(warnings.contains("Two governs Cache.scala, which does not exist"), warnings)
      assert(warnings.contains("Store.scala is governed by One and Two: give it one owner"), warnings)
  }

  test("source files no node governs are found outside src/main too; tests are not production code") {
    for
      ws <- workspace
      _ <- IO.blocking(Files.createDirectories(ws.root.resolve("src/fast/scala")))
      _ <- write(ws.root.resolve("src/fast/scala/Leak.scala"), "object Leak")
      _ <- IO.blocking(Files.createDirectories(ws.root.resolve("src/test/scala")))
      _ <- write(ws.root.resolve("src/test/scala/T.scala"), "object T")
      u <- Workflow(shelfKb, ws).flatMap(_.analysis).map(Governance.ungoverned)
    yield
      assert(u.contains("src/fast/scala/Leak.scala"), u)
      assert(!u.exists(_.contains("src/test")), u)
  }

  test("a proof file of no node is warned of") {
    for
      ws <- workspace
      _ <- IO.blocking(Files.createDirectories(ws.lean.resolve("Proofs/Shelf")))
      _ <- write(ws.lean.resolve("Proofs/Shelf/Gone.lean"), "-- proofs of a node renamed\n")
      warnings <- Workflow(shelfKb, ws).flatMap(_.analysis).map(Governance.codeWarnings)
    yield assert(warnings.exists(_.startsWith("lean/Proofs/Shelf/Gone.lean is the proof file of no node")), warnings)
  }

  test("decisions are written to the ledger, compactly; with no developer key, status fails whatever the ledger says") {
    for
      ws <- workspace
      w <- Workflow(shelfKb, ws)
      _ <- acceptAll(w)
      a <- w.analysis
      text <- IO.blocking(Files.readString(ws.ledgerFile))
      s <- w.status
    yield
      assertEquals(io.circe.parser.decode[Ledger](text), Right(a.ledger))
      assert(a.kb.nodes.forall(a.state(_) == ReviewState.Accepted))
      assert(s.warnings.exists(_.startsWith("no developer key")), s.warnings)
      assert(!s.ok)
  }

  test("the snapshot written is the analysis's") {
    for
      ws <- workspace
      w <- Workflow(callsKb, ws)
      a <- w.analysis
      file <- w.writeSnapshot(a)
      text <- IO.blocking(Files.readString(file))
    yield assertEquals(io.circe.parser.decode[Snapshot](text).map(_.nodes.map(_.id)), Right(a.snapshot.nodes.map(_.id)))
  }
