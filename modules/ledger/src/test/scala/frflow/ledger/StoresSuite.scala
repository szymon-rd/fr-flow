package frflow
package ledger

import cats.effect.IO
import cats.syntax.all.*
import frflow.protocol.*
import io.circe.Json
import java.nio.file.{Files, Path, Paths}
import java.nio.file.attribute.PosixFilePermission
import java.time.Instant

/** Decisions signed with the developer's key, and the files the ledger module keeps (the ledger, the requests, the keys),
  * in temporary directories only: the developer's own key is never read.
  */
class StoresSuite extends munit.CatsEffectSuite:

  private val now = Instant.parse("2026-01-01T00:00:00Z")
  private def decision(reason: String) =
    Decision(Action.Accept, "dev", now, reason, chain = Chain("chain"),
      content = Content("statement" -> Json.fromString("Readers find the books they ask for.")))
  private val (root, part) = (NodeId("Root"), NodeId("Part"))
  private val key = Keys.generate()
  private val keys = Map(key.id -> key.public)
  private def temp(prefix: String): IO[Path] = IO.blocking(Files.createTempDirectory(prefix))
  private def file(name: String): IO[Path] = temp("frflow-store").map(_.resolve(s".frflow/$name"))

  test("a signed decision verifies; changed, or signed by another key, it does not") {
    val d = Signing.sign(key, root, decision("it is the idea, stated"))
    assert(Signing.verify(keys, root, d))
    assert(!Signing.verify(keys, part, d))
    assert(!Signing.verify(keys, root, d.copy(reason = "another reason")))
    assert(!Signing.verify(Map(Keys.generate().id -> Keys.generate().public), root, d))
    assert(!Signing.verify(keys, root, d.unsigned))
  }

  test("the developer's new decisions are signed; one written otherwise is listed, and warned of") {
    val before = Ledger.empty.add(root, decision("it is the idea, stated"))
    assertEquals(Signing.unsigned(before, keys).map(_._1), List(root))
    assert(Signing.warnings(Map.empty, before, Nil).exists(_.startsWith("no developer key")))
    val all = Signing.signNew(Ledger.empty, before.add(part, decision("it is a part of the root")), key)
    assertEquals(Signing.unsigned(all, keys), Nil)
    // An entry appended by hand, as an agent with a shell could.
    val forged = all.add(root, decision("forged by someone").copy(at = Instant.parse("2030-01-01T00:00:00Z")))
    assertEquals(Signing.unsigned(forged, keys).map(_._2.reason), List("forged by someone"))
    assert(Signing.warnings(keys, forged, Signing.unsigned(forged, keys)).exists(_.contains("is not signed by a developer key")))
  }

  test("a key survives its two-line text; text that is not a key does not read") {
    assertEquals(Keys.decode(Keys.encode(key)).map(_.id), Right(key.id))
    assertEquals(Keys.decodePublic(Keys.encodePublic(key.public)).map(Keys.id), Right(key.id))
    assert(Keys.decode("one line").isLeft)
    assert(Keys.decode("bm90IGEga2V5\nbm90IGEga2V5\n").isLeft)
  }

  test("the developer's key is FRFLOW_KEY's, or in ~/.config/frflow") {
    val home = Paths.get("/home/someone")
    assertEquals(KeyStore.keyFile(Map.empty, home), home.resolve(".config/frflow/signing.key"))
    assertEquals(KeyStore.keyFile(Map("FRFLOW_KEY" -> "/keys/dev.key"), home), Paths.get("/keys/dev.key"))
    assertEquals(KeyStore.keyFile(Map("FRFLOW_KEY" -> " "), home), home.resolve(".config/frflow/signing.key"))
  }

  test("the key is created on first use, readable by its owner only, and read back after") {
    for
      dir   <- temp("frflow-key")
      store  = KeyStore.at(dir.resolve("config/signing.key"), dir.resolve("project/.frflow/keys"))
      made  <- store.developer
      again <- store.developer
      perms <- IO.blocking(Files.getPosixFilePermissions(dir.resolve("config/signing.key")))
      _     <- IO.blocking(Files.writeString(dir.resolve("config/signing.key"), "not a key"))
      bad   <- store.developer.attempt
    yield
      assertEquals(again.id, made.id)
      assertEquals(perms, java.util.Set.of(PosixFilePermission.OWNER_READ, PosixFilePermission.OWNER_WRITE))
      assert(bad.left.exists(_.isInstanceOf[LedgerError.BadKey]), bad)
  }

  test("the public key is filed once, under the developer's name, and verifies what they sign") {
    for
      dir   <- temp("frflow-keys")
      keysDir = dir.resolve(".frflow/keys")
      store  = KeyStore.at(dir.resolve("signing.key"), keysDir)
      none  <- KeyStore.projectKeys(keysDir)
      dev   <- store.developer
      _     <- store.publish(dev.public, "dev")
      _     <- store.publish(dev.public, "someone-else")
      files <- IO.blocking(Files.list(keysDir).toArray.toList.map(_.toString))
      known <- KeyStore.projectKeys(keysDir)
    yield
      assertEquals(none, Map.empty)
      assertEquals(files, List(keysDir.resolve("dev.pub").toString))
      assert(Signing.verify(known, root, Signing.sign(dev, root, decision("it is the idea, stated"))))
  }

  test("the ledger survives its file; a file that does not read is an error, not an empty ledger") {
    for
      f     <- file("ledger.json")
      store <- JsonStore.make(f, Ledger.empty)
      empty <- store.load
      l      = Ledger.empty.add(NodeId("Root"), decision("it is the idea"))
      _     <- store.update(_ => Right(l -> ()))
      back  <- store.load
      _     <- IO.blocking(Files.writeString(f, "{ not json"))
      bad   <- store.load.attempt
    yield
      assertEquals(empty, Ledger.empty)
      assertEquals(back, l)
      assert(bad.left.exists(_.isInstanceOf[LedgerError.BadFile]), bad)
  }

  test("an update refused writes nothing; concurrent updates each see the one before") {
    for
      f       <- file("ledger.json")
      store   <- JsonStore.make(f, Ledger.empty)
      refused <- store.update[Refusal, Unit](_ => Left(Refusal.NoReason))
      exists  <- IO.blocking(Files.exists(f))
      _       <- (1 to 20).toList.parTraverse_(i =>
                   store.update[Refusal, Unit](l => Right(l.add(NodeId(s"N$i"), decision(s"reason number $i")) -> ())))
      after   <- store.load
    yield
      assertEquals(refused, Left(Refusal.NoReason))
      assert(!exists)
      assertEquals(after.decisions.size, 20)
  }

  test("requests are asked, answered and closed in their file") {
    for
      f        <- file("requests.json")
      store    <- JsonStore.make(f, List.empty[Request])
      none     <- store.load
      asked    <- store.update[Refusal, Request](rs => Right(Requests.ask(rs, Some(NodeId("Pick")), "Pick faster.", "dev", now)))
      answered <- store.update(Requests.answer(_, "Pick", "Picking is now quicker.", _ => false, now))
      unknown  <- store.update(Requests.answer(_, "Nowhere", "text", _ => false, now))
      closed   <- store.update(Requests.close(_, asked.toOption.map(_.id).toList))
      all      <- store.load
    yield
      assertEquals(none, Nil)
      assertEquals(answered.map(r => (r.id, r.answer)), asked.map(a => (a.id, Some("Picking is now quicker."))))
      assertEquals(unknown, Left(Refusal.UnknownRequest("Nowhere")))
      assertEquals(closed.map(_.map(_.status)), Right(List(RequestStatus.Closed)))
      assertEquals(all.map(r => (r.status, r.answer)), List((RequestStatus.Closed, Some("Picking is now quicker."))))
  }
