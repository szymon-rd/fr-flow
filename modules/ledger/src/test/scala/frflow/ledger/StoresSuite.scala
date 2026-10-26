package frflow
package ledger

import cats.effect.{IO, Resource}
import cats.syntax.all.*
import frflow.protocol.*
import io.circe.Json
import java.nio.file.{Files, Paths}
import java.nio.file.attribute.PosixFilePermission
import java.time.Instant
import java.util.Comparator
import scala.util.Using

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
  // A directory for the test, deleted after it.
  private val temp = ResourceFunFixture(Resource.make(IO.blocking(Files.createTempDirectory("frflow-store")))(d =>
    IO.blocking(Using.resource(Files.walk(d))(_.sorted(Comparator.reverseOrder).forEach(Files.delete(_))))))

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

  temp.test("the key is created on first use, readable by its owner only, and read back after") { dir =>
    val store = KeyStore.at(dir.resolve("config/signing.key"), dir.resolve("project/.frflow/keys"))
    for
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

  temp.test("the public key is filed once, under the developer's name, and verifies what they sign") { dir =>
    val keysDir = dir.resolve(".frflow/keys")
    val store = KeyStore.at(dir.resolve("signing.key"), keysDir)
    for
      none  <- KeyStore.projectKeys(keysDir)
      dev   <- store.developer
      _     <- store.publish(dev.public, "dev")
      _     <- store.publish(dev.public, "someone-else")
      // another key under the name is never filed over it
      _     <- store.publish(Keys.generate().public, "dev")
      files <- IO.blocking(Files.list(keysDir).toArray.toList.map(_.toString))
      known <- KeyStore.projectKeys(keysDir)
    yield
      assertEquals(none, Map.empty)
      assertEquals(files, List(keysDir.resolve("dev.pub").toString))
      assert(Signing.verify(known, root, Signing.sign(dev, root, decision("it is the idea, stated"))))
  }

  temp.test("the ledger survives its file, each of concurrent updates seeing the one before; one refused writes nothing; a file that does not read is an error") { dir =>
    val f = dir.resolve(".frflow/ledger.json")
    for
      store   <- JsonStore.ledger(f)
      empty   <- store.load
      refused <- store.update[Refusal, Unit](_ => Left(Refusal.NoReason))
      exists  <- IO.blocking(Files.exists(f))
      _       <- (1 to 20).toList.parTraverse_(i =>
                   store.update[Refusal, Unit](l => Right(l.add(NodeId(s"N$i"), decision(s"reason number $i")) -> ())))
      back    <- JsonStore.ledger(f).flatMap(_.load)
      _       <- IO.blocking(Files.writeString(f, "{ not json"))
      bad     <- store.load.attempt
    yield
      assertEquals((empty, refused, exists), (Ledger.empty, Left(Refusal.NoReason), false))
      assertEquals((back.decisions.size, back.current(NodeId("N7")).map(_.reason)), (20, Some("reason number 7")))
      assert(bad.left.exists(_.isInstanceOf[LedgerError.BadFile]), bad)
  }
