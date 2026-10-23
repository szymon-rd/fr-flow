package frflow
package ledger

import cats.effect.IO
import frflow.protocol.*
import io.circe.Json
import java.nio.file.{Files, Path, Paths}
import java.nio.file.attribute.PosixFilePermission

/** Decisions signed with the developer's key; one written into the ledger otherwise shows. Keys live
  * in temporary directories only: the developer's own key is never read.
  */
class SigningSuite extends munit.CatsEffectSuite:

  private def decision(reason: String) =
    Decision(Action.Accept, "dev", "2026-01-01T00:00:00Z", reason, chain = Chain("chain"),
      content = Content("statement" -> Json.fromString("Readers find the books they ask for.")))
  private val (root, part) = (NodeId("Root"), NodeId("Part"))
  private val key = Keys.generate()
  private val keys = Map(key.id -> key.public)
  private def temp(prefix: String): IO[Path] = IO.blocking(Files.createTempDirectory(prefix))

  test("a signed decision verifies; changed, or signed by another key, it does not") {
    val d = Signing.sign(key, root, decision("it is the idea, stated"))
    assert(Signing.verify(keys, root, d))
    assert(!Signing.verify(keys, part, d))
    assert(!Signing.verify(keys, root, d.copy(reason = "another reason")))
    assert(!Signing.verify(Map(Keys.generate().id -> Keys.generate().public), root, d))
    assert(!Signing.verify(keys, root, d.unsigned))
  }

  test("the developer's new decisions are signed; those from before are listed, to sign by their entry") {
    val before = Ledger.empty.add(root, decision("it is the idea, stated"))
    assertEquals(Signing.unsigned(before, keys).map(_._1), List(root))
    assert(Signing.warnings(Map.empty, before).exists(_.startsWith("no developer key")))
    val signed = Signing.signNew(before, before.add(part, decision("it is a part of the root")), key)
    assertEquals(Signing.unsigned(signed, keys).map(_._1), List(root))
    val all = Signing.signEntries(signed, Signing.unsigned(signed, keys).map((_, d) => Ledger.entry(d)).toSet, key)
    assertEquals(Signing.warnings(keys, all), Nil)
    // An entry appended by hand, as an agent with a shell could.
    val forged = all.add(root, decision("forged by someone").copy(at = "2030-01-01T00:00:00Z"))
    assertEquals(Signing.unsigned(forged, keys).map(_._2.reason), List("forged by someone"))
    assert(Signing.warnings(keys, forged).exists(_.contains("is not signed by a developer key")))
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
      none  <- store.projectKeys
      dev   <- store.developer
      _     <- store.publish(dev.public, "dev")
      _     <- store.publish(dev.public, "someone-else")
      files <- IO.blocking(Files.list(keysDir).toArray.toList.map(_.toString))
      known <- store.projectKeys
    yield
      assertEquals(none, Map.empty)
      assertEquals(files, List(keysDir.resolve("dev.pub").toString))
      assert(Signing.verify(known, root, Signing.sign(dev, root, decision("it is the idea, stated"))))
  }
