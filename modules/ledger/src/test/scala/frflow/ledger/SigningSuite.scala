package frflow
package ledger

import frflow.protocol.*
import io.circe.Json
import java.nio.file.Files

/** Decisions signed with the developer's key; one written into the ledger otherwise shows. */
class SigningSuite extends munit.FunSuite:

  private def decision(reason: String) =
    Decision(Action.Accept, "dev", "2026-01-01T00:00:00Z", reason, chain = Chain("chain"),
      content = Content("statement" -> Json.fromString("Readers find the books they ask for.")))
  private val (root, part) = (NodeId("Root"), NodeId("Part"))

  test("decisions signed by a key in .frflow/keys verify; one appended by hand, or changed, does not") {
    val dir = Files.createTempDirectory("frflow-signing")
    val keysDir = dir.resolve(".frflow/keys")
    val ledgerFile = dir.resolve(".frflow/ledger.json")
    val (priv, pub) = Signing.loadOrCreate(Files.createTempDirectory("frflow-key").resolve("signing.key"))
    // decisions recorded before the project had a key are no warning of their own, but status fails without a key
    val before = Ledger.empty.add(root, decision("it is the idea, stated"))
    assertEquals(Signing.unsigned(before, keysDir), List(root -> before.current(root).get))
    assert(Signing.warnings(ledgerFile, before).exists(_.startsWith("no developer key")))
    Signing.publish(pub, keysDir, "dev")
    assertEquals(Signing.keys(keysDir).size, 1)
    assert(Files.exists(keysDir.resolve("dev.pub")))
    // the developer's new decisions are signed; those from before are listed, to sign by their entry
    val now = before.add(part, decision("it is a part of the root"))
    val signed = Signing.signNew(before, now, priv, pub)
    assertEquals(Signing.unsigned(signed, keysDir).map(_._1), List(root))
    val all = Signing.signEntries(signed, Signing.unsigned(signed, keysDir).map((_, d) => Ledger.entry(d)).toSet, priv, pub)
    assertEquals(Signing.unsigned(all, keysDir), Nil)
    assertEquals(Signing.warnings(ledgerFile, all), Nil)
    // survives the file
    LedgerStore.save(ledgerFile, all)
    assertEquals(Signing.unsigned(LedgerStore.load(ledgerFile), keysDir), Nil)
    // an entry appended by hand, as an agent with a shell could, and a signed one altered
    val forged = all.add(root, all.current(root).get.unsigned.copy(at = "2030-01-01T00:00:00Z", reason = "forged by someone"))
    assertEquals(Signing.unsigned(forged, keysDir).map(_._2.reason), List("forged by someone"))
    assert(Signing.warnings(ledgerFile, forged).exists(_.contains("not signed by a developer key")))
    val altered = Ledger(all.decisions.updated(part, all.history(part).map(_.copy(reason = "another reason"))))
    assertEquals(Signing.unsigned(altered, keysDir).map(_._1), List(part))
    // the developer signs only what is theirs
    val vouched = Signing.signEntries(forged, Signing.unsigned(forged, keysDir).map((_, d) => Ledger.entry(d)).toSet, priv, pub)
    assertEquals(Signing.unsigned(vouched, keysDir), Nil)
  }
