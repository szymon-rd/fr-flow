package frflow.project.port

import cats.effect.IO
import frflow.decision.ledger.{Decider, Deciders, Seal}
import frflow.project.port.memory.{MemoryGit, MemoryKeys}
import frflow.wire.file.Files as Wire
import frflow.wire.ledger.DecidersFile
import java.security.KeyPairGenerator
import java.util.Base64

/** Keys as FrFlow uses them, in memory only: a verifier is total (a signature that is not Base64 or not of the right
  * length, an entry whose key is not its public key's id, a public key that is not one: none verifies); a deciders'
  * list counts only when every committed version reads and follows the one before.
  */
class KeysSuite extends munit.CatsEffectSuite:
  private val bytes = "what is signed".getBytes

  test("a seal verifies by the entry its key names; changed bytes, another key or a bad signature do not") {
    MemoryKeys[IO].flatMap(k => k.signer.map { sign =>
      val verify = Keys.verifier(List(k.entry("ann")))
      val other = KeyPairGenerator.getInstance("Ed25519").generateKeyPair().getPrivate
      assert(verify(sign(bytes), bytes))
      assert(!verify(sign(bytes), "other bytes".getBytes))
      assert(!verify(Keys.signer(other, k.id)(bytes), bytes))
      assert(!verify(Seal(k.id, "not base64 at all!"), bytes))
      assert(!verify(Seal(k.id, Base64.getEncoder.encodeToString(Array[Byte](1, 2, 3))), bytes))
    })
  }

  test("an entry whose key is not its public key's id, or whose public key is not one, verifies nothing") {
    MemoryKeys[IO].flatMap(k => k.signer.map { sign =>
      val seal = sign(bytes)
      assert(Keys.verifier(List(k.entry("ann")))(seal, bytes))
      assert(!Keys.verifier(List(k.entry("ann").copy(key = "0123456789abcdef")))(seal.copy(key = "0123456789abcdef"),
        bytes))
      assert(!Keys.verifier(List(Decider("ann", k.id, "bm90IGEga2V5")))(seal, bytes))
    })
  }

  test("a key file's private key signs as its public key's id") {
    val pair = KeyPairGenerator.getInstance("Ed25519").generateKeyPair()
    val (priv, pub) = (Base64.getEncoder.encodeToString(pair.getPrivate.getEncoded),
      Base64.getEncoder.encodeToString(pair.getPublic.getEncoded))
    val read = Keys.read(s"$priv\n$pub\n").fold(fail(_), identity)
    assertEquals(read._2, pub)
    val seal = Keys.signer(read._1, Keys.id(pub))(bytes)
    assert(Keys.verifier(List(Decider("ann", Keys.id(pub), pub)))(seal, bytes))
    assert(Keys.read("one line only").isLeft)
  }

  test("the committed list counts when each version follows the one before; one that does not read, none counts") {
    for
      k    <- MemoryKeys[IO]
      git  <- MemoryGit[IO]
      first = k.signed(Deciders(List(k.entry("ann")), None, None))
      _    <- git.commit(Map(KeyRing.path -> Wire.print(DecidersFile.format, first)))
      read <- KeyRing.versions(git)
      _    <- git.commit(Map(KeyRing.path -> "{ not json"))
      bad  <- KeyRing.versions(git)
      _    <- k.list(first)
      held <- k.deciders
    yield
      assertEquals(read.flatMap(KeyRing.committed), Some(first))
      assertEquals(bad, None)
      assertEquals(held, Some(first))
  }
