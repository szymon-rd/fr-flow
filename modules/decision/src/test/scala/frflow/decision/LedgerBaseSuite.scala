package frflow.decision

import frflow.decision.content.Sha
import frflow.decision.ledger.{Decider, Deciders, LedgerBase, Seal, Seals}

/** The ledger's base is signed like the deciders' list: a version counts only when a key a committed list held signed
  * it and it names the one before, the newest signed by a key listed now; the history a ledger is counted against
  * starts at the commit that made the base, whose text must be the base's, and keeps every later version.
  */
class LedgerBaseSuite extends munit.FunSuite:
  private def sign(key: String)(bytes: Array[Byte]): Seal = Seal(key, s"$key:${Sha(String(bytes, "UTF-16"))}")
  private val verify: Seals.Verifier = (s, bytes) => s.signature == sign(s.key)(bytes).signature
  private val (ann, bob) = (Decider("ann", "k1", "public-1"), Decider("bob", "k2", "public-2"))
  private val annOnly = Deciders(List(ann), None, None)
  private val both = Deciders(List(ann, bob), None, None)

  private def base(text: String, before: Option[LedgerBase], key: String): LedgerBase =
    val b = LedgerBase.of(text, before)
    b.copy(seal = Some(sign(key)(b.payload)))

  test("a base counts only when signed by a listed key, after the base before it, and with a deciders' list") {
    val first = base("v2", None, "k1")
    assertEquals(LedgerBase.committed(List(first), List(annOnly), Some(annOnly), verify), Some(first))
    assertEquals(LedgerBase.committed(List(base("v2", None, "k2")), List(annOnly), Some(annOnly), verify), None)
    assertEquals(LedgerBase.committed(List(first), Nil, None, verify), None)
    val second = base("v3", Some(first), "k1")
    assertEquals(LedgerBase.committed(List(first, second), List(annOnly), Some(annOnly), verify), Some(second))
    assertEquals(LedgerBase.committed(List(first, base("v3", None, "k1")), List(annOnly), Some(annOnly), verify), None)
  }

  test("an older version signed by a decider since removed still counts; the newest needs a key listed now") {
    val first = base("v2", None, "k2")
    val second = base("v3", Some(first), "k1")
    assertEquals(LedgerBase.committed(List(first, second), List(both, annOnly), Some(annOnly), verify), Some(second))
    assertEquals(LedgerBase.committed(List(first), List(both, annOnly), Some(annOnly), verify), None)
  }

  test("the history starts at the commit that made the base, and keeps every later version, a text recommitted too") {
    val b = base("v1", None, "k1")
    val commits = List(None -> Some("v0"), Some(b) -> Some("v1"), Some(b) -> Some("v2"), Some(b) -> Some("v1"))
    assertEquals(LedgerBase.from(commits, b), (List("v1", "v2", "v1"), true))
    assertEquals(LedgerBase.from(List(Some(b) -> Some("v2"), Some(b) -> Some("v1")), b),
      (List("v2", "v1"), false))
    assertEquals(LedgerBase.texts(List(None -> Some("v0"), None -> Some("v0"), None -> None, None -> Some("v1"))),
      List("v0", "v1"))
  }
