package frflow.proof.reading

import frflow.core.name.NodeId

/** One case per rule of today's `ProofRules.forbidden`, and what an authored proof may contain. */
class ProofRulesSuite extends munit.FunSuite:
  private def refused(src: String): List[NotAllowed] = ProofRules.notAllowed(ProofFile(NodeId("N"), src)).map(_._2)

  private val allowed = """import FrFlowGen.Crm.Domain
    |import FrFlowGen.Crm.ExpiryJob.Spec
    |import Proofs.Crm.Lemmas
    |set_option maxHeartbeats 400000
    |namespace Crm.ExpiryJob
    |theorem impl : Obl.impl := by
    |  -- native_decide in a comment is not a use of it
    |  unfold Obl.impl; simp [show "axiom" = "axiom" from rfl]
    |end Crm.ExpiryJob
    |""".stripMargin

  test("a proof of theorems over the specs, with an allowed option, is allowed")(assertEquals(refused(allowed), Nil))

  private val cases = List(
    "axiom bad : False"                        -> NotAllowed.Axiom,
    "  admit"                                  -> NotAllowed.Admit,
    "  exact (unsafe foo)"                     -> NotAllowed.Unsafe,
    "  opaque x : Nat"                         -> NotAllowed.Opaque,
    "  @[implemented_by f] theorem t : True"   -> NotAllowed.ImplementedBy,
    "  @[extern \"c\"] theorem t : True"       -> NotAllowed.Extern,
    "  by native_decide"                       -> NotAllowed.NativeDecide,
    "  attribute [simp] foo"                   -> NotAllowed.Attribute,
    "set_option pp.all true"                   -> NotAllowed.SetOption("pp.all"),
    "  #eval 1"                                -> NotAllowed.Metaprogram("#eval"),
    "  run_tac foo"                            -> NotAllowed.Metaprogram("run_tac"),
    "  exact Lean.Meta.foo"                    -> NotAllowed.Metaprogram("Lean."),
    "import Mathlib.Tactic"                    -> NotAllowed.Import("Mathlib.Tactic"),
    "def helper : Nat := 1"                    -> NotAllowed.Command("def"))

  cases.foreach((line, rule) => test(s"refused: ${rule.toString}")(assert(refused(line).contains(rule), refused(line))))

  test("the shared lemmas import no lemmas") {
    val lemmas = ProofFile(NodeId("Lemmas"), "import Proofs.Crm.Lemmas\ntheorem t : True := trivial\n")
    assertEquals(ProofRules.notAllowedInLemmas(lemmas).map(_._2), List(NotAllowed.LemmaImport("Proofs.Crm.Lemmas")))
  }
