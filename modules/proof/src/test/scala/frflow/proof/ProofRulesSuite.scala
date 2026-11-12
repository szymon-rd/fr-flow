package frflow.proof

import frflow.core.name.NodeId
import frflow.proof.reading.*

/** One case per rule of `ProofRules`, and what an authored proof may contain. */
class ProofRulesSuite extends munit.FunSuite:
  private def refused(src: String): List[NotAllowed] = ProofRules.notAllowed(ProofFile(NodeId("N"), src)).map(_._2)

  private val allowed = """Require Export FrFlowGen.Crm.Domain.
    |Require Export FrFlowGen.Crm.ExpiryJob.Spec.
    |Require Export Proofs.Crm.Lemmas.
    |From FrFlow Require Export Base.
    |From Stdlib Require Import Lia.
    |
    |(** Why it holds. Admitted in a comment is not a proof given up. *)
    |Lemma ExpiryJob_Proofs_impl : ExpiryJob_Obl_impl.
    |Proof.
    |  intros; cbn.
    |  - apply (f "Axiom").
    |  - { lia. }
    |Qed.
    |""".stripMargin

  test("lemmas over the specs, each proven by tactics, are allowed")(assertEquals(refused(allowed), Nil))

  private val cases = List(
    "Axiom bad : False."                       -> NotAllowed.Axiom,
    "Parameter x : nat."                       -> NotAllowed.Axiom,
    "Admitted."                                -> NotAllowed.Admit,
    "  admit."                                 -> NotAllowed.Admit,
    "  give_up."                               -> NotAllowed.Admit,
    "Require Import Mathlib.Tactic."           -> NotAllowed.Import("Mathlib.Tactic"),
    "Require Export Proofs.Crm.Other."         -> NotAllowed.Import("Proofs.Crm.Other"),
    "Definition helper : nat := 1."            -> NotAllowed.Command("Definition"),
    "Ltac t := auto."                          -> NotAllowed.Command("Ltac"),
    "Set Printing All."                        -> NotAllowed.Command("Set"))

  cases.foreach((line, rule) => test(s"refused: $line")(assert(refused(line).contains(rule), refused(line))))

  test("the shared lemmas import no lemmas") {
    val lemmas = ProofFile(NodeId("Lemmas"),
      "Require Export Proofs.Crm.Lemmas.\nLemma t : True.\nProof.\n  auto.\nQed.\n")
    assertEquals(ProofRules.notAllowedInLemmas(lemmas).map(_._2), List(NotAllowed.LemmaImport("Proofs.Crm.Lemmas")))
  }
