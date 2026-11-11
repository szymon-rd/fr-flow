import FrFlowGen.Payments.Domain

/-! What the proofs of the payment stream share: how a payment is handled among other calls, step by step. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Payments.Lemmas
open Payments

/-- A statement that holds when its condition does is the condition failing or the statement. -/
theorem or_of_imp {a b : Prop} (h : a → b) : ¬a ∨ b :=
  (Classical.em a).elim (fun ha => Or.inr (h ha)) Or.inl

/-- What other calls keep, the pipeline a step starts from has: what the schedule says they left before step
`k`, when it is one they may leave (`others`), else the pipeline the call last saw. -/
theorem admitted_keeps (p : Payment) (between : Int → Option Pipeline) (P : Pipeline → Prop)
    (hrely : ∀ b s, P b → others p b s → P s) (k : Int) (b : Pipeline) (hb : P b) :
    P (if others p b (Option.getD (between k) b) then Option.getD (between k) b else b) := by
  by_cases h : others p b (Option.getD (between k) b)
  · simp only [h, ite_true]
    exact hrely b _ hb h
  · simp only [h, ite_false]
    exact hb

/-- Handling a payment among other calls, step by step. The pipeline has `P0` at the start; once the payment is
assessed it has `P1` of the answer; once it is posted, or was declined, it has `P2`. Other calls keep `P1` and
`P2`, and each of the stores' transactions, made from a pipeline that has what holds at its point, makes a step
`Q` holds of and leaves a pipeline that has what holds after it. Then `Q` holds of every step, on every
schedule. -/
theorem every_step (assess : Spending → Payment → (Prop × Spending))
    (postOnce : Books → Payment → (Unit × Books)) (advance : Int → Int → (Unit × Int))
    (p : Payment) (between : Int → Option Pipeline) (P0 P2 : Pipeline → Prop) (P1 : Prop → Pipeline → Prop)
    (Q : Pipeline × Pipeline → Prop)
    (h1 : ∀ a b s, P1 a b → others p b s → P1 a s) (h2 : ∀ b s, P2 b → others p b s → P2 s)
    (hassess : ∀ b, P0 b → Q (b, { b with spending := (assess b.spending p).2 }) ∧
      P1 (assess b.spending p).1 { b with spending := (assess b.spending p).2 })
    (hpost : ∀ a b, a → P1 a b → Q (b, { b with books := (postOnce b.books p).2 }) ∧
      P2 { b with books := (postOnce b.books p).2 })
    (hskip : ∀ a b, ¬a → P1 a b → P2 b)
    (hadvance : ∀ b, P2 b → Q (b, { b with committed := (advance b.committed p.offset).2 }))
    (pipeline : Pipeline) (h0 : P0 pipeline) :
    ∀ step ∈ (handleAmongOthersCode assess postOnce advance pipeline between p).2, Q step := by
  intro step hstep
  unfold handleAmongOthersCode at hstep
  extract_lets did s1 tr1 approved seen2 n2 did1 s2 tr2 afterP seen3 n3 did3 s3 tr3 at hstep
  have q1 := hassess pipeline h0
  by_cases happ : approved
  · have q2 := hpost approved n2 happ (admitted_keeps p between (P1 approved) (h1 approved) 2 s1 q1.2)
    have e : afterP.2.1 = s2 := by simp only [afterP, happ, ite_true]
    have p3 : P2 n3 := admitted_keeps p between P2 h2 3 afterP.2.1 (by rw [e]; exact q2.2)
    have q3 := hadvance n3 p3
    simp only [tr3, afterP, happ, ite_true, tr2, tr1, List.nil_append, List.mem_append, List.mem_singleton,
      or_assoc] at hstep
    rcases hstep with rfl | rfl | rfl
    · exact q1.1
    · exact q2.1
    · exact q3
  · have e : afterP.2.1 = s1 := by simp only [afterP, happ, ite_false]
    have p3 : P2 n3 := admitted_keeps p between P2 h2 3 afterP.2.1 (by rw [e]; exact hskip approved s1 happ q1.2)
    have q3 := hadvance n3 p3
    simp only [tr3, afterP, happ, ite_false, tr1, List.nil_append, List.mem_append, List.mem_singleton,
      or_assoc] at hstep
    rcases hstep with rfl | rfl
    · exact q1.1
    · exact q3

end Payments.Lemmas
