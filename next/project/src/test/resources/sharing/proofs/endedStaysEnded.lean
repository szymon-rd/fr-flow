import FrFlowGen.Sharing.endedStaysEnded.Spec
import Proofs.Sharing.Lemmas

/-! Each event keeps the time or moves it on, a wait by what the clock allows (clockNeverGoesBack); and each lifetime,
once over, is over at every later time, whatever the lifetimes are. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.endedStaysEnded.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro events startedAt reaches covers _ _ _ hBack
  refine ⟨fun pre post hev => ?_, fun t u htu => ⟨⟨fun s hs hu => ?_, fun i hi hu => ?_⟩, fun doc hd => ?_⟩⟩
  · subst hev
    unfold atEnd
    exact FrFlow.along_when _ (fun _ e => match e with | Event.Waited d => (0 : Int) ≤ d | _ => True)
      (fun (a b : Moment) => a.now ≤ b.now) _ (fun _ => Int.le_refl _) (fun _ _ _ h1 h2 => Int.le_trans h1 h2)
      (fun m e ok => by cases e <;> simp [step] at ok ⊢ <;> (try split) <;> (try simp) <;> omega)
      pre post (fun p e q h => by have := hBack p e q h; cases e <;> simp_all)
  · apply hs
    intro e he
    have := hu e he
    omega
  · apply hi
    simp only [isOpenCode] at hu ⊢
    omega
  · obtain ⟨a, ha, hat⟩ := hd
    exact ⟨a, ha, by omega⟩

end Sharing.endedStaysEnded.Proofs
