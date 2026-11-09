import FrFlowGen.Sharing.newOwnerOwnsForGood.Spec
import Proofs.Sharing.Lemmas

/-! A transfer that changes the library was asked by the owner of someone who may edit: the document is then
theirs, with their edit share at the front. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.newOwnerOwnsForGood.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro mayEdit _ lib t by_ d to h
  have hc := Lemmas.changed h
  obtain ⟨⟨⟨doc, hd, hid, _⟩, _⟩, _⟩ := id hc
  simp only [ownsForGood]
  unfold transferCode
  split
  · exact ⟨⟨{ doc with owner := to }, List.mem_map.mpr ⟨doc, hd, by simp [hid]⟩, hid, rfl⟩, List.mem_cons_self⟩
  · contradiction

end Sharing.newOwnerOwnsForGood.Proofs
