import FrFlowGen.Sharing.trashUntilGone.Spec
import Proofs.Sharing.Lemmas

/-! The branch is its parts, line by line: who trashes and restores (onlyEditorsTrash), and only before the document
is gone (restoredOnlyBeforeGone); and, at every moment, no document is gone as of one housekeeping period ago:
trashPurgedOnTime, read through what gone is (goneContract). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.trashUntilGone.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro inForce reaches covers gone mayEdit _ _ _ hPurged world g0 g1 g2 g3 g4 g5 g6
  -- The lines about the operations, of their code (the parts state them for every lifetime).
  refine ⟨fun lib t by_ d => ⟨fun h => ?_, fun h => (Lemmas.changed h).2⟩, fun doc hd => ?_⟩
  · rcases h with h | h
    · exact Lemmas.changed h
    · exact (Lemmas.changed h).1
  rintro ⟨a, ha, hle⟩
  have := hPurged world g0 g1 g2 g3 g4 g5 g6 doc hd a ha
  omega

end Sharing.trashUntilGone.Proofs
