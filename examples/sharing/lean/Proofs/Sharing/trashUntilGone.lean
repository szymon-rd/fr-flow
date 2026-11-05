import FrFlowGen.Sharing.trashUntilGone.Spec
import Proofs.Sharing.Lemmas

/-! Trashing and restoring change the library only when the asker may edit the document, restoring only when it is in
the trash and not gone. At every moment no document is gone as of one housekeeping period ago: trashPurgedOnTime. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.trashUntilGone.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro inForce reaches covers _ _ _ hPurged world h1 h2 h3
  refine ⟨fun lib t by_ d => ⟨fun h => Lemmas.changed h, fun h => Lemmas.changed h⟩, fun doc hd => ?_⟩
  rintro ⟨a, ha, hle⟩
  have := hPurged world h1 h2 h3 doc hd a ha
  omega

end Sharing.trashUntilGone.Proofs
