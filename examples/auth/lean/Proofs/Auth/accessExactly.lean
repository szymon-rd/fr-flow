import FrFlowGen.Auth.accessExactly.Spec
import Proofs.Auth.Lemmas

/-! A user gets access exactly when signed in and authorized: a session's token admitted on their behalf is theirs, with
a grant for the path; and a session of theirs, with a grant, has its token admitted for them. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Auth.accessExactly.Proofs

theorem complete : Obl.complete := by
  intro access signedIn authorized grants sessions adm hs hgt hst hreq htn han hgl u r
  rw [hreq hs u r, hst hs u, hgt u r]
  apply propext
  unfold admittedTo
  constructor
  · rintro ⟨s, hm, ha⟩
    have hh := htn hs s.token r u ha
    rw [Lemmas.holder_of_session sessions hs s hm] at hh
    cases hh
    exact ⟨⟨s, hm, rfl⟩, han s.token r s.user ha⟩
  · rintro ⟨⟨s, hm, rfl⟩, hg⟩
    have hh := Lemmas.holder_of_session sessions hs s hm
    exact ⟨s, hm, by rw [hgl hs s.token r ⟨s.user, hh, hg⟩, hh]⟩

end Auth.accessExactly.Proofs
