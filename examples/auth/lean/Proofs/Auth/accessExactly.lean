import FrFlowGen.Auth.accessExactly.Spec
import Proofs.Auth.Lemmas

/-! A user gets access exactly when signed in and authorized: a request admitted on their behalf has a token issued to
them and a grant for the path; and a session of theirs, with a grant, has its token's request admitted for them. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Auth.accessExactly.Proofs

theorem complete : Obl.complete := by
  intro access signedIn authorized grants sessions adm hs hgt hst hreq htn han hgl u r
  rw [hreq u r, hst hs u, hgt u r]
  apply propext
  unfold admittedTo
  constructor
  · intro h
    obtain ⟨t, ht⟩ := Classical.not_forall.1 h
    have ha : adm t r = some u := Classical.not_not.1 ht
    obtain ⟨s, hm, _, hsu⟩ := htn hs t r u ha
    exact ⟨⟨s, hm, hsu⟩, han t r u ha⟩
  · rintro ⟨⟨s, hm, rfl⟩, hg⟩ hall
    apply hall s.token
    have hh := Lemmas.holder_of_session sessions hs s hm
    rw [hgl hs s.token r ⟨s.user, hh, hg⟩, hh]

end Auth.accessExactly.Proofs
