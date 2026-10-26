import FrFlow

set_option autoImplicit false

set_option linter.unusedVariables false

noncomputable section

open Classical

namespace Auth

structure UserId where
  name : String
deriving DecidableEq

structure Path where
  value : String
deriving DecidableEq

structure Grant where
  user : UserId
  path : Path
deriving DecidableEq

structure Session where
  token : String
  user : UserId
deriving DecidableEq

@[frflow_defs] def admits (grants : (List Grant)) (s : Session) (p : Path) : Prop := (∃ g ∈ grants, (g = (Grant.mk s.user p)))

namespace accessExactly
@[frflow_defs] def claim (access : UserId → Path → Prop) (signedIn : UserId → Prop) (authorized : UserId → Path → Prop) : Prop := (∀ (u : UserId), (∀ (p : Path), ((access u p) = ((signedIn u) ∧ (authorized u p)))))
end accessExactly

namespace grantsAuthorize
@[frflow_defs] def claim (authorized : UserId → Path → Prop) (grants : (List Grant)) : Prop := (∀ (u : UserId), (∀ (p : Path), ((authorized u p) = (∃ g ∈ grants, (g = (Grant.mk u p))))))
end grantsAuthorize

namespace sessionsSignIn
@[frflow_defs] def claim (signedIn : UserId → Prop) (sessions : (List Session)) : Prop := (∀ (u : UserId), ((signedIn u) = (∃ s ∈ sessions, (s.user = u))))
end sessionsSignIn

namespace requestsReach
@[frflow_defs] def claim (access : UserId → Path → Prop) (sessions : (List Session)) (grants : (List Grant)) : Prop := (∀ (u : UserId), (∀ (p : Path), ((access u p) = (∃ s ∈ sessions, ((s.user = u) ∧ (Auth.admits grants s p))))))
end requestsReach

namespace Whole

namespace Obl

/-- grantsAuthorize hold together: some meaning of authorized makes each true, for every grants provided. -/
@[frflow_defs] def consistent_0 : Prop :=
  ∀ (grants : (List Grant)), ∃ (authorized : UserId → Path → Prop), (Auth.grantsAuthorize.claim authorized grants)

end Obl

namespace Obl

/-- sessionsSignIn hold together: some meaning of signedIn makes each true, for every sessions provided. -/
@[frflow_defs] def consistent_1 : Prop :=
  ∀ (sessions : (List Session)), ∃ (signedIn : UserId → Prop), (Auth.sessionsSignIn.claim signedIn sessions)

end Obl

namespace Obl

/-- requestsReach hold together: some meaning of access makes each true, for every sessions, grants provided. -/
@[frflow_defs] def consistent_2 : Prop :=
  ∀ (sessions : (List Session)) (grants : (List Grant)), ∃ (access : UserId → Path → Prop), (Auth.requestsReach.claim access sessions grants)

end Obl

theorem consistent_0 : Obl.consistent_0 :=
  fun grants => ⟨(fun (u : UserId) => (fun (p : Path) => (∃ g ∈ grants, (g = (Grant.mk u p))))), by frflow_witness⟩

theorem consistent_1 : Obl.consistent_1 :=
  fun sessions => ⟨(fun (u : UserId) => (∃ s ∈ sessions, (s.user = u))), by frflow_witness⟩

theorem consistent_2 : Obl.consistent_2 :=
  fun sessions grants => ⟨(fun (u : UserId) => (fun (p : Path) => (∃ s ∈ sessions, ((s.user = u) ∧ (Auth.admits grants s p))))), by frflow_witness⟩

end Whole

namespace signedInBySessions
@[frflow_defs] def claim (signedIn : UserId → Prop) (sessions : (List Session)) : Prop := (∀ (u : UserId), ((signedIn u) = (∃ s ∈ sessions, (s.user = u))))
end signedInBySessions

namespace authorizedByGrants
@[frflow_defs] def claim (authorized : UserId → Path → Prop) (grants : (List Grant)) : Prop := (∀ (u : UserId), (∀ (p : Path), ((authorized u p) = (∃ g ∈ grants, (g = (Grant.mk u p))))))
end authorizedByGrants

namespace Bottom

namespace Obl

/-- accessExactly, signedInBySessions, authorizedByGrants hold together: some meaning of access, signedIn, authorized makes each true, for every sessions, grants provided. -/
@[frflow_defs] def consistent_0 : Prop :=
  ∀ (sessions : (List Session)) (grants : (List Grant)), ∃ (access : UserId → Path → Prop) (signedIn : UserId → Prop) (authorized : UserId → Path → Prop), (Auth.accessExactly.claim access signedIn authorized) ∧ (Auth.signedInBySessions.claim signedIn sessions) ∧ (Auth.authorizedByGrants.claim authorized grants)

end Obl

theorem consistent_0 : Obl.consistent_0 :=
  fun sessions grants => ⟨(fun (u : UserId) => (fun (p : Path) => (((fun (u : UserId) => (∃ s ∈ sessions, (s.user = u))) u) ∧ ((fun (u : UserId) => (fun (p : Path) => (∃ g ∈ grants, (g = (Grant.mk u p))))) u p)))), (fun (u : UserId) => (∃ s ∈ sessions, (s.user = u))), (fun (u : UserId) => (fun (p : Path) => (∃ g ∈ grants, (g = (Grant.mk u p))))), by frflow_witness⟩

end Bottom

end Auth
