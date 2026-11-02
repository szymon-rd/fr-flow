import FrFlowGen.Sharing.deliveryGivesBack.Spec
import Proofs.Sharing.Lemmas

/-! A run of delivery takes a connection from the pool and gives it back, whether its sends end well, fail or lose
their race with the time limit: neither the sends nor the outbox's removals touch the pool. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.deliveryGivesBack.Proofs
open Sharing

/-- A notice's delivery computed on the models, as far as the faults it takes say. -/
local macro "body_simp" : tactic => `(tactic| (try simp only [FrFlow.runOnE_bind, FrFlow.runOnE_pure,
  FrFlow.runOnE_lift, FrFlow.runOnE_failing, FrFlow.runOnE_tryCatch, FrFlow.runOnE_ite, MailerModel.Ops.send_onWorldE,
  ClockModel.Ops.sleep_onWorldE, LibraryModel.Ops.load_onWorldE, LibraryModel.Ops.save_onWorldE, FrFlow.runOn_within,
  MailerModel.send, ClockModel.sleep, LibraryModel.load, LibraryModel.save, FrFlow.runOn_get, FrFlow.runOn_set,
  FrFlow.runOn_modify, FrFlow.runOn_bind, FrFlow.runOn_pure]))

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro w
  rcases w with ⟨lib, clock, boxes, pool, faults, races⟩
  rcases races with _ | ⟨_ | _, rs⟩ <;> rcases faults with _ | ⟨_ | _, fs⟩
  all_goals simp only [delivery_run, delivery, FrFlow.runOnE_bind, FrFlow.runOnE_pure, FrFlow.runOnE_lift,
    FrFlow.runOnE_throw, FrFlow.runOnE_failing, FrFlow.runOnE_tryCatch, FrFlow.runOnE_ite, FrFlow.Races.leftWins_exceptT,
    FrFlow.Races.leftWins_onWorld, FrFlow.runOn_nextRace, PoolModel.Ops.take_onWorldE, PoolModel.Ops.give_onWorldE,
    LibraryModel.Ops.load_onWorldE, ClockModel.Ops.sleep_onWorldE, FrFlow.runOn_within, PoolModel.take,
    PoolModel.give, LibraryModel.load, ClockModel.sleep, FrFlow.runOn_get, FrFlow.runOn_set, FrFlow.runOn_modify,
    FrFlow.runOn_bind, FrFlow.runOn_pure, FrFlow.runOn_map]
  all_goals first
    | (simp; done)
    | (generalize hres : FrFlow.runOnE (List.mapM _ _) _ = res
       obtain ⟨bs, hbs, hinv⟩ : ∃ bs, res.1 = .ok bs ∧ World.poolModel res.2 = pool + 1 := by
         rw [← hres]
         refine Lemmas.mapM_inv _ (fun (_ : List Notice) (s : World) => s.poolModel = pool + 1) ?_ _ [] _ rfl
         intro done x s hs
         rcases s with ⟨l, c, b, p, fs, rs⟩
         simp only at hs
         subst hs
         iterate 5 (all_goals (try (rcases fs with _ | ⟨_ | _, fs⟩)); all_goals body_simp)
         all_goals simp
       rcases res with ⟨o, s'⟩
       simp only at hbs hinv
       subst hbs
       simp [hinv])

end Sharing.deliveryGivesBack.Proofs
