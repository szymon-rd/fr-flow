import FrFlowGen.Sharing.deliveryGivesBack.Spec
import Proofs.Sharing.Lemmas

/-! A run of delivery takes a connection from the pool and gives it back, whether its sends end well, fail or lose
their race with the time limit (cancelled between two of their steps, each notice's at its own): neither the sends nor
the outbox's removals touch the pool. Its sends commute as deliveryJob's do. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.deliveryGivesBack.Proofs
open Sharing


set_option maxHeartbeats 4000000 in
theorem impl : Obl.impl := by
  unfold Obl.impl
  intro w _ _ _ _ _ _ _
  rcases w with ⟨boxes, hk, clock, lib, pool, faults, races, ticks⟩
  rcases races with _ | ⟨_ | _, _ | ⟨_ | _, rs⟩⟩ <;> rcases faults with _ | ⟨_ | _, fs⟩
  all_goals simp only [delivery_run, delivery, FrFlow.runOnE_bind, FrFlow.runOnE_pure, FrFlow.runOnE_lift,
    FrFlow.runOnE_throw, FrFlow.runOnE_failing, FrFlow.runOnE_tryCatch, FrFlow.runOnE_ite, FrFlow.Races.leftWins_exceptT,
    FrFlow.Races.leftWins_onWorld, FrFlow.runOn_nextRace, FrFlow.runOnE_cut, FrFlow.runOnE_step,
    FrFlow.runOnE_optionT_bind, FrFlow.runOnE_optionT_pure, FrFlow.runOnE_each, PoolModel.Ops.take_onWorldE,
    PoolModel.Ops.give_onWorldE, LibraryModel.Ops.load_onWorldE, ClockModel.Ops.sleep_onWorldE, FrFlow.runOn_within, Lemmas.now_run, FrFlow.Waits.reach_exceptT, FrFlow.Waits.reach_onWorld, FrFlow.runOn_reach,
    World.move_mailerModel, World.move_housekeptModel, World.move_libraryModel, World.move_poolModel,
    World.move_faults, World.move_races, World.move_ticks, World.ticked_faults, World.ticked_libraryModel,
    World.ticked_mailerModel, World.ticked_housekeptModel, World.ticked_poolModel, World.ticked_races,
    PoolModel.take, PoolModel.give, LibraryModel.load, ClockModel.sleep, FrFlow.runOn_get, FrFlow.runOn_set,
    FrFlow.runOn_modify, FrFlow.runOn_bind, FrFlow.runOn_pure, FrFlow.runOn_map, ↓reduceIte, Bool.false_eq_true,
    ite_false, ite_true]
  all_goals first
    | (simp; done)
    | (generalize hres : FrFlow.runOnE (List.mapM _ _) _ = res
       obtain ⟨bs, hbs, hinv⟩ : ∃ bs, res.1 = .ok bs ∧ World.poolModel res.2 = pool + 1 := by
         rw [← hres]
         refine Lemmas.mapM_inv _ (fun (_ : List Notice) (s : World) => s.poolModel = pool + 1) ?_ _ [] _ rfl
         intro done x s hs
         rcases s with ⟨b, hk', c, l, p, fs, rs, ts⟩
         simp only at hs
         subst hs
         simp only [FrFlow.runOnE_bind, FrFlow.runOnE_pure,
           FrFlow.runOnE_lift, FrFlow.runOnE_failing, FrFlow.runOnE_tryCatch, FrFlow.runOnE_ite,
           MailerModel.Ops.send_onWorldE, ClockModel.Ops.sleep_onWorldE, LibraryModel.Ops.load_onWorldE,
           LibraryModel.Ops.save_onWorldE, FrFlow.runOn_within, Lemmas.now_run, FrFlow.Waits.reach_exceptT, FrFlow.Waits.reach_onWorld, FrFlow.runOn_reach,
    World.move_mailerModel, World.move_housekeptModel, World.move_libraryModel, World.move_poolModel,
    World.move_faults, World.move_races, World.move_ticks, World.ticked_faults, World.ticked_libraryModel,
    World.ticked_mailerModel, World.ticked_housekeptModel, World.ticked_poolModel, World.ticked_races, MailerModel.send, ClockModel.sleep, LibraryModel.load,
           LibraryModel.save, FrFlow.runOn_get, FrFlow.runOn_set, FrFlow.runOn_modify, FrFlow.runOn_bind,
           FrFlow.runOn_pure, FrFlow.runOnE_step, FrFlow.runOnE_optionT_bind, FrFlow.runOnE_optionT_pure,
           FrFlow.runOnE_optionT_tryCatch, FrFlow.runOnE_optionT_ite, FrFlow.Races.leftWins_exceptT,
           FrFlow.Races.leftWins_onWorld, FrFlow.runOn_nextRace, ↓reduceIte, Bool.false_eq_true, ite_false,
           ite_true]
         iterate 14 (all_goals (try (first
           | (rcases rs with _ | ⟨_ | _, rs⟩ <;> simp only [FrFlow.runOnE_bind, FrFlow.runOnE_pure,
           FrFlow.runOnE_lift, FrFlow.runOnE_failing, FrFlow.runOnE_tryCatch, FrFlow.runOnE_ite,
           MailerModel.Ops.send_onWorldE, ClockModel.Ops.sleep_onWorldE, LibraryModel.Ops.load_onWorldE,
           LibraryModel.Ops.save_onWorldE, FrFlow.runOn_within, Lemmas.now_run, FrFlow.Waits.reach_exceptT, FrFlow.Waits.reach_onWorld, FrFlow.runOn_reach,
    World.move_mailerModel, World.move_housekeptModel, World.move_libraryModel, World.move_poolModel,
    World.move_faults, World.move_races, World.move_ticks, World.ticked_faults, World.ticked_libraryModel,
    World.ticked_mailerModel, World.ticked_housekeptModel, World.ticked_poolModel, World.ticked_races, MailerModel.send, ClockModel.sleep, LibraryModel.load,
           LibraryModel.save, FrFlow.runOn_get, FrFlow.runOn_set, FrFlow.runOn_modify, FrFlow.runOn_bind,
           FrFlow.runOn_pure, FrFlow.runOnE_step, FrFlow.runOnE_optionT_bind, FrFlow.runOnE_optionT_pure,
           FrFlow.runOnE_optionT_tryCatch, FrFlow.runOnE_optionT_ite, FrFlow.Races.leftWins_exceptT,
           FrFlow.Races.leftWins_onWorld, FrFlow.runOn_nextRace, ↓reduceIte, Bool.false_eq_true, ite_false,
           ite_true])
           | (rcases fs with _ | ⟨_ | _, fs⟩ <;> simp only [FrFlow.runOnE_bind, FrFlow.runOnE_pure,
           FrFlow.runOnE_lift, FrFlow.runOnE_failing, FrFlow.runOnE_tryCatch, FrFlow.runOnE_ite,
           MailerModel.Ops.send_onWorldE, ClockModel.Ops.sleep_onWorldE, LibraryModel.Ops.load_onWorldE,
           LibraryModel.Ops.save_onWorldE, FrFlow.runOn_within, Lemmas.now_run, FrFlow.Waits.reach_exceptT, FrFlow.Waits.reach_onWorld, FrFlow.runOn_reach,
    World.move_mailerModel, World.move_housekeptModel, World.move_libraryModel, World.move_poolModel,
    World.move_faults, World.move_races, World.move_ticks, World.ticked_faults, World.ticked_libraryModel,
    World.ticked_mailerModel, World.ticked_housekeptModel, World.ticked_poolModel, World.ticked_races, MailerModel.send, ClockModel.sleep, LibraryModel.load,
           LibraryModel.save, FrFlow.runOn_get, FrFlow.runOn_set, FrFlow.runOn_modify, FrFlow.runOn_bind,
           FrFlow.runOn_pure, FrFlow.runOnE_step, FrFlow.runOnE_optionT_bind, FrFlow.runOnE_optionT_pure,
           FrFlow.runOnE_optionT_tryCatch, FrFlow.runOnE_optionT_ite, FrFlow.Races.leftWins_exceptT,
           FrFlow.Races.leftWins_onWorld, FrFlow.runOn_nextRace, ↓reduceIte, Bool.false_eq_true, ite_false,
           ite_true]))))
         all_goals simp
       rcases res with ⟨o, s'⟩
       simp only at hbs hinv
       subst hbs
       simp only
       try (cases List.mapM id bs <;> simp only [])
       all_goals simp [hinv, World.move_poolModel])

/-- Two notices of the outbox's first ones sent at once, each with its own faults, commute: one notice, or two
people's mailboxes (`Lemmas.sends_commute`). The sleeps at once commute as FrFlow's automation shows. -/
theorem commute_2 : Obl.commute_2 := by
  unfold Obl.commute_2
  intro r start n₁ n₂ w f₁ r₁ t₁ f₂ r₂ t₂ h
  exact Lemmas.sends_commute n₁ n₂ (Lemmas.firstOfEach_apart _ _ _ h) w f₁ r₁ f₂ r₂ t₁ t₂

/-- Two removals from the outbox at once, each a transaction with its own faults, commute
(`Lemmas.removals_commute`). -/
theorem commute_6 : Obl.commute_6 := by
  unfold Obl.commute_6
  intro r start n₁ n₂ w f₁ r₁ t₁ f₂ r₂ t₂ _
  exact Lemmas.removals_commute n₁ n₂ w f₁ r₁ f₂ r₂ t₁ t₂

end Sharing.deliveryGivesBack.Proofs
