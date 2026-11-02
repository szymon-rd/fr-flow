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
  intro w
  rcases w with ⟨lib, clock, boxes, pool, faults, races⟩
  rcases races with _ | ⟨_ | _, _ | ⟨_ | _, rs⟩⟩ <;> rcases faults with _ | ⟨_ | _, fs⟩
  all_goals simp only [delivery_run, delivery, FrFlow.runOnE_bind, FrFlow.runOnE_pure, FrFlow.runOnE_lift,
    FrFlow.runOnE_throw, FrFlow.runOnE_failing, FrFlow.runOnE_tryCatch, FrFlow.runOnE_ite, FrFlow.Races.leftWins_exceptT,
    FrFlow.Races.leftWins_onWorld, FrFlow.runOn_nextRace, FrFlow.runOnE_cut, FrFlow.runOnE_step,
    FrFlow.runOnE_optionT_bind, FrFlow.runOnE_optionT_pure, FrFlow.runOnE_each, PoolModel.Ops.take_onWorldE,
    PoolModel.Ops.give_onWorldE, LibraryModel.Ops.load_onWorldE, ClockModel.Ops.sleep_onWorldE, FrFlow.runOn_within,
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
         rcases s with ⟨l, c, b, p, fs, rs⟩
         simp only at hs
         subst hs
         simp only [FrFlow.runOnE_bind, FrFlow.runOnE_pure,
           FrFlow.runOnE_lift, FrFlow.runOnE_failing, FrFlow.runOnE_tryCatch, FrFlow.runOnE_ite,
           MailerModel.Ops.send_onWorldE, ClockModel.Ops.sleep_onWorldE, LibraryModel.Ops.load_onWorldE,
           LibraryModel.Ops.save_onWorldE, FrFlow.runOn_within, MailerModel.send, ClockModel.sleep, LibraryModel.load,
           LibraryModel.save, FrFlow.runOn_get, FrFlow.runOn_set, FrFlow.runOn_modify, FrFlow.runOn_bind,
           FrFlow.runOn_pure, FrFlow.runOnE_step, FrFlow.runOnE_optionT_bind, FrFlow.runOnE_optionT_pure,
           FrFlow.runOnE_optionT_tryCatch, FrFlow.runOnE_optionT_ite, FrFlow.Races.leftWins_exceptT,
           FrFlow.Races.leftWins_onWorld, FrFlow.runOn_nextRace, ↓reduceIte, Bool.false_eq_true, ite_false,
           ite_true]
         iterate 14 (all_goals (try (first
           | (rcases rs with _ | ⟨_ | _, rs⟩ <;> simp only [FrFlow.runOnE_bind, FrFlow.runOnE_pure,
           FrFlow.runOnE_lift, FrFlow.runOnE_failing, FrFlow.runOnE_tryCatch, FrFlow.runOnE_ite,
           MailerModel.Ops.send_onWorldE, ClockModel.Ops.sleep_onWorldE, LibraryModel.Ops.load_onWorldE,
           LibraryModel.Ops.save_onWorldE, FrFlow.runOn_within, MailerModel.send, ClockModel.sleep, LibraryModel.load,
           LibraryModel.save, FrFlow.runOn_get, FrFlow.runOn_set, FrFlow.runOn_modify, FrFlow.runOn_bind,
           FrFlow.runOn_pure, FrFlow.runOnE_step, FrFlow.runOnE_optionT_bind, FrFlow.runOnE_optionT_pure,
           FrFlow.runOnE_optionT_tryCatch, FrFlow.runOnE_optionT_ite, FrFlow.Races.leftWins_exceptT,
           FrFlow.Races.leftWins_onWorld, FrFlow.runOn_nextRace, ↓reduceIte, Bool.false_eq_true, ite_false,
           ite_true])
           | (rcases fs with _ | ⟨_ | _, fs⟩ <;> simp only [FrFlow.runOnE_bind, FrFlow.runOnE_pure,
           FrFlow.runOnE_lift, FrFlow.runOnE_failing, FrFlow.runOnE_tryCatch, FrFlow.runOnE_ite,
           MailerModel.Ops.send_onWorldE, ClockModel.Ops.sleep_onWorldE, LibraryModel.Ops.load_onWorldE,
           LibraryModel.Ops.save_onWorldE, FrFlow.runOn_within, MailerModel.send, ClockModel.sleep, LibraryModel.load,
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
       all_goals simp [hinv])

/-- Two notices of the outbox's first ones, each given its own faults, delivered in either order leave the same:
each branch does what its faults alone decide, to its own person's mailbox, and their removals from the
outbox commute. -/
theorem commute_0 : Obl.commute_0 := by
  unfold Obl.commute_0
  intro r n₁ n₂ w f₁ r₁ f₂ r₂ h₁ h₂ hne
  refine Lemmas.commute_split _ _ n₁ n₂ (fun h => hne (Lemmas.firstOfEach_one _ _ _ h₁ h₂ h)) f₁ r₁ f₂ r₂ ?_ ?_ w
  · clear h₁ h₂ hne r₁ r₂ f₂
    iterate 5 (all_goals (try (rcases f₁ with _ | ⟨_ | _, f₁⟩)); all_goals (try simp only [FrFlow.runOnE_bind,
      FrFlow.runOnE_pure, FrFlow.runOnE_lift, FrFlow.runOnE_failing, FrFlow.runOnE_tryCatch, FrFlow.runOnE_ite,
      MailerModel.Ops.send_onWorldE, ClockModel.Ops.sleep_onWorldE, LibraryModel.Ops.load_onWorldE,
      LibraryModel.Ops.save_onWorldE, FrFlow.runOn_within, MailerModel.send, ClockModel.sleep, LibraryModel.load,
      LibraryModel.save, FrFlow.runOn_get, FrFlow.runOn_set, FrFlow.runOn_bind, FrFlow.runOn_pure, ↓reduceIte]))
    all_goals first
      | exact ⟨true, true, [], _, fun _ _ _ _ _ => rfl⟩
      | exact ⟨false, true, [], _, fun _ _ _ _ _ => rfl⟩
      | exact ⟨false, false, [], _, fun _ _ _ _ _ => rfl⟩
      | exact ⟨true, true, [1], _, fun _ _ _ _ _ => rfl⟩
      | exact ⟨false, true, [1], _, fun _ _ _ _ _ => rfl⟩
      | exact ⟨false, false, [1], _, fun _ _ _ _ _ => rfl⟩
      | exact ⟨true, true, [1, 2], _, fun _ _ _ _ _ => rfl⟩
      | exact ⟨false, true, [1, 2], _, fun _ _ _ _ _ => rfl⟩
      | exact ⟨false, false, [1, 2], _, fun _ _ _ _ _ => rfl⟩
  · clear h₁ h₂ hne r₁ r₂ f₁
    iterate 5 (all_goals (try (rcases f₂ with _ | ⟨_ | _, f₂⟩)); all_goals (try simp only [FrFlow.runOnE_bind,
      FrFlow.runOnE_pure, FrFlow.runOnE_lift, FrFlow.runOnE_failing, FrFlow.runOnE_tryCatch, FrFlow.runOnE_ite,
      MailerModel.Ops.send_onWorldE, ClockModel.Ops.sleep_onWorldE, LibraryModel.Ops.load_onWorldE,
      LibraryModel.Ops.save_onWorldE, FrFlow.runOn_within, MailerModel.send, ClockModel.sleep, LibraryModel.load,
      LibraryModel.save, FrFlow.runOn_get, FrFlow.runOn_set, FrFlow.runOn_bind, FrFlow.runOn_pure, ↓reduceIte]))
    all_goals first
      | exact ⟨true, true, [], _, fun _ _ _ _ _ => rfl⟩
      | exact ⟨false, true, [], _, fun _ _ _ _ _ => rfl⟩
      | exact ⟨false, false, [], _, fun _ _ _ _ _ => rfl⟩
      | exact ⟨true, true, [1], _, fun _ _ _ _ _ => rfl⟩
      | exact ⟨false, true, [1], _, fun _ _ _ _ _ => rfl⟩
      | exact ⟨false, false, [1], _, fun _ _ _ _ _ => rfl⟩
      | exact ⟨true, true, [1, 2], _, fun _ _ _ _ _ => rfl⟩
      | exact ⟨false, true, [1, 2], _, fun _ _ _ _ _ => rfl⟩
      | exact ⟨false, false, [1, 2], _, fun _ _ _ _ _ => rfl⟩

end Sharing.deliveryGivesBack.Proofs
