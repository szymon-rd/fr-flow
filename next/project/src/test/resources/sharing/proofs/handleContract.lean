import FrFlowGen.Sharing.handleContract.Spec
import Proofs.Sharing.Lemmas

/-! The handling's run on the models, one fault at a time: it reads the time (the world's tick after), then the time
and the library, saves the library the request leads to at the time read second when it changed, and reads the time
once more: the answer is given when no more than the limit passed since its first look, else the time is past the
limit. The time each look reads is never before the one before (`Lemmas.tick_le`). A failed read changes nothing of
the stores, and so does a failed save. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.handleContract.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro inForce reaches covers inTrash mayView _ _ _ _ _ r w _ _ _
  rcases hf : w.faults with _ | ⟨_ | _, _ | ⟨_ | _, fs⟩⟩
  all_goals simp only [handleRequest_run, handleRequest, FrFlow.runOnE_bind, FrFlow.runOnE_pure, Lemmas.now_run,
    FrFlow.runOnE_failing, FrFlow.runOnE_ite, LibraryModel.Ops.load_onWorldE,
    LibraryModel.Ops.save_onWorldE, FrFlow.runOn_within, LibraryModel.load, LibraryModel.save, FrFlow.runOn_get,
    FrFlow.runOn_set, FrFlow.runOn_pure, FrFlow.runOn_bind, World.ticked_faults, World.ticked_libraryModel,
    World.ticked_mailerModel, World.ticked_housekeptModel, World.ticked_poolModel, World.ticked_races, hf]
  all_goals refine ⟨?_, ?_⟩
  all_goals first
    | trivial
    | (split <;> first
        | trivial
        | (rename_i heq
           (try split at heq)
           all_goals (try simp only [Prod.mk.injEq, Except.ok.injEq, Except.error.injEq, reduceCtorEq, false_and,
             and_false] at heq)
           all_goals (try obtain ⟨rfl, rfl⟩ := heq)
           all_goals (try obtain ⟨-, rfl⟩ := heq)
           all_goals simp only [World.ticked_libraryModel, World.ticked_mailerModel, World.ticked_housekeptModel,
             World.ticked_poolModel, and_self, and_true]
           all_goals first
             | refine ⟨⟨fun hn => hn (FrFlow.Clock.ticked (fun (w : World) => w.ticks) (fun (w : World) s => { w with ticks := s }) (fun (w : World) => w.clockModel) (fun (w : World) s => { w with clockModel := s }) (fun (w : World) s => True) w).clockModel ⟨⟨⟨Lemmas.tick_le w,
                 Int.le_trans (Lemmas.tick_le (FrFlow.Clock.ticked (fun (w : World) => w.ticks) (fun (w : World) s => { w with ticks := s }) (fun (w : World) => w.clockModel) (fun (w : World) s => { w with clockModel := s }) (fun (w : World) s => True) w)) (Lemmas.tick_le _)⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
             | refine ⟨fun hn => hn (FrFlow.Clock.ticked (fun (w : World) => w.ticks) (fun (w : World) s => { w with ticks := s }) (fun (w : World) => w.clockModel) (fun (w : World) s => { w with clockModel := s }) (fun (w : World) s => True) w).clockModel ⟨⟨⟨Lemmas.tick_le w,
                 Int.le_trans (Lemmas.tick_le (FrFlow.Clock.ticked (fun (w : World) => w.ticks) (fun (w : World) s => { w with ticks := s }) (fun (w : World) => w.clockModel) (fun (w : World) s => { w with clockModel := s }) (fun (w : World) s => True) w)) (Lemmas.tick_le _)⟩, ?_⟩, ?_⟩, ?_⟩
           all_goals (try rfl)
           all_goals (try (rename_i hc; exact (Classical.not_not.mp hc).symm))
           all_goals split
           all_goals first
             | (intro a ha; exact (Option.some.inj ha).symm)
             | (intro a ha; cases ha)
             | (left; simp; done)
             | (right
                refine Int.lt_of_lt_of_le ?_ (Lemmas.tick_le _)
                show w.clockModel + 5 < (FrFlow.Clock.ticked (fun (w : World) => w.ticks) (fun (w : World) s => { w with ticks := s }) (fun (w : World) => w.clockModel) (fun (w : World) s => { w with clockModel := s }) (fun (w : World) s => True) (FrFlow.Clock.ticked (fun (w : World) => w.ticks) (fun (w : World) s => { w with ticks := s }) (fun (w : World) => w.clockModel) (fun (w : World) s => { w with clockModel := s }) (fun (w : World) s => True) w)).clockModel
                omega)))

end Sharing.handleContract.Proofs
