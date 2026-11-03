import FrFlowGen.Stamping.freshWhileScheduled.Spec

/-! Stamping reads the time, the world's tick moves it on, and the time read is stamped. The tick moves the time only
where the schedule allows: with stamps, each at most ten seconds old at the time moved to; each of them of a time
already come, so no later than the time read, which the moved time is then within ten seconds of. With no stamps the
time does not move, and the stamp is of the time now. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Stamping.freshWhileScheduled.Proofs
open Stamping

theorem cover_stamp : Obl.cover_stamp := by
  unfold Obl.cover_stamp Stamping.freshWhileScheduled.keeps_stamp
  intro w hf hp
  rcases w with ⟨st, c, ts⟩
  rcases ts with _ | ⟨d, ts⟩
  all_goals simp only [stampCode_run, stampCode, FrFlow.runOn_bind, ClockModel.Ops.now_onWorld, FrFlow.runOn_tick,
    FrFlow.runOn_within, ClockModel.now, Stamps.Ops.stampAt_onWorld, Stamps.stampAt, FrFlow.runOn_get,
    FrFlow.runOn_set, FrFlow.runOn_pure, FrFlow.Clock.ticked, freshWhileScheduled, pastWhileScheduled] at *
  · intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hf x hx
    · omega
  · by_cases h : tenSeconds (c + ↑d) st
    · simp only [FrFlow.Clock.move, h, ite_true]
      obtain ⟨hne, hall⟩ := h
      intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hall x hx
      · obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hne
        have := hall y hy
        have := hp y hy
        omega
    · simp only [FrFlow.Clock.move, h, ite_false]
      intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hf x hx
      · omega

end Stamping.freshWhileScheduled.Proofs
