/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.Friedrichs.EnergyForm
import Mathlib.Analysis.Normed.Module.WeakDual

/-! # Closed energy sublevels of the Friedrichs form -/

public section

open Filter Set
open scoped InnerProductSpace Topology

namespace CutoffRigidity.Riemann.Diff.FormData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (S : FormData H)

private theorem isClosed_image_energyBall (radius : ℝ) :
    IsClosed (S.ι '' Metric.closedBall (0 : S.K) radius) := by
  let embed : H → WeakDual ℝ H := fun y => StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H y)
  let transfer : WeakDual ℝ S.K → WeakDual ℝ H := fun f =>
    StrongDual.toWeakDual (f.toStrongDual.comp (ContinuousLinearMap.adjoint S.ι))
  have continuousEmbed : Continuous embed :=
    NormedSpace.Dual.toWeakDual_continuous.comp (InnerProductSpace.toDual ℝ H).continuous
  have continuousTransfer : Continuous transfer :=
    WeakDual.continuous_of_continuous_eval fun y =>
      WeakDual.eval_continuous (ContinuousLinearMap.adjoint S.ι y)
  let ball : Set (WeakDual ℝ S.K) := WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 radius
  have closedTransfer : IsClosed (transfer '' ball) :=
    ((WeakDual.isCompact_closedBall (0 : StrongDual ℝ S.K) radius).image
      continuousTransfer).isClosed
  have transferEmbed (x : S.K) :
      transfer (StrongDual.toWeakDual (InnerProductSpace.toDual ℝ S.K x)) = embed (S.ι x) := by
    apply DFunLike.ext _ _
    intro y
    exact ContinuousLinearMap.adjoint_inner_right S.ι x y
  have injectiveEmbed : Function.Injective embed :=
    StrongDual.toWeakDual.injective.comp (InnerProductSpace.toDual ℝ H).injective
  convert closedTransfer.preimage continuousEmbed using 1
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨StrongDual.toWeakDual (InnerProductSpace.toDual ℝ S.K x), ?_, transferEmbed x⟩
    simpa [ball, Metric.mem_closedBall, dist_zero_right] using hx
  · rintro ⟨f, hf, heq⟩
    let x := (InnerProductSpace.toDual ℝ S.K).symm f.toStrongDual
    have hfx : StrongDual.toWeakDual (InnerProductSpace.toDual ℝ S.K x) = f := by
      simp [x]
    refine ⟨x, ?_, injectiveEmbed ?_⟩
    · rw [← hfx] at hf
      simpa [ball, Metric.mem_closedBall, dist_zero_right] using hf
    · rw [← transferEmbed, hfx]
      exact heq

/-- If form-domain vectors converge in the ambient Hilbert space with uniformly bounded
energy, the limit belongs to the form domain and satisfies the same energy bound.
Only an eventual bound is needed. -/
theorem energy_le_of_tendsto {u : ℕ → S.Q} {v : H}
    (hv : Tendsto (fun n => (u n : H)) atTop (𝓝 v)) {bound : ℝ}
    (hbound : ∀ᶠ n in atTop, S.E (u n) (u n) ≤ bound) :
    ∃ w : S.Q, (w : H) = v ∧ S.E w w ≤ bound := by
  have lifts {ε : ℝ} (hε : 0 < ε) :
      ∃ x : S.K, S.ι x = v ∧ ‖x‖ ^ 2 ≤ bound + ‖v‖ ^ 2 + ε := by
    let b := bound + ‖v‖ ^ 2 + ε
    have ht : Tendsto (fun n => ‖(u n : H)‖ ^ 2) atTop (𝓝 (‖v‖ ^ 2)) := hv.norm.pow 2
    have hevent : ∀ᶠ n in atTop, ‖(u n : H)‖ ^ 2 < ‖v‖ ^ 2 + ε :=
      ht.eventually_lt_const (lt_add_of_pos_right _ hε)
    have normBound : ∀ᶠ n in atTop, ‖S.qEquiv.symm (u n)‖ ^ 2 ≤ b := by
      filter_upwards [hevent, hbound] with n hn h
      rw [E, E1, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
      dsimp [b]
      linarith
    obtain ⟨n, hn⟩ := normBound.exists
    have hb : 0 ≤ b := (sq_nonneg _).trans hn
    have hm : ∀ᶠ n in atTop, (u n : H) ∈ S.ι '' Metric.closedBall 0 (Real.sqrt b) := by
      filter_upwards [normBound] with n hn
      refine ⟨S.qEquiv.symm (u n), ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right]
        exact (Real.le_sqrt (norm_nonneg _) hb).2 hn
      · rw [← qEquiv_apply, LinearEquiv.apply_symm_apply]
    obtain ⟨x, hx, rfl⟩ := (S.isClosed_image_energyBall (Real.sqrt b)).mem_of_tendsto hv hm
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    exact ⟨x, rfl, (Real.le_sqrt (norm_nonneg _) hb).1 hx⟩
  obtain ⟨x, hx, _⟩ := lifts one_pos
  refine ⟨S.qEquiv x, hx, le_of_forall_pos_le_add fun ε hε => ?_⟩
  obtain ⟨y, hy, hny⟩ := lifts hε
  have hxy := S.ι_injective (hx.trans hy.symm)
  rw [E_eq, hx, hxy, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  linarith

end CutoffRigidity.Riemann.Diff.FormData
