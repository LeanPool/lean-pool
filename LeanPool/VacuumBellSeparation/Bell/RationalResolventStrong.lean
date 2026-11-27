/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.RationalResolvent

/-!
# Strong continuity of the bounded quadratic resolvent

Only strong convergence of the selfadjoint inputs is required. The exact
resolvent identity multiplies the two input differences at fixed vectors
by uniformly bounded operators. No uniform norm bound on the inputs, or
strong convergence of their squares, is used.
-/

@[expose] public section

namespace VacuumBellSeparation

open Filter Topology ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem boundedOperator_apply_tendsto_zero {ι : Type*} {l : Filter ι}
    {As : ι → H →L[ℂ] H} {xs : ι → H} {C : ℝ}
    (hA : ∀ i, ‖As i‖ ≤ C) (hx : Tendsto xs l (𝓝 0)) :
    Tendsto (fun i => As i (xs i)) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hz : Tendsto (fun i => C * ‖xs i‖) l (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using hx.norm.const_mul C
  apply squeeze_zero (fun _ => norm_nonneg _) _ hz
  intro i
  exact ((As i).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _))

theorem quadraticResolvent_strong_tendsto {ι : Type*} {l : Filter ι}
    {As : ι → H →L[ℂ] H} {A : H →L[ℂ] H}
    (hAs : ∀ i, IsSelfAdjoint (As i)) (hA : IsSelfAdjoint A)
    (hlim : ∀ x, Tendsto (fun i => As i x) l (𝓝 (A x))) (x : H) :
    Tendsto (fun i => quadraticResolvent (As i) x) l (𝓝 (quadraticResolvent A x)) := by
  have hzero (y : H) : Tendsto (fun i => (A - As i) y) l (𝓝 0) := by
    simpa only [sub_apply, sub_self] using
      (tendsto_const_nhds (x := A y)).sub (hlim y)
  have hfirst := boundedOperator_apply_tendsto_zero
    (fun i => quadraticResolvent_mul_norm_le (hAs i))
    (hzero (quadraticResolvent A x))
  have hsecond := boundedOperator_apply_tendsto_zero
    (fun i => quadraticResolvent_norm_le (As i))
    (hzero (A (quadraticResolvent A x)))
  have hsum : Tendsto (fun i =>
      (quadraticResolvent (As i) * As i) ((A - As i) (quadraticResolvent A x)) +
      quadraticResolvent (As i) ((A - As i) (A (quadraticResolvent A x)))) l (𝓝 0) := by
    simpa only [add_zero] using hfirst.add hsecond
  have he (i : ι) : quadraticResolvent (As i) x - quadraticResolvent A x =
      (quadraticResolvent (As i) * As i) ((A - As i) (quadraticResolvent A x)) +
      quadraticResolvent (As i) ((A - As i) (A (quadraticResolvent A x))) := by
    exact congrArg (fun B : H →L[ℂ] H => B x) (quadraticResolvent_sub (hAs i) hA)
  have hdiff : Tendsto (fun i => quadraticResolvent (As i) x - quadraticResolvent A x) l
      (𝓝 0) := by simpa only [he] using hsum
  simpa only [sub_add_cancel, zero_add] using hdiff.add_const (quadraticResolvent A x)

/-- The resulting operators are genuine effects. -/
theorem one_sub_quadraticResolvent_effect {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) :
    0 ≤ 1 - quadraticResolvent A ∧ 1 - quadraticResolvent A ≤ 1 :=
  ⟨sub_nonneg.mpr (quadraticResolvent_le_one hA),
    sub_le_self _ (quadraticResolvent_nonneg A)⟩

theorem one_sub_quadraticResolvent_strong_tendsto {ι : Type*} {l : Filter ι}
    {As : ι → H →L[ℂ] H} {A : H →L[ℂ] H}
    (hAs : ∀ i, IsSelfAdjoint (As i)) (hA : IsSelfAdjoint A)
    (hlim : ∀ x, Tendsto (fun i => As i x) l (𝓝 (A x))) (x : H) :
    Tendsto (fun i => (1 - quadraticResolvent (As i)) x) l
      (𝓝 ((1 - quadraticResolvent A) x)) := by
  exact (tendsto_const_nhds (x := x)).sub (quadraticResolvent_strong_tendsto hAs hA hlim x)

end VacuumBellSeparation
