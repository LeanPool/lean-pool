/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SchwartzEvolution

/-!
# A genuine smooth planar cutoff for finite-propagation energy

The cutoff is zero behind the advancing plane, positive at every point ahead
of it, and between zero and one. Its actual derivative has compact support,
is nonnegative and bounded. Temperate growth makes multiplication on the
Schwartz core literal. No support theorem for a wave solution is assumed.
-/

@[expose] public section

namespace VacuumBellSeparation

open Filter Topology Set
open scoped InnerProductSpace ContDiff

theorem fderiv_smoothTransition_eq_zero_of_not_mem_Icc {x : ℝ}
    (hx : x ∉ Icc (0 : ℝ) 1) : fderiv ℝ Real.smoothTransition x = 0 := by
  have hout : x < 0 ∨ 1 < x := by
    simpa only [mem_Icc, not_and_or, not_le] using hx
  rcases hout with hx | hx
  · have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => 0) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    rw [heq.fderiv_eq]
    exact fderiv_const_apply _
  · have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => 1) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    rw [heq.fderiv_eq]
    exact fderiv_const_apply _

theorem hasCompactSupport_fderiv_smoothTransition :
    HasCompactSupport (fderiv ℝ Real.smoothTransition) :=
  HasCompactSupport.intro isCompact_Icc fun _ hx =>
    fderiv_smoothTransition_eq_zero_of_not_mem_Icc hx

theorem hasCompactSupport_deriv_smoothTransition :
    HasCompactSupport (deriv Real.smoothTransition) := by
  apply HasCompactSupport.intro (K := Icc (0 : ℝ) 1) isCompact_Icc
  intro x hx
  rw [deriv, fderiv_smoothTransition_eq_zero_of_not_mem_Icc hx]
  rfl

theorem contDiff_deriv_smoothTransition :
    ContDiff ℝ (∞ : ℕ∞ω) (deriv Real.smoothTransition) :=
  (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2

theorem hasTemperateGrowth_deriv_smoothTransition :
    Function.HasTemperateGrowth (deriv Real.smoothTransition) :=
  hasCompactSupport_deriv_smoothTransition.hasTemperateGrowth contDiff_deriv_smoothTransition

theorem hasTemperateGrowth_smoothTransition :
    Function.HasTemperateGrowth Real.smoothTransition := by
  apply Function.HasTemperateGrowth.of_fderiv
    (hasCompactSupport_fderiv_smoothTransition.hasTemperateGrowth
      (contDiff_infty_iff_fderiv.mp Real.smoothTransition.contDiff).2)
    ((contDiff_infty_iff_fderiv.mp Real.smoothTransition.contDiff).1) (k := 0) (C := 1)
  intro x
  simpa only [pow_zero, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (Real.smoothTransition.nonneg x)] using Real.smoothTransition.le_one x

theorem deriv_smoothTransition_nonneg (x : ℝ) : 0 ≤ deriv Real.smoothTransition x :=
  Real.smoothTransition.monotone.deriv_nonneg

theorem exists_bound_deriv_smoothTransition :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖deriv Real.smoothTransition x‖ ≤ C := by
  obtain ⟨x₀, hx₀⟩ := contDiff_deriv_smoothTransition.continuous.norm
    |>.exists_forall_ge_of_hasCompactSupport hasCompactSupport_deriv_smoothTransition.norm
  exact ⟨‖deriv Real.smoothTransition x₀‖, norm_nonneg _, hx₀⟩

/-- Planar energy weight defined as `Real.smoothTransition (⟪a, x - x₀⟫_ℝ - R - t)`. -/
noncomputable def planarEnergyWeight (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Real.smoothTransition (⟪a, x - x₀⟫_ℝ - R - t)

/-- Planar energy slope defined as `deriv Real.smoothTransition (⟪a, x - x₀⟫_ℝ - R - t)`. -/
noncomputable def planarEnergySlope (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  deriv Real.smoothTransition (⟪a, x - x₀⟫_ℝ - R - t)

theorem planarEnergyWeight_nonneg (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : 0 ≤ planarEnergyWeight a x₀ R t x :=
  Real.smoothTransition.nonneg _

theorem planarEnergyWeight_le_one (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : planarEnergyWeight a x₀ R t x ≤ 1 :=
  Real.smoothTransition.le_one _

theorem planarEnergySlope_nonneg (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : 0 ≤ planarEnergySlope a x₀ R t x :=
  deriv_smoothTransition_nonneg _

theorem hasTemperateGrowth_planarEnergyWeight (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ) :
    Function.HasTemperateGrowth (planarEnergyWeight a x₀ R t) := by
  apply hasTemperateGrowth_smoothTransition.comp
  change Function.HasTemperateGrowth (fun x => (innerSL ℝ a) (x - x₀) - R - t)
  fun_prop

theorem hasTemperateGrowth_planarEnergySlope (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ) :
    Function.HasTemperateGrowth (planarEnergySlope a x₀ R t) := by
  apply hasTemperateGrowth_deriv_smoothTransition.comp
  change Function.HasTemperateGrowth (fun x => (innerSL ℝ a) (x - x₀) - R - t)
  fun_prop

theorem hasDerivAt_planarEnergyWeight (a x₀ x : EuclideanSpace ℝ (Fin 3)) (R t : ℝ) :
    HasDerivAt (fun s => planarEnergyWeight a x₀ R s x)
      (-planarEnergySlope a x₀ R t x) t := by
  have hd := (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).1
  simpa only [planarEnergyWeight, planarEnergySlope, Function.comp_def,
    Pi.sub_apply, id_eq, zero_sub, mul_neg, mul_one] using!
    (hd _).hasDerivAt.comp t ((hasDerivAt_const t (⟪a, x - x₀⟫_ℝ - R)).sub (hasDerivAt_id t))

theorem hasFDerivAt_planarEnergyWeight (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (planarEnergyWeight a x₀ R t)
      (planarEnergySlope a x₀ R t x • innerSL ℝ a) x := by
  have ha : HasFDerivAt (fun y => ⟪a, y - x₀⟫_ℝ - R - t) (innerSL ℝ a) x := by
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using!
      (((innerSL ℝ a).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x₀)).sub_const R).sub_const t
  exact (((contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).1
    _).hasDerivAt).comp_hasFDerivAt x ha

theorem planarEnergyWeight_zero_of_norm_le {a x₀ x : EuclideanSpace ℝ (Fin 3)}
    (ha : ‖a‖ ≤ 1) {R t : ℝ} (hx : ‖x - x₀‖ ≤ R + t) :
    planarEnergyWeight a x₀ R t x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hi := (real_inner_le_norm a (x - x₀)).trans
    (mul_le_mul_of_nonneg_right ha (norm_nonneg (x - x₀)))
  linarith

theorem planarEnergyWeight_pos {a x₀ x : EuclideanSpace ℝ (Fin 3)} {R t : ℝ}
    (hx : R + t < ⟪a, x - x₀⟫_ℝ) : 0 < planarEnergyWeight a x₀ R t x := by
  apply Real.smoothTransition.pos_of_pos
  linarith

end VacuumBellSeparation
