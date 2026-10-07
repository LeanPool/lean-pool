/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Leray Limit Initial Tail

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The squared energy of an `L²` initial field vanishes outside expanding
balls, as used in `prop:leray-limit`. -/
theorem lerayLimit_initialEnergyTail_tendsto_zero
    (a : Vec3 → Vec3) (ha : MemLp a 2 volume) :
    Tendsto (fun n : ℕ =>
      ∫ x in {x : Vec3 | (n : ℝ) < vec3EuclideanNorm x},
        (vec3EuclideanNorm (a x)) ^ (2 : ℕ) ∂volume) atTop (𝓝 0) := by
  let S : ℕ → Set Vec3 := fun n =>
    {x : Vec3 | (n : ℝ) < vec3EuclideanNorm x}
  let f : Vec3 → ℝ := fun x => (vec3EuclideanNorm (a x)) ^ (2 : ℕ)
  let F : ℕ → Vec3 → ℝ := fun n => (S n).indicator f
  let bound : Vec3 → ℝ := fun x => 9 * ‖a x‖ ^ (2 : ℕ)
  have hS (n : ℕ) : MeasurableSet (S n) := by
    apply (isOpen_lt continuous_const
      (continuous_vec3EuclideanNorm.comp continuous_id)).measurableSet
  have hf : AEStronglyMeasurable f volume := by
    exact (continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      ha.aestronglyMeasurable).pow 2
  have hboundInt : Integrable bound volume := by
    dsimp [bound]
    exact (ha.integrable_norm_pow (by norm_num)).const_mul 9
  have hnormbound (x : Vec3) : vec3EuclideanNorm (a x) ≤ 3 * ‖a x‖ := by
    calc
      vec3EuclideanNorm (a x) ≤ ∑ i : Fin 3, |a x i| :=
        vec3EuclideanNorm_le_sum_abs (a x)
      _ ≤ ∑ _i : Fin 3, ‖a x‖ := by
        apply Finset.sum_le_sum
        intro i hi
        exact norm_le_pi_norm (a x) i
      _ = 3 * ‖a x‖ := by norm_num
  have hbound (n : ℕ) : ∀ᵐ x ∂volume, ‖F n x‖ ≤ bound x := by
    filter_upwards [] with x
    by_cases hx : x ∈ S n
    · change ‖(S n).indicator f x‖ ≤ bound x
      rw [Set.indicator_of_mem hx]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hleft : -(3 * ‖a x‖) ≤ vec3EuclideanNorm (a x) :=
        le_trans (neg_nonpos.mpr (by positivity)) (vec3EuclideanNorm_nonneg _)
      have hsq := sq_le_sq' hleft (hnormbound x)
      dsimp [f, bound]
      nlinarith only [hsq]
    · simp [F, hx, bound]
  have hpoint (x : Vec3) : Tendsto (fun n => F n x) atTop (𝓝 0) := by
    obtain ⟨N, hN⟩ := exists_nat_gt (vec3EuclideanNorm x)
    have hevent : ∀ᶠ n : ℕ in atTop, x ∉ S n := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      simpa [S] using not_lt_of_ge (le_trans hN.le hNn)
    have heq : (fun n => F n x) =ᶠ[atTop] fun _ => (0 : ℝ) := by
      filter_upwards [hevent] with n hn
      simp [F, hn]
    exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := volume) (F := F) bound
    (fun n => (hf.indicator (hS n))) hboundInt hbound
    (Filter.Eventually.of_forall hpoint)
  have hEq (n : ℕ) :
      (∫ x in S n, f x ∂volume) = ∫ x, F n x ∂volume := by
    exact (integral_indicator (hS n)).symm
  have hEqFun : (fun n : ℕ => ∫ x in S n, f x ∂volume) =
      (fun n => ∫ x, F n x ∂volume) := funext hEq
  rw [hEqFun]
  simpa only [integral_zero] using hlim

end CKN.Leray

end
