/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Spatial cutoffs of growing radius

Smooth cutoffs equal to one on balls of radius `n + 1`, with values in `[0, 1]`
and gradients of size `O(1 / (n + 1))`. They localize the mollified cross
pairing in `lem:pv-serrin-uniqueness`.
-/

public section

open MeasureTheory Set Filter
open scoped Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The fixed bump profile equal to one on the unit ball. -/
@[expose] def serrinBump : ContDiffBump (0 : Vec3) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The cutoff of radius `n + 1`. -/
@[expose] def serrinCutoff (n : ℕ) : Vec3 → ℝ := fun x => serrinBump ((1 / ((n : ℝ) + 1)) • x)

theorem serrinCutoff_contDiff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (serrinCutoff n) :=
  serrinBump.contDiff.comp (contDiff_const_smul _)

theorem serrinCutoff_hasCompactSupport (n : ℕ) : HasCompactSupport (serrinCutoff n) := by
  have hc : (1 / ((n : ℝ) + 1)) ≠ 0 := by positivity
  have h := serrinBump.hasCompactSupport.comp_homeomorph (Homeomorph.smulOfNeZero _ hc)
  exact h

theorem serrinCutoff_nonneg (n : ℕ) (x : Vec3) : 0 ≤ serrinCutoff n x :=
  serrinBump.nonneg

theorem serrinCutoff_le_one (n : ℕ) (x : Vec3) : serrinCutoff n x ≤ 1 :=
  serrinBump.le_one

theorem serrinCutoff_abs_le_one (n : ℕ) (x : Vec3) : |serrinCutoff n x| ≤ 1 := by
  rw [abs_of_nonneg (serrinCutoff_nonneg n x)]
  exact serrinCutoff_le_one n x

theorem serrinCutoff_tendsto_one (x : Vec3) :
    Tendsto (fun n => serrinCutoff n x) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
  filter_upwards [eventually_ge_atTop N] with n hn
  symm
  apply serrinBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [one_div, inv_mul_le_iff₀ hpos]
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  calc
    ‖x‖ ≤ N := hN
    _ ≤ (n : ℝ) + 1 := by linarith only [hn']
    _ = ((n : ℝ) + 1) * serrinBump.rIn := by
      change _ = ((n : ℝ) + 1) * 1
      ring

/-- The gradient of the cutoff of radius `n + 1` is uniformly `O(1 / (n + 1))`. -/
theorem serrinCutoff_deriv_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (j : Fin 3) (x : Vec3),
    |spatialDeriv (serrinCutoff n) j x| ≤ C * (1 / ((n : ℝ) + 1)) := by
  have hcont : Continuous (fun y : Vec3 => ‖fderiv ℝ (serrinBump : Vec3 → ℝ) y‖) :=
    ((serrinBump.contDiff (n := (⊤ : ℕ∞))).continuous_fderiv (by simp)).norm
  have hcs : HasCompactSupport (fun y : Vec3 => ‖fderiv ℝ (serrinBump : Vec3 → ℝ) y‖) :=
    (serrinBump.hasCompactSupport.fderiv (𝕜 := ℝ)).norm
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hcont
  refine ⟨|C| * ‖basisVec (d := 3) 0‖ + |C| * ‖basisVec (d := 3) 1‖ +
    |C| * ‖basisVec (d := 3) 2‖, by positivity, ?_⟩
  intro n j x
  set c : ℝ := 1 / ((n : ℝ) + 1) with hcdef
  have hc : 0 < c := by positivity
  have hd : HasFDerivAt (serrinCutoff n)
      ((fderiv ℝ (serrinBump : Vec3 → ℝ) (c • x)).comp (c • ContinuousLinearMap.id ℝ Vec3)) x := by
    have hin : HasFDerivAt (fun y : Vec3 => c • y) (c • ContinuousLinearMap.id ℝ Vec3) x :=
      (hasFDerivAt_id x).const_smul c
    exact (((serrinBump.contDiff (n := (⊤ : ℕ∞))).differentiable (by simp)) (c • x)).hasFDerivAt.comp
      x hin
  have heq : spatialDeriv (serrinCutoff n) j x =
      c * (fderiv ℝ (serrinBump : Vec3 → ℝ) (c • x)) (basisVec j) := by
    simp only [spatialDeriv, hd.fderiv, ContinuousLinearMap.comp_apply,
      smul_apply, ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  rw [heq, abs_mul, abs_of_pos hc]
  have hbound : |(fderiv ℝ (serrinBump : Vec3 → ℝ) (c • x)) (basisVec j)| ≤
      |C| * ‖basisVec (d := 3) j‖ := by
    rw [← Real.norm_eq_abs]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    gcongr
    exact (le_abs_self _).trans' (by simpa using hC (c • x))
  have hj : |C| * ‖basisVec (d := 3) j‖ ≤ |C| * ‖basisVec (d := 3) 0‖ +
      |C| * ‖basisVec (d := 3) 1‖ + |C| * ‖basisVec (d := 3) 2‖ := by
    fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      nlinarith only [mul_nonneg (abs_nonneg C) (norm_nonneg (basisVec (d := 3) 0)),
        mul_nonneg (abs_nonneg C) (norm_nonneg (basisVec (d := 3) 1)),
        mul_nonneg (abs_nonneg C) (norm_nonneg (basisVec (d := 3) 2))]
  calc
    c * |(fderiv ℝ (serrinBump : Vec3 → ℝ) (c • x)) (basisVec j)| ≤
        c * (|C| * ‖basisVec (d := 3) j‖) := by gcongr
    _ ≤ c * (|C| * ‖basisVec (d := 3) 0‖ + |C| * ‖basisVec (d := 3) 1‖ +
        |C| * ‖basisVec (d := 3) 2‖) := by gcongr
    _ = _ := by ring

end ESS
