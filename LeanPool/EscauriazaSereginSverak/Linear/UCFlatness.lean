/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCDefs
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# From pointwise to integral flatness

The all-orders pointwise hypothesis in `thm:uc` implies the local integral
condition used by `lem:uc-gaussian`.
-/

public section


open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Pointwise vanishing of every order implies the integral vanishing
condition at the origin. -/
theorem uc_pointwise_to_integral_flatness
    (R T : ℝ) (hT : 0 < T)
    (w : ParabolicPoint → Vec3)
    (hvanish : ∀ k : ℕ, ∃ C : ℝ,
      ∀ z ∈ spaceTimeSet (vec3Ball 0 R) (Ioo 0 T),
        vec3EuclideanNorm (w z) ≤
          C * (vec3EuclideanNorm z.1 + Real.sqrt z.2) ^ k) :
    UCIntegralFlatness 0 R (min T 1) w := by
  let S : Set ParabolicPoint := spaceTimeSet (vec3Ball 0 1) (Ioo 0 1)
  have hSfinite : volume S < (∞ : ℝ≥0∞) := by
    change ((volume : Measure Vec3).prod (volume : Measure ℝ))
      (vec3Ball 0 1 ×ˢ Ioo (0 : ℝ) 1) < ∞
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top
      (CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top (x := 0) (r := 1))
      (by simp)
  intro m
  obtain ⟨C, hC⟩ := hvanish m
  let M : ℝ := volume.real S
  have hM : 0 ≤ M := measureReal_nonneg
  refine ⟨1 + M * C ^ 2, 1 / 4, ?_, by norm_num, ?_⟩
  · have hC2 := sq_nonneg C
    nlinarith only [hM, hC2, mul_nonneg hM hC2]
  intro r hr hrbound
  have hrR : r < R := lt_of_lt_of_le hrbound (min_le_left _ _)
  have hrTroot : r < Real.sqrt (min T 1) :=
    lt_of_lt_of_le hrbound (min_le_right _ _ |>.trans (min_le_left _ _))
  have hrquarter : r < 1 / 4 :=
    lt_of_lt_of_le hrbound (min_le_right _ _ |>.trans (min_le_right _ _))
  have hrone : r < 1 := by linarith only [hrquarter]
  have hr2one : r ^ 2 < 1 := by
    nlinarith only [hr, hrone, sq_nonneg (r - 1)]
  have hminT : 0 ≤ min T 1 := le_of_lt (lt_min hT (by norm_num))
  have hr2T : r ^ 2 < T := by
    have hsqrt : r ^ 2 < (Real.sqrt (min T 1)) ^ 2 :=
      pow_lt_pow_left₀ hrTroot (le_of_lt hr) (by norm_num)
    rw [Real.sq_sqrt hminT] at hsqrt
    exact lt_of_lt_of_le hsqrt (min_le_left _ _)
  let s : Set ParabolicPoint :=
    spaceTimeSet (vec3Ball 0 r) (Ioo 0 (r ^ 2))
  have hsS : s ⊆ S := by
    rintro z ⟨hzx, hzt⟩
    exact ⟨(mem_vec3Ball).2
        (lt_trans ((mem_vec3Ball).1 hzx) hrone),
      ⟨hzt.1, lt_trans hzt.2 hr2one⟩⟩
  have hsfinite : volume s < (∞ : ℝ≥0∞) :=
    (measure_mono hsS).trans_lt hSfinite
  have hmeasure : volume.real s ≤ M :=
    measureReal_mono hsS hSfinite.ne
  have hsmall : (2 * r) ^ 2 ≤ r := by
    have h4 : 4 * r ≤ 1 := by linarith only [hrquarter]
    have hmul := mul_le_mul_of_nonneg_right h4 (le_of_lt hr)
    nlinarith only [hmul]
  have hpoint (z : ParabolicPoint) (hz : z ∈ s) :
      vec3EuclideanNorm (w z) ^ 2 ≤ C ^ 2 * r ^ m := by
    have hzR : z ∈ spaceTimeSet (vec3Ball 0 R) (Ioo 0 T) := by
      exact ⟨(mem_vec3Ball).2
          (lt_trans ((mem_vec3Ball).1 hz.1) hrR),
        ⟨hz.2.1, lt_trans hz.2.2 hr2T⟩⟩
    have hsqrtr : Real.sqrt z.2 < r := by
      have hpow : (Real.sqrt z.2) ^ 2 < r ^ 2 := by
        rw [Real.sq_sqrt (le_of_lt hz.2.1)]
        exact hz.2.2
      exact (sq_lt_sq₀ (Real.sqrt_nonneg _) (le_of_lt hr)).1 hpow
    have hbase : 0 ≤ vec3EuclideanNorm z.1 + Real.sqrt z.2 := by
      exact add_nonneg (vec3EuclideanNorm_nonneg _) (Real.sqrt_nonneg _)
    have hgeom : vec3EuclideanNorm z.1 + Real.sqrt z.2 ≤ 2 * r := by
      have hx := (mem_vec3Ball).1 hz.1
      have hx0 : vec3EuclideanNorm z.1 < r := by
        simpa using hx
      linarith only [hx0, hsqrtr]
    have hpow : (vec3EuclideanNorm z.1 + Real.sqrt z.2) ^ m ≤
        (2 * r) ^ m := pow_le_pow_left₀ hbase hgeom m
    have hnorm : vec3EuclideanNorm (w z) ≤ |C| * (2 * r) ^ m := by
      calc
        _ ≤ C * (vec3EuclideanNorm z.1 + Real.sqrt z.2) ^ m := hC z hzR
        _ ≤ |C| * (vec3EuclideanNorm z.1 + Real.sqrt z.2) ^ m :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hbase _)
        _ ≤ |C| * (2 * r) ^ m :=
          mul_le_mul_of_nonneg_left hpow (abs_nonneg C)
    have hsq : vec3EuclideanNorm (w z) ^ 2 ≤
        (|C| * (2 * r) ^ m) ^ 2 :=
      (sq_le_sq₀ (vec3EuclideanNorm_nonneg _) (by positivity)).2 hnorm
    have hpowe : ((2 * r) ^ m) ^ 2 = ((2 * r) ^ 2) ^ m := by
      calc
        _ = (2 * r) ^ (m * 2) := (pow_mul _ _ _).symm
        _ = (2 * r) ^ (2 * m) := by rw [mul_comm m 2]
        _ = _ := pow_mul _ _ _
    have hpow2 : ((2 * r) ^ 2) ^ m ≤ r ^ m :=
      pow_le_pow_left₀ (sq_nonneg _) hsmall m
    calc
      _ ≤ (|C| * (2 * r) ^ m) ^ 2 := hsq
      _ = C ^ 2 * ((2 * r) ^ 2) ^ m := by rw [mul_pow, sq_abs, hpowe]
      _ ≤ C ^ 2 * r ^ m :=
        mul_le_mul_of_nonneg_left hpow2 (sq_nonneg C)
  have hint : IntegrableOn (fun _ : ParabolicPoint => C ^ 2 * r ^ m) s volume :=
    integrableOn_const hsfinite.ne
  have hbound :
      (∫ z in s, vec3EuclideanNorm (w z) ^ 2) ≤
        volume.real s * (C ^ 2 * r ^ m) := by
    calc
      _ ≤ ∫ _z in s, C ^ 2 * r ^ m :=
        setIntegral_mono_of_nonneg (fun z hz => sq_nonneg _)
          hpoint hint
      _ = _ := by rw [setIntegral_const]; simp only [smul_eq_mul]
  have hcoeff : 0 ≤ C ^ 2 * r ^ m :=
    mul_nonneg (sq_nonneg _) (pow_nonneg (le_of_lt hr) _)
  calc
    _ ≤ volume.real s * (C ^ 2 * r ^ m) := hbound
    _ ≤ M * (C ^ 2 * r ^ m) :=
      mul_le_mul_of_nonneg_right hmeasure hcoeff
    _ = (M * C ^ 2) * r ^ m := by ring
    _ ≤ (1 + M * C ^ 2) * r ^ m := by
      have hrpow : 0 ≤ r ^ m := pow_nonneg (le_of_lt hr) _
      nlinarith only [hrpow]

end ESS
