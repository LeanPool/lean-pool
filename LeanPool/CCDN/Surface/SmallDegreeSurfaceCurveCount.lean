/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Statements
import LeanPool.CCDN.Analysis.SmallDegreeSurfaceNumerics
import LeanPool.CCDN.Curve.AffineCurveCount
import LeanPool.CCDN.Surface.NonlinearCount

/-! Nonlinear initial curves whose degrees are at most logarithmic in the
box radius. The full affine curve theorem and the strict surface exponent
gap give a linear bound in every surface degree at least five. -/

@[expose] public section
namespace CCDN
noncomputable section

private theorem curveBound_logarithmic_degree {δ : ℕ} (hδ : 2 ≤ δ)
    {B D : ℝ} (hB : 1 ≤ B) (_hD : 0 ≤ D)
    (hδD : (δ : ℝ) ≤ D * (Real.log B + 1)) :
    curveBound δ B ≤ (δ : ℝ) * D ^ 2 * (D + 1) *
      B ^ (1 / 2 : ℝ) * (Real.log B + 1) ^ 3 := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hlog := Real.log_nonneg hB
  have hδR : (2 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hpow : B ^ (1 / (δ : ℝ)) ≤ B ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hB
      (one_div_le_one_div_of_le (by norm_num) hδR)
  have hsq : (δ : ℝ) ^ 2 ≤ (D * (Real.log B + 1)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hδD 2
  have hlogδ : Real.log B + δ ≤ (D + 1) * (Real.log B + 1) := by nlinarith
  have hcube : (δ : ℝ) ^ 3 ≤ (δ : ℝ) * (D * (Real.log B + 1)) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hsq (show (0 : ℝ) ≤ δ by positivity)
    nlinarith
  unfold curveBound
  calc
    _ ≤ ((δ : ℝ) * (D * (Real.log B + 1)) ^ 2) *
        B ^ (1 / 2 : ℝ) * ((D + 1) * (Real.log B + 1)) := by
      apply mul_le_mul (mul_le_mul hcube hpow (by positivity) (by positivity)) hlogδ
      · positivity
      · positivity
    _ = _ := by ring

private theorem sum_curveBound_logarithmic_degrees {ι : Type*}
    (S : Finset ι) (δ : ι → ℕ) (k : ℕ) {d : ℕ} (hd : 5 ≤ d)
    {A D B : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (hB : 1 ≤ B)
    (hδ : ∀ i ∈ S, 2 ≤ δ i)
    (hcap : ∀ i ∈ S, (δ i : ℝ) ≤ D * (Real.log B + 1))
    (hbudget : (∑ i ∈ S, (δ i : ℝ)) ≤
      A * B ^ (1 / Real.sqrt (d : ℝ)) * (Real.log B + 1) ^ k) :
    ∑ i ∈ S, curveBound (δ i) B ≤
      ((k + 3).factorial / (1 / 20 : ℝ) ^ (k + 3) * Real.exp (1 / 20)) *
        A * D ^ 2 * (D + 1) * B := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hlog := Real.log_nonneg hB
  let C := ((k + 3).factorial / (1 / 20 : ℝ) ^ (k + 3) * Real.exp (1 / 20))
  have hsum : (∑ i ∈ S, curveBound (δ i) B) ≤
      (∑ i ∈ S, (δ i : ℝ)) * D ^ 2 * (D + 1) *
        B ^ (1 / 2 : ℝ) * (Real.log B + 1) ^ 3 := by
    calc
      _ ≤ ∑ i ∈ S, (δ i : ℝ) * D ^ 2 * (D + 1) *
          B ^ (1 / 2 : ℝ) * (Real.log B + 1) ^ 3 :=
        Finset.sum_le_sum (fun i hi => curveBound_logarithmic_degree
          (hδ i hi) hB hD (hcap i hi))
      _ = _ := by simp only [Finset.sum_mul]
  calc
    _ ≤ _ := hsum
    _ ≤ (A * B ^ (1 / Real.sqrt (d : ℝ)) * (Real.log B + 1) ^ k) *
        D ^ 2 * (D + 1) *
        B ^ (1 / 2 : ℝ) * (Real.log B + 1) ^ 3 := by
      gcongr
    _ = (A * D ^ 2 * (D + 1)) *
        (B ^ (1 / Real.sqrt (d : ℝ) + 1 / 2) * (Real.log B + 1) ^ (k + 3)) := by
      rw [Real.rpow_add hB0, pow_add]
      ring
    _ ≤ (A * D ^ 2 * (D + 1)) * (C * B) :=
      mul_le_mul_of_nonneg_left (surface_nonlinear_polylog_weight hd (k + 3) hB)
        (by positivity)
    _ = _ := by dsimp only [C]; ring

/-- For each `k`, there is a constant `C` such that, for `d ≥ 5` and a finite family of
integral affine curves of degree at least two, each of degree at most `D (log B + 1)` and of
total degree at most `A B^(1/√d) (log B + 1)^k`, the union of the curves has at most
`C A D² (D + 1) B` integral points of height at most `B`. -/
theorem logarithmic_degree_curve_union_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : Finset (Ideal (CoordinatePolynomial 3)))
        (δ : Ideal (CoordinatePolynomial 3) → ℕ) (d : ℕ), 5 ≤ d →
      ∀ A D B : ℝ, 0 ≤ A → 0 ≤ D → 1 ≤ B →
      (∀ P ∈ S, P.IsPrime ∧ 2 ≤ δ P ∧ HasAffineCurveDegree P (δ P)) →
      (∀ P ∈ S, (δ P : ℝ) ≤ D * (Real.log B + 1)) →
      (∑ P ∈ S, (δ P : ℝ)) ≤
        A * B ^ (1 / Real.sqrt (d : ℝ)) * (Real.log B + 1) ^ k →
      (count (⋃ P ∈ S, idealZeroLocus P) B : ℝ) ≤ C * A * D ^ 2 * (D + 1) * B := by
  obtain ⟨K, hK, hcount⟩ := affine_curve_count 3 (by omega)
  let C₀ := ((k + 3).factorial / (1 / 20 : ℝ) ^ (k + 3) * Real.exp (1 / 20))
  have hC₀ : 0 < C₀ := by dsimp only [C₀]; positivity
  refine ⟨K * C₀, mul_pos hK hC₀, ?_⟩
  intro S δ d hd A D B hA hD hB hcurve hcap hbudget
  have hsum := sum_curveBound_logarithmic_degrees S δ k hd hA hD hB
    (fun P hP => (hcurve P hP).2.1) hcap hbudget
  calc
    _ ≤ ∑ P ∈ S, (count (idealZeroLocus P) B : ℝ) := by
      exact_mod_cast count_biUnion_finset_le S idealZeroLocus B
    _ ≤ ∑ P ∈ S, K * curveBound (δ P) B := by
      apply Finset.sum_le_sum
      intro P hP
      obtain ⟨hp, hδ, hdeg⟩ := hcurve P hP
      exact hcount P hp (δ P) (by omega) hdeg B hB
    _ = K * ∑ P ∈ S, curveBound (δ P) B := (Finset.mul_sum _ _ _).symm
    _ ≤ K * (C₀ * A * D ^ 2 * (D + 1) * B) :=
      mul_le_mul_of_nonneg_left hsum hK.le
    _ = _ := by ring

end
end CCDN
