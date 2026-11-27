/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.Agazzi.Defs
public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Basic
public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.BeurlingAhlfors.Basic
public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Complex.RadialStretch

/-!
# Bridges: the definitions of `Agazzi.Defs` and the facts that the paper states about them

* The jacobian, the unit square and periodicity are those of the package `CalculusOfVariations`
  (`grad`, `unitCube 2`, the periodicity in `QuasiconvexAtPeriodic`); the Beurling–Ahlfors
  transform, its norm and the Wirtinger derivatives are those of the package `HarmonicAnalysis`
  (`beurlingPow 1`, `beurlingPowNorm 1`, `dz`, `dzbar`), and so are `L^p_loc`, weak derivatives and
  the radial stretch (`MemLpLoc`, `HasWeakLineDerivOn`, `radialStretch`).
* The facts that the paper states in the introduction (TeX lines 264–268): with
  `A z = a₊ z + a₋ (conj z)`, the operator norm is `|A| = |a₊| + |a₋|` (`opNorm_eq`) and
  `det A = |a₊|² − |a₋|²` (`det_eq`).
* `p* − 1 = (p − 1)⁻¹` for `1 < p ≤ 2` and `p − 1` for `p ≥ 2` (the second equality of
  `(eq:BA-sharp-norm)`).
* The torus `Q` has measure `1` (`volume_unitSquare`).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap FourierTransform ENNReal ComplexConjugate

namespace Agazzi

theorem jacobian_eq_grad (φ : (Fin 2 → ℝ) → Fin 2 → ℝ) (x : Fin 2 → ℝ) :
    jacobian φ x = CalculusOfVariations.grad φ x := rfl

theorem unitSquare_eq_unitCube : unitSquare = CalculusOfVariations.unitCube 2 := rfl

/-- `|Q| = 1`. Proof: `(0, 1)²` is a product of two intervals of length `1`. -/
theorem volume_unitSquare : volume unitSquare = 1 := by
  simp [unitSquare, volume_pi_pi]

/-- Proof: both are `𝓕⁻¹ (((conj ξ) / ξ) · 𝓕 f)`, the package's symbol to the first power. -/
theorem beurling_eq_beurlingPow (f : ℂ → ℂ) :
    beurling f = HarmonicAnalysis.beurlingPow 1 f := by
  simp [beurling, HarmonicAnalysis.beurlingPow, HarmonicAnalysis.fourierMultiplier,
    HarmonicAnalysis.beurlingSymbol]

/-- Proof: the two suprema have the same terms, by `beurling_eq_beurlingPow`. -/
theorem beurlingNorm_eq_beurlingPowNorm (p : ℝ) :
    beurlingNorm p = HarmonicAnalysis.beurlingPowNorm 1 p := by
  unfold beurlingNorm
  simp_rw [beurling_eq_beurlingPow]
  rfl

theorem dz_eq (g : ℂ → ℂ) : dz g = HarmonicAnalysis.dz g := rfl

theorem memLpLoc_iff {f : ℂ → ℂ} {p : ℝ≥0∞} {Ω : Set ℂ} :
    MemLpLoc f p Ω ↔ HarmonicAnalysis.MemLpLoc f p Ω := Iff.rfl

theorem hasWeakLineDerivOn_iff {Ω : Set ℂ} {f g : ℂ → ℂ} {v : ℂ} :
    HasWeakLineDerivOn Ω f g v ↔ HarmonicAnalysis.HasWeakLineDerivOn Ω f g v := Iff.rfl

theorem radialStretch_eq : radialStretch = HarmonicAnalysis.radialStretch := rfl

theorem dzbar_eq (g : ℂ → ℂ) : dzbar g = HarmonicAnalysis.dzbar g := rfl

/-- `𝒮 ∘ ∂_zbar = ∂_z` on Schwartz functions: the characterization `(eq:BA-definition)` of the
Beurling–Ahlfors transform (the package's `HarmonicAnalysis.beurlingPow_dzbar_iterate`).

Proof: the package's `𝓑^k (∂_zbar^k F) = ∂^k F` for `k = 1`. -/
theorem beurling_dzbar (F : 𝓢(ℂ, ℂ)) : beurling (dzbar F) = dz F := by
  have h := HarmonicAnalysis.beurlingPow_dzbar_iterate 1 F
  rw [Function.iterate_one, Function.iterate_one] at h
  rw [beurling_eq_beurlingPow, dzbar_eq, dz_eq]
  exact h

/-- `det A = |a₊|² − |a₋|²` (TeX line 268).

Proof: expand `|a₊|² = ((a₁₁ + a₂₂)² + (a₂₁ − a₁₂)²) / 4` and
`|a₋|² = ((a₁₁ − a₂₂)² + (a₂₁ + a₁₂)²) / 4`. -/
theorem det_eq (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.det = ‖conformalPart A‖ ^ 2 - ‖anticonformalPart A‖ ^ 2 := by
  rw [Matrix.det_fin_two, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply]
  simp only [conformalPart, anticonformalPart]
  ring

/-- The point `x₀ + i x₁ ∈ ℂ` of `x ∈ ℝ²`. -/
private def rowalgC (x : EuclideanSpace ℝ (Fin 2)) : ℂ := ⟨x 0, x 1⟩

private lemma norm_rowalgC (x : EuclideanSpace ℝ (Fin 2)) : ‖rowalgC x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Complex.norm_eq_sqrt_sq_add_sq]
  simp [rowalgC, Real.norm_eq_abs, sq_abs]

/-- `A z = a₊ z + a₋ (conj z)` under `ℝ² = ℂ`. -/
private lemma rowalgC_apply (A : Matrix (Fin 2) (Fin 2) ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    rowalgC (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A x) =
      conformalPart A * rowalgC x + anticonformalPart A * conj (rowalgC x) := by
  apply Complex.ext <;>
  simp [rowalgC, conformalPart, anticonformalPart, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
  ring

/-- For `a, b ∈ ℂ` there is a unit `z` with `|a z + b (conj z)| = |a| + |b|`: if `a, b ≠ 0`, a
square root
`z` of `u = ā b / (|a| |b|)` (then `(conj z) (a z² + b) = (|a| / |b| + 1) (conj z) b`); otherwise
`z = 1`. -/
private lemma rowalg_exists_unit (a b : ℂ) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ‖a * z + b * conj z‖ = ‖a‖ + ‖b‖ := by
  by_cases h : a = 0 ∨ b = 0
  · refine ⟨1, by simp, ?_⟩
    rcases h with rfl | rfl <;> simp
  · obtain ⟨ha, hb⟩ := not_or.1 h
    have ha' : 0 < ‖a‖ := norm_pos_iff.2 ha
    have hb' : 0 < ‖b‖ := norm_pos_iff.2 hb
    set u : ℂ := conj a * b / ((‖a‖ * ‖b‖ : ℝ) : ℂ) with hu
    have hu1 : ‖u‖ = 1 := by
      rw [hu, norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (mul_pos ha' hb')]
      field_simp
    obtain ⟨z, hz⟩ : ∃ z : ℂ, z ^ 2 = u := ⟨_, Complex.cpow_nat_inv_pow u two_ne_zero⟩
    have hz1 : ‖z‖ = 1 := by
      have h2 : ‖z‖ ^ 2 = 1 := by rw [← norm_pow, hz, hu1]
      have h0 := norm_nonneg z
      nlinarith
    refine ⟨z, hz1, ?_⟩
    have hzc : conj z * z = 1 := by rw [Complex.conj_mul', hz1]; simp
    have h1 : a * z ^ 2 + b = ((‖a‖ / ‖b‖ + 1 : ℝ) : ℂ) * b := by
      have hab : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast ha'.ne'
      have hbb : (‖b‖ : ℂ) ≠ 0 := by exact_mod_cast hb'.ne'
      rw [hz, hu, mul_div_assoc', ← mul_assoc, Complex.mul_conj']
      push_cast
      field_simp
    have key : a * z + b * conj z = conj z * (((‖a‖ / ‖b‖ + 1 : ℝ) : ℂ) * b) := by
      rw [← h1]
      linear_combination (-(a * z)) * hzc
    rw [key, norm_mul, Complex.norm_conj, hz1, one_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    field_simp

/-- The operator norm of `A` on Euclidean `ℝ²` is `|a₊| + |a₋|` (TeX line 268).

Proof: with `ℝ² = ℂ`, `A z = a₊ z + a₋ (conj z)`, so `|A z| ≤ (|a₊| + |a₋|) |z|` by the triangle
inequality, with equality at a unit `z` for which `a₊ z` and `a₋ (conj z)` point the same way
(`z² = ā₊ a₋ / |a₊ a₋|` if `a₊ a₋ ≠ 0`, `z = 1` otherwise). -/
theorem opNorm_eq (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A‖ =
      ‖conformalPart A‖ + ‖anticonformalPart A‖ := by
  set T := Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    rw [← norm_rowalgC, ← norm_rowalgC, rowalgC_apply]
    calc _ ≤ ‖conformalPart A * rowalgC x‖ + ‖anticonformalPart A * conj (rowalgC x)‖ :=
          norm_add_le _ _
      _ = _ := by rw [norm_mul, norm_mul, Complex.norm_conj]; ring
  · obtain ⟨z, hz1, hz⟩ := rowalg_exists_unit (conformalPart A) (anticonformalPart A)
    set x : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![z.re, z.im]
    have hx : rowalgC x = z := by simp [x, rowalgC]
    have hx1 : ‖x‖ = 1 := by rw [← norm_rowalgC, hx, hz1]
    calc ‖conformalPart A‖ + ‖anticonformalPart A‖ = ‖T x‖ := by
          rw [← norm_rowalgC, rowalgC_apply, hx, hz]
      _ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
      _ = ‖T‖ := by rw [hx1, mul_one]

/-- `p* − 1 = (p − 1)⁻¹` for `1 < p ≤ 2` (`(eq:BA-sharp-norm)`).

Proof: `p ≤ p / (p − 1)` as `p − 1 ≤ 1`, so `p* = p / (p − 1)`, and
`p / (p − 1) − 1 = 1 / (p − 1)`. -/
theorem pStar_sub_one_of_le_two {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) :
    pStar p - 1 = (p - 1)⁻¹ := by
  have h1 : 0 < p - 1 := by linarith
  have hle : p ≤ p / (p - 1) := by
    rw [le_div_iff₀ h1]; nlinarith
  rw [pStar, max_eq_right hle]
  field_simp
  ring

/-- `p* − 1 = p − 1` for `p ≥ 2` (`(eq:BA-sharp-norm)`).

Proof: `p / (p − 1) ≤ p` as `p − 1 ≥ 1`, so `p* = p`. -/
theorem pStar_sub_one_of_two_le {p : ℝ} (hp2 : 2 ≤ p) : pStar p - 1 = p - 1 := by
  have h1 : 0 < p - 1 := by linarith
  have hle : p / (p - 1) ≤ p := by
    rw [div_le_iff₀ h1]; nlinarith
  rw [pStar, max_eq_left hle]

/-- For `1 < p < 2`, `B_p = (p − 1)⁻¹ (|a₊| − (p − 1) |a₋|) (|a₊| + |a₋|)^{p−1}`: a positive
multiple of the form of the Burkholder function used for `1 < p ≤ 2`.

Proof: `p* − 1 = (p − 1)⁻¹` (`pStar_sub_one_of_le_two`). -/
theorem burkholderB_of_lt_two {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    burkholderB p A = (p - 1)⁻¹ * ((‖conformalPart A‖ + ‖anticonformalPart A‖) ^ (p - 1) *
      (‖conformalPart A‖ - (p - 1) * ‖anticonformalPart A‖)) := by
  have h1 : p - 1 ≠ 0 := by linarith
  simp only [burkholderB, hp2, ↓reduceIte, pStar_sub_one_of_le_two hp hp2.le]
  field_simp

end Agazzi
