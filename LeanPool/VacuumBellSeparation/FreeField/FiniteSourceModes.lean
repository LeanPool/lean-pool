/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.FiniteSourceComplex
public import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Genuine canonical coordinates for the finite physical sources

Strict positivity of the physical Gram gives commutation frequencies less
than two. Scaling the constructed orthonormal skew basis gives an actual
basis of smooth sources with canonical symplectic matrix and covariance
diag(1/ν). In particular every covariance mode is strictly greater than 1/2.
-/

@[expose] public section

open scoped InnerProductSpace

namespace VacuumBellSeparation

open Gaussian.HilbertComplexification

variable {m : ℝ} (hm : 0 < m) (S : Submodule ℝ TimeZeroSource)
  [FiniteDimensional ℝ S]

theorem finiteSource_skew_frequency_lt_two
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hSU : S ≤ localizedTimeZeroSources U)
    (hU : Bornology.IsBounded U) {n : ℕ} (ν : Fin n → ℝ)
    (b : OrthonormalBasis (Fin n × Fin 2) ℝ (FiniteSourceSpace hm S))
    (hb : ∀ i, finiteSourceCommutation hm S (b (i, 0)) = (-ν i) • b (i, 1) ∧
      finiteSourceCommutation hm S (b (i, 1)) = ν i • b (i, 0)) (i : Fin n) :
    ν i < 2 := by
  let z := mk (b (i, 0)) (b (i, 1))
  have hz : z ≠ 0 := by
    intro h
    have he : b (i, 0) = 0 := congrArg Gaussian.HilbertComplexification.re h
    have hn := b.norm_eq_one (i, 0)
    rw [he, norm_zero] at hn
    norm_num at hn
  have hp := inner_finiteSourceGram_pos hm S hSU hU z hz
  have he : (⟪z, finiteSourceGram hm S z⟫_ℂ).re = 2 - ν i := by
    rw [finiteSourceGram_eq_normalized_commutation]
    change (⟪z, z + (Complex.I / 2) •
      Gaussian.complexify (finiteSourceCommutation hm S) z⟫_ℂ).re = _
    simp [Gaussian.HilbertComplexification.inner_eq, z,
      (hb i).1, (hb i).2, real_inner_smul_right,
      orthonormal_iff_ite.mp b.orthonormal];
      simp [← Complex.ofReal_pow, Gaussian.HilbertComplexification.norm_sq, b.norm_eq_one]; ring
  rw [he] at hp
  linarith

/-- Rescaling is through nonzero units, so these vectors are an actual basis. -/
noncomputable def finiteSourceCanonicalBasis {n : ℕ} (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i)
    (b : OrthonormalBasis (Fin n × Fin 2) ℝ (FiniteSourceSpace hm S)) :
    Module.Basis (Fin n × Fin 2) ℝ (FiniteSourceSpace hm S) :=
  b.toBasis.isUnitSMul (w := fun i => (Real.sqrt (ν i.1))⁻¹)
    (fun i => isUnit_iff_ne_zero.mpr (inv_ne_zero (Real.sqrt_pos.mpr (hν i.1)).ne'))

omit [FiniteDimensional ℝ ↥S] in
theorem finiteSourceCanonicalBasis_apply {n : ℕ} (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i)
    (b : OrthonormalBasis (Fin n × Fin 2) ℝ (FiniteSourceSpace hm S))
    (i : Fin n × Fin 2) :
    finiteSourceCanonicalBasis hm S ν hν b i = (Real.sqrt (ν i.1))⁻¹ • b i :=
  Module.Basis.isUnitSMul_apply _ _

omit [FiniteDimensional ℝ ↥S] in
/-- The literal Fourier covariance in the constructed canonical basis. -/
theorem finiteSourceCanonicalBasis_covariance {n : ℕ} (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i)
    (b : OrthonormalBasis (Fin n × Fin 2) ℝ (FiniteSourceSpace hm S))
    (i j : Fin n × Fin 2) :
    timeZeroFourierCovariance m (finiteSourceCanonicalBasis hm S ν hν b i).1
      (finiteSourceCanonicalBasis hm S ν hν b j).1 =
        Gaussian.modeDiagonal (fun k => (ν k)⁻¹) i j := by
  rw [← finiteSourceSpace_inner hm S]
  simp only [finiteSourceCanonicalBasis_apply, real_inner_smul_left,
    real_inner_smul_right, orthonormal_iff_ite.mp b.orthonormal,
    Gaussian.modeDiagonal, Matrix.diagonal_apply]
  split_ifs with hij
  · subst j
    rw [mul_one, ← mul_inv, Real.mul_self_sqrt (hν i.1).le]
  · simp

/-- The exact positive-orientation canonical symplectic matrix. -/
theorem finiteSourceCanonicalBasis_symplectic {n : ℕ} (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i)
    (b : OrthonormalBasis (Fin n × Fin 2) ℝ (FiniteSourceSpace hm S))
    (hb : ∀ i, finiteSourceCommutation hm S (b (i, 0)) = (-ν i) • b (i, 1) ∧
      finiteSourceCommutation hm S (b (i, 1)) = ν i • b (i, 0))
    (i j : Fin n × Fin 2) :
    timeZeroSymplectic (finiteSourceCanonicalBasis hm S ν hν b i).1
      (finiteSourceCanonicalBasis hm S ν hν b j).1 = Gaussian.modeSymplecticForm i j := by
  rw [← finiteSourceCommutation_symplectic hm S]
  rcases i with ⟨i, a⟩
  rcases j with ⟨j, c⟩
  by_cases hij : i = j
  · subst j
    have hs : (Real.sqrt (ν i)) ^ 2 = ν i := Real.sq_sqrt (hν i).le
    have hn : Real.sqrt (ν i) ≠ 0 := (Real.sqrt_pos.mpr (hν i)).ne'
    fin_cases a <;> fin_cases c <;>
      simp [finiteSourceCanonicalBasis_apply, map_smul, (hb i).1, (hb i).2,
        real_inner_smul_left, real_inner_smul_right, orthonormal_iff_ite.mp b.orthonormal,
        Gaussian.modeSymplecticForm, Gaussian.oneModeSymplecticForm] <;>
      field_simp <;> nlinarith
  · fin_cases a <;> fin_cases c <;>
      simp [finiteSourceCanonicalBasis_apply, map_smul, (hb j).1, (hb j).2,
        real_inner_smul_left, real_inner_smul_right, orthonormal_iff_ite.mp b.orthonormal,
        Gaussian.modeSymplecticForm, Gaussian.oneModeSymplecticForm, hij, Prod.mk.injEq]

theorem reciprocal_finiteSource_frequency_gt_half {ν : ℝ} (hν : 0 < ν) (hν2 : ν < 2) :
    (1 / 2 : ℝ) < ν⁻¹ := by
  rw [inv_eq_one_div, lt_div_iff₀ hν]
  linarith

end VacuumBellSeparation
