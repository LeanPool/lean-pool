/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.DistillationScaling
public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

/-!
# Norm approximation by actual projection compression

This is an ingredient for the normal-state corollary following HC00
Proposition 1. It applies to every positive unital functional, without
assuming that the functional is a vector state in a chosen representation.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open scoped ComplexOrder

variable {C : Type*} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- Actual conjugation, positive on the original algebra. -/
def compressionPositive (q : C) : C →ₚ[ℂ] C where
  toFun x := star q * x * q
  map_add' x y := by simp only [mul_add, add_mul]
  map_smul' c x := by simp only [mul_smul_comm, smul_mul_assoc, RingHom.id_apply]
  monotone' := fun _ _ h => star_left_conjugate_le_conjugate h q

@[simp] theorem compressionPositive_apply (q x : C) :
    compressionPositive q x = star q * x * q := rfl

/-- The compressed positive functional is not silently normalized. -/
def compressionFunctional (φ : C →ₚ[ℂ] ℂ) (q : C) : C →ₚ[ℂ] ℂ :=
  φ.comp (compressionPositive q)

@[simp] theorem compressionFunctional_apply (φ : C →ₚ[ℂ] ℂ) (q x : C) :
    compressionFunctional φ q x = φ (star q * x * q) := rfl

/-- The actual operator-norm continuous functional supplied by positivity. -/
def compressionDual (φ : C →ₚ[ℂ] ℂ) (q : C) : StrongDual ℂ C :=
  (PositiveContinuousLinearMap.ofClass (compressionFunctional φ q)).toContinuousLinearMap

private theorem state_sqrt_star_mul_le_norm (φ : C →ₚ[ℂ] ℂ) (hφ : φ 1 = 1)
    (x : C) : Real.sqrt ‖φ (star x * x)‖ ≤ ‖x‖ := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨norm_nonneg x, ?_⟩
  calc
    ‖φ (star x * x)‖ ≤ ‖star x * x‖ := stateFunctional_norm_apply_le φ hφ _
    _ = ‖x‖ ^ 2 := by rw [CStarRing.norm_star_mul_self, pow_two]

private theorem state_sqrt_mul_star_le_norm (φ : C →ₚ[ℂ] ℂ) (hφ : φ 1 = 1)
    (x : C) : Real.sqrt ‖φ (x * star x)‖ ≤ ‖x‖ := by
  simpa only [star_star, norm_star] using state_sqrt_star_mul_le_norm φ hφ (star x)

/-- Uniform on every observable, not merely pointwise convergence. -/
theorem state_compression_apply_error_le (φ : C →ₚ[ℂ] ℂ) (hφ : φ 1 = 1)
    (q : C) (hq : IsStarProjection q) (x : C) :
    ‖φ x - compressionFunctional φ q x‖ ≤ 2 * Real.sqrt ‖φ (1 - q)‖ * ‖x‖ := by
  let e := 1 - q
  have he : IsStarProjection e := hq.one_sub
  have hleft : ‖φ (e * x)‖ ≤ Real.sqrt ‖φ e‖ * ‖x‖ := by
    have h := PositiveLinearMap.cauchy_schwarz_star_mul φ e x
    rw [he.isSelfAdjoint.star_eq, he.isIdempotentElem.eq] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (state_sqrt_star_mul_le_norm φ hφ x) (Real.sqrt_nonneg _))
  have hright : ‖φ (q * x * e)‖ ≤ ‖x‖ * Real.sqrt ‖φ e‖ := by
    have h := PositiveLinearMap.cauchy_schwarz_mul_star φ (q * x) e
    rw [he.isSelfAdjoint.star_eq, he.isIdempotentElem.eq] at h
    have hn : ‖q * x‖ ≤ ‖x‖ := calc
      ‖q * x‖ ≤ ‖q‖ * ‖x‖ := norm_mul_le _ _
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (IsStarProjection.norm_le q hq) (norm_nonneg x)
      _ = ‖x‖ := one_mul _
    exact h.trans (mul_le_mul_of_nonneg_right
      ((state_sqrt_mul_star_le_norm φ hφ (q * x)).trans hn) (Real.sqrt_nonneg _))
  have hx : x - star q * x * q = e * x + q * x * e := by
    rw [hq.isSelfAdjoint.star_eq]
    dsimp [e]
    noncomm_ring
  calc
    ‖φ x - compressionFunctional φ q x‖ = ‖φ (e * x) + φ (q * x * e)‖ := by
      rw [compressionFunctional_apply, ← map_sub, hx, map_add]
    _ ≤ ‖φ (e * x)‖ + ‖φ (q * x * e)‖ := norm_add_le _ _
    _ ≤ Real.sqrt ‖φ e‖ * ‖x‖ + ‖x‖ * Real.sqrt ‖φ e‖ := add_le_add hleft hright
    _ = 2 * Real.sqrt ‖φ (1 - q)‖ * ‖x‖ := by dsimp [e]; ring

/-- The norm here is the norm of the full dual, not the weak-star topology. -/
theorem state_compression_dual_error_le (φ : C →ₚ[ℂ] ℂ) (hφ : φ 1 = 1)
    (q : C) (hq : IsStarProjection q) :
    ‖(PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap -
      compressionDual φ q‖ ≤ 2 * Real.sqrt ‖φ (1 - q)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  exact state_compression_apply_error_le φ hφ q hq x

/-- Normalization uses the genuine mass of the projection; positivity of
this mass is a premise of the normalization theorem, not of approximation. -/
def normalizedCompression (φ : C →ₚ[ℂ] ℂ) (q : C) : C →ₚ[ℂ] ℂ :=
  distillationScaleFunctional (‖φ q‖⁻¹) (inv_nonneg.mpr (norm_nonneg _))
    (compressionFunctional φ q)

@[simp] theorem normalizedCompression_apply (φ : C →ₚ[ℂ] ℂ) (q x : C) :
    normalizedCompression φ q x = ‖φ q‖⁻¹ • φ (star q * x * q) := rfl

theorem normalizedCompression_one (φ : C →ₚ[ℂ] ℂ) (q : C)
    (hq : IsStarProjection q) (hp : 0 < ‖φ q‖) :
    normalizedCompression φ q 1 = 1 := by
  have he : φ q = (‖φ q‖ : ℂ) := Complex.eq_coe_norm_of_nonneg (φ.map_nonneg hq.nonneg)
  rw [normalizedCompression_apply, mul_one, hq.isSelfAdjoint.star_eq,
    hq.isIdempotentElem.eq]
  calc
    ‖φ q‖⁻¹ • φ q = ‖φ q‖⁻¹ • (‖φ q‖ : ℂ) :=
      congrArg (fun z : ℂ => ‖φ q‖⁻¹ • z) he
    _ = 1 := by
      simp only [Complex.real_smul, ← Complex.ofReal_mul,
        inv_mul_cancel₀ hp.ne', Complex.ofReal_one]

/-- A Bell operator equal to the identity on the surviving subspace has
exact expectation one in the normalized compressed state. -/
theorem normalizedCompression_eq_one_of_mul_eq (φ : C →ₚ[ℂ] ℂ) (q R : C)
    (hq : IsStarProjection q) (hp : 0 < ‖φ q‖) (hRq : R * q = q) :
    normalizedCompression φ q R = 1 := by
  have he : star q * R * q = star q * 1 * q := by
    rw [mul_assoc, hRq, mul_one]
  calc
    normalizedCompression φ q R = normalizedCompression φ q 1 := by
      simp only [normalizedCompression_apply, he]
    _ = 1 := normalizedCompression_one φ q hq hp

theorem state_projection_mass_complement (φ : C →ₚ[ℂ] ℂ) (hφ : φ 1 = 1)
    (q : C) (hq : IsStarProjection q) : ‖φ q‖ + ‖φ (1 - q)‖ = 1 := by
  have hqreal : (φ q).re = ‖φ q‖ := by
    simpa only [Complex.ofReal_re] using congrArg Complex.re
      (Complex.eq_coe_norm_of_nonneg (φ.map_nonneg hq.nonneg))
  have hereal : (φ (1 - q)).re = ‖φ (1 - q)‖ := by
    simpa only [Complex.ofReal_re] using congrArg Complex.re
      (Complex.eq_coe_norm_of_nonneg (φ.map_nonneg hq.one_sub.nonneg))
  have h := congrArg Complex.re (show φ q + φ (1 - q) = 1 by
    rw [← map_add, show q + (1 - q) = 1 by abel, hφ])
  simpa only [Complex.add_re, hqreal, hereal, Complex.one_re] using h

theorem normalizedCompression_apply_error_le (φ : C →ₚ[ℂ] ℂ) (hφ : φ 1 = 1)
    (q : C) (hq : IsStarProjection q) (hp : 0 < ‖φ q‖) (x : C) :
    ‖φ x - normalizedCompression φ q x‖ ≤
      (2 * Real.sqrt ‖φ (1 - q)‖ + ‖φ (1 - q)‖) * ‖x‖ := by
  have hmass := state_projection_mass_complement φ hφ q hq
  have hscale : compressionFunctional φ q x = ‖φ q‖ • normalizedCompression φ q x := by
    change φ (star q * x * q) = ‖φ q‖ • (‖φ q‖⁻¹ • φ (star q * x * q))
    rw [smul_smul, mul_inv_cancel₀ hp.ne', one_smul]
  have hdiff : compressionFunctional φ q x - normalizedCompression φ q x =
      (-‖φ (1 - q)‖) • normalizedCompression φ q x := by
    calc
      _ = (‖φ q‖ - 1) • normalizedCompression φ q x := by
        rw [sub_smul, one_smul, hscale]
      _ = _ := by congr 1; linarith
  have hb : ‖compressionFunctional φ q x - normalizedCompression φ q x‖ ≤
      ‖φ (1 - q)‖ * ‖x‖ := by
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (stateFunctional_norm_apply_le _ (normalizedCompression_one φ q hq hp) x)
      (norm_nonneg _)
  calc
    ‖φ x - normalizedCompression φ q x‖ ≤
        ‖φ x - compressionFunctional φ q x‖ +
          ‖compressionFunctional φ q x - normalizedCompression φ q x‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * Real.sqrt ‖φ (1 - q)‖ * ‖x‖ + ‖φ (1 - q)‖ * ‖x‖ :=
      add_le_add (state_compression_apply_error_le φ hφ q hq x) hb
    _ = _ := by ring

theorem normalizedCompression_dual_error_le (φ : C →ₚ[ℂ] ℂ) (hφ : φ 1 = 1)
    (q : C) (hq : IsStarProjection q) (hp : 0 < ‖φ q‖) :
    ‖(PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap -
      (PositiveContinuousLinearMap.ofClass (normalizedCompression φ q)).toContinuousLinearMap‖ ≤
        2 * Real.sqrt ‖φ (1 - q)‖ + ‖φ (1 - q)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact normalizedCompression_apply_error_le φ hφ q hq hp

end VacuumBellSeparation.Bipartite
