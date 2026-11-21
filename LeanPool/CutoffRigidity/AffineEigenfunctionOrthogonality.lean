/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.AffineEigenfunctionMoments

/-! # Normalized affine eigenfunction rows

The Gaussian factor gives the actual second moments of affine eigenfunctions.
Polarization then turns their L² orthonormality into the Euclidean row
normalization used by the affine projection in Lemma 3.3.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory

variable {d k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The pointwise affine eigenfunction equation, expressed as a drift equation. -/
theorem affine_eigenfunction_iff_drift (V : E → ℝ) (a : E) (b ρ : ℝ) :
    (∀ x, langevinDifferentialOperator V (fun y => inner ℝ a y + b) x =
      -ρ * (inner ℝ a x + b)) ↔
    ∀ x, inner ℝ a (gradient V x) = ρ * (inner ℝ a x + b) := by
  simp only [show (fun y : E => inner ℝ a y + b) =
    (fun y => (innerSL ℝ a) y + b) from rfl, langevinDifferentialOperator_affine,
    innerSL_apply_apply]
  constructor <;> intro h x <;> have hx := h x <;> linarith

/-- A zero affine coefficient forces the constant eigenfunction to vanish. -/
theorem affine_eigenfunction_constant_zero (V : E → ℝ) (b ρ : ℝ) (hρ : 0 < ρ)
    (heigen : ∀ x, langevinDifferentialOperator V (fun y => inner ℝ (0 : E) y + b) x =
      -ρ * (inner ℝ (0 : E) x + b)) : b = 0 := by
  have h := (affine_eigenfunction_iff_drift V 0 b ρ).mp heigen 0
  simp only [inner_zero_left, zero_add] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hρ.ne'

/-- The second moment formula includes the zero coefficient case. -/
theorem affine_eigenfunction_second_moment_all
    (V : E → ℝ) (hV : Differentiable ℝ V) (a : E) (b ρ : ℝ) (hρ : 0 < ρ)
    (heigen : ∀ x, langevinDifferentialOperator V (fun y => inner ℝ a y + b) x =
      -ρ * (inner ℝ a x + b))
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    ∫ x, (inner ℝ a x + b) ^ 2 ∂gibbsMeasure volume V = ‖a‖ ^ 2 / ρ := by
  by_cases ha : a = 0
  · subst a
    rw [affine_eigenfunction_constant_zero V b ρ hρ heigen]
    simp
  · exact affine_eigenfunction_second_moment V hV a ha b ρ hρ heigen hprob

/-- The L² assertion includes identically zero eigenfunctions. -/
theorem affine_eigenfunction_memLp_all
    (V : E → ℝ) (hV : Differentiable ℝ V) (a : E) (b ρ : ℝ) (hρ : 0 < ρ)
    (heigen : ∀ x, langevinDifferentialOperator V (fun y => inner ℝ a y + b) x =
      -ρ * (inner ℝ a x + b))
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    MemLp (fun x => inner ℝ a x + b) 2 (gibbsMeasure volume V) := by
  by_cases ha : a = 0
  · subst a
    rw [affine_eigenfunction_constant_zero V b ρ hρ heigen]
    simp
  · exact affine_eigenfunction_memLp V hV a ha b ρ hρ heigen hprob

/-- Polarization of the genuine second moments computes all cross moments. -/
theorem affine_eigenfunction_cross_moment
    (V : E → ℝ) (hV : Differentiable ℝ V) (a c : E) (b e ρ : ℝ) (hρ : 0 < ρ)
    (ha : ∀ x, langevinDifferentialOperator V (fun y => inner ℝ a y + b) x =
      -ρ * (inner ℝ a x + b))
    (hc : ∀ x, langevinDifferentialOperator V (fun y => inner ℝ c y + e) x =
      -ρ * (inner ℝ c x + e))
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    ∫ x, (inner ℝ a x + b) * (inner ℝ c x + e) ∂gibbsMeasure volume V =
      inner ℝ a c / ρ := by
  have hasum : ∀ x, langevinDifferentialOperator V
      (fun y => inner ℝ (a + c) y + (b + e)) x =
      -ρ * (inner ℝ (a + c) x + (b + e)) := by
    apply (affine_eigenfunction_iff_drift V (a + c) (b + e) ρ).mpr
    intro x
    rw [inner_add_left, inner_add_left,
      (affine_eigenfunction_iff_drift V a b ρ).mp ha x,
      (affine_eigenfunction_iff_drift V c e ρ).mp hc x]
    ring
  have hfa := affine_eigenfunction_memLp_all V hV a b ρ hρ ha hprob
  have hfc := affine_eigenfunction_memLp_all V hV c e ρ hρ hc hprob
  have hs := affine_eigenfunction_second_moment_all V hV (a + c) (b + e) ρ hρ hasum hprob
  have hexpand : (fun x : E => (inner ℝ (a + c) x + (b + e)) ^ 2) =
      fun x => (inner ℝ a x + b) ^ 2 +
        2 * ((inner ℝ a x + b) * (inner ℝ c x + e)) + (inner ℝ c x + e) ^ 2 := by
    funext x
    rw [inner_add_left]
    ring
  have hp : Integrable (fun x : E => (inner ℝ a x + b) * (inner ℝ c x + e))
      (gibbsMeasure volume V) := hfa.integrable_mul hfc
  have hp2 : Integrable (fun x : E => 2 * ((inner ℝ a x + b) * (inner ℝ c x + e)))
      (gibbsMeasure volume V) := hp.const_mul 2
  have hp1 : Integrable (fun x : E => (inner ℝ a x + b) ^ 2 +
      2 * ((inner ℝ a x + b) * (inner ℝ c x + e)))
      (gibbsMeasure volume V) := hfa.integrable_sq.add hp2
  rw [hexpand, integral_add hp1 hfc.integrable_sq,
    integral_add hfa.integrable_sq hp2, integral_const_mul,
    affine_eigenfunction_second_moment_all V hV a b ρ hρ ha hprob,
    affine_eigenfunction_second_moment_all V hV c e ρ hρ hc hprob] at hs
  have hn : ‖a + c‖ ^ 2 = ‖a‖ ^ 2 + 2 * inner ℝ a c + ‖c‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm c a]
    ring
  rw [hn] at hs
  apply (eq_div_iff hρ.ne').mpr
  field_simp at hs
  linarith

/-- L² orthonormal affine eigenfunctions have Euclidean gradient Gram matrix `ρ I`. -/
theorem affine_eigenfunction_row_gram
    (V : E → ℝ) (hV : Differentiable ℝ V) (a : Fin k → E) (b : Fin k → ℝ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (heigen : ∀ i x, langevinDifferentialOperator V (fun y => inner ℝ (a i) y + b i) x =
      -ρ * (inner ℝ (a i) x + b i))
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (horth : ∀ i j, ∫ x, (inner ℝ (a i) x + b i) * (inner ℝ (a j) x + b j)
      ∂gibbsMeasure volume V = if i = j then 1 else 0) :
    ∀ i j, inner ℝ (a i) (a j) = if i = j then ρ else 0 := by
  intro i j
  have h := affine_eigenfunction_cross_moment V hV (a i) (a j) (b i) (b j) ρ hρ
    (heigen i) (heigen j) hprob
  rw [horth i j] at h
  by_cases hij : i = j <;> simp only [hij, ite_true, ite_false] at h ⊢ <;>
    field_simp at h <;> linarith

/-- Normalize the actual coefficient vectors by the square root of the eigenvalue. -/
@[expose] noncomputable def normalizedAffineRows (a : Fin k → E) (ρ : ℝ) : Fin k → E :=
  fun i => (Real.sqrt ρ)⁻¹ • a i

/-- The normalized gradients are orthonormal, as asserted in Remark 3.2. -/
theorem affine_eigenfunction_normalized_rows_orthonormal
    (V : E → ℝ) (hV : Differentiable ℝ V) (a : Fin k → E) (b : Fin k → ℝ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (heigen : ∀ i x, langevinDifferentialOperator V (fun y => inner ℝ (a i) y + b i) x =
      -ρ * (inner ℝ (a i) x + b i))
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (horth : ∀ i j, ∫ x, (inner ℝ (a i) x + b i) * (inner ℝ (a j) x + b j)
      ∂gibbsMeasure volume V = if i = j then 1 else 0) :
    Orthonormal ℝ (normalizedAffineRows a ρ) := by
  rw [orthonormal_iff_ite]
  intro i j
  simp only [normalizedAffineRows, real_inner_smul_left, inner_smul_right,
    affine_eigenfunction_row_gram V hV a b ρ hρ heigen hprob horth i j]
  have hs : (Real.sqrt ρ) ^ 2 = ρ := Real.sq_sqrt hρ.le
  have hn : Real.sqrt ρ ≠ 0 := (Real.sqrt_pos.mpr hρ).ne'
  by_cases hij : i = j
  · simp only [hij, ite_true]
    field_simp
    nlinarith [hs]
  · simp [hij]

/-- Recover the affine coordinate from its normalized row, pointwise. -/
theorem normalizedAffineRows_recover (a : Fin k → E) (b : Fin k → ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (i : Fin k) (x : E) :
    Real.sqrt ρ * inner ℝ (normalizedAffineRows a ρ i) x + b i =
      inner ℝ (a i) x + b i := by
  simp only [normalizedAffineRows, real_inner_smul_left]
  rw [← mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.mpr hρ).ne', one_mul]

/-- The actual normalized eigenmap represents the whole affine eigenfunction family. -/
theorem affine_eigenfunction_eigenmap_representation (a : Fin k → E) (b : Fin k → ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (x : E) :
    eigenmapCLM (normalizedAffineRows a ρ) ρ x + WithLp.toLp 2 b =
      WithLp.toLp 2 (fun i => inner ℝ (a i) x + b i) := by
  ext i
  change Real.sqrt ρ * inner ℝ (normalizedAffineRows a ρ i) x + b i = _
  exact normalizedAffineRows_recover a b hρ i x

end CutoffRigidity
