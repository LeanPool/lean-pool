/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.AffineEigenspace
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! # The genuine standard Gaussian equilibrium eigenmap law

Every linear combination of actual affine eigenfunctions satisfies the same
pointwise eigen-equation. Its Gaussian law follows from the proved Gibbs
factorization, and the actual L² Gram matrix fixes its variance. Characteristic
functions then identify the full tuple law without an equilibrium-law premise.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory

variable {d k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The forced Gaussian law also covers the identically zero affine eigenfunction. -/
theorem affine_eigenfunction_hasLaw_gaussian_all
    (V : E → ℝ) (hV : Differentiable ℝ V) (a : E) (b ρ : ℝ) (hρ : 0 < ρ)
    (heigen : ∀ x, langevinDifferentialOperator V (fun y => inner ℝ a y + b) x =
      -ρ * (inner ℝ a x + b))
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    HasLaw (fun x : E => inner ℝ a x + b)
      (gaussianReal 0 (‖a‖ ^ 2 / ρ).toNNReal) (gibbsMeasure volume V) := by
  by_cases ha : a = 0
  · subst a
    have hb := affine_eigenfunction_constant_zero V b ρ hρ heigen
    subst b
    let := hprob
    refine ⟨by fun_prop, ?_⟩
    simp [gaussianReal_zero_var]
  · exact affine_eigenfunction_hasLaw_gaussian V hV a ha b ρ hρ heigen hprob

/-- Actual affine pointwise eigenfunctions are closed under finite linear combination. -/
theorem affine_eigenfunction_linearCombination
    (V : E → ℝ) (a : Fin k → E) (b c : Fin k → ℝ) (ρ : ℝ)
    (heigen : ∀ i x, langevinDifferentialOperator V (fun y => inner ℝ (a i) y + b i) x =
      -ρ * (inner ℝ (a i) x + b i)) :
    ∀ x, langevinDifferentialOperator V
      (fun y => inner ℝ (∑ i, c i • a i) y + ∑ i, c i * b i) x =
      -ρ * (inner ℝ (∑ i, c i • a i) x + ∑ i, c i * b i) := by
  apply (affine_eigenfunction_iff_drift V _ _ ρ).mpr
  intro x
  simp only [sum_inner, real_inner_smul_left]
  simp_rw [(affine_eigenfunction_iff_drift V _ _ ρ).mp (heigen _) x]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The normalized affine eigenfunction tuple has exactly the standard
Gaussian pushforward law under the actual normalized Gibbs measure. -/
theorem affine_eigenmap_hasLaw_stdGaussian
    (V : E → ℝ) (hV : Differentiable ℝ V) (a : Fin k → E) (b : Fin k → ℝ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (heigen : ∀ i x, langevinDifferentialOperator V (fun y => inner ℝ (a i) y + b i) x =
      -ρ * (inner ℝ (a i) x + b i))
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (horth : ∀ i j, ∫ x, (inner ℝ (a i) x + b i) * (inner ℝ (a j) x + b j)
      ∂gibbsMeasure volume V = if i = j then 1 else 0) :
    HasLaw (fun x : E => WithLp.toLp 2 (fun i => inner ℝ (a i) x + b i))
      (stdGaussian (EuclideanSpace ℝ (Fin k))) (gibbsMeasure volume V) := by
  let := hprob
  have hm : Measurable (fun x : E => WithLp.toLp 2 (fun i => inner ℝ (a i) x + b i)) := by
    fun_prop
  refine ⟨hm.aemeasurable, ?_⟩
  apply Measure.ext_of_charFun
  funext c
  have hnorm : ‖∑ i, c i • a i‖ ^ 2 = ρ * ‖c‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [sum_inner, inner_sum, real_inner_smul_left, inner_smul_right,
      affine_eigenfunction_row_gram V hV a b ρ hρ heigen hprob horth]
    simp only [mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    simp only [Real.inner_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hg := affine_eigenfunction_hasLaw_gaussian_all V hV (∑ i, c i • a i)
    (∑ i, c i * b i) ρ hρ (affine_eigenfunction_linearCombination V a b c ρ heigen) hprob
  have hid : (fun x : E => inner ℝ (WithLp.toLp 2 (fun i => inner ℝ (a i) x + b i)) c) =
      fun x => inner ℝ (∑ i, c i • a i) x + ∑ i, c i * b i := by
    funext x
    rw [sum_inner]
    simp only [real_inner_smul_left]
    rw [PiLp.inner_apply]
    simp only [Real.inner_apply]
    change (∑ i, (inner ℝ (a i) x + b i) * c i) =
      (∑ i, c i * inner ℝ (a i) x) + ∑ i, c i * b i
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [charFun_map_eq_charFun_map_inner_one hm.aemeasurable, hid, hg.map_eq,
    charFun_gaussianReal, charFun_stdGaussian, hnorm]
  simp [Real.toNNReal_of_nonneg (sq_nonneg ‖c‖), hρ.ne', Complex.ofReal_pow, neg_div]

/-- The actual normalized-row eigenmap, including its affine constant, sends
Gibbs equilibrium to the standard Gaussian law. -/
theorem normalized_affine_eigenmap_hasLaw_stdGaussian
    (V : E → ℝ) (hV : Differentiable ℝ V) (a : Fin k → E) (b : Fin k → ℝ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (heigen : ∀ i x, langevinDifferentialOperator V (fun y => inner ℝ (a i) y + b i) x =
      -ρ * (inner ℝ (a i) x + b i))
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (horth : ∀ i j, ∫ x, (inner ℝ (a i) x + b i) * (inner ℝ (a j) x + b j)
      ∂gibbsMeasure volume V = if i = j then 1 else 0) :
    HasLaw (fun x : E => eigenmapCLM (normalizedAffineRows a ρ) ρ x + WithLp.toLp 2 b)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) (gibbsMeasure volume V) := by
  have hid : (fun x : E => eigenmapCLM (normalizedAffineRows a ρ) ρ x + WithLp.toLp 2 b) =
      fun x => WithLp.toLp 2 (fun i => inner ℝ (a i) x + b i) := by
    funext x
    exact affine_eigenfunction_eigenmap_representation a b hρ x
  rw [hid]
  exact affine_eigenmap_hasLaw_stdGaussian V hV a b ρ hρ heigen hprob horth

/-- The constructed finite affine pointwise eigenspace basis has the actual
standard Gaussian tuple law under Gibbs equilibrium. -/
theorem affineEigenBasis_hasLaw_stdGaussian (V : E → ℝ) (hV : Differentiable ℝ V)
    {ρ : ℝ} (hρ : 0 < ρ) (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    HasLaw (fun x : E => WithLp.toLp 2 (fun i => affineEigenBasisFunction V ρ i x))
      (stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ (affineEigenRows V ρ)))))
      (gibbsMeasure volume V) := by
  exact affine_eigenmap_hasLaw_stdGaussian V hV
    (fun i => (affineEigenBasisCoefficient V ρ i : E))
    (fun i => affineEigenConstant V ρ (affineEigenBasisCoefficient V ρ i)) ρ hρ
    (fun i x => affineEigenBasisFunction_eigenfunction V hρ i x) hprob
    (fun i j => affineEigenBasisFunction_integral_mul V hV hρ hprob i j)

end CutoffRigidity
