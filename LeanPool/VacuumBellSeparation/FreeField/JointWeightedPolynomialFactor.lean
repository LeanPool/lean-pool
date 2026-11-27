/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointMidpointRegionMoments
public import LeanPool.VacuumBellSeparation.FreeField.JointSymmetricPolynomialPairing
public import LeanPool.VacuumBellSeparation.FreeField.JointPolynomialComplexification
public import LeanPool.VacuumBellSeparation.FreeField.JointPolynomialOperatorIdentification
public import LeanPool.VacuumBellSeparation.Gaussian.ComplexificationDenseExt

/-!
# Literal reserve factorizations of the actual joint polynomials

The finite symmetric sums use genuine weighted midpoint moments. Their
sandwiches agree with the existing original-source polynomial operators,
by the same compact-test integrals and completion density.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open Gaussian Gaussian.HilbertComplexification MvPolynomial
open scoped InnerProductSpace ENNReal

private theorem inner_complexification_ofReal {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x y : E) :
    inner ℂ (ofReal x) (ofReal y) = (inner ℝ x y : ℂ) := by
  simp only [HilbertComplexification.inner_eq, ofReal_re, ofReal_im,
    inner_zero_left, inner_zero_right, add_zero, sub_zero]
  rfl

theorem jointWeighted_field_factor {μ s b : ℝ} (hμ : 0 < μ) (hs : s ≠ 0)
    (v : JointWeightedMomentFamily hμ s b)
    (w : JointSourceMomentFamily hμ (jointSourceRegion s)) (P : MvPolynomial (Fin 6) ℂ) :
    sourceReserve hμ (jointSourceRegion s) ^ b * jointSymmetricPolynomialOperator v.field P *
        sourceReserve hμ (jointSourceRegion s) ^ b =
      complexify (jointPolynomialMomentOperator w.field
        (jointPhysicalPolynomial s (-(P + rename swapSpatialSix P)))) := by
  apply complexification_operator_ext_dense_real
    (e := fun x : SourceTestSpace hμ (jointSourceRegion s) => (x : SourceHilbert hμ
      (jointSourceRegion s)))
    (f := fun x : SourceTestSpace hμ (jointSourceRegion s) => (x : SourceHilbert hμ
      (jointSourceRegion s)))
    UniformSpace.Completion.denseRange_coe UniformSpace.Completion.denseRange_coe
  intro x y
  rw [weighted_jointSymmetricPolynomial_pairing hμ (jointSourceRegion s)
    (spatialAxisDisplacement (s / 2) 0) s v.field P (fun x => x.1.1) v.field_pairing,
    complexify_ofReal, inner_complexification_ofReal, jointPhysicalPolynomial_field_pairing]
  simp only [jointPhysicalMidpoint_eq_centeredScaled hs]

theorem jointWeighted_momentum_factor {μ s b : ℝ} (hμ : 0 < μ) (hs : s ≠ 0)
    (v : JointWeightedMomentFamily hμ s b)
    (w : JointSourceMomentFamily hμ (jointSourceRegion s)) (P : MvPolynomial (Fin 6) ℂ) :
    sourceReserve hμ (jointSourceRegion s) ^ b * jointSymmetricPolynomialOperator v.momentum P *
        sourceReserve hμ (jointSourceRegion s) ^ b =
      complexify (jointPolynomialMomentOperator w.momentum
        (jointPhysicalPolynomial s (-(P + rename swapSpatialSix P)))) := by
  apply complexification_operator_ext_dense_real
    (e := fun x : SourceTestSpace hμ (jointSourceRegion s) => (x : SourceHilbert hμ
      (jointSourceRegion s)))
    (f := fun x : SourceTestSpace hμ (jointSourceRegion s) => (x : SourceHilbert hμ
      (jointSourceRegion s)))
    UniformSpace.Completion.denseRange_coe UniformSpace.Completion.denseRange_coe
  intro x y
  rw [weighted_jointSymmetricPolynomial_pairing hμ (jointSourceRegion s)
    (spatialAxisDisplacement (s / 2) 0) s v.momentum P (fun x => x.1.2) v.momentum_pairing,
    complexify_ofReal, inner_complexification_ofReal, jointPhysicalPolynomial_momentum_pairing]
  simp only [jointPhysicalMidpoint_eq_centeredScaled hs]

/-- Joint weighted polynomial operator. -/
def jointWeightedPolynomialOperator {μ s b : ℝ} {hμ : 0 < μ}
    (v : JointWeightedMomentFamily hμ s b) (F G : (Fin 6 → ℂ) → ℂ) (n : ℕ) :
    ComplexSourceHilbert hμ (jointSourceRegion s) →L[ℂ] ComplexSourceHilbert hμ
      (jointSourceRegion s) :=
  jointSymmetricPolynomialOperator v.field (jointMidpointOriented F n) +
    jointSymmetricPolynomialOperator v.momentum (jointMidpointOriented G n)

theorem jointWeightedPolynomialOperator_isSelfAdjoint {μ s b : ℝ} {hμ : 0 < μ}
    (v : JointWeightedMomentFamily hμ s b) (F G : (Fin 6 → ℂ) → ℂ) (n : ℕ) :
    IsSelfAdjoint (jointWeightedPolynomialOperator v F G n) :=
  (jointSymmetricPolynomialOperator_isSelfAdjoint _ _).add
    (jointSymmetricPolynomialOperator_isSelfAdjoint _ _)

theorem jointSymmetricPolynomialOperator_isCompactOperator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : (Fin 3 → ℕ) → E) (P : MvPolynomial (Fin 6) ℂ) :
    IsCompactOperator (jointSymmetricPolynomialOperator v P) :=
  isCompactOperator_of_range_le_finiteDimensional _ _ le_rfl

theorem jointWeightedPolynomialOperator_isCompactOperator {μ s b : ℝ} {hμ : 0 < μ}
    (v : JointWeightedMomentFamily hμ s b) (F G : (Fin 6 → ℂ) → ℂ) (n : ℕ) :
    IsCompactOperator (jointWeightedPolynomialOperator v F G n) :=
  (jointSymmetricPolynomialOperator_isCompactOperator _ _).add
    (jointSymmetricPolynomialOperator_isCompactOperator _ _)

/-- The sandwich is the actual polynomial approximant already defined
from the original error kernels, with no representation premise. -/
theorem jointWeightedPolynomialOperator_factor {μ s b : ℝ}
    (hμ : 0 < μ) (hs : 600 ≤ s) (v : JointWeightedMomentFamily hμ s b) (n : ℕ) :
    sourceReserve hμ (jointSourceRegion s) ^ b *
        jointWeightedPolynomialOperator v (jointNormalizedFieldKernel μ s)
          (jointNormalizedMomentumKernel μ s) n * sourceReserve hμ (jointSourceRegion s) ^ b =
      complexify (jointPolynomialKernelOperator hμ hs n) := by
  have hs₀ : s ≠ 0 := ne_of_gt (by linarith)
  rw [jointPolynomialKernelOperator_eq_moments hμ hs (jointRegionMomentFamily hμ s) n,
    complexify_add]
  unfold jointWeightedPolynomialOperator
  rw [mul_add, add_mul, jointWeighted_field_factor hμ hs₀ v (jointRegionMomentFamily hμ s),
    jointWeighted_momentum_factor hμ hs₀ v (jointRegionMomentFamily hμ s)]
  rfl

/-- Exact coefficient growth before any mass-envelope simplification. -/
theorem nuclear_jointWeightedPolynomialOperator_le
    {μ s b : ℝ} {hμ : 0 < μ} (v : JointWeightedMomentFamily hμ s b)
    {Af Ag L Mf Mg : ℝ} (hAf : 0 ≤ Af) (hAg : 0 ≤ Ag) (hL : 1 ≤ L)
    (hMf : 0 ≤ Mf) (hMg : 0 ≤ Mg)
    (hvf : ∀ α, ‖v.field α‖ ≤ Af * L ^ (∑ j, α j))
    (hvg : ∀ α, ‖v.momentum α‖ ≤ Ag * L ^ (∑ j, α j))
    (F G : (Fin 6 → ℂ) → ℂ)
    (hF : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), ‖F z‖ ≤ Mf)
    (hG : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), ‖G z‖ ≤ Mg) (n : ℕ) :
    operatorTraceNorm (jointWeightedPolynomialOperator v F G n) ≤
      ENNReal.ofReal (128 * (Af ^ 2 * Mf + Ag ^ 2 * Mg) *
        (L ^ 9 * 314572800) ^ n) := by
  have hL₀ : 0 ≤ L := le_trans zero_le_one hL
  have hf := nuclear_jointSymmetricPolynomialOperator_growth v.field (jointMidpointOriented F n)
    hAf hL (jointMidpointOriented_degree F n) hvf
  have hg := nuclear_jointSymmetricPolynomialOperator_growth v.momentum (jointMidpointOriented G n)
    hAg hL (jointMidpointOriented_degree G n) hvg
  have hcf := jointMidpointOriented_coefficientNorm hMf F hF n
  have hcg := jointMidpointOriented_coefficientNorm hMg G hG n
  apply (operatorTraceNorm_add_le
    (jointSymmetricPolynomialOperator_isCompactOperator _ _)
    (jointSymmetricPolynomialOperator_isCompactOperator _ _)
    (jointSymmetricPolynomialOperator_isSelfAdjoint _ _)
    (jointSymmetricPolynomialOperator_isSelfAdjoint _ _)).trans
  apply (add_le_add hf hg).trans
  rw [← ENNReal.ofReal_add
    (mul_nonneg (by positivity) (mvCoefficientNorm_nonneg _))
    (mul_nonneg (by positivity) (mvCoefficientNorm_nonneg _))]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ 2 * Af ^ 2 * L ^ (9 * n) * (64 * Mf * (314572800 : ℝ) ^ n) +
        2 * Ag ^ 2 * L ^ (9 * n) * (64 * Mg * (314572800 : ℝ) ^ n) := by gcongr
    _ = _ := by simp only [mul_pow, pow_mul]; ring

end VacuumBellSeparation
