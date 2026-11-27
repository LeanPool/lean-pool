/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointSmoothKernelCauchySchwarz
public import LeanPool.VacuumBellSeparation.FreeField.SpatialFourier

/-!
# Actual compact product tests and their six-dimensional Fourier transform

The product test is a genuine Schwartz map on the L2 Hilbert product.
Euclidean product volume and the Fourier phase both split without a
Jacobian. The scalar pairing is the original real-test kernel pairing.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open MeasureTheory FourierTransform Set
open scoped SchwartzMap FourierTransform ComplexConjugate

theorem hasCompactSupport_jointSpatialTestProduct (f g : SpatialTestFunction) :
    HasCompactSupport (fun x : JointKernelSpace => (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ)) := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ
    (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3))
  apply HasCompactSupport.of_support_subset_isCompact
    ((f.2.2.isCompact.prod g.2.2.isCompact).image e.symm.continuous)
  intro x hx
  have hfg : (f.1 x.fst : ℂ) ≠ 0 ∧ (g.1 x.snd : ℂ) ≠ 0 := mul_ne_zero_iff.mp hx
  refine ⟨(x.fst, x.snd), ⟨subset_tsupport f.1 ?_, subset_tsupport g.1 ?_⟩, rfl⟩
  · exact_mod_cast hfg.1
  · exact_mod_cast hfg.2

/-- Joint spatial test product. -/
def jointSpatialTestProduct (f g : SpatialTestFunction) : SchwartzMap JointKernelSpace ℂ :=
  (hasCompactSupport_jointSpatialTestProduct f g).toSchwartzMap
    (((Complex.ofRealCLM.contDiff.comp f.2.1).comp
      (WithLp.fstL 2 ℝ (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3))).contDiff).mul
      ((Complex.ofRealCLM.contDiff.comp g.2.1).comp
        (WithLp.sndL 2 ℝ (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3))).contDiff))

@[simp] theorem jointSpatialTestProduct_apply (f g : SpatialTestFunction)
    (x : JointKernelSpace) :
    jointSpatialTestProduct f g x = (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) := rfl

theorem integral_jointKernel_ofLp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (F : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) → G) :
    (∫ x : JointKernelSpace, F (WithLp.ofLp x)) = ∫ x, F x :=
  (WithLp.volume_preserving_ofLp (EuclideanSpace ℝ (Fin 3))
    (EuclideanSpace ℝ (Fin 3))).integral_comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin 3))
        (EuclideanSpace ℝ (Fin 3))).toHomeomorph.measurableEmbedding F

/-- Literal product Fourier formula on the true six-dimensional carrier. -/
theorem fourier_jointSpatialTestProduct (f g : SpatialTestFunction) (ξ : JointKernelSpace) :
    (𝓕 (jointSpatialTestProduct f g)) ξ =
      (𝓕 (spatialSchwartz f)) ξ.fst * (𝓕 (spatialSchwartz g)) ξ.snd := by
  simp only [SchwartzMap.fourier_coe, Real.fourier_eq', smul_eq_mul]
  let a := fun x : EuclideanSpace ℝ (Fin 3) =>
    Complex.exp (((-2 * Real.pi * inner ℝ x ξ.fst : ℝ) : ℂ) * Complex.I) * (f.1 x : ℂ)
  let b := fun y : EuclideanSpace ℝ (Fin 3) =>
    Complex.exp (((-2 * Real.pi * inner ℝ y ξ.snd : ℝ) : ℂ) * Complex.I) * (g.1 y : ℂ)
  have hphase (x : JointKernelSpace) :
      Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) *
        jointSpatialTestProduct f g x = a x.fst * b x.snd := by
    rw [WithLp.prod_inner_apply, jointSpatialTestProduct_apply]
    have he : (((-2 * Real.pi *
        (inner ℝ x.fst ξ.fst + inner ℝ x.snd ξ.snd) : ℝ) : ℂ) * Complex.I) =
        (((-2 * Real.pi * inner ℝ x.fst ξ.fst : ℝ) : ℂ) * Complex.I) +
          (((-2 * Real.pi * inner ℝ x.snd ξ.snd : ℝ) : ℂ) * Complex.I) := by
      push_cast
      ring
    change Complex.exp (((-2 * Real.pi *
      (inner ℝ x.fst ξ.fst + inner ℝ x.snd ξ.snd) : ℝ) : ℂ) * Complex.I) *
        ((f.1 x.fst : ℂ) * (g.1 x.snd : ℂ)) = a x.fst * b x.snd
    rw [he, Complex.exp_add]
    dsimp only [a, b]
    ring
  simp_rw [hphase]
  change (∫ x : JointKernelSpace, (fun y => a y.1 * b y.2) (WithLp.ofLp x)) = _
  rw [integral_jointKernel_ofLp (fun x => a x.1 * b x.2)]
  change (∫ x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
    a x.1 * b x.2 ∂(volume.prod volume)) = (∫ x, a x) * ∫ y, b y
  exact integral_prod_mul a b

/-- Joint test frequency weight given by `(1 + (2 * Real.pi) ^ 2 * ‖p‖ ^ 2)⁻¹`. -/
def jointTestFrequencyWeight (p : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (1 + (2 * Real.pi) ^ 2 * ‖p‖ ^ 2)⁻¹

theorem jointTestFrequencyWeight_nonneg (p : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ jointTestFrequencyWeight p := by unfold jointTestFrequencyWeight; positivity

theorem jointTestFrequencyWeight_le_one (p : EuclideanSpace ℝ (Fin 3)) :
    jointTestFrequencyWeight p ≤ 1 := by
  apply (inv_le_one₀ (by positivity : 0 < 1 + (2 * Real.pi) ^ 2 * ‖p‖ ^ 2)).mpr
  exact le_add_of_nonneg_right (by positivity)

theorem integrable_jointTestFrequencyWeight (f : SpatialTestFunction) :
    Integrable (fun p => jointTestFrequencyWeight p * ‖(𝓕 (spatialSchwartz f)) p‖ ^ 2) := by
  have hc : Continuous (fun p : EuclideanSpace ℝ (Fin 3) =>
      jointTestFrequencyWeight p * ‖(𝓕 (spatialSchwartz f)) p‖ ^ 2) := by
    have hden : Continuous (fun p : EuclideanSpace ℝ (Fin 3) =>
        1 + (2 * Real.pi) ^ 2 * ‖p‖ ^ 2) := by fun_prop
    exact (hden.inv₀ (fun p =>
      (show 0 < 1 + (2 * Real.pi) ^ 2 * ‖p‖ ^ 2 by positivity).ne')).mul
        ((𝓕 (spatialSchwartz f)).continuous.norm.pow 2)
  apply (((𝓕 (spatialSchwartz f)).memLp 2).norm.integrable_sq).mono'
    hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => by
    rw [Real.norm_of_nonneg (mul_nonneg (jointTestFrequencyWeight_nonneg p) (sq_nonneg _))]
    exact mul_le_of_le_one_left (sq_nonneg _) (jointTestFrequencyWeight_le_one p)

/-- Exact factorization of the inverse-weighted test energy. -/
theorem integral_inverseWeight_jointSpatialTestProduct (f g : SpatialTestFunction) :
    (∫ ξ, (jointKernelPolynomialWeight ξ)⁻¹ * ‖(𝓕 (jointSpatialTestProduct f g)) ξ‖ ^ 2) =
      (∫ p, jointTestFrequencyWeight p * ‖(𝓕 (spatialSchwartz f)) p‖ ^ 2) *
        (∫ q, jointTestFrequencyWeight q * ‖(𝓕 (spatialSchwartz g)) q‖ ^ 2) := by
  have he (ξ : JointKernelSpace) :
      (jointKernelPolynomialWeight ξ)⁻¹ * ‖(𝓕 (jointSpatialTestProduct f g)) ξ‖ ^ 2 =
        (jointTestFrequencyWeight ξ.fst * ‖(𝓕 (spatialSchwartz f)) ξ.fst‖ ^ 2) *
          (jointTestFrequencyWeight ξ.snd * ‖(𝓕 (spatialSchwartz g)) ξ.snd‖ ^ 2) := by
    rw [fourier_jointSpatialTestProduct]
    simp only [jointKernelPolynomialWeight, jointTestFrequencyWeight, mul_inv_rev, norm_mul,
      mul_pow]
    ring
  simp_rw [he]
  change (∫ ξ : JointKernelSpace,
    (fun x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      (jointTestFrequencyWeight x.1 * ‖(𝓕 (spatialSchwartz f)) x.1‖ ^ 2) *
        (jointTestFrequencyWeight x.2 * ‖(𝓕 (spatialSchwartz g)) x.2‖ ^ 2))
      (WithLp.ofLp ξ)) = _
  let a : EuclideanSpace ℝ (Fin 3) → ℝ := fun p =>
    jointTestFrequencyWeight p * ‖(𝓕 (spatialSchwartz f)) p‖ ^ 2
  let b : EuclideanSpace ℝ (Fin 3) → ℝ := fun p =>
    jointTestFrequencyWeight p * ‖(𝓕 (spatialSchwartz g)) p‖ ^ 2
  calc
    _ = ∫ x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3), a x.1 * b x.2 :=
      integral_jointKernel_ofLp (G := ℝ) (fun x => a x.1 * b x.2)
    _ = _ := integral_prod_mul a b

/-- The real compact-test kernel form, with no abstract pairing hypothesis. -/
theorem jointKernel_real_test_pairing_le (K : SchwartzMap JointKernelSpace ℂ)
    (f g : SpatialTestFunction) :
    ‖∫ x : JointKernelSpace, (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) * K x‖ ≤
      Real.sqrt (jointKernelDerivativeEnergy K) *
        Real.sqrt ((∫ p, jointTestFrequencyWeight p * ‖(𝓕 (spatialSchwartz f)) p‖ ^ 2) *
          (∫ q, jointTestFrequencyWeight q * ‖(𝓕 (spatialSchwartz g)) q‖ ^ 2)) := by
  simpa only [jointSpatialTestProduct_apply, map_mul, Complex.conj_ofReal,
    integral_inverseWeight_jointSpatialTestProduct] using
      jointKernel_pairing_le K (jointSpatialTestProduct f g)

end VacuumBellSeparation
