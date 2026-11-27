/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointSmoothKernelSourceWeights
public import LeanPool.VacuumBellSeparation.Gaussian.RealBilinearCompletion

/-!
# Genuine smooth-kernel operators in the joint source norm

The original compact-test double integral first defines a bilinear form.
The proved Fourier estimates bound it in the total-source covariance norm;
completion and Riesz representation then construct the actual bounded
operator. No regional synthesis inverse or form-representation premise is used.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open MeasureTheory FourierTransform
open scoped SchwartzMap FourierTransform InnerProductSpace

theorem integrable_jointKernelTest (K : SchwartzMap JointKernelSpace ℂ)
    (f g : SpatialTestFunction) :
    Integrable (fun x : JointKernelSpace => (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) * K x) := by
  have hc : Continuous (fun x : JointKernelSpace =>
      (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) * K x) :=
    (jointSpatialTestProduct f g).continuous.mul K.continuous
  exact hc.integrable_of_hasCompactSupport
    ((hasCompactSupport_jointSpatialTestProduct f g).mul_right)

/-- Joint kernel test pair given by `(∫ x : JointKernelSpace, (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) * K
x).re`. -/
def jointKernelTestPair (K : SchwartzMap JointKernelSpace ℂ)
    (f g : SpatialTestFunction) : ℝ :=
  (∫ x : JointKernelSpace, (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) * K x).re

theorem jointKernelTestPair_add_left (K : SchwartzMap JointKernelSpace ℂ)
    (f₁ f₂ g : SpatialTestFunction) :
    jointKernelTestPair K (f₁ + f₂) g = jointKernelTestPair K f₁ g + jointKernelTestPair K f₂ g
      := by
  unfold jointKernelTestPair
  change (∫ x : JointKernelSpace, ((f₁.1 x.fst + f₂.1 x.fst : ℝ) : ℂ) *
    (g.1 x.snd : ℂ) * K x).re = _
  simp only [Complex.ofReal_add, add_mul]
  rw [integral_add (integrable_jointKernelTest K f₁ g) (integrable_jointKernelTest K f₂ g),
    Complex.add_re]

theorem jointKernelTestPair_add_right (K : SchwartzMap JointKernelSpace ℂ)
    (f g₁ g₂ : SpatialTestFunction) :
    jointKernelTestPair K f (g₁ + g₂) = jointKernelTestPair K f g₁ + jointKernelTestPair K f g₂
      := by
  unfold jointKernelTestPair
  change (∫ x : JointKernelSpace, (f.1 x.fst : ℂ) *
    ((g₁.1 x.snd + g₂.1 x.snd : ℝ) : ℂ) * K x).re = _
  simp only [Complex.ofReal_add, mul_add, add_mul]
  rw [integral_add (integrable_jointKernelTest K f g₁) (integrable_jointKernelTest K f g₂),
    Complex.add_re]

theorem jointKernelTestPair_smul_left (K : SchwartzMap JointKernelSpace ℂ)
    (c : ℝ) (f g : SpatialTestFunction) :
    jointKernelTestPair K (c • f) g = c • jointKernelTestPair K f g := by
  unfold jointKernelTestPair
  change (∫ x : JointKernelSpace, ((c * f.1 x.fst : ℝ) : ℂ) *
    (g.1 x.snd : ℂ) * K x).re = _
  simp only [Complex.ofReal_mul, mul_assoc]
  rw [integral_const_mul, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, smul_eq_mul]

theorem jointKernelTestPair_smul_right (K : SchwartzMap JointKernelSpace ℂ)
    (c : ℝ) (f g : SpatialTestFunction) :
    jointKernelTestPair K f (c • g) = c • jointKernelTestPair K f g := by
  unfold jointKernelTestPair
  have he (x : JointKernelSpace) :
      (f.1 x.fst : ℂ) * ((c * g.1 x.snd : ℝ) : ℂ) * K x =
        (c : ℂ) * ((f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) * K x) := by
    push_cast
    ring
  change (∫ x : JointKernelSpace, (f.1 x.fst : ℂ) *
    ((c * g.1 x.snd : ℝ) : ℂ) * K x).re = _
  simp_rw [he]
  rw [integral_const_mul, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, smul_eq_mul]

/-- Linear map for the joint kernel test bilinear, of type `E →ₗ[ℝ] E →ₗ[ℝ] ℝ`. -/
def jointKernelTestBilinear {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : E →ₗ[ℝ] SpatialTestFunction) (K : SchwartzMap JointKernelSpace ℂ) : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => jointKernelTestPair K (P u) (P v))
    (by intro u v w; rw [map_add, jointKernelTestPair_add_left])
    (by intro c u v; rw [map_smul, jointKernelTestPair_smul_left])
    (by intro u v w; rw [map_add, jointKernelTestPair_add_right])
    (by intro c u v; rw [map_smul, jointKernelTestPair_smul_right])

/-- The source-to-test projection is literal, with its original support. -/
def sourceFieldTestProjection {μ : ℝ} (hμ : 0 < μ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) : SourceTestSpace hμ U →ₗ[ℝ] SpatialTestFunction where
  toFun u := u.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The linear projection taking the momentum test function of a source pair. -/
def sourceMomentumTestProjection {μ : ℝ} (hμ : 0 < μ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) : SourceTestSpace hμ U →ₗ[ℝ] SpatialTestFunction where
  toFun u := u.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem sqrt_product_energy_le {a b c x y : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hax : a ≤ c * x ^ 2) (hby : b ≤ c * y ^ 2) :
    Real.sqrt (a * b) ≤ c * x * y := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    a * b ≤ (c * x ^ 2) * (c * y ^ 2) := mul_le_mul hax hby hb (by positivity)
    _ = (c * x * y) ^ 2 := by ring

/-- Generic form estimate after the actual inverse-weighted source bound. -/
theorem jointKernelTestPair_le_source_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E →ₗ[ℝ] SpatialTestFunction) (K : SchwartzMap JointKernelSpace ℂ)
    {c : ℝ} (hc : 0 ≤ c)
    (hP : ∀ u, (∫ p, jointTestFrequencyWeight p * ‖(𝓕 (spatialSchwartz (P u))) p‖ ^ 2) ≤
      c * ‖u‖ ^ 2) (u v : E) :
    ‖jointKernelTestBilinear P K u v‖ ≤
      (c * Real.sqrt (jointKernelDerivativeEnergy K)) * ‖u‖ * ‖v‖ := by
  have h := jointKernel_real_test_pairing_le K (P u) (P v)
  have hs := sqrt_product_energy_le
    (integral_nonneg fun p => mul_nonneg (jointTestFrequencyWeight_nonneg p) (sq_nonneg _))
    hc (norm_nonneg u) (norm_nonneg v) (hP u) (hP v)
  calc
    _ ≤ ‖∫ x : JointKernelSpace, ((P u).1 x.fst : ℂ) * ((P v).1 x.snd : ℂ) * K x‖ :=
      Complex.abs_re_le_norm _
    _ ≤ _ := h.trans (by
      have hh := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg (jointKernelDerivativeEnergy K))
      convert hh using 1; ring)

/-- Actual bounded form on test sources, with no regional decomposition. -/
def boundedJointKernelTestForm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E →ₗ[ℝ] SpatialTestFunction) (K : SchwartzMap JointKernelSpace ℂ)
    {c : ℝ} (hc : 0 ≤ c)
    (hP : ∀ u, (∫ p, jointTestFrequencyWeight p * ‖(𝓕 (spatialSchwartz (P u))) p‖ ^ 2) ≤
      c * ‖u‖ ^ 2) : E →L[ℝ] E →L[ℝ] ℝ :=
  (jointKernelTestBilinear P K).mkContinuous₂ (c * Real.sqrt (jointKernelDerivativeEnergy K))
    (jointKernelTestPair_le_source_bound P K hc hP)

theorem norm_boundedJointKernelTestForm_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E →ₗ[ℝ] SpatialTestFunction) (K : SchwartzMap JointKernelSpace ℂ)
    {c : ℝ} (hc : 0 ≤ c)
    (hP : ∀ u, (∫ p, jointTestFrequencyWeight p * ‖(𝓕 (spatialSchwartz (P u))) p‖ ^ 2) ≤
      c * ‖u‖ ^ 2) :
    ‖boundedJointKernelTestForm P K hc hP‖ ≤ c * Real.sqrt (jointKernelDerivativeEnergy K) :=
  (jointKernelTestBilinear P K).mkContinuous₂_norm_le (by positivity) _

end VacuumBellSeparation
