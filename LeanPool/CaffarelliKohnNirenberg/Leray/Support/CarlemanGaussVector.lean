/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanGaussAbsorb
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradient
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradientSq
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Coordinate identities for the vector Gaussian estimate

These identities translate componentwise scalar estimates into the vector
norms in `prop:carleman-gauss` of the Escauriaza–Seregin–Šverák manuscript.
-/

public section

open CKN CKN.Foundation.Parabolic
open MeasureTheory Set

noncomputable section

namespace CKN

/-- The square of the Euclidean norm on Vec3 is the sum of coordinate squares. -/
theorem gauss_vec3EuclideanNorm_sq (x : Vec3) :
    vec3EuclideanNorm x ^ 2 = ∑ i : Fin 3, x i ^ 2 := by
  unfold vec3EuclideanNorm
  rw [Real.sq_sqrt]
  exact Finset.sum_nonneg fun i _ => sq_nonneg (x i)

/-- The gradient density is the sum of scalar gradient densities. -/
theorem gauss_spatialGradientSq_eq_sum_scalarGradSq
    (w : ParabolicPoint → Vec3) (z : ParabolicPoint) :
    spatialGradientSq w (spatialGradient w) z =
      ∑ i : Fin 3, scalarGradSq (fun y => w y i) z := by
  rfl

/-- The backward heat operator has the expected sum-of-squares norm. -/
theorem gauss_heatVec_norm_sq (w : ParabolicPoint → Vec3)
    (z : ParabolicPoint) :
    vec3EuclideanNorm (fun i => timePartial (fun y => w y i) z +
      ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2 =
      ∑ i : Fin 3,
        (timePartial (fun y => w y i) z +
          scalarLaplacian (fun y => w y i) z) ^ 2 := by
  rw [gauss_vec3EuclideanNorm_sq]
  rfl

/-- Scalar exponential conjugation scales the squared vector norm. -/
theorem gauss_conjugated_norm_sq (φ : ParabolicPoint → ℝ)
    (w : ParabolicPoint → Vec3) (z : ParabolicPoint) :
    vec3EuclideanNorm (fun i => Real.exp (φ z) * w z i) ^ 2 =
      Real.exp (φ z) ^ 2 * vec3EuclideanNorm (w z) ^ 2 := by
  rw [gauss_vec3EuclideanNorm_sq, gauss_vec3EuclideanNorm_sq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The exponential of twice the phase is the Gaussian weight with parameter `q`. -/
theorem gauss_exp_two_phase_eq_weight (q : ℝ)
    (z : ParabolicPoint) (ht : 0 < z.2) :
    Real.exp (2 * gaussCarlemanPhase q z) =
      gaussCarlemanTimeWeight z.2 ^ (-2 * q) *
        Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2)) := by
  have hweight : 0 < gaussCarlemanTimeWeight z.2 := by
    unfold gaussCarlemanTimeWeight
    exact mul_pos ht (Real.exp_pos _)
  rw [Real.rpow_def_of_pos hweight, ← Real.exp_add]
  congr 1
  rw [gauss_vec3EuclideanNorm_sq]
  unfold gaussCarlemanPhase
  simp only [smul_eq_mul]
  field_simp [ne_of_gt ht]
  ring

/-- Shifting the Gaussian time exponent by one produces exactly `h²`. -/
theorem gauss_timeWeight_shift (a t : ℝ) (ht : 0 < t) :
    gaussCarlemanTimeWeight t ^ (-2 * a) =
      gaussCarlemanTimeWeight t ^ 2 *
        gaussCarlemanTimeWeight t ^ (-2 * (a + 1)) := by
  have hweight : 0 < gaussCarlemanTimeWeight t := by
    unfold gaussCarlemanTimeWeight
    exact mul_pos ht (Real.exp_pos _)
  calc
    gaussCarlemanTimeWeight t ^ (-2 * a) =
        gaussCarlemanTimeWeight t ^ (-2 * (a + 1) + 2) := by congr 1; ring
    _ = gaussCarlemanTimeWeight t ^ (-2 * (a + 1)) *
        gaussCarlemanTimeWeight t ^ (2 : ℝ) := Real.rpow_add hweight _ _
    _ = gaussCarlemanTimeWeight t ^ 2 *
        gaussCarlemanTimeWeight t ^ (-2 * (a + 1)) := by
      rw [Real.rpow_two]
      ring

/-- The original Gaussian weight differs from the conjugation weight by `h²`. -/
theorem gauss_weight_eq_timeWeight_sq_mul_exp_phase (a : ℝ)
    (z : ParabolicPoint) (ht : 0 < z.2) :
    gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
        Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2)) =
      gaussCarlemanTimeWeight z.2 ^ 2 *
        Real.exp (2 * gaussCarlemanPhase (a + 1) z) := by
  rw [gauss_timeWeight_shift a z.2 ht,
    gauss_exp_two_phase_eq_weight (a + 1) z ht]
  ring

/-- The original weight is controlled by the phase weight with the first
factor `e^(2/3)` from the time comparison. -/
theorem gauss_weight_le_phase (a : ℝ) (z : ParabolicPoint)
    (ht0 : 0 < z.2) (ht2 : z.2 < 2) :
    gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
        Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2)) ≤
      Real.exp (2 / 3 : ℝ) *
        (z.2 ^ 2 * Real.exp (2 * gaussCarlemanPhase (a + 1) z)) := by
  have hratio := (gaussTimeWeight_div_sq_bounds ht0 ht2).2
  have hsq : gaussCarlemanTimeWeight z.2 ^ 2 =
      (gaussCarlemanTimeWeight z.2 / z.2) ^ 2 * z.2 ^ 2 := by
    field_simp [ne_of_gt ht0]
  have hweight : gaussCarlemanTimeWeight z.2 ^ 2 ≤
      Real.exp (2 / 3 : ℝ) * z.2 ^ 2 := by
    rw [hsq]
    exact mul_le_mul_of_nonneg_right hratio (sq_nonneg z.2)
  rw [gauss_weight_eq_timeWeight_sq_mul_exp_phase a z ht0]
  have hnonneg : 0 ≤ Real.exp (2 * gaussCarlemanPhase (a + 1) z) :=
    le_of_lt (Real.exp_pos _)
  nlinarith only [mul_le_mul_of_nonneg_right hweight hnonneg]

/-- The phase-weighted operator energy is controlled by the original weight
with the second factor `e^(2/3)`. -/
theorem gauss_phase_le_weight (a : ℝ) (z : ParabolicPoint)
    (ht0 : 0 < z.2) (ht2 : z.2 < 2) :
    z.2 ^ 2 * Real.exp (2 * gaussCarlemanPhase (a + 1) z) ≤
      Real.exp (2 / 3 : ℝ) *
        (gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
          Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) := by
  have hratio := (gaussTimeRatio_sq_bounds ht0 ht2).2
  have hweight : 0 < gaussCarlemanTimeWeight z.2 := by
    unfold gaussCarlemanTimeWeight
    exact mul_pos ht0 (Real.exp_pos _)
  have hsq : z.2 ^ 2 =
      (z.2 / gaussCarlemanTimeWeight z.2) ^ 2 *
        gaussCarlemanTimeWeight z.2 ^ 2 := by
    field_simp [ne_of_gt hweight]
  have htime : z.2 ^ 2 ≤
      Real.exp (2 / 3 : ℝ) * gaussCarlemanTimeWeight z.2 ^ 2 := by
    rw [hsq]
    exact mul_le_mul_of_nonneg_right hratio (sq_nonneg _)
  rw [gauss_weight_eq_timeWeight_sq_mul_exp_phase a z ht0]
  have hnonneg : 0 ≤ Real.exp (2 * gaussCarlemanPhase (a + 1) z) :=
    le_of_lt (Real.exp_pos _)
  nlinarith only [mul_le_mul_of_nonneg_right htime hnonneg]

/-- A density supported inside the open cylinder has the same integral on
the cylinder and on the full space-time domain. -/
theorem gauss_setIntegral_eq_integral_of_zero_outside
    (f : ParabolicPoint → ℝ)
    (h : ∀ z ∉ spaceTimeSet univ (Ioo (0 : ℝ) 2), f z = 0) :
    ∫ z in spaceTimeSet univ (Ioo (0 : ℝ) 2), f z = ∫ z, f z := by
  nth_rw 2 [← setIntegral_univ]
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ
    (subset_univ (spaceTimeSet univ (Ioo (0 : ℝ) 2)))
  intro z hz
  exact h z (notMem_of_mem_sdiff hz)

/-- A component and its first and second derivatives vanish off the support
of a smooth vector field. -/
theorem gauss_component_zero_outside
    (w : ParabolicPoint → Vec3)
    (z : ParabolicPoint)
    (hz : z ∉ tsupport (show Vec3 × ℝ → Vec3 from w)) (i : Fin 3) :
    w z i = 0 ∧
      timePartial (fun y => w y i) z = 0 ∧
      (∀ j : Fin 3, spatialPartial (fun y => w y i) j z = 0 ∧
        spatialSecondPartial (fun y => w y i) j j z = 0) := by
  have hsupp : tsupport (show Vec3 × ℝ → ℝ from fun y => w y i) ⊆
      tsupport (show Vec3 × ℝ → Vec3 from w) :=
    tsupport_comp_subset (g := fun x : Vec3 => x i) rfl
      (show Vec3 × ℝ → Vec3 from w)
  have hnot : z ∉ tsupport (show Vec3 × ℝ → ℝ from fun y => w y i) :=
    fun h => hz (hsupp h)
  refine ⟨image_eq_zero_of_notMem_tsupport (f := fun y : Vec3 × ℝ => w y i) hnot,
    CKN.timePartial_eq_zero_off_tsupport hnot, ?_⟩
  intro j
  exact ⟨CKN.spatialPartial_eq_zero_off_tsupport hnot j,
    CKN.spatialSecondPartial_eq_zero_off_tsupport hnot j j⟩

end CKN
