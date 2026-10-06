/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffineFlatnessPrep
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.MultiscaleEllipticity
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubePoisson.Solver
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.MeanZero
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# High-contrast homogenization: Provider.Regularity.AffineBestFit

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Affine best fits on centered Euclidean cubes

This module constructs the unique `L²` best affine approximation on a centered
triadic cube.  Its coefficient and slope maps are algebraic linear maps.  In
particular, no quantitative statement below uses the ambient function-space
norm on `Vec d`; later slope estimates must be stated with `euclideanNorm`.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Intercept and Euclidean slope of a scalar affine function. -/
abbrev AffineCoefficients (d : ℕ) := ℝ × Vec d

/-- The H¹ affine function `x ↦ p.1 + p.2 · x` on the origin cube at scale `k`. -/
@[expose]
public noncomputable def originCubeAffineH1OfCoefficients
    (d : ℕ) (k : ℤ) (p : AffineCoefficients d) :
    H1Function
      (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d)) :=
  H1Function.const p.1 +
    H1Function.affineOnIsSobolevRegularDomain
      (Book.Ch02.cubeDomain (originCube d k)).isDomain.isSobolevRegularDomain
      p.2

@[simp] private theorem originCubeAffineH1OfCoefficients_toFun
    (d : ℕ) [NeZero d] (k : ℤ) (p : AffineCoefficients d) :
    (originCubeAffineH1OfCoefficients d k p).toFun =
      fun x => p.1 + vecDot p.2 x := by
  funext x
  simp only [originCubeAffineH1OfCoefficients, H1Function.add_toFun,
    H1Function.const_apply, H1Function.affineOnIsSobolevRegularDomain_apply, vecDot]

@[simp] private theorem originCubeAffineH1OfCoefficients_grad
    (d : ℕ) [NeZero d] (k : ℤ) (p : AffineCoefficients d) :
    (originCubeAffineH1OfCoefficients d k p).grad = fun _ => p.2 := by
  funext x
  simp only [originCubeAffineH1OfCoefficients, H1Function.add_grad,
    H1Function.grad_const, H1Function.affineOnIsSobolevRegularDomain_grad, zero_add]

theorem originCubeAffineH1OfCoefficients_add
    (d : ℕ) [NeZero d] (k : ℤ)
    (p q : AffineCoefficients d) :
    originCubeAffineH1OfCoefficients d k (p + q) =
      originCubeAffineH1OfCoefficients d k p +
        originCubeAffineH1OfCoefficients d k q := by
  apply H1Function.ext
  · funext x
    simp only [originCubeAffineH1OfCoefficients_toFun, H1Function.add_toFun,
      vecDot_add_left, Prod.fst_add, Prod.snd_add]
    ring
  · funext x
    simp only [originCubeAffineH1OfCoefficients_grad, H1Function.add_grad, Prod.snd_add]

theorem originCubeAffineH1OfCoefficients_smul
    (d : ℕ) [NeZero d] (k : ℤ) (r : ℝ)
    (p : AffineCoefficients d) :
    originCubeAffineH1OfCoefficients d k (r • p) =
      r • originCubeAffineH1OfCoefficients d k p := by
  apply H1Function.ext
  · funext x
    simp only [originCubeAffineH1OfCoefficients_toFun, H1Function.smul_toFun,
      vecDot_smul_left, smul_eq_mul, Prod.smul_fst, Prod.smul_snd]
    ring
  · funext x
    simp only [originCubeAffineH1OfCoefficients_grad, H1Function.smul_grad, Prod.smul_snd]

/-- The affine-coefficient embedding into `H¹` on a centered cube. -/
@[expose]
noncomputable def originCubeAffineH1LinearMap
    (d : ℕ) [NeZero d] (k : ℤ) :
    AffineCoefficients d →ₗ[ℝ]
      H1Function
        (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d)) where
  toFun := originCubeAffineH1OfCoefficients d k
  map_add' := originCubeAffineH1OfCoefficients_add d k
  map_smul' := originCubeAffineH1OfCoefficients_smul d k

/-- The affine embedding has the literal representative `c + e · x`. -/
theorem originCubeAffineH1LinearMap_toFun
    (d : ℕ) [NeZero d] (k : ℤ) (p : AffineCoefficients d) :
    (originCubeAffineH1LinearMap d k p).toFun =
      fun x => p.1 + vecDot p.2 x :=
  originCubeAffineH1OfCoefficients_toFun d k p

/-- The weak gradient of the affine embedding is its slope. -/
theorem originCubeAffineH1LinearMap_grad
    (d : ℕ) [NeZero d] (k : ℤ) (p : AffineCoefficients d) :
    (originCubeAffineH1LinearMap d k p).grad = fun _ => p.2 :=
  originCubeAffineH1OfCoefficients_grad d k p

/-- The affine-coefficient embedding into scalar `L²` on a centered cube. -/
@[expose]
noncomputable def originCubeAffineL2LinearMap
    (d : ℕ) [NeZero d] (k : ℤ) :
    AffineCoefficients d →ₗ[ℝ]
      ScalarL2
        (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d)) where
  toFun p := (originCubeAffineH1LinearMap d k p).toScalarL2
  map_add' p q := by
    rw [map_add, H1Function.toScalarL2_add]
  map_smul' r p := by
    rw [map_smul, H1Function.toScalarL2_smul, RingHom.id_apply]

/-- The `L²` affine embedding is the realization of the corresponding `H¹`
function. -/
theorem originCubeAffineL2LinearMap_apply
    (d : ℕ) [NeZero d] (k : ℤ) (p : AffineCoefficients d) :
    originCubeAffineL2LinearMap d k p =
      (originCubeAffineH1LinearMap d k p).toScalarL2 :=
  rfl

/-- The `L²` affine embedding has its expected almost-everywhere
representative. -/
theorem originCubeAffineL2LinearMap_ae_eq
    (d : ℕ) [NeZero d] (k : ℤ) (p : AffineCoefficients d) :
    originCubeAffineL2LinearMap d k p
      =ᵐ[volumeMeasureOn
        (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d))]
      fun x => p.1 + vecDot p.2 x := by
  simpa only [originCubeAffineL2LinearMap_apply,
    originCubeAffineH1LinearMap_toFun] using
    H1Function.coeFn_toScalarL2 (originCubeAffineH1LinearMap d k p)

private theorem continuous_affineCoefficients_toFun
    {d : ℕ} (p : AffineCoefficients d) :
    Continuous (fun x : Vec d => p.1 + vecDot p.2 x) := by
  unfold vecDot
  exact continuous_const.add
    (continuous_finsetSum _ fun i _ =>
      continuous_const.mul (continuous_apply i))

private theorem zero_mem_originCubeDomain
    (d : ℕ) (k : ℤ) :
    (0 : Vec d) ∈
      (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d)) := by
  rw [Book.Ch02.cubeDomain_coe, mem_openCubeSet_originCube_iff]
  intro i
  have hpow : 0 < (3 : ℝ) ^ k :=
    zpow_pos (by norm_num) k
  exact
    ⟨mul_neg_of_neg_of_pos (by norm_num) hpow,
      mul_pos (by norm_num) hpow⟩

private theorem quarterScale_smul_basisVec_mem_originCubeDomain
    {d : ℕ} (k : ℤ) (i : Fin d) :
    ((1 / 4 : ℝ) * (3 : ℝ) ^ k) • basisVec i ∈
      (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d)) := by
  rw [Book.Ch02.cubeDomain_coe, mem_openCubeSet_originCube_iff]
  intro j
  have hpow : 0 < (3 : ℝ) ^ k :=
    zpow_pos (by norm_num) k
  have hleft : (-(1 / 2 : ℝ)) * (3 : ℝ) ^ k < 0 :=
    mul_neg_of_neg_of_pos (by norm_num) hpow
  have hright : 0 < (1 / 2 : ℝ) * (3 : ℝ) ^ k :=
    mul_pos (by norm_num) hpow
  have hrpos : 0 < (1 / 4 : ℝ) * (3 : ℝ) ^ k :=
    mul_pos (by norm_num) hpow
  have hrlt :
      (1 / 4 : ℝ) * (3 : ℝ) ^ k <
        (1 / 2 : ℝ) * (3 : ℝ) ^ k :=
    mul_lt_mul_of_pos_right (by norm_num) hpow
  by_cases hji : j = i
  · subst j
    simp only [Pi.smul_apply, basisVec_apply, ite_true, smul_eq_mul,
      mul_one]
    constructor
    · nlinarith only [hpow]
    · nlinarith only [hpow]
  · simp only [Pi.smul_apply, basisVec_apply, ite_eq_right hji, smul_eq_mul,
      mul_zero]
    exact ⟨hleft, hright⟩

/-- Affine coefficients are determined by their `L²` class on a
positive-dimensional origin cube. -/
theorem originCubeAffineL2LinearMap_injective
    (d : ℕ) [NeZero d] (k : ℤ) :
    Function.Injective (originCubeAffineL2LinearMap d k) := by
  intro p q hpq
  let U : Set (Vec d) :=
    (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d))
  have hcoe :
      (originCubeAffineL2LinearMap d k p : Vec d → ℝ)
        =ᵐ[volumeMeasureOn U]
      (originCubeAffineL2LinearMap d k q : Vec d → ℝ) := by
    rw [hpq]
  have hp := originCubeAffineL2LinearMap_ae_eq d k p
  have hq := originCubeAffineL2LinearMap_ae_eq d k q
  have haff :
      (fun x : Vec d => p.1 + vecDot p.2 x)
        =ᵐ[volumeMeasureOn U]
      fun x => q.1 + vecDot q.2 x := by
    exact hp.symm.trans (hcoe.trans hq)
  have hpoint : Set.EqOn
      (fun x : Vec d => p.1 + vecDot p.2 x)
      (fun x : Vec d => q.1 + vecDot q.2 x) U := by
    apply MeasureTheory.Measure.eqOn_open_of_ae_eq
      (μ := MeasureTheory.volume)
      (U := U)
    · simpa only [volumeMeasureOn] using haff
    · exact (Book.Ch02.cubeDomain (originCube d k)).isOpen
    · exact (continuous_affineCoefficients_toFun p).continuousOn
    · exact (continuous_affineCoefficients_toFun q).continuousOn
  have hintercept : p.1 = q.1 := by
    have h := hpoint (zero_mem_originCubeDomain d k)
    simpa [vecDot] using h
  apply Prod.ext
  · exact hintercept
  · funext i
    let r : ℝ := (1 / 4 : ℝ) * (3 : ℝ) ^ k
    have hrpos : 0 < r := by
      dsimp [r]
      exact mul_pos (by norm_num) (zpow_pos (by norm_num) k)
    have haxis :=
      hpoint (quarterScale_smul_basisVec_mem_originCubeDomain k i)
    have haxis' :
        p.1 + r * p.2 i = q.1 + r * q.2 i := by
      simpa [r, vecDot_smul_right, vecDot_basisVec_right] using haxis
    have hmul : r * p.2 i = r * q.2 i := by
      rw [hintercept] at haxis'
      exact add_left_cancel haxis'
    exact mul_left_cancel₀ hrpos.ne' hmul

/-- The finite-dimensional subspace of scalar `L²` represented by affine
functions on an origin cube. -/
@[expose]
noncomputable def originCubeAffineL2Submodule
    (d : ℕ) [NeZero d] (k : ℤ) :
    Submodule ℝ
      (ScalarL2
        (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d))) :=
  LinearMap.range (originCubeAffineL2LinearMap d k)

noncomputable local instance originCubeAffineL2SubmoduleHasOrthogonalProjection
    (d : ℕ) [NeZero d] (k : ℤ) :
    (originCubeAffineL2Submodule d k).HasOrthogonalProjection := by
  let : FiniteDimensional ℝ (originCubeAffineL2Submodule d k) :=
    (originCubeAffineL2LinearMap d k).finiteDimensional_range
  let : CompleteSpace (originCubeAffineL2Submodule d k) :=
    FiniteDimensional.complete ℝ _
  infer_instance

/-- Affine coefficients are linearly equivalent to the literal range of the
affine `L²` embedding. -/
@[expose]
noncomputable def originCubeAffineL2EquivRange
    (d : ℕ) [NeZero d] (k : ℤ) :
    AffineCoefficients d ≃ₗ[ℝ] originCubeAffineL2Submodule d k :=
  LinearEquiv.ofInjective (originCubeAffineL2LinearMap d k)
    (originCubeAffineL2LinearMap_injective d k)

/-- Coefficients of the orthogonal `L²` projection onto affine functions. -/
@[expose]
noncomputable def originCubeAffineBestFitCoefficients
    (d : ℕ) [NeZero d] (k : ℤ) :
    ScalarL2
        (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d)) →ₗ[ℝ]
      AffineCoefficients d :=
  (originCubeAffineL2EquivRange d k).symm.toLinearMap.comp
    (originCubeAffineL2Submodule d k).orthogonalProjectionOnto.toLinearMap

/-- Intercept of the unique affine `L²` best fit. -/
@[expose]
noncomputable def originCubeAffineBestFitIntercept
    (d : ℕ) [NeZero d] (k : ℤ) :
    ScalarL2
        (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d)) →ₗ[ℝ]
      ℝ :=
  (LinearMap.fst ℝ ℝ (Vec d)).comp
    (originCubeAffineBestFitCoefficients d k)

/-- Slope of the unique affine `L²` best fit. -/
@[expose]
noncomputable def originCubeAffineBestFitSlope
    (d : ℕ) [NeZero d] (k : ℤ) :
    ScalarL2
        (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d)) →ₗ[ℝ]
      Vec d :=
  (LinearMap.snd ℝ ℝ (Vec d)).comp
    (originCubeAffineBestFitCoefficients d k)

/-- The best coefficient pair consists of the exported intercept and slope. -/
theorem originCubeAffineBestFitCoefficients_eq
    (d : ℕ) [NeZero d] (k : ℤ)
    (F : ScalarL2
      (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d))) :
    originCubeAffineBestFitCoefficients d k F =
      (originCubeAffineBestFitIntercept d k F,
        originCubeAffineBestFitSlope d k F) := by
  apply Prod.ext <;> rfl

/-- Re-embedding the best coefficients gives the orthogonal projection onto
the affine range. -/
theorem originCubeAffineL2LinearMap_bestFitCoefficients
    (d : ℕ) [NeZero d] (k : ℤ)
    (F : ScalarL2
      (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d))) :
    originCubeAffineL2LinearMap d k
        (originCubeAffineBestFitCoefficients d k F) =
      (originCubeAffineL2Submodule d k).starProjection F := by
  change originCubeAffineL2LinearMap d k
      ((originCubeAffineL2EquivRange d k).symm
        ((originCubeAffineL2Submodule d k).orthogonalProjectionOnto F)) = _
  calc
    _ = ↑((originCubeAffineL2EquivRange d k)
        ((originCubeAffineL2EquivRange d k).symm
          ((originCubeAffineL2Submodule d k).orthogonalProjectionOnto F))) := rfl
    _ = ↑((originCubeAffineL2Submodule d k).orthogonalProjectionOnto F) := by
      exact congrArg Subtype.val
        ((originCubeAffineL2EquivRange d k).apply_symm_apply _)
    _ = (originCubeAffineL2Submodule d k).starProjection F := rfl

/-- The best-fit residual is orthogonal to every affine function. -/
theorem inner_sub_originCubeAffineBestFit_eq_zero
    (d : ℕ) [NeZero d] (k : ℤ)
    (F : ScalarL2
      (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d)))
    (p : AffineCoefficients d) :
    inner ℝ
      (F - originCubeAffineL2LinearMap d k
        (originCubeAffineBestFitCoefficients d k F))
      (originCubeAffineL2LinearMap d k p) = 0 := by
  rw [originCubeAffineL2LinearMap_bestFitCoefficients]
  exact (originCubeAffineL2Submodule d k).starProjection_inner_eq_zero F
    (originCubeAffineL2LinearMap d k p)
    (LinearMap.mem_range_self (originCubeAffineL2LinearMap d k) p)

/-- Pythagorean identity comparing the best affine fit with any affine
candidate. -/
theorem norm_sub_originCubeAffineBestFit_sq
    (d : ℕ) [NeZero d] (k : ℤ)
    (F : ScalarL2
      (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d)))
    (p : AffineCoefficients d) :
    ‖F - originCubeAffineL2LinearMap d k p‖ ^ 2 =
      ‖F - originCubeAffineL2LinearMap d k
        (originCubeAffineBestFitCoefficients d k F)‖ ^ 2 +
      ‖originCubeAffineL2LinearMap d k
          (originCubeAffineBestFitCoefficients d k F) -
        originCubeAffineL2LinearMap d k p‖ ^ 2 := by
  let b := originCubeAffineBestFitCoefficients d k F
  let i := originCubeAffineL2LinearMap d k
  have horth : inner ℝ (F - i b) (i b - i p) = 0 := by
    have h := inner_sub_originCubeAffineBestFit_eq_zero d k F (b - p)
    simpa only [map_sub] using h
  calc
    ‖F - i p‖ ^ 2 = ‖(F - i b) + (i b - i p)‖ ^ 2 := by
      congr 1
      abel_nf
    _ = ‖F - i b‖ ^ 2 + ‖i b - i p‖ ^ 2 := by
      simpa only [pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_real horth

/-- The projected affine function minimizes `L²` distance. -/
theorem norm_sub_originCubeAffineBestFit_le
    (d : ℕ) [NeZero d] (k : ℤ)
    (F : ScalarL2
      (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d)))
    (p : AffineCoefficients d) :
    ‖F - originCubeAffineL2LinearMap d k
        (originCubeAffineBestFitCoefficients d k F)‖ ≤
      ‖F - originCubeAffineL2LinearMap d k p‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sub_originCubeAffineBestFit_sq d k F p]
  exact le_add_of_nonneg_right
    (sq_nonneg ‖originCubeAffineL2LinearMap d k
      (originCubeAffineBestFitCoefficients d k F) -
        originCubeAffineL2LinearMap d k p‖)

private theorem h1Function_toScalarL2_sub
    {d : ℕ} {U : Set (Vec d)} (u v : H1Function U) :
    (u - v).toScalarL2 = u.toScalarL2 - v.toScalarL2 := by
  rw [sub_eq_add_neg, H1Function.toScalarL2_add]
  have hneg : (-v).toScalarL2 = -(v.toScalarL2) := by
    simpa using H1Function.toScalarL2_smul (-1 : ℝ) v
  rw [hneg, ← sub_eq_add_neg]

/-- The normalized affine error is exactly the unnormalized scalar `L²` norm
times the probability-measure and scale factors. -/
theorem normalizedAffineCandidateError_eq_affineL2Norm
    (d : ℕ) [NeZero d] (k : ℤ)
    (u : H1Function
      (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d)))
    (c : ℝ) (e : Vec d) :
    normalizedAffineCandidateError (originCube d k) u.toFun c e =
      cubeBesovScaleWeight (1 : ℝ) (originCube d k) *
        (((cubeVolume (originCube d k))⁻¹) ^ (1 / 2 : ℝ) *
          ‖u.toScalarL2 -
            originCubeAffineL2LinearMap d k (c, e)‖) := by
  let Q : TriadicCube d := originCube d k
  let v : H1Function
      (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d)) :=
    u - originCubeAffineH1LinearMap d k (c, e)
  have hvfun :
      (fun x => u.toFun x - (c + vecDot e x)) =
        fun x => v.toFun x := by
    have hraw := H1Function.sub_toFun u (originCubeAffineH1LinearMap d k (c, e))
    rw [originCubeAffineH1LinearMap_toFun] at hraw
    exact hraw.symm
  have hvMem :
      MeasureTheory.MemLp (fun x => v.toFun x) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := by
    simpa [Q, Book.Ch02.cubeDomain_coe] using
      H1Function.memL2_normalizedCubeMeasure (Q := Q) v
  have hnorm :
      ‖HCPolySupport.toScalarL2
        (memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hvMem)‖ =
        ‖v.toScalarL2‖ := by
    congr 1
  have hcube :
      cubeLpNorm Q (2 : ℝ≥0∞) (fun x => v.toFun x) =
        ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) * ‖v.toScalarL2‖ := by
    rw [cubeLpNorm_two_eq_volume_inv_rpow_half_mul_norm_toScalarL2_openCubeSet
      Q hvMem, hnorm]
  have hvL2 :
      v.toScalarL2 =
        u.toScalarL2 - originCubeAffineL2LinearMap d k (c, e) := by
    show (u - originCubeAffineH1LinearMap d k (c, e)).toScalarL2 =
        u.toScalarL2 - originCubeAffineL2LinearMap d k (c, e)
    rw [h1Function_toScalarL2_sub, originCubeAffineL2LinearMap_apply]
  unfold normalizedAffineCandidateError normalizedCubeL2Distance
  change cubeBesovScaleWeight (1 : ℝ) Q *
      cubeLpNorm Q (2 : ℝ≥0∞)
        (fun x => u.toFun x - (c + vecDot e x)) = _
  rw [hvfun, hcube, hvL2]

/-- The projected coefficients attain the normalized affine-candidate
error. -/
theorem normalizedAffineCandidateError_bestFit_le
    (d : ℕ) [NeZero d] (k : ℤ)
    (u : H1Function
      (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d)))
    (c : ℝ) (e : Vec d) :
    normalizedAffineCandidateError (originCube d k) u.toFun
        (originCubeAffineBestFitIntercept d k u.toScalarL2)
        (originCubeAffineBestFitSlope d k u.toScalarL2) ≤
      normalizedAffineCandidateError (originCube d k) u.toFun c e := by
  let F := u.toScalarL2
  let cBest := originCubeAffineBestFitIntercept d k F
  let eBest := originCubeAffineBestFitSlope d k F
  have hcoeff :
      (cBest, eBest) = originCubeAffineBestFitCoefficients d k F :=
    (originCubeAffineBestFitCoefficients_eq d k F).symm
  have hnorm :=
    norm_sub_originCubeAffineBestFit_le d k F (c, e)
  rw [← hcoeff] at hnorm
  have hvolume_nonneg :
      0 ≤ ((cubeVolume (originCube d k))⁻¹) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg _)) _
  have hscaled := mul_le_mul_of_nonneg_left hnorm hvolume_nonneg
  have hweighted := mul_le_mul_of_nonneg_left hscaled
    (cubeBesovScaleWeight_nonneg 1 (originCube d k))
  rw [normalizedAffineCandidateError_eq_affineL2Norm d k u cBest eBest,
    normalizedAffineCandidateError_eq_affineL2Norm d k u c e]
  simpa [F, cBest, eBest] using hweighted

end

end HighContrast
end HCPolySupport
