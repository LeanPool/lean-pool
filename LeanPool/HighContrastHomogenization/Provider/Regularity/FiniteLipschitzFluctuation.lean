/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.HarmonicNormalized

/-!
# High-contrast homogenization: Provider.Regularity.FiniteLipschitzFluctuation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Normalized fluctuation of an affine approximation

The normalized fluctuation of a scalar Sobolev function is bounded by its
error from a specified affine function and by the Euclidean magnitude of the
affine slope.  This elementary estimate is independent of the multiscale
finite-energy recurrence.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The normalized fluctuation of a square-integrable function is at most twice
its normalized `L²` norm. -/
theorem cubeLpNorm_two_cubeFluctuation_le_two_mul
    {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q f) ≤
      2 * cubeLpNorm Q (2 : ℝ≥0∞) f := by
  have hconst : MemLp (fun _ : Vec d ↦ -cubeAverage Q f)
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_const (-cubeAverage Q f)
  have hadd := cubeLpNorm_add_le Q (2 : ℝ≥0∞) f
    (fun _ : Vec d ↦ -cubeAverage Q f) hf hconst (by norm_num)
  have havg : |cubeAverage Q f| ≤ cubeLpNorm Q (2 : ℝ≥0∞) f := by
    simpa only [Real.norm_eq_abs] using
      norm_cubeAverage_le_cubeLpNorm_two Q f hf
  calc
    cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q f) ≤
        cubeLpNorm Q (2 : ℝ≥0∞) f +
          cubeLpNorm Q (2 : ℝ≥0∞) (fun _ : Vec d ↦ -cubeAverage Q f) := by
      simpa [cubeFluctuation, sub_eq_add_neg] using! hadd
    _ = cubeLpNorm Q (2 : ℝ≥0∞) f + |cubeAverage Q f| := by
      rw [cubeLpNorm_const (Q := Q) (p := (2 : ℝ≥0∞))
        (c := -cubeAverage Q f) (by norm_num)]
      simp
    _ ≤ cubeLpNorm Q (2 : ℝ≥0∞) f +
        cubeLpNorm Q (2 : ℝ≥0∞) f := add_le_add_right havg _
    _ = 2 * cubeLpNorm Q (2 : ℝ≥0∞) f := by ring

/-- The normalized fluctuation is controlled by the error from a specified
affine function and the Euclidean magnitude of its slope. -/
theorem normalized_fluctuation_le_affine_error_add_slope
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (u : H1Function (openCubeSet Q)) (c : ℝ) (e : Vec d) :
    cubeBesovScaleWeight 1 Q *
        cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u.toFun) ≤
      2 * (normalizedAffineCandidateError Q u.toFun c e +
        cubeBesovW12LocalPoincareConstant d * euclideanNorm e) := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let ell : H1Function (openCubeSet Q) :=
    H1Function.const c +
      H1Function.affineOnIsSobolevRegularDomain
        (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain e
  let cbar : ℝ := cubeAverage Q ell.toFun
  let f : Vec d → ℝ := fun x ↦ u.toFun x - cbar
  let r : Vec d → ℝ := fun x ↦ u.toFun x - ell.toFun x
  let q : Vec d → ℝ := fun x ↦ ell.toFun x - cbar
  have hf : MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    u.memL2_normalizedCubeMeasure.sub (memLp_const cbar)
  have hr : MemLp r (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    u.memL2_normalizedCubeMeasure.sub ell.memL2_normalizedCubeMeasure
  have hq : MemLp q (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    ell.memL2_normalizedCubeMeasure.sub (memLp_const cbar)
  have htri := cubeLpNorm_add_le Q (2 : ℝ≥0∞) r q hr hq (by norm_num)
  have hfEq : f = r + q := by
    funext x
    dsimp [f, r, q]
    ring
  have hfluctEq : cubeFluctuation Q f = cubeFluctuation Q u.toFun := by
    exact cubeFluctuation_sub_const Q u.toFun cbar
      u.memL2_normalizedCubeMeasure
  have hresidual :
      cubeBesovScaleWeight 1 Q * cubeLpNorm Q (2 : ℝ≥0∞) r =
        normalizedAffineCandidateError Q u.toFun c e := by
    unfold normalizedAffineCandidateError normalizedCubeL2Distance
    congr 2
    funext x
    simp [r, ell, vecDot]
  have haffine :=
    normalizedAffineCandidateError_cubeAverage_le_euclideanGradient
      Q ell.toFun 0 (0 : Vec d) ell (by
        funext x
        simp only [zero_add, vecDot_zero_left, sub_zero])
  have haffine' :
      cubeBesovScaleWeight 1 Q * cubeLpNorm Q (2 : ℝ≥0∞) q ≤
        cubeBesovW12LocalPoincareConstant d * euclideanNorm e := by
    simpa only [q, cbar, normalizedAffineCandidateError,
      normalizedCubeL2Distance, zero_add, add_zero, vecDot_zero_left,
      ell, H1Function.add_grad, H1Function.grad_const,
      H1Function.affineOnIsSobolevRegularDomain_grad,
      cubeLpNorm_const (Q := Q) (p := (2 : ℝ≥0∞))
        (c := euclideanNorm e) (by norm_num),
      Real.norm_of_nonneg, euclideanNorm_nonneg] using haffine
  have hweight : 0 ≤ cubeBesovScaleWeight 1 Q :=
    cubeBesovScaleWeight_nonneg 1 Q
  calc
    cubeBesovScaleWeight 1 Q *
          cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u.toFun) =
        cubeBesovScaleWeight 1 Q *
          cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q f) := by
      rw [hfluctEq]
    _ ≤ cubeBesovScaleWeight 1 Q *
        (2 * cubeLpNorm Q (2 : ℝ≥0∞) f) :=
      mul_le_mul_of_nonneg_left
        (cubeLpNorm_two_cubeFluctuation_le_two_mul Q f hf) hweight
    _ = 2 *
        (cubeBesovScaleWeight 1 Q * cubeLpNorm Q (2 : ℝ≥0∞) f) := by
      ring
    _ ≤ 2 * (cubeBesovScaleWeight 1 Q *
          (cubeLpNorm Q (2 : ℝ≥0∞) r +
            cubeLpNorm Q (2 : ℝ≥0∞) q)) := by
      rw [hfEq]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left htri hweight) (by norm_num)
    _ = 2 *
        (cubeBesovScaleWeight 1 Q * cubeLpNorm Q (2 : ℝ≥0∞) r +
          cubeBesovScaleWeight 1 Q * cubeLpNorm Q (2 : ℝ≥0∞) q) := by
      ring
    _ ≤ 2 * (normalizedAffineCandidateError Q u.toFun c e +
          cubeBesovW12LocalPoincareConstant d * euclideanNorm e) := by
      rw [hresidual]
      exact mul_le_mul_of_nonneg_left
        (add_le_add (le_refl _) haffine') (by norm_num)

end

end HighContrast
end HCPolySupport
