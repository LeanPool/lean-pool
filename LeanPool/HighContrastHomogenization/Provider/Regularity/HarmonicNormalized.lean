/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.HarmonicCaccioppoli
public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffineFlatnessPrep
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.QuantitativeCutoffInputs.Setup.ScaleBounds
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeBesovPoincare.W12LocalPoincare
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubePoisson.AnalyticInput

/-!
# High-contrast homogenization: Provider.Regularity.HarmonicNormalized

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Normalized harmonic estimates on Euclidean cubes

These lemmas convert an unnormalized interior energy estimate to normalized
cube `L²` notation and turn the local Poincare estimate into an affine error
bound with the cube-average intercept.
-/

namespace HCPolySupport

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

/-- The raw central-child Caccioppoli estimate in normalized `L²` notation,
using the Euclidean magnitude of the stored weak gradient. -/
theorem harmonic_centralChild_euclideanGradient_cubeLpNorm_sq_le
    {d : ℕ} (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    (hu : WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0)) :
    (cubeLpNorm (centralChild Q) (2 : ℝ≥0∞)
        (fun x => euclideanNorm (u.grad x))) ^ (2 : ℕ) ≤
      (((3 ^ d : ℕ) : ℝ) *
          (4 * ((d : ℝ) *
            (quantitativeCubeCutoffGradientConst d /
              (((3 / 4 : ℝ) - 1 / 2) * cubeRadius Q)) ^ 2))) *
        (cubeLpNorm Q (2 : ℝ≥0∞) u.toFun) ^ (2 : ℕ) := by
  let R : TriadicCube d := centralChild Q
  let K : ℝ :=
    4 * ((d : ℝ) *
      (quantitativeCubeCutoffGradientConst d /
        (((3 / 4 : ℝ) - 1 / 2) * cubeRadius Q)) ^ 2)
  have hR : R ∈ descendantsAtDepth Q 1 := by
    simpa [R] using centralDescendant_mem_descendantsAtDepth Q 1
  let uR : H1Function (openCubeSet R) := u.restrictToOpenSubcube hR
  let wR : W1pFunction (openCubeSet R) (2 : ℝ≥0∞) :=
    { toFun := uR.toFun
      grad := uR.grad
      memLp := uR.memL2
      gradMemLp := uR.gradMemL2
      hasWeakGradient := uR.hasWeakGradient }
  have hgradMem : MemLp (fun x => euclideanNorm (u.grad x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure R) := by
    have hmem := wR.gradEuclideanMemLp
      ((isOpenBoundedConvexDomain_openCubeSet R).toBoundedMeasurableDomain
        (Book.Ch02.openCubeSet_nonempty R)) (2 : ℝ≥0∞)
    rw [openCubeSet_boundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
      at hmem
    simpa [wR, uR] using hmem
  have huMem : MemLp u.toFun (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa using u.memL2_normalizedCubeMeasure
  have hchild :
      ∫ x in openCubeSet R, vecNormSq (u.grad x) ∂volume =
        cubeVolume R *
          (cubeLpNorm R (2 : ℝ≥0∞)
            (fun x => euclideanNorm (u.grad x))) ^ (2 : ℕ) := by
    have hnorm :=
      setIntegral_openCubeSet_sq_eq_cubeVolume_mul_cubeLpNorm_two_rpow R
        (fun x => euclideanNorm (u.grad x)) hgradMem
    calc
      ∫ x in openCubeSet R, vecNormSq (u.grad x) ∂volume =
          ∫ x in openCubeSet R,
            euclideanNorm (u.grad x) * euclideanNorm (u.grad x) ∂volume := by
        apply MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet R)
        intro x _hx
        change vecNormSq (u.grad x) =
          euclideanNorm (u.grad x) * euclideanNorm (u.grad x)
        rw [← euclideanNorm_sq]
        ring
      _ = cubeVolume R *
          (cubeLpNorm R (2 : ℝ≥0∞)
            (fun x => euclideanNorm (u.grad x))) ^ (2 : ℝ) := hnorm
      _ = cubeVolume R *
          (cubeLpNorm R (2 : ℝ≥0∞)
            (fun x => euclideanNorm (u.grad x))) ^ (2 : ℕ) := by
        rw [Real.rpow_two]
  have hparent :
      ∫ x in openCubeSet Q, u.toFun x ^ 2 ∂volume =
        cubeVolume Q *
          (cubeLpNorm Q (2 : ℝ≥0∞) u.toFun) ^ (2 : ℕ) := by
    have hnorm :=
      setIntegral_openCubeSet_sq_eq_cubeVolume_mul_cubeLpNorm_two_rpow Q
        u.toFun huMem
    calc
      ∫ x in openCubeSet Q, u.toFun x ^ 2 ∂volume =
          ∫ x in openCubeSet Q, u.toFun x * u.toFun x ∂volume := by
        apply MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet Q)
        intro x _hx
        ring
      _ = cubeVolume Q *
          (cubeLpNorm Q (2 : ℝ≥0∞) u.toFun) ^ (2 : ℝ) := hnorm
      _ = cubeVolume Q *
          (cubeLpNorm Q (2 : ℝ≥0∞) u.toFun) ^ (2 : ℕ) := by
        rw [Real.rpow_two]
  have hraw :
      ∫ x in openCubeSet R, vecNormSq (u.grad x) ∂volume ≤
        K * ∫ x in openCubeSet Q, u.toFun x ^ 2 ∂volume := by
    simpa [R, K] using harmonic_centralChild_gradient_energy_le Q u hu
  have hvolume :
      cubeVolume Q = ((3 ^ d : ℕ) : ℝ) * cubeVolume R := by
    simpa [R] using centralDescendant_cubeVolume_eq Q 1
  change
    (cubeLpNorm R (2 : ℝ≥0∞)
        (fun x => euclideanNorm (u.grad x))) ^ (2 : ℕ) ≤
      (((3 ^ d : ℕ) : ℝ) * K) *
        (cubeLpNorm Q (2 : ℝ≥0∞) u.toFun) ^ (2 : ℕ)
  apply (mul_le_mul_iff_of_pos_left (cubeVolume_pos R)).mp
  calc
    cubeVolume R *
          (cubeLpNorm R (2 : ℝ≥0∞)
            (fun x => euclideanNorm (u.grad x))) ^ (2 : ℕ) =
        ∫ x in openCubeSet R, vecNormSq (u.grad x) ∂volume := hchild.symm
    _ ≤ K * ∫ x in openCubeSet Q, u.toFun x ^ 2 ∂volume := hraw
    _ = cubeVolume R *
        ((((3 ^ d : ℕ) : ℝ) * K) *
          (cubeLpNorm Q (2 : ℝ≥0∞) u.toFun) ^ (2 : ℕ)) := by
      rw [hparent, hvolume]
      ring

end CubeCalderonZygmund

namespace HighContrast

/-- Choosing the residual cube average as the intercept correction turns the
normalized affine error into an oscillation controlled by the Euclidean
gradient magnitude. -/
theorem normalizedAffineCandidateError_cubeAverage_le_euclideanGradient
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (h : Vec d → ℝ)
    (c : ℝ) (e : Vec d) (v : H1Function (openCubeSet Q))
    (hv : v.toFun = fun x => h x - (c + vecDot e x)) :
    normalizedAffineCandidateError Q h (c + cubeAverage Q v.toFun) e ≤
      cubeBesovW12LocalPoincareConstant d *
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (v.grad x)) := by
  let w : W1pFunction (openCubeSet Q) (2 : ℝ≥0∞) :=
    { toFun := v.toFun
      grad := v.grad
      memLp := v.memL2
      gradMemLp := v.gradMemL2
      hasWeakGradient := v.hasWeakGradient }
  have hresidual :
      (fun x => h x - ((c + cubeAverage Q v.toFun) + vecDot e x)) =
        cubeFluctuation Q v.toFun := by
    funext x
    have hvx := congrFun hv x
    simp only [cubeFluctuation]
    rw [hvx]
    ring
  have herror :
      normalizedAffineCandidateError Q h (c + cubeAverage Q v.toFun) e =
        cubeBesovScaleWeight (1 : ℝ) Q *
          cubeBesovOscillation Q (2 : ℝ≥0∞) v.toFun := by
    unfold normalizedAffineCandidateError normalizedCubeL2Distance
    rw [hresidual]
    rfl
  have hpoincare :
      cubeBesovOscillation Q (2 : ℝ≥0∞) v.toFun ≤
        cubeBesovW12LocalPoincareConstant d * cubeScaleFactor Q *
          cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x => euclideanNorm (v.grad x)) := by
    have hlocal :=
      cubeBesovOscillation_two_le_cubeScaleFactor_mul_normalizedW1pSeminorm Q w
    rw [openCubeSet_normalizedW1pSeminorm_two_eq_cubeLpNorm_euclideanGrad]
      at hlocal
    simpa [w] using hlocal
  have hweight : 0 ≤ cubeBesovScaleWeight (1 : ℝ) Q :=
    cubeBesovScaleWeight_nonneg 1 Q
  have hscale :
      cubeBesovScaleWeight (1 : ℝ) Q * cubeScaleFactor Q = 1 := by
    calc
      cubeBesovScaleWeight (1 : ℝ) Q * cubeScaleFactor Q =
          cubeScaleFactor Q * cubeBesovScaleWeight (1 : ℝ) Q := mul_comm _ _
      _ = cubeBesovScaleWeight (-1 : ℝ) Q *
          cubeBesovScaleWeight (1 : ℝ) Q := by
        rw [cubeBesovScaleWeight_neg_one_eq_cubeScaleFactor]
      _ = 1 := cubeBesovScaleWeight_neg_one_mul_cubeBesovScaleWeight_one_eq_one Q
  calc
    normalizedAffineCandidateError Q h (c + cubeAverage Q v.toFun) e =
        cubeBesovScaleWeight (1 : ℝ) Q *
          cubeBesovOscillation Q (2 : ℝ≥0∞) v.toFun := herror
    _ ≤ cubeBesovScaleWeight (1 : ℝ) Q *
        (cubeBesovW12LocalPoincareConstant d * cubeScaleFactor Q *
          cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x => euclideanNorm (v.grad x))) :=
      mul_le_mul_of_nonneg_left hpoincare hweight
    _ = cubeBesovW12LocalPoincareConstant d *
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (v.grad x)) := by
      calc
        cubeBesovScaleWeight (1 : ℝ) Q *
            (cubeBesovW12LocalPoincareConstant d * cubeScaleFactor Q *
              cubeLpNorm Q (2 : ℝ≥0∞)
                (fun x => euclideanNorm (v.grad x))) =
            cubeBesovW12LocalPoincareConstant d *
              (cubeBesovScaleWeight (1 : ℝ) Q * cubeScaleFactor Q) *
                cubeLpNorm Q (2 : ℝ≥0∞)
                  (fun x => euclideanNorm (v.grad x)) := by ring
        _ = cubeBesovW12LocalPoincareConstant d *
            cubeLpNorm Q (2 : ℝ≥0∞)
              (fun x => euclideanNorm (v.grad x)) := by rw [hscale, mul_one]

end HighContrast

end

end HCPolySupport
