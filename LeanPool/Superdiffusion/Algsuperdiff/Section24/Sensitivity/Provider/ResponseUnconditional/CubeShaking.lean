/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional.Aggregation
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Shaking.LambdaShaking

/-!
# CubeShaking

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The per-mesoscopic-cube shaking step

Source: ABK26, the display

```
J(z+cu_{-h}, (mu s0)^{-1/2}e, (mu s0)^{1/2}e; a+h)
  <= 6 mu^{-1} J(z+cu_{-h}, s0^{-1/2}e, s0^{1/2}e; a)
     + 4 mu^{-1}(mu-1)^2 s0 lambda_{1/2,2}^{-1}(z+cu_{-h}; a)
     + C mu^{-1} s0^{-1} lambda_{1/2,2}^{-1}(z+cu_{-h}; a) 3^{-2h} |h|^2_{W^{1,inf}}
     + C lambda_{1/2,2}^{-2}(z+cu_{-h}; a) 3^{-4h} |grad h|^2_{W^{1,inf}} ,
```

obtained from the conditional `J`-sensitivity at `delta = 1` followed by
`e.shaking.lambda` at `lam = mu` and `e.ellipticities.monotone.ordered`.

This module contains the **shaking half** of that display, which is
unconditional, together with the fold that turns a conditional per-cube
`(p,q)`-sensitivity into exactly the `hcube` hypothesis of
`Provider.ResponseUnconditional.Aggregation`.

## The remaining consumption point

* the mesoscopic gate (which the mesoscopic depth supplies unconditionally,
  exactly as `LambdaUnconditional.deep_cube_smallness` does for the `lambda`
  half), and
* a Term A budget carrying the cube scale factor and an `L^2` value budget
  rather than the root `W^{1,infinity}` value norm.

Every declaration in this module is an internal helper for the Section 2.4
sensitivity providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.Mesoscale
open Algsuperdiff.Section24.Sensitivity.Provider.Shaking

noncomputable section

variable {d : ℕ}

/-! ## The coarse gauge bounds the shaken quadratic form -/

/-- The `sigma_*^{-1}` quadratic form at the `sigma0`-normalized co-loading is
bounded by `sigma0 lambda_{3/8,2}^{-1}(R; a)`.  This is
`e.ellipticities.monotone.ordered` in the form used in ABK26. -/
theorem vecDot_sigmaStarInvCoarse_scalarLoading_le [NeZero d] (R : TriadicCube d)
    (F : TriadicCoeffFamily d) {σ0 : ℝ} (hσ0 : 0 < σ0) {e : Vec d}
    (he : vecNorm e = 1) :
    vecDot (Real.sqrt σ0 • e)
        (matVecMul (Ch02.sigmaStarInvCoarse (cubeDomain R) (F.coeffOn R))
          (Real.sqrt σ0 • e)) ≤
      σ0 * (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ := by
  classical
  set M : Mat d := Ch02.sigmaStarInvCoarse (cubeDomain R) (F.coeffOn R) with hM
  have habs := Ch02.abs_vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq M
    (Real.sqrt σ0 • e)
  have hnorm : Ch02.matrixOperatorNorm M = Ch02.coarseSigmaStarInvMatrixNorm R F := by
    rw [Ch02.coarseSigmaStarInvMatrixNorm, Ch02.matrixNorm_eq_matrixOperatorNorm, hM]
  have hle := Ch02.oneCube_sigmaStarInv_le_lambdaSq_finite_inv R F
    (s := (3 / 8 : ℝ)) (q := (2 : ℝ)) (by norm_num) (by norm_num)
  have hsq : vecNormSq (Real.sqrt σ0 • e) = σ0 := by
    have hsmul : vecNormSq (Real.sqrt σ0 • e) = Real.sqrt σ0 ^ 2 * vecNormSq e :=
      vecNormSq_smul (Real.sqrt σ0) e
    have he2 : vecNormSq e = 1 := by
      have := Ch02.vecNorm_sq_eq_vecNormSq e
      rw [he] at this
      simpa using this.symm
    rw [hsmul, he2, Real.sq_sqrt hσ0.le, mul_one]
  have hnn : (0 : ℝ) ≤ Ch02.matrixOperatorNorm M := Ch02.matrixOperatorNorm_nonneg M
  calc vecDot (Real.sqrt σ0 • e) (matVecMul M (Real.sqrt σ0 • e))
      ≤ |vecDot (Real.sqrt σ0 • e) (matVecMul M (Real.sqrt σ0 • e))| := le_abs_self _
    _ ≤ Ch02.matrixOperatorNorm M * vecNormSq (Real.sqrt σ0 • e) := habs
    _ = Ch02.coarseSigmaStarInvMatrixNorm R F * σ0 := by rw [hnorm, hsq]
    _ ≤ (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ * σ0 :=
        mul_le_mul_of_nonneg_right hle hσ0.le
    _ = σ0 * (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ := by ring

/-! ## The shaking step at a mesoscopic cube -/

/-- **The shaking step of the per-cube display.**  At any triadic cube, the
response of the base field at the `(mu sigma0)`-normalized loading is bounded by
twice `mu^{-1}` times the response at the `sigma0`-normalized loading plus the
`(mu-1)^2` gauge term.

This is `e.shaking.lambda` at `lam = mu` followed by
`e.ellipticities.monotone.ordered`; it is unconditional. -/
theorem responseJ_normalizedLoading_shaking_le [NeZero d] (R : TriadicCube d)
    (F : TriadicCoeffFamily d) {μ σ0 : ℝ} (hμ : 0 < μ) (hσ0 : 0 < σ0) {e : Vec d}
    (he : vecNorm e = 1) :
    responseJ (cubeDomain R) (F.coeffOn R)
        ((Real.sqrt (μ * σ0))⁻¹ • e) (Real.sqrt (μ * σ0) • e) ≤
      2 * μ⁻¹ * responseJ (cubeDomain R) (F.coeffOn R)
          ((Real.sqrt σ0)⁻¹ • e) (Real.sqrt σ0 • e) +
        μ⁻¹ * (μ - 1) ^ 2 * (σ0 * (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹) := by
  classical
  set Jb : ℝ := responseJ (cubeDomain R) (F.coeffOn R)
    ((Real.sqrt σ0)⁻¹ • e) (Real.sqrt σ0 • e) with hJb
  set Vform : ℝ := vecDot (Real.sqrt σ0 • e)
    (matVecMul (Ch02.sigmaStarInvCoarse (cubeDomain R) (F.coeffOn R))
      (Real.sqrt σ0 • e)) with hVform
  set Vg : ℝ := σ0 * (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ with hVg
  have hJbnn : 0 ≤ Jb := Ch02.responseJ_nonneg _ _ _ _
  have hVgnn : 0 ≤ Vg := by
    have : (0 : ℝ) ≤ (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ :=
      inv_nonneg.mpr (Ch02.lambdaSq_nonneg R F (by norm_num)
        (by simp [Ch02.MultiscaleExponent.IsAdmissible]))
    rw [hVg]; positivity
  have hVle : Vform ≤ Vg := vecDot_sigmaStarInvCoarse_scalarLoading_le R F hσ0 he
  have hshake := responseJ_shaking_lambda_normalizedLoading (cubeDomain R)
    (F.coeffOn R) (mu := μ) (sigma0 := σ0) hμ e
  refine le_of_shaking_lambda_bound (K := responseJ (cubeDomain R) (F.coeffOn R)
      ((Real.sqrt (μ * σ0))⁻¹ • e) (Real.sqrt (μ * σ0) • e))
    (J := Jb) (V := Vg) (μ := μ) hμ hJbnn hVgnn ?_
  refine hshake.trans ?_
  have hmono : Real.sqrt Vform ≤ Real.sqrt Vg := Real.sqrt_le_sqrt hVle
  have hinner : Real.sqrt Jb + Real.sqrt 2⁻¹ * |μ - 1| * Real.sqrt Vform ≤
      Real.sqrt Jb + Real.sqrt 2⁻¹ * |μ - 1| * Real.sqrt Vg := by
    have hco : (0 : ℝ) ≤ Real.sqrt 2⁻¹ * |μ - 1| :=
      mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
    have := mul_le_mul_of_nonneg_left hmono hco
    linarith
  have hnn : (0 : ℝ) ≤ Real.sqrt Jb + Real.sqrt 2⁻¹ * |μ - 1| * Real.sqrt Vform := by
    have : (0 : ℝ) ≤ Real.sqrt 2⁻¹ * |μ - 1| * Real.sqrt Vform := by positivity
    have h2 : (0 : ℝ) ≤ Real.sqrt Jb := Real.sqrt_nonneg _
    linarith
  have hsq : (Real.sqrt Jb + Real.sqrt 2⁻¹ * |μ - 1| * Real.sqrt Vform) ^ 2 ≤
      (Real.sqrt Jb + Real.sqrt 2⁻¹ * |μ - 1| * Real.sqrt Vg) ^ 2 :=
    pow_le_pow_left₀ hnn hinner 2
  exact mul_le_mul_of_nonneg_left hsq (inv_pos.mpr hμ).le

/-! ## From a conditional per-cube sensitivity to the aggregation hypothesis -/

/-- **The per-mesoscopic-cube estimate of the source display.**

`hsens` is the display of ABK26, before shaking: the factor `3 = 1 + delta +
(gate)` at `delta = 1`, the Term A error `|p|^2 λ_{3/8,2}^{-1}(R) (V R + 3^{-2H}
‖∇h‖^2)` with `|p|^2 = (μ σ0)^{-1}`, and the Term BC error `|p·q| 3^{-2H}
λ_{3/8,2}^{-2}(R) ‖∇h‖^2` with `|p·q| = 1`. -/
theorem mesoscale_cube_bound_of_conditional_sensitivity [NeZero d]
    (R : TriadicCube d) (F G : TriadicCoeffFamily d)
    {μ σ0 K₁ D2 gr Vr : ℝ} {e : Vec d} (hμ : 0 < μ) (hσ0 : 0 < σ0)
    (he : vecNorm e = 1) (hD2 : 0 ≤ D2) (hVr : 0 ≤ Vr)
    (hsens : responseJ (cubeDomain R) (G.coeffOn R)
        ((Real.sqrt (μ * σ0))⁻¹ • e) (Real.sqrt (μ * σ0) • e) ≤
      3 * responseJ (cubeDomain R) (F.coeffOn R)
          ((Real.sqrt (μ * σ0))⁻¹ • e) (Real.sqrt (μ * σ0) • e) +
        K₁ * ((μ * σ0)⁻¹ * (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ *
          (Vr + D2 * gr ^ 2)) +
        K₁ * (D2 * (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ ^ 2 * gr ^ 2)) :
    responseJ (cubeDomain R) (G.coeffOn R)
        ((Real.sqrt (μ * σ0))⁻¹ • e) (Real.sqrt (μ * σ0) • e) ≤
      6 * μ⁻¹ * responseJ (cubeDomain R) (F.coeffOn R)
          ((Real.sqrt σ0)⁻¹ • e) (Real.sqrt σ0 • e) +
        max 3 K₁ * μ⁻¹ * (μ - 1) ^ 2 * σ0 *
          (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ +
        max 3 K₁ * μ⁻¹ * σ0⁻¹ * (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ *
          (Vr + D2 * gr ^ 2) +
        max 3 K₁ * D2 * (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ ^ 2 * gr ^ 2 := by
  classical
  set Ψ : ℝ := (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ with hΨ
  set Jb : ℝ := responseJ (cubeDomain R) (F.coeffOn R)
    ((Real.sqrt σ0)⁻¹ • e) (Real.sqrt σ0 • e) with hJb
  set K : ℝ := max 3 K₁ with hK
  have hΨnn : 0 ≤ Ψ := by
    rw [hΨ]
    exact inv_nonneg.mpr (Ch02.lambdaSq_nonneg R F (by norm_num)
      (by simp [Ch02.MultiscaleExponent.IsAdmissible]))
  have hJbnn : 0 ≤ Jb := Ch02.responseJ_nonneg _ _ _ _
  have hμinv : (0 : ℝ) < μ⁻¹ := inv_pos.mpr hμ
  have hσinv : (0 : ℝ) < σ0⁻¹ := inv_pos.mpr hσ0
  have h3K : (3 : ℝ) ≤ K := le_max_left _ _
  have hK₁K : K₁ ≤ K := le_max_right _ _
  have hgr2 : (0 : ℝ) ≤ gr ^ 2 := sq_nonneg gr
  refine hsens.trans ?_
  -- the shaking step on the main term
  have hshake := responseJ_normalizedLoading_shaking_le R F hμ hσ0 he
  have hmain : 3 * responseJ (cubeDomain R) (F.coeffOn R)
        ((Real.sqrt (μ * σ0))⁻¹ • e) (Real.sqrt (μ * σ0) • e) ≤
      6 * μ⁻¹ * Jb + 3 * (μ⁻¹ * (μ - 1) ^ 2 * (σ0 * Ψ)) := by
    have := mul_le_mul_of_nonneg_left hshake (by norm_num : (0 : ℝ) ≤ 3)
    linarith [this]
  -- the two error families
  have hinvmul : (μ * σ0)⁻¹ = μ⁻¹ * σ0⁻¹ := by
    rw [mul_inv]
  have hVD : (0 : ℝ) ≤ Vr + D2 * gr ^ 2 := by positivity
  have herr1 : K₁ * ((μ * σ0)⁻¹ * Ψ * (Vr + D2 * gr ^ 2)) ≤
      K * μ⁻¹ * σ0⁻¹ * Ψ * (Vr + D2 * gr ^ 2) := by
    rw [hinvmul]
    have hnn : (0 : ℝ) ≤ μ⁻¹ * σ0⁻¹ * Ψ * (Vr + D2 * gr ^ 2) := by positivity
    calc K₁ * (μ⁻¹ * σ0⁻¹ * Ψ * (Vr + D2 * gr ^ 2))
        ≤ K * (μ⁻¹ * σ0⁻¹ * Ψ * (Vr + D2 * gr ^ 2)) :=
          mul_le_mul_of_nonneg_right hK₁K hnn
      _ = K * μ⁻¹ * σ0⁻¹ * Ψ * (Vr + D2 * gr ^ 2) := by ring
  have herr2 : K₁ * (D2 * Ψ ^ 2 * gr ^ 2) ≤ K * D2 * Ψ ^ 2 * gr ^ 2 := by
    have hnn : (0 : ℝ) ≤ D2 * Ψ ^ 2 * gr ^ 2 := by positivity
    calc K₁ * (D2 * Ψ ^ 2 * gr ^ 2) ≤ K * (D2 * Ψ ^ 2 * gr ^ 2) :=
          mul_le_mul_of_nonneg_right hK₁K hnn
      _ = K * D2 * Ψ ^ 2 * gr ^ 2 := by ring
  have hshakecoef : 3 * (μ⁻¹ * (μ - 1) ^ 2 * (σ0 * Ψ)) ≤
      K * μ⁻¹ * (μ - 1) ^ 2 * σ0 * Ψ := by
    have hnn : (0 : ℝ) ≤ μ⁻¹ * (μ - 1) ^ 2 * σ0 * Ψ := by positivity
    calc 3 * (μ⁻¹ * (μ - 1) ^ 2 * (σ0 * Ψ))
        = 3 * (μ⁻¹ * (μ - 1) ^ 2 * σ0 * Ψ) := by ring
      _ ≤ K * (μ⁻¹ * (μ - 1) ^ 2 * σ0 * Ψ) := mul_le_mul_of_nonneg_right h3K hnn
      _ = K * μ⁻¹ * (μ - 1) ^ 2 * σ0 * Ψ := by ring
  linarith [hmain, herr1, herr2, hshakecoef]

end

end Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional
