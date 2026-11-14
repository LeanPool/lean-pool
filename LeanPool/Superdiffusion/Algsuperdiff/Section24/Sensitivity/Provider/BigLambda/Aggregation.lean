/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.BigLambda.CubeJSensitivity
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Multiscale.GeometricResummation

/-!
# Aggregation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The descendant `b`-matrix estimate and its geometric resummation

Source: ABK26.

`Provider.Multiscale.GeometricResummation` already performs the resummation

```
Lambda_{s,2}(cu_0; a₁) ≤ 4 Lambda_{s,2}(cu_0; a₀)
                            + K (3/8 - s)^{-1} lambda_{s,2}^{-1}(cu_0; a₀)
```

from the per-descendant estimate with the **fixed** same-index factor `4`.  The
free-`δ` statement needs the same resummation with a general coefficient `c`.

`coarseBMatrixNorm_perturb_le` is the per-descendant input: the pure-potential
`J`-sensitivity of `BigLambda.CubeJSensitivity` combined with the identity
`2 J(R,p,0;a) = p·b(R;a)p` of `BigLambda.BMatrix`.

Every declaration in this module is an internal helper for the Section 2.4
sensitivity providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.BigLambda

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz
open Algsuperdiff.Section24.Sensitivity.Provider.Lambda
open Algsuperdiff.Section24.Sensitivity.Provider.Multiscale
open Algsuperdiff.Section24.UnitCubeMultiscale
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The resummation with a general same-index coefficient -/

/-- **The `Lambda_{s,2}` endpoint with a general same-index coefficient.** -/
theorem LambdaSq_two_le_of_descendant_bound_coeff
    (Q : TriadicCube d) (A₀ A₁ : Ch02.TriadicCoeffFamily d) {K c s : ℝ}
    (hK : 0 ≤ K) (hc : 0 ≤ c) (hs0 : 0 < s) (hs : s < 3 / 8)
    (hdesc : ∀ n : ℕ, ∀ R ∈ descendantsAtScale Q (Q.scale - (n : ℤ)),
      coarseBMatrixNorm R A₁ ≤
        c * coarseBMatrixNorm R A₀ +
          K * (Ch02.lambdaSq R (3 / 8 : ℝ) (.finite 2) A₀)⁻¹) :
    Ch02.LambdaSq Q s (.finite 2) A₁ ≤
      c * Ch02.LambdaSq Q s (.finite 2) A₀ +
        K * (3 / 8 - s)⁻¹ * (Ch02.lambdaSq Q s (.finite 2) A₀)⁻¹ :=
  Algsuperdiff.Section24.Sensitivity.Provider.Multiscale.LambdaSq_two_le_of_descendant_bound_coeff
    Q A₀ A₁ hK hc hs0 hs hdesc

/-! ## The descendant `b`-matrix estimate -/

/-- **The descendant `b`-matrix estimate**, the display of ABK26 in its free-`δ`
form.  The constant is cube-independent. -/
theorem coarseBMatrixNorm_perturb_le (dimension : 2 ≤ d)
    (a : CoeffOn (cubeDomain (originCube d 0))) (h : UnitCubeSkewW2Infinity d)
    (hgate : h.gradientW1Infinity ≤
      (bigLambdaGateConst d)⁻¹ * unitCubeLambda (3 / 8) (.finite 2) a)
    (F G : Ch03.CoeffFamily d) (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    (hG : CoeffOn.AEEq (G.coeffOn (originCube d 0))
      (perturbCoeffOn (cubeDomain (originCube d 0)) a h.toLInfSkewMatrixFieldOn 1))
    {k : ℤ} (hk : k ≤ (originCube d 0).scale) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d 0) k)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    coarseBMatrixNorm R G ≤
      (1 + δ + 2 * (potCubeConstB d * h.gradientW1Infinity *
          (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹)) * coarseBMatrixNorm R F +
        2 * δ⁻¹ * potCubeConstA d ^ 2 * h.w1Infinity ^ 2 *
          (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ := by
  classical
  set g : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0)) :=
    h.toLInfSkewMatrixFieldOn with hgdef
  set gR : LInfSkewMatrixFieldOn (cubeDomain R) := descendantField hk hR g with hgRdef
  set β : ℝ := potCubeConstB d * h.gradientW1Infinity *
    (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ with hβ
  set LRF : ℝ := (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ with hLRF
  have hLRFnn : 0 ≤ LRF := lambdaSq_inv_nonneg R F
  have hwnn : 0 ≤ h.w1Infinity := w1Infinity_nonneg h
  have hgnn : 0 ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
  have hAnn : (0 : ℝ) ≤ potCubeConstA d := potCubeConstA_nonneg d
  have hBnn : (0 : ℝ) ≤ potCubeConstB d := potCubeConstB_nonneg d
  have hlampos : 0 < unitCubeLambda (3 / 8) (.finite 2) a :=
    unitCubeLambda_pos a (by norm_num) (by simp [Ch02.MultiscaleExponent.IsAdmissible])
  have hβnn : 0 ≤ β := by
    rw [hβ]
    have : (0 : ℝ) ≤ (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ :=
      (inv_pos.mpr hlampos).le
    positivity
  have hbFnn : 0 ≤ coarseBMatrixNorm R F := coarseBMatrixNorm_nonneg R F
  set c : ℝ := 1 + δ + 2 * β with hc
  set K : ℝ := 2 * δ⁻¹ * potCubeConstA d ^ 2 * h.w1Infinity ^ 2 with hK
  have hcnn : 0 ≤ c := by rw [hc]; linarith
  have hKnn : 0 ≤ K := by
    rw [hK]
    have : (0 : ℝ) ≤ δ⁻¹ := (inv_pos.mpr hδ0).le
    positivity
  refine coarseBMatrixNorm_le_of_forall_responseJ_potential R G
    (M := c * coarseBMatrixNorm R F + K * LRF)
    (by positivity) ?_
  intro p
  have hGR : CoeffOn.AEEq (G.coeffOn R)
      (perturbCoeffOn (cubeDomain R) (F.coeffOn R) gR 1) :=
    coeffOn_descendant_aeeq_perturbCoeffOn a g 1 F G hF hG hk hR
  have hJG : responseJ (cubeDomain R) (G.coeffOn R) p 0 =
      responseJ (cubeDomain R) (perturbCoeffOn (cubeDomain R) (F.coeffOn R) gR 1) p 0 :=
    responseJ_eq_ofAEEq hGR p 0
  have hmain := responseJ_potential_cube_sensitivity dimension a h hgate F hF hk hR p
    hδ0 hδ1
  have hbase := two_mul_responseJ_potential_le_coarseBMatrixNorm R F p
  have hpnn : (0 : ℝ) ≤ vecNormSq p := vecNormSq_nonneg p
  have hstep : 2 * responseJ (cubeDomain R) (G.coeffOn R) p 0 ≤
      (1 + δ / 2 + 2 * β) * (2 * responseJ (cubeDomain R) (F.coeffOn R) p 0) +
        2 * (δ⁻¹ * (potCubeConstA d ^ 2 * h.w1Infinity ^ 2 * vecNormSq p * LRF)) := by
    rw [hJG]
    have := mul_le_mul_of_nonneg_left hmain (by norm_num : (0:ℝ) ≤ 2)
    refine this.trans (le_of_eq ?_)
    rw [hβ, hLRF]
    ring
  refine hstep.trans ?_
  have hcoef : (1 + δ / 2 + 2 * β) ≤ c := by rw [hc]; linarith
  have hfirst : (1 + δ / 2 + 2 * β) * (2 * responseJ (cubeDomain R) (F.coeffOn R) p 0) ≤
      c * (coarseBMatrixNorm R F * vecNormSq p) := by
    have h2J : (0 : ℝ) ≤ 2 * responseJ (cubeDomain R) (F.coeffOn R) p 0 := by
      have := Ch02.responseJ_nonneg (cubeDomain R) (F.coeffOn R) p 0; linarith
    calc (1 + δ / 2 + 2 * β) * (2 * responseJ (cubeDomain R) (F.coeffOn R) p 0)
        ≤ c * (2 * responseJ (cubeDomain R) (F.coeffOn R) p 0) :=
          mul_le_mul_of_nonneg_right hcoef h2J
      _ ≤ c * (coarseBMatrixNorm R F * vecNormSq p) :=
          mul_le_mul_of_nonneg_left hbase hcnn
  have hsecond : 2 * (δ⁻¹ * (potCubeConstA d ^ 2 * h.w1Infinity ^ 2 * vecNormSq p * LRF))
      = K * LRF * vecNormSq p := by rw [hK]; ring
  rw [hsecond]
  have hfold : c * (coarseBMatrixNorm R F * vecNormSq p) + K * LRF * vecNormSq p
      = (c * coarseBMatrixNorm R F + K * LRF) * vecNormSq p := by ring
  linarith [hfirst, hfold]

end

end Algsuperdiff.Section24.Sensitivity.Provider.BigLambda
