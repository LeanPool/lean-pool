/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.BigLambda.CubeGaugePath
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.BigLambda.CubePotentialDh
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.BigLambda.PathODE
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.BigLambda.BMatrix

/-!
# CubeJSensitivity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The descendant `b`-matrix estimate

Source: ABK26, the display

```
|b(z + cu_n; a + h)| ≤ 4 |b(z + cu_n; a)| + C ‖h‖²_{W^{1,∞}(cu_0)}
                          λ_{3/8,2}^{-1}(z + cu_n; a) ,
```

obtained by applying the `J`-sensitivity estimate on each descendant cube with
the scaled-norm inequalities of that display.

The route here is:

1. the pure-potential `D_h` bound of `BigLambda.CubePotentialDh`, transported
   along the perturbation path and priced against the base descendant gauge and
   the base root gauge (`BigLambda.CubeGaugePath`);
2. the frozen derivative identity `Provider.Response.PathDerivative` turns it
   into the affine differential inequality `y' ≤ m + c y` after a pointwise
   Young step (`BigLambda.PathODE`);
3. exact integration of that inequality gives the `J`-sensitivity at the
   pure-potential loading, uniformly in the descendant;
4. the identity `2 J(R, p, 0; a) = p · b(R; a) p` of `BigLambda.BMatrix`
   converts it into the descendant `b`-matrix estimate, with the *same-index*
   factor `4` and a cube-independent constant `K = C(d) ‖h‖²_{W^{1,∞}}`.

Every declaration in this module is an internal helper for the Section 2.4
sensitivity providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.BigLambda

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz
open Algsuperdiff.Section24.Sensitivity.Provider.Lambda
open Algsuperdiff.Section24.Sensitivity.Provider.Multiscale
open Algsuperdiff.Section24.Sensitivity.Provider.Response
open Algsuperdiff.Section24.UnitCubeMultiscale
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

def bigLambdaGateConst (d : ℕ) [NeZero d] : ℝ :=
  max (gaugeGateConst d) (4 * potCubeConstB d)

theorem bigLambdaGateConst_pos (d : ℕ) [NeZero d] : 0 < bigLambdaGateConst d :=
  lt_of_lt_of_le (gaugeGateConst_pos d) (le_max_left _ _)

theorem gaugeGateConst_le_bigLambdaGateConst (d : ℕ) [NeZero d] :
    gaugeGateConst d ≤ bigLambdaGateConst d := le_max_left _ _

theorem four_mul_potCubeConstB_le_bigLambdaGateConst (d : ℕ) [NeZero d] :
    4 * potCubeConstB d ≤ bigLambdaGateConst d := le_max_right _ _

theorem gaugeGate_of_bigLambdaGate [NeZero d]
    (a : CoeffOn (cubeDomain (originCube d 0))) (h : UnitCubeSkewW2Infinity d)
    (hgate : h.gradientW1Infinity ≤
      (bigLambdaGateConst d)⁻¹ * unitCubeLambda (3 / 8) (.finite 2) a) :
    h.gradientW1Infinity ≤
      (gaugeGateConst d)⁻¹ * unitCubeLambda (3 / 8) (.finite 2) a := by
  have hlampos : 0 < unitCubeLambda (3 / 8) (.finite 2) a :=
    unitCubeLambda_pos a (by norm_num) (by simp [Ch02.MultiscaleExponent.IsAdmissible])
  refine hgate.trans (mul_le_mul_of_nonneg_right ?_ hlampos.le)
  exact inv_anti₀ (gaugeGateConst_pos d) (gaugeGateConst_le_bigLambdaGateConst d)

/-! ## The pure-potential `D_h` bound along the path -/

/-- **The pure-potential `D_h` bound at a descendant, priced against the base
gauges.**  The Term A factor uses the *descendant* gauge at the base point; the
Term BC factor uses the *root* gauge at the base point. -/
theorem abs_dhPotentialForm_le_base_gauges [NeZero d] (dimension : 2 ≤ d)
    (a : CoeffOn (cubeDomain (originCube d 0))) (h : UnitCubeSkewW2Infinity d)
    (hgate : h.gradientW1Infinity ≤
      (bigLambdaGateConst d)⁻¹ * unitCubeLambda (3 / 8) (.finite 2) a)
    (F : Ch03.CoeffFamily d) (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    {k : ℤ} (hk : k ≤ (originCube d 0).scale) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d 0) k)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (p : Vec d) :
    |dhPotentialForm (cubeDomain R)
        (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
          (descendantField hk hR h.toLInfSkewMatrixFieldOn) τ)
        (descendantField hk hR h.toLInfSkewMatrixFieldOn) p| ≤
      (potCubeConstA d * Real.sqrt 2) * h.w1Infinity * vecNorm p *
          (Real.sqrt ((Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹) *
            Real.sqrt (responseJ (cubeDomain R)
              (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
                (descendantField hk hR h.toLInfSkewMatrixFieldOn) τ) p 0)) +
        potCubeConstB d * h.gradientW1Infinity *
          (2 * (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
          responseJ (cubeDomain R)
            (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
              (descendantField hk hR h.toLInfSkewMatrixFieldOn) τ) p 0 := by
  classical
  set g : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0)) :=
    h.toLInfSkewMatrixFieldOn with hgdef
  set hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)) :=
    openCubeSet_subset_of_mem_descendantsAtScale hk hR with hsubdef
  set b : CoeffOn (cubeDomain R) :=
    perturbCoeffOn (cubeDomain R) (F.coeffOn R) (descendantField hk hR g) τ with hbdef
  obtain ⟨G, hG⟩ := exists_compatibleTriadicCoeffFamily
    (perturbCoeffOn (cubeDomain (originCube d 0)) a g τ)
  have hGR : CoeffOn.AEEq (G.coeffOn R) b :=
    coeffOn_descendant_aeeq_perturbCoeffOn a g τ F G hF hG hk hR
  have hL : cubeScaleFactor R ≤ 1 :=
    cubeScaleFactor_le_one_of_mem_descendantsAtScale hk hR
  have hmain := abs_dhPotentialForm_cube_le h hsub hL b G hGR p
  set J : ℝ := responseJ (cubeDomain R) b p 0 with hJ
  have hJnn : 0 ≤ J := Ch02.responseJ_nonneg (cubeDomain R) b p 0
  have hwnn : 0 ≤ h.w1Infinity := w1Infinity_nonneg h
  have hgnn : 0 ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
  have hAnn : (0 : ℝ) ≤ potCubeConstA d := potCubeConstA_nonneg d
  have hBnn : (0 : ℝ) ≤ potCubeConstB d := potCubeConstB_nonneg d
  have hpnn : 0 ≤ vecNorm p := Ch02.vecNorm_nonneg p
  have hLRFnn : (0 : ℝ) ≤ (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ :=
    lambdaSq_inv_nonneg R F
  have hLRGnn : (0 : ℝ) ≤ (Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹ :=
    lambdaSq_inv_nonneg R G
  -- the descendant gauge at most doubles
  have hgaugeR := lambdaSq_inv_perturb_cube_le_two_mul dimension a h
    (gaugeGate_of_bigLambdaGate a h hgate) F G hF hτ0 hτ1 hG hk hR
  have hsqrtR : Real.sqrt ((Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹) ≤
      Real.sqrt 2 * Real.sqrt ((Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹) := by
    have := Real.sqrt_le_sqrt hgaugeR
    rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at this
  -- the root gauge at most doubles
  have hroot : (Ch02.lambdaSq (originCube d 0) (3 / 8) (.finite 2) G)⁻¹ =
      pathGauge a g τ := by
    rw [pathGauge, unitCubeLambda_characterization (3 / 8 : ℝ) (.finite 2) _ G hG]
  have hscaleGauge := cubeScaleFactor_mul_lambdaSq_inv_le G hk hR
  have hpathle := pathGauge_le_two_mul_of_gate dimension a h
    (gaugeGate_of_bigLambdaGate a h hgate) hτ0 hτ1
  have hBCgauge : cubeScaleFactor R * (Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹ ≤
      2 * (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ := by
    refine hscaleGauge.trans ?_
    rw [hroot]
    exact hpathle
  refine hmain.trans ?_
  refine add_le_add ?_ ?_
  · have hcoef : (0 : ℝ) ≤ potCubeConstA d * h.w1Infinity * vecNorm p := by positivity
    have hstep : Real.sqrt ((Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹) * Real.sqrt J ≤
        (Real.sqrt 2 * Real.sqrt ((Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹)) *
          Real.sqrt J :=
      mul_le_mul_of_nonneg_right hsqrtR (Real.sqrt_nonneg _)
    calc potCubeConstA d * h.w1Infinity * vecNorm p *
          (Real.sqrt ((Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹) * Real.sqrt J)
        ≤ potCubeConstA d * h.w1Infinity * vecNorm p *
            ((Real.sqrt 2 * Real.sqrt ((Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹)) *
              Real.sqrt J) := mul_le_mul_of_nonneg_left hstep hcoef
      _ = (potCubeConstA d * Real.sqrt 2) * h.w1Infinity * vecNorm p *
            (Real.sqrt ((Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹) * Real.sqrt J) := by
          ring
  · have hcoef : (0 : ℝ) ≤ potCubeConstB d * h.gradientW1Infinity := by positivity
    have hstep := mul_le_mul_of_nonneg_left hBCgauge hcoef
    have := mul_le_mul_of_nonneg_right hstep hJnn
    calc potCubeConstB d * h.gradientW1Infinity * cubeScaleFactor R *
          (Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹ * J
        = potCubeConstB d * h.gradientW1Infinity *
            (cubeScaleFactor R * (Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹) * J := by
          ring
      _ ≤ potCubeConstB d * h.gradientW1Infinity *
            (2 * (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) * J := this

/-! ## The per-cube `J`-sensitivity at the pure-potential loading -/

/-- **The pure-potential `J`-sensitivity on a descendant cube.**

The `δ`-range is the frozen one, `0 < δ ≤ 1`; the energy term carries the
*descendant* gauge, exactly as in the source display. -/
theorem responseJ_potential_cube_sensitivity [NeZero d] (dimension : 2 ≤ d)
    (a : CoeffOn (cubeDomain (originCube d 0))) (h : UnitCubeSkewW2Infinity d)
    (hgate : h.gradientW1Infinity ≤
      (bigLambdaGateConst d)⁻¹ * unitCubeLambda (3 / 8) (.finite 2) a)
    (F : Ch03.CoeffFamily d) (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    {k : ℤ} (hk : k ≤ (originCube d 0).scale) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d 0) k) (p : Vec d)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    responseJ (cubeDomain R)
        (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
          (descendantField hk hR h.toLInfSkewMatrixFieldOn) 1) p 0 ≤
      (1 + δ / 2 + 2 * (potCubeConstB d * h.gradientW1Infinity *
          (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹)) *
          responseJ (cubeDomain R) (F.coeffOn R) p 0 +
        δ⁻¹ * (potCubeConstA d ^ 2 * h.w1Infinity ^ 2 * vecNormSq p *
          (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹) := by
  classical
  set g : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0)) :=
    h.toLInfSkewMatrixFieldOn with hgdef
  set gR : LInfSkewMatrixFieldOn (cubeDomain R) := descendantField hk hR g with hgRdef
  set y : ℝ → ℝ := fun τ =>
    responseJ (cubeDomain R) (perturbCoeffOn (cubeDomain R) (F.coeffOn R) gR τ) p 0
    with hy
  set y' : ℝ → ℝ := fun τ =>
    (1 / 2 : ℝ) * dhPotentialForm (cubeDomain R)
      (perturbCoeffOn (cubeDomain R) (F.coeffOn R) gR τ) gR p with hy'
  have hderiv : ∀ τ, HasDerivAt y (y' τ) τ := fun τ =>
    hasDerivAt_responseJ_perturbCoeffOn_pair dimension (cubeDomain R)
      (F.coeffOn R) gR p 0 τ
  have hynn : ∀ τ, 0 ≤ y τ := fun τ => Ch02.responseJ_nonneg _ _ p 0
  -- the two uniform coefficients
  set LRF : ℝ := (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ with hLRF
  set Lroot : ℝ := (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ with hLroot
  have hLRFnn : 0 ≤ LRF := lambdaSq_inv_nonneg R F
  have hlampos : 0 < unitCubeLambda (3 / 8) (.finite 2) a :=
    unitCubeLambda_pos a (by norm_num) (by simp [Ch02.MultiscaleExponent.IsAdmissible])
  have hLrootnn : 0 ≤ Lroot := (inv_pos.mpr hlampos).le
  have hwnn : 0 ≤ h.w1Infinity := w1Infinity_nonneg h
  have hgnn : 0 ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
  have hAnn : (0 : ℝ) ≤ potCubeConstA d := potCubeConstA_nonneg d
  have hBnn : (0 : ℝ) ≤ potCubeConstB d := potCubeConstB_nonneg d
  have hpnn : 0 ≤ vecNorm p := Ch02.vecNorm_nonneg p
  set A : ℝ := potCubeConstA d * Real.sqrt 2 * h.w1Infinity * vecNorm p *
    Real.sqrt LRF with hA
  set β : ℝ := potCubeConstB d * h.gradientW1Infinity * Lroot with hβ
  have hAnn' : 0 ≤ A := by
    rw [hA]; positivity
  have hβnn : 0 ≤ β := by rw [hβ]; positivity
  -- the gate bounds `β`
  have hβle : β ≤ 1 / 4 := by
    have hM : 0 < bigLambdaGateConst d := bigLambdaGateConst_pos d
    have hgateinv : h.gradientW1Infinity * Lroot ≤ (bigLambdaGateConst d)⁻¹ := by
      have hstep := mul_le_mul_of_nonneg_right hgate hLrootnn
      rwa [hLroot, mul_assoc, mul_inv_cancel₀ hlampos.ne', mul_one] at hstep
    have hstep : β ≤ potCubeConstB d * (bigLambdaGateConst d)⁻¹ := by
      rw [hβ, mul_assoc]
      exact mul_le_mul_of_nonneg_left hgateinv hBnn
    refine hstep.trans ?_
    rw [inv_eq_one_div, mul_one_div, div_le_iff₀ hM]
    have hkey : 4 * potCubeConstB d ≤ bigLambdaGateConst d :=
      four_mul_potCubeConstB_le_bigLambdaGateConst d
    linarith only [hkey]
  -- the pointwise derivative bound
  have hbound : ∀ τ, (0:ℝ) ≤ τ → τ ≤ 1 →
      y' τ ≤ A ^ 2 / (4 * δ) + (β + δ / 4) * y τ := by
    intro τ hτ0 hτ1
    have hdh := abs_dhPotentialForm_le_base_gauges dimension a h hgate F hF hk hR
      hτ0 hτ1 p
    have habs : y' τ ≤ (1 / 2 : ℝ) *
        |dhPotentialForm (cubeDomain R)
          (perturbCoeffOn (cubeDomain R) (F.coeffOn R) gR τ) gR p| := by
      rw [hy']
      exact mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
    have hstep : y' τ ≤ (1 / 2 : ℝ) *
        (A * Real.sqrt (y τ) + 2 * β * y τ) := by
      refine habs.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
      refine hdh.trans (le_of_eq ?_)
      rw [hA, hβ, hy]
      ring
    have hyoung := mul_sqrt_le_young_div (A := A / 2) (y := y τ) (θ := δ / 2)
      (hynn τ) (by linarith only [hδ0])
    have hsqsub : (A / 2) ^ 2 / (2 * (δ / 2)) = A ^ 2 / (4 * δ) := by
      field_simp
      ring
    rw [hsqsub] at hyoung
    have hexpand : (1 / 2 : ℝ) * (A * Real.sqrt (y τ) + 2 * β * y τ) =
        (A / 2) * Real.sqrt (y τ) + β * y τ := by ring
    rw [hexpand] at hstep
    refine hstep.trans ?_
    have : (δ / 2) / 2 * y τ = δ / 4 * y τ := by ring
    linarith only [hyoung, this, hynn τ]
  -- integrate
  have hcnn : (0 : ℝ) ≤ β + δ / 4 := by positivity
  have hmnn : (0 : ℝ) ≤ A ^ 2 / (4 * δ) := by positivity
  have hint := le_exp_mul_add_of_hasDerivAt_le hderiv hcnn hmnn hbound
    (by norm_num : (0:ℝ) ≤ 1)
  rw [sub_zero, mul_one, mul_one] at hint
  -- exponential comparison
  have hcle : β + δ / 4 ≤ 1 / 2 := by linarith only [hβle, hδ1]
  have hexp : Real.exp (β + δ / 4) ≤ 1 + 2 * (β + δ / 4) :=
    exp_le_one_add_two_mul hcnn hcle
  have hfac : (0 : ℝ) ≤ y 0 + A ^ 2 / (4 * δ) := by
    have := hynn 0; linarith only [this, hmnn]
  have hstep1 : y 1 ≤ (1 + 2 * (β + δ / 4)) * (y 0 + A ^ 2 / (4 * δ)) :=
    hint.trans (mul_le_mul_of_nonneg_right hexp hfac)
  -- the base point
  have hy0 : y 0 = responseJ (cubeDomain R) (F.coeffOn R) p 0 := by
    rw [hy]
    refine responseJ_eq_ofAEEq ?_ p 0
    refine Filter.Eventually.of_forall fun x => ?_
    show (F.coeffOn R).toCoeffField x + (0 : ℝ) • gR.1.1 x = (F.coeffOn R).toCoeffField x
    simp
  -- the energy term
  have hA2 : A ^ 2 = 2 * (potCubeConstA d ^ 2 * h.w1Infinity ^ 2 * vecNormSq p * LRF) := by
    rw [hA]
    have h2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have hl : Real.sqrt LRF ^ 2 = LRF := Real.sq_sqrt hLRFnn
    have hp : vecNorm p ^ 2 = vecNormSq p := Ch02.vecNorm_sq_eq_vecNormSq p
    calc (potCubeConstA d * Real.sqrt 2 * h.w1Infinity * vecNorm p * Real.sqrt LRF) ^ 2
        = potCubeConstA d ^ 2 * Real.sqrt 2 ^ 2 * h.w1Infinity ^ 2 *
            vecNorm p ^ 2 * Real.sqrt LRF ^ 2 := by ring
      _ = 2 * (potCubeConstA d ^ 2 * h.w1Infinity ^ 2 * vecNormSq p * LRF) := by
          rw [h2, hl, hp]; ring
  set E : ℝ := potCubeConstA d ^ 2 * h.w1Infinity ^ 2 * vecNormSq p * LRF with hE
  have hEnn : 0 ≤ E := by
    rw [hE]
    have : (0 : ℝ) ≤ vecNormSq p := vecNormSq_nonneg p
    positivity
  have hquot : A ^ 2 / (4 * δ) = E / (2 * δ) := by
    rw [hA2]
    field_simp
    ring
  rw [hquot, hy0] at hstep1
  set Y : ℝ := responseJ (cubeDomain R) (F.coeffOn R) p 0 with hY
  have hYnn : 0 ≤ Y := Ch02.responseJ_nonneg _ _ p 0
  have hcoefle : 1 + 2 * (β + δ / 4) ≤ 2 := by linarith only [hcle]
  have hEterm : (1 + 2 * (β + δ / 4)) * (E / (2 * δ)) ≤ δ⁻¹ * E := by
    have hEd : (0 : ℝ) ≤ E / (2 * δ) := by positivity
    have := mul_le_mul_of_nonneg_right hcoefle hEd
    refine this.trans (le_of_eq ?_)
    field_simp
  have hYterm : (1 + 2 * (β + δ / 4)) * Y ≤ (1 + δ / 2 + 2 * β) * Y := by
    refine mul_le_mul_of_nonneg_right (le_of_eq ?_) hYnn
    ring
  calc y 1 ≤ (1 + 2 * (β + δ / 4)) * (Y + E / (2 * δ)) := hstep1
    _ = (1 + 2 * (β + δ / 4)) * Y + (1 + 2 * (β + δ / 4)) * (E / (2 * δ)) := by ring
    _ ≤ (1 + δ / 2 + 2 * β) * Y + δ⁻¹ * E := add_le_add hYterm hEterm

end

end Algsuperdiff.Section24.Sensitivity.Provider.BigLambda
