/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.HomogBridge.Bridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.LambdaUnconditional.CubeGauge
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional.MesoscaleArithmetic

/-!
# Aggregation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Mesoscale aggregation for the unconditional response estimate

Source: ABK26, the aggregation half of the `J` statement of
`l.J.sensitivity.no.conditions`.

The source proof of `e.J.sensitivity.no.conditions` has two halves.

* A **per-mesoscopic-cube** conditional estimate: on every triadic cube `R` of
  the mesoscopic depth `H`, the response of the perturbed field at the loading
  `((mu sigma0)^{-1/2} e, (mu sigma0)^{1/2} e)` is bounded by `6 mu^{-1}` times
  the response of the base field at the `sigma0`-normalized loading, plus three
  error families carrying the `R`-local coarse gauge `lambda_{3/8,2}^{-1}(R;a)`.
* An **aggregation**: subadditivity at depth `H`, the homogenization-error
  bridge for the main term, the descendant scaling of the coarse gauge for the
  gauge terms, and the Young/`min` bookkeeping of
  `Provider.Mesoscale.ScaleSelection` for the gradient terms.

This module contains **only the aggregation half**, in the exact shape of the
frozen conclusion.  The per-cube estimate enters as the hypothesis `hcube` of
`responseJ_le_frozen_of_mesoscale_cube_bound`; nothing here proves or assumes
any part of it.  The gauge-free arithmetic is in
`Provider.ResponseUnconditional.MesoscaleArithmetic`.

## Consumption points

1. **`hcube`.**  The per-mesoscopic-cube conditional estimate.  It is written
   with the root family `F` on the right-hand side (so the main term is exactly
   the quantity fed to `Provider.HomogBridge.Bridge`), the `R`-local coarse
   gauge `lambda_{3/8,2}^{-1}(R; F)`, and the constant scale factor `3^{-2H}` of
   the mesoscopic depth (which equals `cubeScaleFactor R ^ 2` on every cube of
   `descendantsAtDepth (originCube d 0) H`).
2. **`hV`.**  An abstract nonnegative *value budget* `V` whose depth-`H`
   descendant average is at most `h.valueL2 ^ 2`.  For the concrete `D_h` route
   `V R` is the normalized `L^2` average of `|h|^2` over `R`, and `hV` is then
   the exact tower identity
   `cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn`.

Every declaration in this module is an internal helper for the Section 2.4
sensitivity providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.HomogBridge
open Algsuperdiff.Section24.Sensitivity.Provider.LambdaUnconditional
open Algsuperdiff.Section24.Sensitivity.Provider.Mesoscale
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## The pointwise fold of the per-cube right-hand side

Pure real arithmetic: the three gauge-carrying families of the per-cube estimate
are bounded by their values at the uniform gauge bound `WL`, leaving only the
main term and the value budget inside the descendant average. -/

/-- Replacing the `R`-local gauge `ψ` by its uniform bound `WL` in the three
error families of the per-cube estimate. -/
private theorem cube_gauge_fold {K μi σi σ ψ WL V D2 g Mu : ℝ}
    (hK : 0 ≤ K) (hμi : 0 ≤ μi) (hσi : 0 ≤ σi) (hσ : 0 ≤ σ)
    (hψ : 0 ≤ ψ) (hWL : ψ ≤ WL) (hV : 0 ≤ V) (hD2 : 0 ≤ D2) (hMu : 0 ≤ Mu) :
    K * μi * Mu * σ * ψ + K * μi * σi * ψ * (V + D2 * g ^ 2) +
        K * D2 * ψ ^ 2 * g ^ 2 ≤
      K * μi * σi * WL * V +
        (K * μi * Mu * σ * WL + K * μi * σi * WL * (D2 * g ^ 2) +
          K * D2 * WL ^ 2 * g ^ 2) := by
  have hg2 : (0 : ℝ) ≤ g ^ 2 := sq_nonneg g
  have hWLnn : (0 : ℝ) ≤ WL := le_trans hψ hWL
  have hc1 : (0 : ℝ) ≤ K * μi * Mu * σ := by positivity
  have hc2 : (0 : ℝ) ≤ K * μi * σi := by positivity
  have hc3 : (0 : ℝ) ≤ K * D2 * g ^ 2 := by positivity
  have t1 : (K * μi * Mu * σ) * ψ ≤ (K * μi * Mu * σ) * WL :=
    mul_le_mul_of_nonneg_left hWL hc1
  have t2 : (K * μi * σi) * (ψ * V) ≤ (K * μi * σi) * (WL * V) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hWL hV) hc2
  have t3 : (K * μi * σi) * (ψ * (D2 * g ^ 2)) ≤ (K * μi * σi) * (WL * (D2 * g ^ 2)) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hWL (mul_nonneg hD2 hg2)) hc2
  have hsq : ψ ^ 2 ≤ WL ^ 2 := by nlinarith
  have t4 : (K * D2 * g ^ 2) * ψ ^ 2 ≤ (K * D2 * g ^ 2) * WL ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hc3
  calc K * μi * Mu * σ * ψ + K * μi * σi * ψ * (V + D2 * g ^ 2) +
        K * D2 * ψ ^ 2 * g ^ 2
      = (K * μi * Mu * σ) * ψ + (K * μi * σi) * (ψ * V) +
          (K * μi * σi) * (ψ * (D2 * g ^ 2)) + (K * D2 * g ^ 2) * ψ ^ 2 := by ring
    _ ≤ (K * μi * Mu * σ) * WL + (K * μi * σi) * (WL * V) +
          (K * μi * σi) * (WL * (D2 * g ^ 2)) + (K * D2 * g ^ 2) * WL ^ 2 :=
        add_le_add (add_le_add (add_le_add t1 t2) t3) t4
    _ = K * μi * σi * WL * V +
          (K * μi * Mu * σ * WL + K * μi * σi * WL * (D2 * g ^ 2) +
            K * D2 * WL ^ 2 * g ^ 2) := by ring

/-! ## The uniform mesoscopic gauge bound -/

/-- **The descendant scaling of the coarse gauge at the mesoscopic depth.**  For
every triadic cube `R` of depth `H` below the unit cube,

```
λ_{3/8,2}^{-1}(R; a) ≤ λ_{s,2}^{-1}(R; a) ≤ 3^{2 s H} λ_{s,2}^{-1}(□₀; a) .
```

This is the display of ABK26; the first step uses `2 s ≤ 1/2 < 3/4`. -/
theorem lambdaSq_inv_le_rpow_mul_unitCubeLambda_inv [NeZero d]
    (a : CoeffOn (cubeDomain (originCube d 0))) (F : TriadicCoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 4) (H : ℕ)
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d 0) H) :
    (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ ≤
      Real.rpow (3 : ℝ) (2 * s * (H : ℝ)) * (unitCubeLambda s (.finite 2) a)⁻¹ := by
  classical
  have hscale0 : ((originCube d 0).scale) = (0 : ℤ) := rfl
  set k : ℤ := (originCube d 0).scale - (H : ℤ) with hkdef
  have hk : k ≤ (originCube d 0).scale := by rw [hkdef]; omega
  have hRk : R ∈ descendantsAtScale (originCube d 0) k := by
    rw [hkdef]
    exact mem_descendantsAtScale_sub_nat_of_mem_descendantsAtDepth hR
  have hposs : 0 < Ch02.lambdaSq R s (.finite 2) F :=
    Ch02.lambdaSq_pos R F hs0 isAdmissible_finite_two
  have hmono : Ch02.lambdaSq R s (.finite 2) F ≤
      Ch02.lambdaSq R (3 / 8) (.finite 2) F :=
    Ch02.lambdaSq_mono R F hs0 (by linarith) isAdmissible_finite_two
  have hinv : (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ ≤
      (Ch02.lambdaSq R s (.finite 2) F)⁻¹ := by gcongr
  have hloc := Ch02.maxDescendant_lambdaSq_inv_le (originCube d 0) F hk hs0
    isAdmissible_finite_two
  have hmem : (Ch02.lambdaSq R s (.finite 2) F)⁻¹ ≤
      Ch02.maxDescendantLowerEllipticityInvAtScale (originCube d 0) k s (.finite 2) F :=
    le_finsetSupReal_of_mem _ (fun T => (Ch02.lambdaSq T s (.finite 2) F)⁻¹) hRk
  have hweight : Ch02.multiscaleDescendantWeight (originCube d 0) k s =
      Real.rpow (3 : ℝ) (2 * s * (H : ℝ)) := by
    rw [Ch02.multiscaleDescendantWeight]
    congr 1
    rw [hkdef, hscale0]
    push_cast
    ring
  have hroot : (unitCubeLambda s (.finite 2) a)⁻¹ =
      (Ch02.lambdaSq (originCube d 0) s (.finite 2) F)⁻¹ := by
    rw [unitCubeLambda_characterization s (.finite 2) a F hF]
  rw [hroot]
  refine hinv.trans ((hmem.trans hloc).trans (le_of_eq ?_))
  rw [hweight]

/-! ## The aggregation -/

/-- **The mesoscale aggregation of the unconditional response estimate.**

Given the per-mesoscopic-cube conditional estimate `hcube` at the mesoscopic
depth `H = mesoscaleDepth s (1 + C₀ ‖∇h‖ λ_{s,2}^{-1})`, the four families of
terms aggregate to exactly the four terms of the frozen conclusion
`Algsuperdiff.Frozen.Section24.responseJ_sensitivity_unconditional`, with the
explicit constant `aggConst C₀ K`.

This is ABK26. -/
theorem responseJ_le_frozen_of_mesoscale_cube_bound [NeZero d]
    (a : CoeffOn (cubeDomain (originCube d 0))) (hgrad : UnitCubeSkewW2Infinity d)
    (F G : TriadicCoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    (hG : CoeffOn.AEEq (G.coeffOn (originCube d 0))
      (perturbCoeffOn (cubeDomain (originCube d 0)) a
        hgrad.toLInfSkewMatrixFieldOn 1))
    {s t μ σ0 C₀ K : ℝ} {e : Vec d}
    (hs0 : 0 < s) (hs : s ≤ 1 / 4) (ht0 : 0 < t) (ht : t ≤ 1 / 4)
    (hμ : 0 < μ) (hσ0 : 0 < σ0) (he : vecNorm e = 1)
    (hC₀ : 1 ≤ C₀) (hK : 0 ≤ K)
    (V : TriadicCube d → ℝ) (hV0 : ∀ R, 0 ≤ V R)
    (hV : descendantsAverage (originCube d 0)
        (mesoscaleDepth s (1 + C₀ * (hgrad.gradientW1Infinity *
          (unitCubeLambda s (.finite 2) a)⁻¹))) V ≤ hgrad.valueL2 ^ 2)
    (hcube : ∀ R ∈ descendantsAtDepth (originCube d 0)
        (mesoscaleDepth s (1 + C₀ * (hgrad.gradientW1Infinity *
          (unitCubeLambda s (.finite 2) a)⁻¹))),
      responseJ (cubeDomain R) (G.coeffOn R)
          ((Real.sqrt (μ * σ0))⁻¹ • e) (Real.sqrt (μ * σ0) • e) ≤
        6 * μ⁻¹ * responseJ (cubeDomain R) (F.coeffOn R)
            ((Real.sqrt σ0)⁻¹ • e) (Real.sqrt σ0 • e) +
          K * μ⁻¹ * (μ - 1) ^ 2 * σ0 *
            (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ +
          K * μ⁻¹ * σ0⁻¹ * (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ *
            (V R + Real.rpow (3 : ℝ) (-(2 * ((mesoscaleDepth s
              (1 + C₀ * (hgrad.gradientW1Infinity *
                (unitCubeLambda s (.finite 2) a)⁻¹)) : ℕ) : ℝ))) *
              hgrad.gradientW1Infinity ^ 2) +
          K * Real.rpow (3 : ℝ) (-(2 * ((mesoscaleDepth s
              (1 + C₀ * (hgrad.gradientW1Infinity *
                (unitCubeLambda s (.finite 2) a)⁻¹)) : ℕ) : ℝ))) *
            (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ ^ 2 *
            hgrad.gradientW1Infinity ^ 2) :
    responseJ (cubeDomain (originCube d 0))
        (perturbCoeffOn (cubeDomain (originCube d 0)) a
          hgrad.toLInfSkewMatrixFieldOn 1)
        ((Real.sqrt (μ * σ0))⁻¹ • e) (Real.sqrt (μ * σ0) • e) ≤
      aggConst C₀ K * μ⁻¹ * Real.rpow
          (1 + hgrad.gradientW1Infinity * (unitCubeLambda s (.finite 2) a)⁻¹)
          (2 * t / (1 - 2 * s)) *
          (unitCubeHomogenizationError t (.finite 2) (.finite 2) a
            (scalarMatrix (d := d) σ0)) ^ 2 +
        aggConst C₀ K * μ⁻¹ * σ0 * (unitCubeLambda s (.finite 2) a)⁻¹ *
          Real.rpow
            (1 + hgrad.gradientW1Infinity * (unitCubeLambda s (.finite 2) a)⁻¹)
            (2 * s / (1 - 2 * s)) *
          (σ0⁻¹ ^ 2 * hgrad.valueL2 ^ 2 + (μ - 1) ^ 2) +
        aggConst C₀ K * μ⁻¹ ^ 2 * σ0⁻¹ ^ 2 * hgrad.gradientW1Infinity ^ 2 +
        aggConst C₀ K *
          min 1 (hgrad.gradientW1Infinity *
            (unitCubeLambda s (.finite 2) a)⁻¹) ^ 2 := by
  classical
  set gr : ℝ := hgrad.gradientW1Infinity with hgrdef
  set L : ℝ := (unitCubeLambda s (.finite 2) a)⁻¹ with hLdef
  set X : ℝ := gr * L with hXdef
  set H : ℕ := mesoscaleDepth s (1 + C₀ * X) with hHdef
  set E : ℝ := unitCubeHomogenizationError t (.finite 2) (.finite 2) a
    (scalarMatrix (d := d) σ0) with hEdef
  set P : Vec d := (Real.sqrt (μ * σ0))⁻¹ • e with hPdef
  set Q : Vec d := Real.sqrt (μ * σ0) • e with hQdef
  set Ψ : TriadicCube d → ℝ := fun R => (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹
    with hΨdef
  set Jb : TriadicCube d → ℝ := fun R => responseJ (cubeDomain R) (F.coeffOn R)
    ((Real.sqrt σ0)⁻¹ • e) (Real.sqrt σ0 • e) with hJbdef
  set D2 : ℝ := Real.rpow (3 : ℝ) (-(2 * (H : ℝ))) with hD2def
  set W : ℝ := Real.rpow (3 : ℝ) (2 * s * (H : ℝ)) with hWdef
  set Wt : ℝ := Real.rpow (3 : ℝ) (2 * t * (H : ℝ)) with hWtdef
  have hC₀pos : (0 : ℝ) < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hgrnn : 0 ≤ gr :=
    Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz.gradientW1Infinity_nonneg
      hgrad
  have hLnn : 0 ≤ L := by
    rw [hLdef, unitCubeLambda_characterization s (.finite 2) a F hF]
    exact inv_nonneg.mpr (Ch02.lambdaSq_nonneg _ F hs0 isAdmissible_finite_two)
  have hXnn : 0 ≤ X := mul_nonneg hgrnn hLnn
  have hμinv : (0 : ℝ) < μ⁻¹ := inv_pos.mpr hμ
  have hσ0inv : (0 : ℝ) < σ0⁻¹ := inv_pos.mpr hσ0
  have hΨnn : ∀ R, 0 ≤ Ψ R := fun R =>
    inv_nonneg.mpr (Ch02.lambdaSq_nonneg R F (by norm_num) isAdmissible_finite_two)
  have hWnn : (0 : ℝ) ≤ W := Real.rpow_nonneg (by norm_num) _
  have hD2nn : (0 : ℝ) ≤ D2 := Real.rpow_nonneg (by norm_num) _
  have hgauge : ∀ R ∈ descendantsAtDepth (originCube d 0) H, Ψ R ≤ W * L :=
    fun R hR => lambdaSq_inv_le_rpow_mul_unitCubeLambda_inv a F hF hs0 hs H hR
  set c0 : ℝ := K * μ⁻¹ * (μ - 1) ^ 2 * σ0 * (W * L) +
    K * μ⁻¹ * σ0⁻¹ * (W * L) * (D2 * gr ^ 2) +
    K * D2 * (W * L) ^ 2 * gr ^ 2 with hc0def
  -- Step 1: subadditivity plus the pointwise per-cube bound
  have hsub := responseJOnCube_le_descendantsAverage_responseJ G (originCube d 0) H P Q
  have hroot : responseJ (cubeDomain (originCube d 0)) (G.coeffOn (originCube d 0)) P Q =
      responseJ (cubeDomain (originCube d 0))
        (perturbCoeffOn (cubeDomain (originCube d 0)) a
          hgrad.toLInfSkewMatrixFieldOn 1) P Q := responseJ_eq_ofAEEq hG P Q
  have hpoint : ∀ R ∈ descendantsAtDepth (originCube d 0) H,
      responseJ (cubeDomain R) (G.coeffOn R) P Q ≤
        6 * μ⁻¹ * Jb R + K * μ⁻¹ * σ0⁻¹ * (W * L) * V R + c0 := by
    intro R hR
    refine (hcube R hR).trans ?_
    have hfold := cube_gauge_fold (K := K) (μi := μ⁻¹) (σi := σ0⁻¹) (σ := σ0)
      (ψ := Ψ R) (WL := W * L) (V := V R) (D2 := D2) (g := gr) (Mu := (μ - 1) ^ 2)
      hK hμinv.le hσ0inv.le hσ0.le (hΨnn R) (hgauge R hR) (hV0 R) hD2nn (sq_nonneg _)
    rw [hc0def]
    linarith [hfold]
  -- Step 2: average the pointwise bound
  have haverage : descendantsAverage (originCube d 0) H
      (fun R => responseJ (cubeDomain R) (G.coeffOn R) P Q) ≤
      6 * μ⁻¹ * descendantsAverage (originCube d 0) H Jb +
        K * μ⁻¹ * σ0⁻¹ * (W * L) * descendantsAverage (originCube d 0) H V + c0 := by
    refine (descendantsAverage_le_descendantsAverage (originCube d 0) H hpoint).trans
      (le_of_eq ?_)
    rw [show (fun R => 6 * μ⁻¹ * Jb R + K * μ⁻¹ * σ0⁻¹ * (W * L) * V R + c0) =
        (fun R => (6 * μ⁻¹ * Jb R + K * μ⁻¹ * σ0⁻¹ * (W * L) * V R) + c0) from rfl]
    rw [descendantsAverage_add, descendantsAverage_add, descendantsAverage_const,
      descendantsAverage_mul_left, descendantsAverage_mul_left]
  -- Step 3: the homogenization-error bridge and the value budget
  have hbridge : descendantsAverage (originCube d 0) H Jb ≤ Wt * E ^ 2 :=
    descendantsAverage_responseJ_scalarLoading_le_rpow_mul_unitCubeHomogenizationError_sq
      a F hF ht0 hσ0 he H
  have hmain : responseJ (cubeDomain (originCube d 0))
      (perturbCoeffOn (cubeDomain (originCube d 0)) a
        hgrad.toLInfSkewMatrixFieldOn 1) P Q ≤
      6 * μ⁻¹ * (Wt * E ^ 2) +
        K * μ⁻¹ * σ0⁻¹ * (W * L) * hgrad.valueL2 ^ 2 + c0 := by
    rw [← hroot]
    refine hsub.trans (haverage.trans ?_)
    have h1 : 6 * μ⁻¹ * descendantsAverage (originCube d 0) H Jb ≤
        6 * μ⁻¹ * (Wt * E ^ 2) :=
      mul_le_mul_of_nonneg_left hbridge (by positivity)
    have h2 : K * μ⁻¹ * σ0⁻¹ * (W * L) * descendantsAverage (originCube d 0) H V ≤
        K * μ⁻¹ * σ0⁻¹ * (W * L) * hgrad.valueL2 ^ 2 :=
      mul_le_mul_of_nonneg_left hV (by positivity)
    linarith [h1, h2]
  refine hmain.trans ?_
  rw [hc0def]
  -- Step 4: the gauge-free arithmetic fold
  have hWtle : Wt ≤ 3 * C₀ * Real.rpow (1 + X) (2 * t / (1 - 2 * s)) := by
    rw [hWtdef, hHdef]
    exact three_rpow_two_mul_depth_le_const_mul_rpow hs0 hs ht0.le ht hXnn hC₀
  have hWle : W ≤ 3 * C₀ * Real.rpow (1 + X) (2 * s / (1 - 2 * s)) := by
    rw [hWdef, hHdef]
    exact three_rpow_two_mul_depth_le_const_mul_rpow hs0 hs hs0.le hs hXnn hC₀
  have hDm1 : Real.rpow (3 : ℝ) (-(2 * ((1 - 2 * s) * (H : ℝ)))) ≤ 1 :=
    three_rpow_neg_two_one_sub_two_mul_le_one hs H
  have hD2W : D2 * W ≤ Real.rpow (3 : ℝ) (-(2 * ((1 - 2 * s) * (H : ℝ)))) := by
    rw [hD2def, hWdef]
    exact three_rpow_neg_two_mul_rpow_le hs0.le H
  have hD2W2 : D2 * W ^ 2 = Real.rpow (3 : ℝ) (-(2 * ((1 - 2 * s) * (H : ℝ)))) := by
    rw [hD2def, hWdef]
    exact three_rpow_neg_two_mul_rpow_sq_eq H
  have hminX : X ^ 2 * Real.rpow (3 : ℝ) (-(2 * ((1 - 2 * s) * (H : ℝ)))) ≤
      (C₀ ^ 2)⁻¹ * (max 1 (C₀ ^ 2) * min 1 X ^ 2) := by
    rw [hHdef]
    exact sq_mul_damping_le_min hs0 hs hXnn hC₀
  have hYt0 : (0 : ℝ) ≤ Real.rpow (1 + X) (2 * t / (1 - 2 * s)) :=
    Real.rpow_nonneg (by linarith) _
  have hYs0 : (0 : ℝ) ≤ Real.rpow (1 + X) (2 * s / (1 - 2 * s)) :=
    Real.rpow_nonneg (by linarith) _
  have hfold := mesoscale_fold (μ := μ) (σ0 := σ0) (C₀ := C₀) (K := K) (L := L)
    (gr := gr) (val := hgrad.valueL2) (E := E) (Wt := Wt) (W := W) (D2 := D2)
    (Dm := Real.rpow (3 : ℝ) (-(2 * ((1 - 2 * s) * (H : ℝ)))))
    (Yt := Real.rpow (1 + X) (2 * t / (1 - 2 * s)))
    (Ys := Real.rpow (1 + X) (2 * s / (1 - 2 * s)))
    hμ hσ0 hC₀ hK hLnn hWnn hD2nn hYt0 hYs0 hWtle hWle hDm1 hD2W hD2W2
    (by rw [hXdef] at hminX; exact hminX)
  rw [hXdef] at hfold
  linarith [hfold]

end

end Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional
