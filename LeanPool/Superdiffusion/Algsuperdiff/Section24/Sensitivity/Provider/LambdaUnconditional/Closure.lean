/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.LambdaUnconditional.CubeRatio
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Mesoscale.LambdaAssembly

/-!
# Closure

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The unconditional `lambda_{t,q}` sensitivity provider

Source: ABK26, the `lambda` half of `l.J.sensitivity.no.conditions`.

This module discharges the single consumption point `hdeep` of
`Provider.Mesoscale.LambdaAssembly.unitCubeLambda_inv_le_of_mesoscale_descendant_ratio`
and assembles the provider form of the frozen target
`Algsuperdiff.Frozen.Section24.lambda_sensitivity_unconditional`.

## The mesoscopic depth kills the smallness gate

With `X = C ‖∇h‖ λ_{s,2}^{-1}(□₀; a)` and `h = mesoscaleDepth s (1 + X)`, the
scale-selection arithmetic of `Provider.Mesoscale.ScaleSelection` gives
`X · 3^{-(1-2s)h} ≤ 1`.  On a triadic descendant `R` of the unit cube at scale
`k ≤ -h`, the sharp descendant scaling of the coarse gauge gives

```
|R| λ_{3/8,2}^{-1}(R; a) ≤ |R| λ_{s,2}^{-1}(R; a) ≤ 3^{(1-2s)k} λ_{s,2}^{-1}(□₀; a)
                        ≤ 3^{-(1-2s)h} λ_{s,2}^{-1}(□₀; a) ,
```

using `2s ≤ 1/2 < 3/4` for the first step (`Book.Ch02.lambdaSq_mono`).  With
`C = 4 max{1, C_flux(d)}` this is exactly the mesoscopic smallness condition
`4 K_R λ_{3/8,2}^{-1}(R; a) ≤ 1/2` of the conditional per-cube estimate.  No
hypothesis on `X` is needed: when `X` is large the mesoscopic depth is large,
and the depth is chosen so that the estimate closes for every `X ≥ 0`.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.LambdaUnconditional

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.Lambda
open Algsuperdiff.Section24.Sensitivity.Provider.Mesoscale
open Algsuperdiff.Section24.Sensitivity.Provider.Multiscale

noncomputable section

variable {d : ℕ}

/-- CoarseGraining writes multiscale weights with explicit `Real.rpow`. -/
private theorem rpow_eq_pow (x y : ℝ) : Real.rpow x y = x ^ y := rfl

/-! ## The sharp descendant scaling at the unit cube -/

/-- **The sharp descendant scaling of the coarse gauge at the unit cube.**  The
scale-normalized gauge of a triadic descendant at scale `k ≤ 0` gains exactly
the factor `3^{(1-2s) k}`.  This is the display of ABK26. -/
theorem cubeScaleFactor_mul_lambdaSq_inv_le_rpow [NeZero d]
    (F : TriadicCoeffFamily d) {s : ℝ} {q : Ch02.MultiscaleExponent} (hs0 : 0 < s)
    (hq : q.IsAdmissible) {k : ℤ} (hk : k ≤ (originCube d 0).scale)
    {R : TriadicCube d} (hR : R ∈ descendantsAtScale (originCube d 0) k) :
    cubeScaleFactor R * (Ch02.lambdaSq R s q F)⁻¹ ≤
      Real.rpow (3 : ℝ) ((1 - 2 * s) * (k : ℝ)) *
        (Ch02.lambdaSq (originCube d 0) s q F)⁻¹ := by
  have hloc := Ch02.maxDescendant_lambdaSq_inv_le (originCube d 0) F hk hs0 hq
  have hmem : (Ch02.lambdaSq R s q F)⁻¹ ≤
      Ch02.maxDescendantLowerEllipticityInvAtScale (originCube d 0) k s q F :=
    le_finsetSupReal_of_mem _ (fun T => (Ch02.lambdaSq T s q F)⁻¹) hR
  have hchain : (Ch02.lambdaSq R s q F)⁻¹ ≤
      Ch02.multiscaleDescendantWeight (originCube d 0) k s *
        (Ch02.lambdaSq (originCube d 0) s q F)⁻¹ := hmem.trans hloc
  have hLnn : (0 : ℝ) ≤ cubeScaleFactor R := (cubeScaleFactor_pos_cube R).le
  have hrootnn : (0 : ℝ) ≤ (Ch02.lambdaSq (originCube d 0) s q F)⁻¹ :=
    inv_nonneg.mpr (Ch02.lambdaSq_nonneg _ F hs0 hq)
  have hfac : cubeScaleFactor R = Real.rpow (3 : ℝ) ((k : ℝ)) := by
    rw [cubeScaleFactor_eq_rpow, scale_eq_of_mem_descendantsAtScale hR]
  have hweight : Ch02.multiscaleDescendantWeight (originCube d 0) k s =
      Real.rpow (3 : ℝ) (-(2 * s) * (k : ℝ)) := by
    rw [Ch02.multiscaleDescendantWeight]
    congr 1
    have h0 : ((originCube d 0).scale : ℤ) = 0 := rfl
    push_cast [h0]
    ring
  have hprod : cubeScaleFactor R *
      Ch02.multiscaleDescendantWeight (originCube d 0) k s =
      Real.rpow (3 : ℝ) ((1 - 2 * s) * (k : ℝ)) := by
    rw [hfac, hweight]
    simp only [rpow_eq_pow]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  calc cubeScaleFactor R * (Ch02.lambdaSq R s q F)⁻¹
      ≤ cubeScaleFactor R *
          (Ch02.multiscaleDescendantWeight (originCube d 0) k s *
            (Ch02.lambdaSq (originCube d 0) s q F)⁻¹) :=
        mul_le_mul_of_nonneg_left hchain hLnn
    _ = (cubeScaleFactor R * Ch02.multiscaleDescendantWeight (originCube d 0) k s) *
          (Ch02.lambdaSq (originCube d 0) s q F)⁻¹ := by ring
    _ = Real.rpow (3 : ℝ) ((1 - 2 * s) * (k : ℝ)) *
          (Ch02.lambdaSq (originCube d 0) s q F)⁻¹ := by rw [hprod]

/-! ## The dimensional constant -/

/-- The constant of the frozen unconditional estimate:
`C = 4 max{1, C_flux(d)}`, where `C_flux(d)` is the constant of the pure-flux
`D_h` bound of `Provider.Lambda.CubeBound`. -/
def unconditionalConst (d : ℕ) : ℝ  := 4 * max 1 (fluxCubeConst d)

theorem unconditionalConst_pos (d : ℕ) : 0 < unconditionalConst d  := by
  have : (1 : ℝ) ≤ max 1 (fluxCubeConst d) := le_max_left _ _
  unfold unconditionalConst
  linarith

theorem fluxCubeConst_le_max (d : ℕ) : fluxCubeConst d ≤ max 1 (fluxCubeConst d)  := le_max_right
  _ _

/-- The frozen coarse gauge is nonnegative. -/
theorem unitCubeLambda_inv_nonneg [NeZero d]
    (a : CoeffOn (cubeDomain (originCube d 0))) {s : ℝ}
    {q : Ch02.MultiscaleExponent} (hs : 0 < s) (hq : q.IsAdmissible) :
    0 ≤ (unitCubeLambda s q a)⁻¹ := by
  obtain ⟨F, hF⟩ :=
    Algsuperdiff.Section24.UnitCubeMultiscale.exists_compatibleTriadicCoeffFamily a
  rw [unitCubeLambda_characterization s q a F hF]
  exact inv_nonneg.mpr (Ch02.lambdaSq_nonneg _ F hs hq)

/-! ## Deep-cube smallness -/

/-- **The smallness condition holds at every deep cube, unconditionally.**  At
every triadic descendant of the unit cube of scale at most `-h`, with `h` the
mesoscopic depth attached to the dimensionless parameter
`X = C ‖∇h‖ λ_{s,2}^{-1}(□₀; a)`, the dimensionless quantity governing the
conditional per-cube estimate is at most `1/2`.

This is the verification step of ABK26.  No hypothesis on `X` is assumed: the
mesoscopic depth grows with `X` exactly fast enough. -/
theorem deep_cube_smallness [NeZero d]
    (a : CoeffOn (cubeDomain (originCube d 0))) (h : UnitCubeSkewW2Infinity d)
    (F : TriadicCoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 4) {k : ℤ}
    (hkH : k ≤ (originCube d 0).scale -
      ((mesoscaleDepth s (1 + unconditionalConst d * h.gradientW1Infinity *
        (unitCubeLambda s (.finite 2) a)⁻¹) : ℕ) : ℤ))
    {R : TriadicCube d} (hR : R ∈ descendantsAtScale (originCube d 0) k) :
    4 * mesoFluxConst d h R * cubeGauge R a h.toLInfSkewMatrixFieldOn 0 ≤ 1 / 2 := by
  classical
  set g : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0)) :=
    h.toLInfSkewMatrixFieldOn with hgdef
  have hgnn : 0 ≤ h.gradientW1Infinity :=
    Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz.gradientW1Infinity_nonneg h
  have hCpos : 0 < unconditionalConst d := unconditionalConst_pos d
  have hLnn : (0 : ℝ) ≤ (unitCubeLambda s (.finite 2) a)⁻¹ :=
    unitCubeLambda_inv_nonneg a hs0 isAdmissible_finite_two
  set L : ℝ := (unitCubeLambda s (.finite 2) a)⁻¹ with hLdef
  set u : ℝ := 1 + unconditionalConst d * h.gradientW1Infinity * L with hudef
  have hu1 : 1 ≤ u := by
    have : 0 ≤ unconditionalConst d * h.gradientW1Infinity * L := by positivity
    rw [hudef]; linarith
  set H : ℕ := mesoscaleDepth s u with hHdef
  have hscale0 : ((originCube d 0).scale) = (0 : ℤ) := rfl
  have hHnn : (0 : ℤ) ≤ (H : ℤ) := Int.natCast_nonneg H
  have hkroot : k ≤ (originCube d 0).scale := by rw [hscale0] at hkH ⊢; omega
  have hLeq : L = (Ch02.lambdaSq (originCube d 0) s (.finite 2) F)⁻¹ := by
    rw [hLdef, unitCubeLambda_characterization s (.finite 2) a F hF]
  -- the mesoscopic gauge at the base point
  have hg0 : cubeGauge R a g 0 = (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ :=
    (cubeGauge_zero_eq_of_family a g hkroot hR F hF).symm
  have hposs : 0 < Ch02.lambdaSq R s (.finite 2) F :=
    Ch02.lambdaSq_pos R F hs0 isAdmissible_finite_two
  have hmono : Ch02.lambdaSq R s (.finite 2) F ≤
      Ch02.lambdaSq R (3 / 8) (.finite 2) F :=
    Ch02.lambdaSq_mono R F hs0 (by linarith) isAdmissible_finite_two
  have hinv : (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ ≤
      (Ch02.lambdaSq R s (.finite 2) F)⁻¹ := by
    gcongr
  have hdesc := cubeScaleFactor_mul_lambdaSq_inv_le_rpow F hs0
    isAdmissible_finite_two hkroot hR
  set W : ℝ := Real.rpow (3 : ℝ) (-((1 - 2 * s) * (H : ℝ))) with hWdef
  have hWnn : (0 : ℝ) ≤ W := Real.rpow_nonneg (by norm_num) _
  have hWmono : Real.rpow (3 : ℝ) ((1 - 2 * s) * (k : ℝ)) ≤ W := by
    rw [hWdef]
    simp only [rpow_eq_pow]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hkle : (k : ℝ) ≤ -(H : ℝ) := by
      have hkz : k ≤ -(H : ℤ) := by rw [hscale0] at hkH; omega
      exact_mod_cast hkz
    nlinarith [hs, hs0]
  have hkey : (u - 1) * W ≤ 1 := by
    rw [hWdef, hHdef]
    exact sub_one_mul_three_rpow_neg_mesoscaleDepth_le_one hs0 hs hu1
  -- the gauge chain of the source display
  have hchain : cubeScaleFactor R * cubeGauge R a g 0 ≤ W * L := by
    rw [hg0]
    calc cubeScaleFactor R * (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹
        ≤ cubeScaleFactor R * (Ch02.lambdaSq R s (.finite 2) F)⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (cubeScaleFactor_pos_cube R).le
      _ ≤ Real.rpow (3 : ℝ) ((1 - 2 * s) * (k : ℝ)) *
            (Ch02.lambdaSq (originCube d 0) s (.finite 2) F)⁻¹ := hdesc
      _ ≤ W * L := by
          rw [hLeq]
          exact mul_le_mul_of_nonneg_right hWmono
            (inv_nonneg.mpr (Ch02.lambdaSq_nonneg _ F hs0 isAdmissible_finite_two))
  -- assemble
  have hP : (0 : ℝ) ≤ 2 * fluxCubeConst d * h.gradientW1Infinity := by
    have := fluxCubeConst_nonneg d
    positivity
  have heq : 4 * mesoFluxConst d h R * cubeGauge R a g 0 =
      (2 * fluxCubeConst d * h.gradientW1Infinity) *
        (cubeScaleFactor R * cubeGauge R a g 0) := by
    unfold mesoFluxConst
    ring
  rw [heq]
  refine (mul_le_mul_of_nonneg_left hchain hP).trans ?_
  have hu1' : u - 1 = unconditionalConst d * h.gradientW1Infinity * L := by
    rw [hudef]; ring
  have hd : (0 : ℝ) ≤
      (max 1 (fluxCubeConst d) - fluxCubeConst d) * h.gradientW1Infinity * L * W :=
    mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr (fluxCubeConst_le_max d)) hgnn)
      hLnn) hWnn
  have hfinal : (2 * fluxCubeConst d * h.gradientW1Infinity) * (W * L) ≤
      (1 / 2 : ℝ) * ((u - 1) * W) := by
    rw [hu1']
    unfold unconditionalConst
    nlinarith [hd]
  have hhalf : (1 / 2 : ℝ) * ((u - 1) * W) ≤ 1 / 2 := by linarith [hkey]
  linarith [hfinal, hhalf]

/-! ## The provider -/

/-- **Unconditional sensitivity of `lambda_{t,q}`.**

This is the provider form of the frozen target
`Algsuperdiff.Frozen.Section24.lambda_sensitivity_unconditional`, with exactly
the frozen binders: the full range `0 < s, t ≤ 1/4`, every admissible `q`
including the endpoint `q = infinity`, the literal constant `6`, the exponent
`2t/(1-2s)`, and no smallness gate. -/
theorem lambda_sensitivity_unconditional {d : ℕ} (dimension : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : CoeffOn (cubeDomain (originCube d 0)))
      (h : UnitCubeSkewW2Infinity d) (s t : ℝ) (q : Book.Ch02.MultiscaleExponent),
      0 < s → s ≤ 1 / 4 → 0 < t → t ≤ 1 / 4 → q.IsAdmissible →
      (unitCubeLambda t q
        (perturbCoeffOn (cubeDomain (originCube d 0)) a h.toLInfSkewMatrixFieldOn 1))⁻¹
        ≤ 6 * Real.rpow
          (1 + C * h.gradientW1Infinity *
            (unitCubeLambda s (.finite 2) a)⁻¹)
          (2 * t / (1 - 2 * s)) *
          (unitCubeLambda t q a)⁻¹ := by
  classical
  have : NeZero d := ⟨by omega⟩
  refine ⟨unconditionalConst d, unconditionalConst_pos d, ?_⟩
  intro a h s t q hs0 hs ht0 ht hq
  have hgnn : 0 ≤ h.gradientW1Infinity :=
    Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz.gradientW1Infinity_nonneg h
  have hLnn : (0 : ℝ) ≤ (unitCubeLambda s (.finite 2) a)⁻¹ :=
    unitCubeLambda_inv_nonneg a hs0 isAdmissible_finite_two
  have hXnn : (0 : ℝ) ≤ unconditionalConst d * h.gradientW1Infinity *
      (unitCubeLambda s (.finite 2) a)⁻¹ := by
    have := unconditionalConst_pos d
    positivity
  refine unitCubeLambda_inv_le_of_mesoscale_descendant_ratio a
    (perturbCoeffOn (cubeDomain (originCube d 0)) a h.toLInfSkewMatrixFieldOn 1)
    hs0 hs ht0 ht hq hXnn ?_
  intro F G hF hG k hk R hR
  have hscale0 : ((originCube d 0).scale) = (0 : ℤ) := rfl
  have hHnn : (0 : ℤ) ≤
      ((mesoscaleDepth s (1 + unconditionalConst d * h.gradientW1Infinity *
        (unitCubeLambda s (.finite 2) a)⁻¹) : ℕ) : ℤ) := Int.natCast_nonneg _
  have hkroot : k ≤ (originCube d 0).scale := by
    rw [hscale0] at hk ⊢; omega
  exact coarseSigmaStarInvMatrixNorm_perturb_le_two dimension a h F G hF hG hkroot hR
    (deep_cube_smallness a h F hF hs0 hs hk hR)

end

end Algsuperdiff.Section24.Sensitivity.Provider.LambdaUnconditional
