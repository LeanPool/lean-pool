/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional.CubeShaking

/-!
# Closure

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The unconditional response estimate, modulo the per-mesoscopic-cube input

Source: ABK26, the `J` half of `l.J.sensitivity.no.conditions`.

The result

```
responseJ_sensitivity_unconditional_of_mesoscale_cube_sensitivity
```

has **exactly the frozen conclusion** of
`Algsuperdiff.Frozen.Section24.responseJ_sensitivity_unconditional`, including
the `letI : NeZero d`, and exactly one hypothesis, `hcube`, which is the missing
analytic input in its precise form.

## What `hcube` says

There are dimensional constants `C₀ ≥ 1` and `K₁ ≥ 0` such that, at the
mesoscopic depth `H = mesoscaleDepth s (1 + C₀ ‖∇h‖ λ_{s,2}^{-1}(□₀;a))`, on
every triadic cube `R` of depth `H` below the unit cube,

```
J(R, a+h, (μσ₀)^{-1/2}e, (μσ₀)^{1/2}e)
  ≤ 3 J(R, a, (μσ₀)^{-1/2}e, (μσ₀)^{1/2}e)
    + K₁ (μσ₀)^{-1} λ_{3/8,2}^{-1}(R;a) (V R + 3^{-2H} ‖∇h‖²)
    + K₁ 3^{-2H} λ_{3/8,2}^{-2}(R;a) ‖∇h‖² ,
```

together with a nonnegative **value budget** `V` whose depth-`H` descendant
average is at most `‖h‖²_{L²(□₀)}`.

This is precisely the conditional `J`-sensitivity of the frozen theorem
`responseJ_sensitivity` at `δ = 1`, transplanted from the root cube to a
mesoscopic cube:

* the factor `3 = 1 + δ + (gate)` needs the *mesoscopic* smallness gate, which
  the mesoscopic depth supplies unconditionally — exactly as
  `Provider.LambdaUnconditional.deep_cube_smallness` does for the `λ` half;
* the Term A error carries `|p|² = (μσ₀)^{-1}` and must be priced against the
  *cube-local* `L²` value budget `V R` plus the scale-damped gradient
  `3^{-2H} ‖∇h‖²`, not against the root `W^{1,∞}` value norm: the aggregation
  below is false with the undamped root `W^{1,∞}` norm in that slot;
* the Term BC error carries `|p·q| = 1` and the two damped gauges.

Every declaration in this module is an internal helper for the Section 2.4
sensitivity providers.  There is no public provider for the frozen theorem
here: `hcube` is not discharged.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.Mesoscale
open Algsuperdiff.Section24.UnitCubeMultiscale

noncomputable section

/-- **The unconditional response estimate, modulo the per-mesoscopic-cube
conditional `J`-sensitivity.**

The conclusion is the frozen statement of
`Algsuperdiff.Frozen.Section24.responseJ_sensitivity_unconditional` verbatim.
The single hypothesis `hcube` is the missing analytic input; see the module
docstring. -/
theorem responseJ_sensitivity_unconditional_of_mesoscale_cube_sensitivity
    {d : ℕ} (dimension : 2 ≤ d)
    (hcube :
      letI : NeZero d := ⟨by omega⟩
      ∃ C₀ K₁ : ℝ, 1 ≤ C₀ ∧ 0 ≤ K₁ ∧
        ∀ (a : CoeffOn (cubeDomain (originCube d 0)))
          (h : UnitCubeSkewW2Infinity d) (F G : TriadicCoeffFamily d),
          CoeffOn.AEEq (F.coeffOn (originCube d 0)) a →
          CoeffOn.AEEq (G.coeffOn (originCube d 0))
            (perturbCoeffOn (cubeDomain (originCube d 0)) a
              h.toLInfSkewMatrixFieldOn 1) →
          ∀ (s μ σ0 : ℝ) (e : Vec d),
          0 < s → s ≤ 1 / 4 → 0 < μ → 0 < σ0 → vecNorm e = 1 →
          ∃ V : TriadicCube d → ℝ, (∀ R, 0 ≤ V R) ∧
            descendantsAverage (originCube d 0)
                (mesoscaleDepth s (1 + C₀ * (h.gradientW1Infinity *
                  (unitCubeLambda s (.finite 2) a)⁻¹))) V ≤ h.valueL2 ^ 2 ∧
            ∀ R ∈ descendantsAtDepth (originCube d 0)
                (mesoscaleDepth s (1 + C₀ * (h.gradientW1Infinity *
                  (unitCubeLambda s (.finite 2) a)⁻¹))),
              responseJ (cubeDomain R) (G.coeffOn R)
                  ((Real.sqrt (μ * σ0))⁻¹ • e) (Real.sqrt (μ * σ0) • e) ≤
                3 * responseJ (cubeDomain R) (F.coeffOn R)
                    ((Real.sqrt (μ * σ0))⁻¹ • e) (Real.sqrt (μ * σ0) • e) +
                  K₁ * ((μ * σ0)⁻¹ *
                    (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ *
                    (V R + Real.rpow (3 : ℝ) (-(2 * ((mesoscaleDepth s
                      (1 + C₀ * (h.gradientW1Infinity *
                        (unitCubeLambda s (.finite 2) a)⁻¹)) : ℕ) : ℝ))) *
                      h.gradientW1Infinity ^ 2)) +
                  K₁ * (Real.rpow (3 : ℝ) (-(2 * ((mesoscaleDepth s
                      (1 + C₀ * (h.gradientW1Infinity *
                        (unitCubeLambda s (.finite 2) a)⁻¹)) : ℕ) : ℝ))) *
                    (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ ^ 2 *
                    h.gradientW1Infinity ^ 2)) :
    letI : NeZero d := ⟨by omega⟩
    ∃ C : ℝ, 0 < C ∧ ∀ (a : CoeffOn (cubeDomain (originCube d 0)))
      (h : UnitCubeSkewW2Infinity d) (s t μ σ0 : ℝ) (e : Vec d),
      0 < s → s ≤ 1 / 4 → 0 < t → t ≤ 1 / 4 → 0 < μ → 0 < σ0 → vecNorm e = 1 →
      responseJ (cubeDomain (originCube d 0))
          (perturbCoeffOn (cubeDomain (originCube d 0)) a h.toLInfSkewMatrixFieldOn 1)
          ((Real.sqrt (μ * σ0))⁻¹ • e) (Real.sqrt (μ * σ0) • e)
        ≤ C * μ⁻¹ * Real.rpow
            (1 + h.gradientW1Infinity *
              (unitCubeLambda s (.finite 2) a)⁻¹)
            (2 * t / (1 - 2 * s)) *
            (unitCubeHomogenizationError t (.finite 2) (.finite 2)
              a (scalarMatrix σ0)) ^ 2 +
          C * μ⁻¹ * σ0 *
            (unitCubeLambda s (.finite 2) a)⁻¹ *
            Real.rpow
              (1 + h.gradientW1Infinity *
                (unitCubeLambda s (.finite 2) a)⁻¹)
              (2 * s / (1 - 2 * s)) *
            (σ0⁻¹ ^ 2 * h.valueL2 ^ 2 + (μ - 1) ^ 2) +
          C * μ⁻¹ ^ 2 * σ0⁻¹ ^ 2 * h.gradientW1Infinity ^ 2 +
          C * min 1 (h.gradientW1Infinity *
            (unitCubeLambda s (.finite 2) a)⁻¹) ^ 2 := by
  classical
  let : NeZero d := ⟨by omega⟩
  obtain ⟨C₀, K₁, hC₀, hK₁, hmain⟩ := hcube
  have hKnn : (0 : ℝ) ≤ max 3 K₁ :=
    le_trans (by norm_num : (0 : ℝ) ≤ 3) (le_max_left 3 K₁)
  refine ⟨aggConst C₀ (max 3 K₁), aggConst_pos hC₀ hKnn, ?_⟩
  intro a h s t μ σ0 e hs0 hs ht0 ht hμ hσ0 he
  obtain ⟨F, hF⟩ := exists_compatibleTriadicCoeffFamily a
  obtain ⟨G, hG⟩ := exists_compatibleTriadicCoeffFamily
    (perturbCoeffOn (cubeDomain (originCube d 0)) a h.toLInfSkewMatrixFieldOn 1)
  obtain ⟨V, hV0, hV, hsens⟩ := hmain a h F G hF hG s μ σ0 e hs0 hs hμ hσ0 he
  refine responseJ_le_frozen_of_mesoscale_cube_bound a h F G hF hG hs0 hs ht0 ht
    hμ hσ0 he hC₀ hKnn V hV0 hV ?_
  intro R hR
  exact mesoscale_cube_bound_of_conditional_sensitivity R F G hμ hσ0 he
    (Real.rpow_nonneg (by norm_num) _) (hV0 R) (hsens R hR)

end

end Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional
