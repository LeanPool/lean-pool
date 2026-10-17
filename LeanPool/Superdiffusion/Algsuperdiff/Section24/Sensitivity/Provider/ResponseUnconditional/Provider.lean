/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional.CubeSensitivity
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional.Closure

/-!
# Provider

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The unconditional response estimate

Source: ABK26, the `J` half of `l.J.sensitivity.no.conditions`.

`Provider.ResponseUnconditional.Closure` reduces the frozen target
`Algsuperdiff.Frozen.Section24.responseJ_sensitivity_unconditional` to a single
analytic input, the per-mesoscopic-cube conditional `J`-sensitivity at the
normalized loading `p = (μσ₀)^{-1/2} e`, `q = (μσ₀)^{1/2} e`.
`Provider.ResponseUnconditional.CubeSensitivity` proves exactly that input at a
general loading.  This module instantiates the loading and assembles the
provider.

At the normalized loading

```
|p|² = (μσ₀)^{-1} ,      |p·q| = |e|² = 1 ,
```

which is precisely the pairing of the two `K₁` groups of the frozen statement,
and at a cube of depth `H` below the unit cube
`|R|² = 3^{-2H}`, the damping factor of the frozen statement.

The value budget is `Provider.ResponseUnconditional.valueBudget`, whose depth-`H`
descendant average over the unit cube is exactly `‖h‖²_{L²(□₀)}`.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz
open Algsuperdiff.Section24.Sensitivity.Provider.Lambda
open Algsuperdiff.Section24.Sensitivity.Provider.Mesoscale
open Algsuperdiff.Section24.Sensitivity.Provider.Multiscale
open Algsuperdiff.Section24.UnitCubeMultiscale
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-- CoarseGraining writes multiscale weights with explicit `Real.rpow`. -/
private theorem rpow_eq_pow (x y : ℝ) : Real.rpow x y = x ^ y := rfl

/-! ## The normalized loading -/

theorem vecNormSq_normalized_left {d : ℕ} {μ σ0 : ℝ} (hμ : 0 < μ) (hσ0 : 0 < σ0)
    {e : Vec d} (he : vecNorm e = 1) :
    vecNormSq ((Real.sqrt (μ * σ0))⁻¹ • e) = (μ * σ0)⁻¹ := by
  have hpos : 0 < μ * σ0 := mul_pos hμ hσ0
  have hsq : Real.sqrt (μ * σ0) ^ 2 = μ * σ0 := Real.sq_sqrt hpos.le
  have he2 : vecNormSq e = 1 := by
    have := Ch02.vecNorm_sq_eq_vecNormSq e
    rw [he] at this
    simpa using this.symm
  rw [vecNormSq_smul, he2, mul_one, inv_pow, hsq]

theorem vecDot_normalized {d : ℕ} {μ σ0 : ℝ} (hμ : 0 < μ) (hσ0 : 0 < σ0)
    {e : Vec d} (he : vecNorm e = 1) :
    vecDot ((Real.sqrt (μ * σ0))⁻¹ • e) (Real.sqrt (μ * σ0) • e) = 1 := by
  have hpos : 0 < μ * σ0 := mul_pos hμ hσ0
  have hspos : 0 < Real.sqrt (μ * σ0) := Real.sqrt_pos.mpr hpos
  have he2 : vecDot e e = 1 := by
    have := Ch02.vecNorm_sq_eq_vecNormSq e
    rw [he] at this
    have : vecNormSq e = 1 := by simpa using this.symm
    exact this
  rw [vecDot_smul_left, vecDot_smul_right, he2, mul_one]
  exact inv_mul_cancel₀ hspos.ne'

/-! ## The per-mesoscopic-cube input -/

/-- **The per-mesoscopic-cube conditional `J`-sensitivity at the normalized
loading**, in exactly the shape consumed by
`responseJ_sensitivity_unconditional_of_mesoscale_cube_sensitivity`. -/
theorem mesoscale_cube_sensitivity (dimension : 2 ≤ d) :
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
                  h.gradientW1Infinity ^ 2) := by
  classical
  let : NeZero d := ⟨by omega⟩
  refine ⟨jGateConst d, jErrorConst d, one_le_jGateConst d, jErrorConst_nonneg d, ?_⟩
  intro a h F G hF hG s μ σ0 e hs0 hs hμ hσ0 he
  refine ⟨valueBudget h, fun R => valueBudget_nonneg h R, ?_, ?_⟩
  · exact le_of_eq (descendantsAverage_valueBudget h (jDepth d a h s))
  · intro R hRd
    have hscale0 : ((originCube d 0).scale) = (0 : ℤ) := rfl
    have hk : (-((jDepth d a h s : ℕ) : ℤ)) ≤ (originCube d 0).scale := by
      rw [hscale0]
      exact neg_nonpos.mpr (Int.natCast_nonneg _)
    have hconv : descendantsAtScale (originCube d 0)
          (-((jDepth d a h s : ℕ) : ℤ)) =
        descendantsAtDepth (originCube d 0) (jDepth d a h s) := by
      rw [descendantsAtScale_eq_descendantsAtDepth (originCube d 0) hk, hscale0]
      congr 1
      omega
    have hRs : R ∈ descendantsAtScale (originCube d 0)
        (-((jDepth d a h s : ℕ) : ℤ)) := by
      rw [hconv]
      exact hRd
    -- the sensitivity at the general loading
    have hmain := responseJ_mesoscale_cube_sensitivity dimension a h F hF hs0 hs
      hk hRs rfl ((Real.sqrt (μ * σ0))⁻¹ • e) (Real.sqrt (μ * σ0) • e)
    -- the left-hand side at the family representative
    have hGR : CoeffOn.AEEq (G.coeffOn R)
        (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
          (descendantField hk hRs h.toLInfSkewMatrixFieldOn) 1) :=
      coeffOn_descendant_aeeq_perturbCoeffOn a h.toLInfSkewMatrixFieldOn 1 F G hF hG
        hk hRs
    rw [responseJ_eq_ofAEEq hGR ((Real.sqrt (μ * σ0))⁻¹ • e)
      (Real.sqrt (μ * σ0) • e)]
    -- the loading data
    have hp : vecNormSq ((Real.sqrt (μ * σ0))⁻¹ • e) = (μ * σ0)⁻¹ :=
      vecNormSq_normalized_left hμ hσ0 he
    have hpq : |vecDot ((Real.sqrt (μ * σ0))⁻¹ • e) (Real.sqrt (μ * σ0) • e)| = 1 := by
      rw [vecDot_normalized hμ hσ0 he]
      norm_num
    -- the damping factor
    have hRscale : R.scale = -((jDepth d a h s : ℕ) : ℤ) :=
      scale_eq_of_mem_descendantsAtScale hRs
    have hcf : cubeScaleFactor R =
        Real.rpow (3 : ℝ) (-((jDepth d a h s : ℕ) : ℝ)) := by
      rw [LambdaUnconditional.cubeScaleFactor_eq_rpow, hRscale]
      congr 1
      push_cast
      ring
    have hD : cubeScaleFactor R ^ 2 =
        Real.rpow (3 : ℝ) (-(2 * ((jDepth d a h s : ℕ) : ℝ))) := by
      rw [hcf]
      simp only [rpow_eq_pow]
      rw [sq, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    rw [hp, hpq, hD, mul_one] at hmain
    exact hmain

/-! ## The provider -/

/-- **Unconditional four-term sensitivity estimate for the response
functional.**

This is the provider form of the frozen target
`Algsuperdiff.Frozen.Section24.responseJ_sensitivity_unconditional`, with
exactly the frozen binders. -/
theorem responseJ_sensitivity_unconditional {d : ℕ} (dimension : 2 ≤ d) :
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
            (unitCubeLambda s (.finite 2) a)⁻¹) ^ 2 :=
  responseJ_sensitivity_unconditional_of_mesoscale_cube_sensitivity dimension
    (mesoscale_cube_sensitivity dimension)

end

end Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional
