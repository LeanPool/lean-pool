/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Lambda.Engine

/-!
# Spine

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The conditional `lambda_{s,q}` sensitivity spine

Source: ABK26 (`l.lambda.sensitivity`).

This module assembles the ratio engine of `Provider.Lambda.Engine` with the
self-referential bootstrap of `Provider.Lambda.Bootstrap` into the exact shape
of the frozen conclusion

```
lambda_{s,q}^{-1}(a + h) ≤ (1 + C ‖∇h‖ lambda_{3/8,2}^{-1}(a)) lambda_{s,q}^{-1}(a)
```

for every `s > 0` and every admissible `q`, from two inputs:

* `hcube` — the per-cube `D_h` bound at `p = 0` on every triadic descendant of
  the unit cube, with the *root* gauge as coefficient;
* `hcrude` — any finite bound for the root gauge along the segment.  The
  bootstrap uses it only to choose the mesh of the compounding grid; it does not
  enter the conclusion.

Both are premises of the internal helper below and must be discharged at every
use.  In particular the public provider result will carry neither.

Every declaration is an internal helper for the Section 2.4 sensitivity
providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Lambda

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.Multiscale

noncomputable section

variable {d : ℕ}

/-! ## The frozen gauge is an a.e. invariant -/

/-- The frozen scalar `unitCubeLambda` is positive at every admissible
exponent pair. -/
theorem unitCubeLambda_pos [NeZero d] (a : CoeffOn (cubeDomain (originCube d 0)))
    {s : ℝ} {q : Ch02.MultiscaleExponent} (hs : 0 < s) (hq : q.IsAdmissible) :
    0 < unitCubeLambda s q a := by
  obtain ⟨F, hF⟩ :=
    Algsuperdiff.Section24.UnitCubeMultiscale.exists_compatibleTriadicCoeffFamily a
  rw [unitCubeLambda_characterization s q a F hF]
  exact Ch02.lambdaSq_pos (originCube d 0) F hs hq

/-- The frozen scalar `unitCubeLambda` only depends on the coefficient field up
to a.e. equality. -/
theorem unitCubeLambda_eq_of_aeeq (s : ℝ) (q : Ch02.MultiscaleExponent)
    {a b : CoeffOn (cubeDomain (originCube d 0))} (hab : CoeffOn.AEEq a b) :
    unitCubeLambda s q a = unitCubeLambda s q b := by
  obtain ⟨F, hF⟩ :=
    Algsuperdiff.Section24.UnitCubeMultiscale.exists_compatibleTriadicCoeffFamily a
  rw [unitCubeLambda_characterization s q a F hF,
    unitCubeLambda_characterization s q b F (hF.trans hab)]

/-- The perturbation path starts at the base coefficient. -/
theorem perturbCoeffOn_zero_aeeq (a : CoeffOn (cubeDomain (originCube d 0)))
    (h : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0))) :
    CoeffOn.AEEq (perturbCoeffOn (cubeDomain (originCube d 0)) a h 0) a := by
  refine Filter.Eventually.of_forall fun x => ?_
  show a.toCoeffField x + (0 : ℝ) • h.1.1 x = a.toCoeffField x
  simp

@[simp] theorem pathGauge_zero (a : CoeffOn (cubeDomain (originCube d 0)))
    (h : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0))) :
    pathGauge a h 0 = (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ := by
  rw [pathGauge, unitCubeLambda_eq_of_aeeq (3 / 8) (.finite 2)
    (perturbCoeffOn_zero_aeeq a h)]

@[simp] theorem pathLambdaInv_zero (a : CoeffOn (cubeDomain (originCube d 0)))
    (h : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0)))
    (s : ℝ) (q : Ch02.MultiscaleExponent) :
    pathLambdaInv a h s q 0 = (unitCubeLambda s q a)⁻¹ := by
  rw [pathLambdaInv, unitCubeLambda_eq_of_aeeq s q (perturbCoeffOn_zero_aeeq a h)]

theorem pathLambdaInv_gauge (a : CoeffOn (cubeDomain (originCube d 0)))
    (h : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0))) :
    pathLambdaInv a h (3 / 8) (.finite 2) = pathGauge a h := rfl

/-! ## The spine -/

/-- **The conditional `lambda_{s,q}` sensitivity, given the per-cube `D_h`
bound.**

`hcube` is the `p = 0` specialization of the `D_h` bound applied on every
triadic descendant of the unit cube and at every point of the segment, with the
root coarse gauge as its coefficient.  `hcrude` is any finite bound for the root
gauge along the segment.  Both are consumption points; neither appears in the
final provider statement. -/
theorem unitCubeLambda_inv_perturb_le_of_cube_dhFluxForm_bound [NeZero d]
    (dimension : 2 ≤ d) (a : CoeffOn (cubeDomain (originCube d 0)))
    (h : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0))) {K B : ℝ}
    (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hcrude : ∀ t, 0 ≤ t → t ≤ 1 → pathGauge a h t ≤ B)
    (hcube : ∀ F : TriadicCoeffFamily d,
      CoeffOn.AEEq (F.coeffOn (originCube d 0)) a →
      ∀ k : ℤ, ∀ hk : k ≤ (originCube d 0).scale,
        ∀ R : TriadicCube d, ∀ hR : R ∈ descendantsAtScale (originCube d 0) k,
          ∀ (τ : ℝ) (w : Vec d),
            |dhFluxForm (cubeDomain R)
                (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
                  (descendantField hk hR h) τ) (descendantField hk hR h) w| ≤
              2 * (K * pathGauge a h τ) * responseJ (cubeDomain R)
                (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
                  (descendantField hk hR h) τ) 0 w)
    (hsmall : 4 * K * (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ ≤ 1 / 2)
    (s : ℝ) (q : Ch02.MultiscaleExponent) (hs : 0 < s) (hq : q.IsAdmissible) :
    (unitCubeLambda s q
        (perturbCoeffOn (cubeDomain (originCube d 0)) a h 1))⁻¹ ≤
      (1 + 4 * K * (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
        (unitCubeLambda s q a)⁻¹ := by
  have hgauge0 : pathGauge a h 0 = (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ :=
    pathGauge_zero a h
  have hΨ : ∀ t, 0 ≤ pathGauge a h t := pathGauge_nonneg a h
  have hY : 0 ≤ pathLambdaInv a h s q 0 := by
    rw [pathLambdaInv_zero]
    exact le_of_lt (inv_pos.mpr (unitCubeLambda_pos a hs hq))
  have hengine : ∀ t₁ t₂ C : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ 1 →
      (∀ τ, t₁ ≤ τ → τ ≤ t₂ → pathGauge a h τ ≤ C) →
      pathGauge a h t₂ ≤ Real.exp (K * C * (t₂ - t₁)) * pathGauge a h t₁ := by
    intro t₁ t₂ C h1 h12 h2 hC
    have := pathLambdaInv_ratio_engine dimension a h (K := K)
      (s := (3 / 8 : ℝ)) (q := .finite 2) (by norm_num)
      (by simp [Ch02.MultiscaleExponent.IsAdmissible]) hcube t₁ t₂ C h1 h12 h2 hK hC
    rwa [pathLambdaInv_gauge] at this
  have hengineY : ∀ C : ℝ, (∀ τ, 0 ≤ τ → τ ≤ 1 → pathGauge a h τ ≤ C) →
      pathLambdaInv a h s q 1 ≤ Real.exp (K * C) * pathLambdaInv a h s q 0 := by
    intro C hC
    have := pathLambdaInv_ratio_engine dimension a h (K := K) (s := s) (q := q)
      hs hq hcube 0 1 C le_rfl (by norm_num) le_rfl hK
      (fun τ hτ₁ hτ₂ => hC τ hτ₁ hτ₂)
    simpa using this
  have hmain := le_one_add_four_mul_of_ratio_engine (Ψ := pathGauge a h)
    (Y := pathLambdaInv a h s q) hΨ hK hB hY hcrude hengine hengineY
    (by rw [hgauge0]; exact hsmall)
  rw [hgauge0, pathLambdaInv_zero] at hmain
  exact hmain

end

end Algsuperdiff.Section24.Sensitivity.Provider.Lambda
