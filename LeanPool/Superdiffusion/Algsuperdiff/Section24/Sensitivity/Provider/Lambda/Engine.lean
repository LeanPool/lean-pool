/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Lambda.DescendantBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Lambda.PathGronwall
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Lambda.Bootstrap
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge.EllipticityOrdered

/-!
# Engine

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The ratio engine of the conditional `lambda_{s,q}` sensitivity estimate

Source: ABK26.  This module assembles the two previous steps into the *ratio
engine* consumed by `Provider.Lambda.Bootstrap`:

* on each triadic descendant `R` of the unit cube and at each loading `w`, the
  pure-flux response `t ↦ J(R; a + t h; 0, w)` is differentiable with derivative
  one half of the `D_h` flux form (`Provider.Lambda.PathGronwall`), so the
  per-cube `D_h` bound is a differential inequality, and Grönwall turns it into
  a multiplicative ratio over any subinterval;
* that ratio is uniform in `R` and `w`, so it aggregates to a ratio for
  `lambda_{s,q}^{-1}` (`Provider.Lambda.DescendantBridge`) at every `s > 0` and
  every admissible `q`, including `q = infinity`.

The per-cube `D_h` bound is the analytic input `hcube`; it is a premise of the
internal helpers here and is discharged where they are used.  No aggregate is
ever differentiated.

Every declaration is an internal helper for the Section 2.4 sensitivity
providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Lambda

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.Multiscale

noncomputable section

variable {d : ℕ}

/-! ## The two path functions -/

/-- The frozen coarse gauge `lambda_{3/8,2}^{-1}` along the perturbation
path. -/
def pathGauge (a : CoeffOn (cubeDomain (originCube d 0)))
    (h : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0))) (t : ℝ) : ℝ :=
  (unitCubeLambda (3 / 8) (.finite 2)
    (perturbCoeffOn (cubeDomain (originCube d 0)) a h t))⁻¹

/-- The frozen coarse gauge `lambda_{s,q}^{-1}` along the perturbation path. -/
def pathLambdaInv (a : CoeffOn (cubeDomain (originCube d 0)))
    (h : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0)))
    (s : ℝ) (q : Ch02.MultiscaleExponent) (t : ℝ) : ℝ :=
  (unitCubeLambda s q (perturbCoeffOn (cubeDomain (originCube d 0)) a h t))⁻¹

theorem pathGauge_nonneg [NeZero d] (a : CoeffOn (cubeDomain (originCube d 0)))
    (h : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0))) (t : ℝ) :
    0 ≤ pathGauge a h t := by
  rw [pathGauge]
  exact le_of_lt (inv_pos.mpr
    (Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge.unitCubeLambda_sensitivity_pos
      _))

/-! ## The per-cube Grönwall step -/

/-- The per-cube `D_h` bound at `p = 0`, valid along the whole path, is a
Grönwall differential inequality for the pure-flux response and therefore gives
a multiplicative ratio over any subinterval. -/
theorem responseJ_cube_ratio_of_dhFluxForm_bound (dimension : 2 ≤ d)
    (_a : CoeffOn (cubeDomain (originCube d 0)))
    (h : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0))) {K C t₁ t₂ : ℝ}
    (F : TriadicCoeffFamily d) {k : ℤ} (hk : k ≤ (originCube d 0).scale)
    {R : TriadicCube d} (hR : R ∈ descendantsAtScale (originCube d 0) k)
    (w : Vec d) (ht : t₁ ≤ t₂)
    (hcube : ∀ τ : ℝ, t₁ ≤ τ → τ ≤ t₂ →
      |dhFluxForm (cubeDomain R)
          (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
            (descendantField hk hR h) τ) (descendantField hk hR h) w| ≤
        2 * (K * C) * responseJ (cubeDomain R)
          (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
            (descendantField hk hR h) τ) 0 w) :
    responseJ (cubeDomain R)
        (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
          (descendantField hk hR h) t₂) 0 w ≤
      Real.exp (K * C * (t₂ - t₁)) *
        responseJ (cubeDomain R)
          (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
            (descendantField hk hR h) t₁) 0 w := by
  set g : LInfSkewMatrixFieldOn (cubeDomain R) := descendantField hk hR h with hg
  set y : ℝ → ℝ := fun τ =>
    responseJ (cubeDomain R)
      (perturbCoeffOn (cubeDomain R) (F.coeffOn R) g τ) 0 w with hy
  set y' : ℝ → ℝ := fun τ =>
    (1 / 2 : ℝ) * dhFluxForm (cubeDomain R)
      (perturbCoeffOn (cubeDomain R) (F.coeffOn R) g τ) g w with hy'
  have hderiv : ∀ τ, HasDerivAt y (y' τ) τ := fun τ =>
    hasDerivAt_responseJ_perturbCoeffOn dimension (cubeDomain R) (F.coeffOn R) g w τ
  have hbound : ∀ τ, t₁ ≤ τ → τ ≤ t₂ → y' τ ≤ (K * C) * y τ := by
    intro τ hτ₁ hτ₂
    have habs := hcube τ hτ₁ hτ₂
    have hle := (le_abs_self _).trans habs
    rw [hy']
    linarith
  have := le_exp_mul_of_hasDerivAt_le hderiv hbound ht
  simpa [hy] using this

/-! ## The aggregated ratio engine -/

/-- **The ratio engine.**  Given the per-cube `D_h` bound at `p = 0` on all
triadic descendants and along the whole path, with the root gauge as the
coefficient, the frozen aggregate `lambda_{s,q}^{-1}` satisfies a multiplicative
ratio estimate on every subinterval of `[0,1]` on which the root gauge is
bounded by `C`. -/
theorem pathLambdaInv_ratio_engine [NeZero d] (dimension : 2 ≤ d)
    (a : CoeffOn (cubeDomain (originCube d 0)))
    (h : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0))) {K : ℝ}
    {s : ℝ} {q : Ch02.MultiscaleExponent} (hs : 0 < s) (hq : q.IsAdmissible)
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
    (t₁ t₂ C : ℝ) (_ht₁ : 0 ≤ t₁) (ht : t₁ ≤ t₂) (_ht₂ : t₂ ≤ 1) (hK : 0 ≤ K)
    (hC : ∀ τ, t₁ ≤ τ → τ ≤ t₂ → pathGauge a h τ ≤ C) :
    pathLambdaInv a h s q t₂ ≤
      Real.exp (K * C * (t₂ - t₁)) * pathLambdaInv a h s q t₁ := by
  refine unitCubeLambda_inv_le_of_cube_responseJ_ratio a h t₁ t₂
    (Real.exp_pos _).le hs hq ?_
  intro F hF k hk R hR w
  refine responseJ_cube_ratio_of_dhFluxForm_bound dimension a h F hk hR w ht ?_
  intro τ hτ₁ hτ₂
  refine (hcube F hF k hk R hR τ w).trans ?_
  have hJ : 0 ≤ responseJ (cubeDomain R)
      (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
        (descendantField hk hR h) τ) 0 w :=
    Ch02.responseJ_nonneg _ _ 0 w
  have hgauge : pathGauge a h τ ≤ C := hC τ hτ₁ hτ₂
  have : K * pathGauge a h τ ≤ K * C := mul_le_mul_of_nonneg_left hgauge hK
  nlinarith [hJ]

end

end Algsuperdiff.Section24.Sensitivity.Provider.Lambda
