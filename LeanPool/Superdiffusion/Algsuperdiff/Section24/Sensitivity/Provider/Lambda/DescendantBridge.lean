/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Lambda.CubeRatio
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Multiscale.DescendantRatio
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Multiscale.UnitCubeTransfer

/-!
# DescendantBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# From per-descendant pure-flux ratios to the frozen `unitCubeLambda` ratio

Source: ABK26.  Having applied the `D_h` bound at `p = 0` on every triadic
descendant `R` of the unit cube, the source aggregates the resulting one-cube
ratios into a ratio for `lambda_{s,q}^{-1}`.

This module performs that aggregation once and for all, at an arbitrary pair of
path parameters `t₁ ≤ t₂` (the source's `tau` and `tau + dtau`).  The chain is

```
J(R; a + t₂ h; 0, w) ≤ rho · J(R; a + t₁ h; 0, w)   (all descendants R, all w)
  ⟹ |sigma_*^{-1}(R; a + t₂ h)| ≤ rho · |sigma_*^{-1}(R; a + t₁ h)|
                                                    (Provider.Lambda.CubeRatio)
  ⟹ lambda_{s,q}^{-1}(a + t₂ h)   ≤ rho · lambda_{s,q}^{-1}(a + t₁ h)
                                        (Multiscale.DescendantRatio, all
                                         admissible q including infinity)
```

The middle step needs the descendant localization of the perturbation
(`Multiscale.UnitCubeTransfer.coeffOn_descendant_aeeq_perturbCoeffOn`), which is
already available at an arbitrary path parameter.

Every declaration is an internal helper for the Section 2.4 sensitivity
providers.  The per-cube hypothesis is the analytic input; it is discharged at
every application.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Lambda

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.Multiscale

noncomputable section

variable {d : ℕ}

/-- The restriction of a unit-cube skew field to a triadic descendant. -/
abbrev descendantField {k : ℤ} (hk : k ≤ (originCube d 0).scale)
    {R : TriadicCube d} (hR : R ∈ descendantsAtScale (originCube d 0) k)
    (h : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0))) :
    LInfSkewMatrixFieldOn (cubeDomain R) :=
  restrictLInfSkewMatrixFieldOn
    (U := cubeDomain (originCube d 0)) (V := cubeDomain R)
    (openCubeSet_subset_of_mem_descendantsAtScale hk hR) h

/-! ## One descendant cube -/

/-- A pure-flux response ratio on a descendant cube, stated for the restricted
perturbation path, is a one-cube `sigma_*^{-1}` ratio at the family level. -/
theorem coarseSigmaStarInvMatrixNorm_le_of_cube_responseJ_ratio
    (a : CoeffOn (cubeDomain (originCube d 0)))
    (h : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0))) (t₁ t₂ : ℝ)
    (F G₁ G₂ : TriadicCoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    (hG₁ : CoeffOn.AEEq (G₁.coeffOn (originCube d 0))
      (perturbCoeffOn (cubeDomain (originCube d 0)) a h t₁))
    (hG₂ : CoeffOn.AEEq (G₂.coeffOn (originCube d 0))
      (perturbCoeffOn (cubeDomain (originCube d 0)) a h t₂))
    {ρ : ℝ} (hρ : 0 ≤ ρ) {k : ℤ} (hk : k ≤ (originCube d 0).scale)
    {R : TriadicCube d} (hR : R ∈ descendantsAtScale (originCube d 0) k)
    (hJ : ∀ w : Vec d,
      responseJ (cubeDomain R)
          (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
            (descendantField hk hR h) t₂) 0 w ≤
        ρ * responseJ (cubeDomain R)
          (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
            (descendantField hk hR h) t₁) 0 w) :
    coarseSigmaStarInvMatrixNorm R G₂ ≤ ρ * coarseSigmaStarInvMatrixNorm R G₁ := by
  have hae₁ := coeffOn_descendant_aeeq_perturbCoeffOn a h t₁ F G₁ hF hG₁ hk hR
  have hae₂ := coeffOn_descendant_aeeq_perturbCoeffOn a h t₂ F G₂ hF hG₂ hk hR
  rw [coarseSigmaStarInvMatrixNorm, coarseSigmaStarInvMatrixNorm,
    Ch02.sigmaStarInvCoarse_eq_ofAEEq hae₁, Ch02.sigmaStarInvCoarse_eq_ofAEEq hae₂]
  exact matrixNorm_sigmaStarInvCoarse_le_of_responseJ_le (cubeDomain R) _ _ hρ hJ

/-! ## Aggregation to the frozen unit-cube gauge -/

/-- **The aggregated ratio for the frozen `unitCubeLambda`.**

A uniform per-descendant, all-loadings pure-flux response ratio between the two
path parameters `t₁` and `t₂` transfers verbatim to the frozen scalar
`unitCubeLambda s q` for every `s > 0` and every admissible `q`, including the
endpoint `q = infinity`. -/
theorem unitCubeLambda_inv_le_of_cube_responseJ_ratio [NeZero d]
    (a : CoeffOn (cubeDomain (originCube d 0)))
    (h : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0))) (t₁ t₂ : ℝ)
    {ρ s : ℝ} {q : Ch02.MultiscaleExponent} (hρ : 0 ≤ ρ) (hs : 0 < s)
    (hq : q.IsAdmissible)
    (hJ : ∀ F : TriadicCoeffFamily d,
      CoeffOn.AEEq (F.coeffOn (originCube d 0)) a →
      ∀ k : ℤ, ∀ hk : k ≤ (originCube d 0).scale,
        ∀ R : TriadicCube d, ∀ hR : R ∈ descendantsAtScale (originCube d 0) k,
          ∀ w : Vec d,
            responseJ (cubeDomain R)
                (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
                  (descendantField hk hR h) t₂) 0 w ≤
              ρ * responseJ (cubeDomain R)
                (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
                  (descendantField hk hR h) t₁) 0 w) :
    (unitCubeLambda s q
        (perturbCoeffOn (cubeDomain (originCube d 0)) a h t₂))⁻¹ ≤
      ρ * (unitCubeLambda s q
        (perturbCoeffOn (cubeDomain (originCube d 0)) a h t₁))⁻¹ := by
  classical
  obtain ⟨F, hF⟩ :=
    Algsuperdiff.Section24.UnitCubeMultiscale.exists_compatibleTriadicCoeffFamily a
  refine unitCubeLambda_inv_le_of_family_bound
    (perturbCoeffOn (cubeDomain (originCube d 0)) a h t₁)
    (perturbCoeffOn (cubeDomain (originCube d 0)) a h t₂) s q ρ ?_
  intro G₁ G₂ hG₁ hG₂
  refine lambdaSq_inv_le_of_descendant_ratio (originCube d 0) G₁ G₂ hρ hs hq ?_
  intro k hk R hR
  exact coarseSigmaStarInvMatrixNorm_le_of_cube_responseJ_ratio a h t₁ t₂ F G₁ G₂
    hF hG₁ hG₂ hρ hk hR (hJ F hF k hk R hR)

end

end Algsuperdiff.Section24.Sensitivity.Provider.Lambda
