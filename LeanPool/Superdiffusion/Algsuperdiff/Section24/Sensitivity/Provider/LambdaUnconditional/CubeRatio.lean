/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.LambdaUnconditional.CubeGauge

/-!
# CubeRatio

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The conditional per-cube estimate at a mesoscopic cube

Source: ABK26.  Once the smallness condition has been verified at a mesoscopic
triadic cube `R`, the *conditional* sensitivity machinery applies there and
yields

```
lambda_{t,q}^{-1}(R; a + h)  <=  2 lambda_{t,q}^{-1}(R; a) .
```

This module proves the one-cube specialization of that statement, namely the
factor-two ratio for the pure-flux response and hence for `|sigma_*^{-1}(R)|`.

* the ratio engine at `R` (`CubeGauge.cubeGauge_ratio_engine`) together with the
  crude bound (`CubeGauge.cubeGauge_le_crude`) feeds the gauge-free
  self-referential bootstrap `Provider.Lambda.Bootstrap`, whose smallness gate
  `4 K Psi(0) <= 1/2` is exactly the mesoscopic smallness condition;
* the bootstrap's closed form gives the ratio `1 + 4 K Psi(0) <= 2` for the
  pure-flux response at `R`;
* `Provider.Lambda.DescendantBridge` converts the all-loadings response ratio
  into the `|sigma_*^{-1}(R)|` ratio consumed by the mesoscale assembly.

The smallness condition is a hypothesis of both statements below; it is
discharged, unconditionally, in `LambdaUnconditional.Closure`.

Every declaration in this module is an internal helper for the Section 2.4
sensitivity providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.LambdaUnconditional

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.Lambda
open Algsuperdiff.Section24.Sensitivity.Provider.Multiscale

noncomputable section

variable {d : ℕ}

/-- The perturbation path starts at the base coefficient, at any domain. -/
theorem perturbCoeffOn_zero_aeeq_domain (U : Domain d) (c : CoeffOn U)
    (g : LInfSkewMatrixFieldOn U) : CoeffOn.AEEq (perturbCoeffOn U c g 0) c := by
  refine Filter.Eventually.of_forall fun x => ?_
  show c.toCoeffField x + (0 : ℝ) • g.1.1 x = c.toCoeffField x
  simp

/-- **The per-cube conditional estimate at a mesoscopic cube.**  Under the
mesoscopic smallness condition, the pure-flux response of the perturbed field is
at most twice the pure-flux response of the base field, at every loading.

`hsmall` is the mesoscopic smallness condition; it is discharged
unconditionally at the mesoscopic depth in `LambdaUnconditional.Closure`. -/
theorem responseJ_perturb_le_two_mul [NeZero d] (dimension : 2 ≤ d)
    (a : CoeffOn (cubeDomain (originCube d 0))) (h : UnitCubeSkewW2Infinity d)
    (F : TriadicCoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    {k : ℤ} (hk : k ≤ (originCube d 0).scale) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d 0) k)
    (hsmall : 4 * mesoFluxConst d h R *
      cubeGauge R a h.toLInfSkewMatrixFieldOn 0 ≤ 1 / 2) (w : Vec d) :
    responseJ (cubeDomain R)
        (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
          (descendantField hk hR h.toLInfSkewMatrixFieldOn) 1) 0 w ≤
      2 * responseJ (cubeDomain R)
        (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
          (descendantField hk hR h.toLInfSkewMatrixFieldOn) 0) 0 w := by
  classical
  set g : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0)) :=
    h.toLInfSkewMatrixFieldOn with hgdef
  set K : ℝ := mesoFluxConst d h R with hKdef
  have hKnn : 0 ≤ K := mesoFluxConst_nonneg d h R
  have hRscale : R.scale ≤ 0 := by
    have hRk : R.scale = k := scale_eq_of_mem_descendantsAtScale hR
    have hk0 : k ≤ 0 := by simpa using! hk
    omega
  have hRR : R ∈ descendantsAtScale R k := by
    have hRk : R.scale = k := scale_eq_of_mem_descendantsAtScale hR
    rw [← hRk]
    exact mem_descendantsAtScale_self R
  set Ψ : ℝ → ℝ := fun τ => cubeGauge R a g τ with hΨdef
  set Y : ℝ → ℝ := fun τ =>
    responseJ (cubeDomain R)
      (perturbCoeffOn (cubeDomain R) (F.coeffOn R) (descendantField hk hR g) τ) 0 w
    with hYdef
  have hΨnn : ∀ τ, 0 ≤ Ψ τ := fun τ => cubeGauge_nonneg R a g τ
  have hYnn : 0 ≤ Y 0 := Ch02.responseJ_nonneg _ _ 0 w
  have hBnn : (0 : ℝ) ≤ 4 * (d : ℝ) * (a.lam)⁻¹ := by
    have := a.lam_pos
    positivity
  have hcrude : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → Ψ τ ≤ 4 * (d : ℝ) * (a.lam)⁻¹ :=
    fun τ _ _ => cubeGauge_le_crude R a g τ
  have hengine : ∀ τ₁ τ₂ C : ℝ, 0 ≤ τ₁ → τ₁ ≤ τ₂ → τ₂ ≤ 1 →
      (∀ τ, τ₁ ≤ τ → τ ≤ τ₂ → Ψ τ ≤ C) →
      Ψ τ₂ ≤ Real.exp (K * C * (τ₂ - τ₁)) * Ψ τ₁ := by
    intro τ₁ τ₂ C _h1 h12 _h2 hC
    exact cubeGauge_ratio_engine dimension a h F hF hk hR τ₁ τ₂ C h12 hC
  have hengineY : ∀ C : ℝ, (∀ τ, 0 ≤ τ → τ ≤ 1 → Ψ τ ≤ C) →
      Y 1 ≤ Real.exp (K * C) * Y 0 := by
    intro C hC
    have hmain := responseJ_cube_ratio_of_dhFluxForm_bound dimension a g F hk hR w
      (t₁ := 0) (t₂ := 1) (K := K) (C := C) (by norm_num) ?_
    · simpa using hmain
    · intro τ hτ₁ hτ₂
      refine (abs_dhFluxForm_le_cubeGauge a h F hF hRscale hk hR hRR τ w).trans ?_
      have hJnn : (0 : ℝ) ≤ responseJ (cubeDomain R)
          (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
            (descendantField hk hR g) τ) 0 w :=
        Ch02.responseJ_nonneg _ _ 0 w
      have hgle : K * cubeGauge R a g τ ≤ K * C :=
        mul_le_mul_of_nonneg_left (hC τ hτ₁ hτ₂) hKnn
      nlinarith [hJnn, hgle]
  have hmain := le_one_add_four_mul_of_ratio_engine (Ψ := Ψ) (Y := Y) (K := K)
    (B := 4 * (d : ℝ) * (a.lam)⁻¹) hΨnn hKnn hBnn hYnn hcrude hengine hengineY
    hsmall
  refine hmain.trans ?_
  have hfac : 1 + 4 * K * Ψ 0 ≤ 2 := by
    have hgate := hsmall
    simp only [hΨdef, hKdef] at hgate ⊢
    linarith
  exact mul_le_mul_of_nonneg_right hfac hYnn

/-- **The per-cube `sigma_*^{-1}` ratio at a mesoscopic cube.**  This is the
form consumed by the mesoscale assembly
`Provider.Mesoscale.LambdaAssembly.unitCubeLambda_inv_le_of_mesoscale_descendant_ratio`. -/
theorem coarseSigmaStarInvMatrixNorm_perturb_le_two [NeZero d] (dimension : 2 ≤ d)
    (a : CoeffOn (cubeDomain (originCube d 0))) (h : UnitCubeSkewW2Infinity d)
    (F G : TriadicCoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    (hG : CoeffOn.AEEq (G.coeffOn (originCube d 0))
      (perturbCoeffOn (cubeDomain (originCube d 0)) a h.toLInfSkewMatrixFieldOn 1))
    {k : ℤ} (hk : k ≤ (originCube d 0).scale) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d 0) k)
    (hsmall : 4 * mesoFluxConst d h R *
      cubeGauge R a h.toLInfSkewMatrixFieldOn 0 ≤ 1 / 2) :
    coarseSigmaStarInvMatrixNorm R G ≤ 2 * coarseSigmaStarInvMatrixNorm R F := by
  classical
  set g : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0)) :=
    h.toLInfSkewMatrixFieldOn with hgdef
  have hF0 : CoeffOn.AEEq (F.coeffOn (originCube d 0))
      (perturbCoeffOn (cubeDomain (originCube d 0)) a g 0) :=
    hF.trans (perturbCoeffOn_zero_aeeq_domain _ a g).symm
  exact coarseSigmaStarInvMatrixNorm_le_of_cube_responseJ_ratio a g 0 1 F F G
    hF hF0 hG (by norm_num) hk hR
    (fun w => responseJ_perturb_le_two_mul dimension a h F hF hk hR hsmall w)

end

end Algsuperdiff.Section24.Sensitivity.Provider.LambdaUnconditional
