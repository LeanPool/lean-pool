/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.LambdaUnconditional.CubeScaling

/-!
# CubeGauge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The coarse gauge of the perturbation path at a mesoscopic cube

Source: ABK26.  The unconditional sensitivity estimate runs the conditional
per-cube machinery on a *mesoscopic* triadic cube `R` of the unit-cube
hierarchy rather than on the unit cube itself.  The gauge that controls the
machinery there is the `R`-local coarse gauge `lambda_{3/8,2}^{-1}(R; a + tau
h)`.

This module

* defines that gauge as a function of the path parameter, by evaluating
  `Book.Ch02.lambdaSq` at the concrete family
  `Provider.Lambda.CrudeBound.rootCoeffFamily` (so no choice is involved) and
  proves that *any* compatible family computes the same value
  (`cubeGauge_eq_of_family`, from `lambdaSq_inv_eq_of_aeeq_of_openCubeSet_subset`);
* records the crude uniform bound `4 d a.lam^{-1}` valid along the whole
  segment, which the self-referential bootstrap of `Provider.Lambda.Bootstrap`
  consumes only through the choice of the compounding mesh;
* upgrades the pure-flux `D_h` bound of `Provider.Lambda.CubeBound` from the
  descendant gauge to the *mesoscopic* gauge, using the general-cube descendant
  scaling of `CubeScaling`; and
* assembles the resulting differential inequality into the *ratio engine* at
  `R`, exactly as `Provider.Lambda.Engine` does at the unit cube, but with the
  `R`-local gauge and the `R`-local constant.

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

theorem isAdmissible_finite_two :
    (Ch02.MultiscaleExponent.finite 2).IsAdmissible := by
  simp [Ch02.MultiscaleExponent.IsAdmissible]

/-! ## The mesoscopic-cube gauge along the path -/

/-- **The mesoscopic-cube coarse gauge along the perturbation path.**  The
`R`-local value of `lambda_{3/8,2}^{-1}` at the coefficient field `a + tau h`,
evaluated at the concrete compatible family `rootCoeffFamily`. -/
def cubeGauge (R : TriadicCube d) (a : CoeffOn (cubeDomain (originCube d 0)))
    (h : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0))) (τ : ℝ) : ℝ :=
  (Ch02.lambdaSq R (3 / 8) (.finite 2)
      (rootCoeffFamily (perturbCoeffOn (cubeDomain (originCube d 0)) a h τ)))⁻¹

theorem cubeGauge_nonneg [NeZero d] (R : TriadicCube d)
    (a : CoeffOn (cubeDomain (originCube d 0)))
    (h : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0))) (τ : ℝ) :
    0 ≤ cubeGauge R a h τ :=
  inv_nonneg.mpr (Ch02.lambdaSq_nonneg R _ (by norm_num) isAdmissible_finite_two)

/-- **Any compatible family computes the mesoscopic-cube gauge.** -/
theorem cubeGauge_eq_of_family [NeZero d]
    (a : CoeffOn (cubeDomain (originCube d 0)))
    (h : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0))) (τ : ℝ)
    {k : ℤ} (hk : k ≤ (originCube d 0).scale) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d 0) k) (A : TriadicCoeffFamily d)
    (hA : CoeffOn.AEEq (A.coeffOn (originCube d 0))
      (perturbCoeffOn (cubeDomain (originCube d 0)) a h τ)) :
    (Ch02.lambdaSq R (3 / 8) (.finite 2) A)⁻¹ = cubeGauge R a h τ := by
  refine lambdaSq_inv_eq_of_aeeq_of_openCubeSet_subset
    (openCubeSet_subset_of_mem_descendantsAtScale hk hR) A _ ?_ (by norm_num)
    isAdmissible_finite_two
  exact hA.trans (rootCoeffFamily_aeeq _).symm

/-- The base point of the path: any family compatible with `a` computes the
mesoscopic-cube gauge at `tau = 0`. -/
theorem cubeGauge_zero_eq_of_family [NeZero d]
    (a : CoeffOn (cubeDomain (originCube d 0)))
    (h : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0)))
    {k : ℤ} (hk : k ≤ (originCube d 0).scale) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d 0) k) (F : TriadicCoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a) :
    (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ = cubeGauge R a h 0 := by
  refine cubeGauge_eq_of_family a h 0 hk hR F (hF.trans ?_)
  refine Filter.Eventually.of_forall fun x => ?_
  change a.toCoeffField x = a.toCoeffField x + (0 : ℝ) • h.1.1 x
  simp

/-- **The crude uniform bound for the mesoscopic-cube gauge.**  The microscopic
ellipticity constant of the base coefficient appears here and only here; the
bootstrap consumes it through the compounding mesh only. -/
theorem cubeGauge_le_crude [NeZero d] (R : TriadicCube d)
    (a : CoeffOn (cubeDomain (originCube d 0)))
    (h : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0))) (τ : ℝ) :
    cubeGauge R a h τ ≤ 4 * (d : ℝ) * (a.lam)⁻¹ := by
  have hlam0 : (0 : ℝ) < a.lam := a.lam_pos
  have hMnn : (0 : ℝ) ≤ 4 * (d : ℝ) * (a.lam)⁻¹ := by positivity
  refine lambdaSqFinite_inv_le_of_uniform_maxDescendant R
    (rootCoeffFamily (perturbCoeffOn (cubeDomain (originCube d 0)) a h τ))
    (by norm_num) (by norm_num) hMnn ?_
  intro n
  have hbase := maxDescendantSigmaStarInvMatrixNormAtScale_le_uniform R
    (rootCoeffFamily (perturbCoeffOn (cubeDomain (originCube d 0)) a h τ)) n
  rwa [rootCoeffFamily_lam] at hbase

/-! ## The mesoscopic-cube constant of the `D_h` bound -/

/-- The constant of the pure-flux `D_h` bound at the mesoscopic cube `R`, in the
normalization `|D_h| <= 2 (K Psi) J` used by the ratio engine. -/
def mesoFluxConst (d : ℕ) (h : UnitCubeSkewW2Infinity d) (R : TriadicCube d) : ℝ :=
  (1 / 2 : ℝ) * (fluxCubeConst d * h.gradientW1Infinity * cubeScaleFactor R)

theorem mesoFluxConst_nonneg (d : ℕ) (h : UnitCubeSkewW2Infinity d)
    (R : TriadicCube d) : 0 ≤ mesoFluxConst d h R := by
  have h1 : (0 : ℝ) ≤ fluxCubeConst d := fluxCubeConst_nonneg d
  have h2 : (0 : ℝ) ≤ h.gradientW1Infinity :=
    Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz.gradientW1Infinity_nonneg h
  have h3 : (0 : ℝ) ≤ cubeScaleFactor R := (cubeScaleFactor_pos_cube R).le
  unfold mesoFluxConst
  positivity

/-! ## The `D_h` bound with the mesoscopic gauge -/

/-- **The pure-flux `D_h` bound with the mesoscopic gauge.**  On every triadic
descendant `S` of the mesoscopic cube `R`, and along the whole perturbation
path, the pure-flux `D_h` form is controlled by the `R`-local coarse gauge. -/
theorem abs_dhFluxForm_le_cubeGauge [NeZero d]
    (a : CoeffOn (cubeDomain (originCube d 0))) (h : UnitCubeSkewW2Infinity d)
    (F : TriadicCoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    {R : TriadicCube d} (hRscale : R.scale ≤ 0)
    {l : ℤ} (hlroot : l ≤ (originCube d 0).scale) {S : TriadicCube d}
    (hSroot : S ∈ descendantsAtScale (originCube d 0) l)
    (hSR : S ∈ descendantsAtScale R l) (τ : ℝ) (w : Vec d) :
    |dhFluxForm (cubeDomain S)
        (perturbCoeffOn (cubeDomain S) (F.coeffOn S)
          (descendantField hlroot hSroot h.toLInfSkewMatrixFieldOn) τ)
        (descendantField hlroot hSroot h.toLInfSkewMatrixFieldOn) w| ≤
      2 * (mesoFluxConst d h R * cubeGauge R a h.toLInfSkewMatrixFieldOn τ) *
        responseJ (cubeDomain S)
          (perturbCoeffOn (cubeDomain S) (F.coeffOn S)
            (descendantField hlroot hSroot h.toLInfSkewMatrixFieldOn) τ) 0 w := by
  classical
  set g : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0)) :=
    h.toLInfSkewMatrixFieldOn with hgdef
  set hsub : ((cubeDomain S : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)) :=
    openCubeSet_subset_of_mem_descendantsAtScale hlroot hSroot with hsubdef
  set A : TriadicCoeffFamily d :=
    rootCoeffFamily (perturbCoeffOn (cubeDomain (originCube d 0)) a g τ) with hAdef
  set b : CoeffOn (cubeDomain S) :=
    perturbCoeffOn (cubeDomain S) (F.coeffOn S) (descendantField hlroot hSroot g) τ
    with hbdef
  have hAS : CoeffOn.AEEq (A.coeffOn S) b :=
    coeffOn_descendant_aeeq_perturbCoeffOn a g τ F A hF (rootCoeffFamily_aeeq _)
      hlroot hSroot
  have hlR : l ≤ R.scale := descendant_scale_le_of_mem_descendantsAtScale hSR
  have hSscale : S.scale = l := scale_eq_of_mem_descendantsAtScale hSroot
  have hL : cubeScaleFactor S ≤ 1 :=
    cubeScaleFactor_le_one_of_scale_nonpos (by omega)
  have hmain := abs_dhFluxForm_cube_le h hsub hL b A hAS w
  have hJnn : (0 : ℝ) ≤ responseJ (cubeDomain S) b 0 w := Ch02.responseJ_nonneg _ b 0 w
  have hgnn : 0 ≤ h.gradientW1Infinity :=
    Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz.gradientW1Infinity_nonneg h
  have hCnn : (0 : ℝ) ≤ fluxCubeConst d := fluxCubeConst_nonneg d
  have hscale := cubeScaleFactor_mul_lambdaSq_inv_le_of_mem_descendantsAtScale R A
    (s := (3 / 8 : ℝ)) (q := .finite 2) (by norm_num) (by norm_num)
    isAdmissible_finite_two hlR hSR
  have hgaugeR : (Ch02.lambdaSq R (3 / 8) (.finite 2) A)⁻¹ = cubeGauge R a g τ := rfl
  rw [hgaugeR] at hscale
  refine hmain.trans ?_
  have hcoef : (0 : ℝ) ≤ fluxCubeConst d * h.gradientW1Infinity :=
    mul_nonneg hCnn hgnn
  have hstep := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hscale hcoef) hJnn
  calc fluxCubeConst d * h.gradientW1Infinity * cubeScaleFactor S *
        (Ch02.lambdaSq S (3 / 8) (.finite 2) A)⁻¹ * responseJ (cubeDomain S) b 0 w
      = fluxCubeConst d * h.gradientW1Infinity *
          (cubeScaleFactor S * (Ch02.lambdaSq S (3 / 8) (.finite 2) A)⁻¹) *
          responseJ (cubeDomain S) b 0 w := by ring
    _ ≤ fluxCubeConst d * h.gradientW1Infinity *
          (cubeScaleFactor R * cubeGauge R a g τ) *
          responseJ (cubeDomain S) b 0 w := hstep
    _ = 2 * (mesoFluxConst d h R * cubeGauge R a g τ) *
          responseJ (cubeDomain S) b 0 w := by
        unfold mesoFluxConst; ring

/-! ## The ratio engine at the mesoscopic cube -/

/-- **The ratio engine at the mesoscopic cube.**  Given a bound `C` for the
`R`-local coarse gauge on a subinterval of the path, the gauge itself obeys the
multiplicative Grönwall ratio on that subinterval.  This is
`Provider.Lambda.Engine.pathLambdaInv_ratio_engine` transplanted from the unit
cube to the mesoscopic cube `R`. -/
theorem cubeGauge_ratio_engine [NeZero d] (dimension : 2 ≤ d)
    (a : CoeffOn (cubeDomain (originCube d 0))) (h : UnitCubeSkewW2Infinity d)
    (F : TriadicCoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    {k : ℤ} (hk : k ≤ (originCube d 0).scale) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d 0) k)
    (τ₁ τ₂ C : ℝ) (h12 : τ₁ ≤ τ₂)
    (hC : ∀ τ, τ₁ ≤ τ → τ ≤ τ₂ → cubeGauge R a h.toLInfSkewMatrixFieldOn τ ≤ C) :
    cubeGauge R a h.toLInfSkewMatrixFieldOn τ₂ ≤
      Real.exp (mesoFluxConst d h R * C * (τ₂ - τ₁)) *
        cubeGauge R a h.toLInfSkewMatrixFieldOn τ₁ := by
  classical
  set g : LInfSkewMatrixFieldOn (cubeDomain (originCube d 0)) :=
    h.toLInfSkewMatrixFieldOn with hgdef
  set K : ℝ := mesoFluxConst d h R with hKdef
  have hKnn : 0 ≤ K := mesoFluxConst_nonneg d h R
  have hRscale : R.scale ≤ 0 := by
    have hRk : R.scale = k := scale_eq_of_mem_descendantsAtScale hR
    have hk0 : k ≤ 0 := by simpa using! hk
    omega
  set ρ : ℝ := Real.exp (K * C * (τ₂ - τ₁)) with hρdef
  have hρnn : (0 : ℝ) ≤ ρ := (Real.exp_pos _).le
  set A₁ : TriadicCoeffFamily d :=
    rootCoeffFamily (perturbCoeffOn (cubeDomain (originCube d 0)) a g τ₁) with hA₁
  set A₂ : TriadicCoeffFamily d :=
    rootCoeffFamily (perturbCoeffOn (cubeDomain (originCube d 0)) a g τ₂) with hA₂
  change (Ch02.lambdaSq R (3 / 8) (.finite 2) A₂)⁻¹ ≤
    ρ * (Ch02.lambdaSq R (3 / 8) (.finite 2) A₁)⁻¹
  refine lambdaSq_inv_le_of_descendant_ratio R A₁ A₂ hρnn (by norm_num)
    isAdmissible_finite_two ?_
  intro l _hl S hS
  have hSroot : S ∈ descendantsAtScale (originCube d 0) l :=
    mem_descendantsAtScale_trans hR hS
  have hlroot : l ≤ (originCube d 0).scale :=
    descendant_scale_le_of_mem_descendantsAtScale hSroot
  refine coarseSigmaStarInvMatrixNorm_le_of_cube_responseJ_ratio a g τ₁ τ₂ F A₁ A₂
    hF (rootCoeffFamily_aeeq _) (rootCoeffFamily_aeeq _) hρnn hlroot hSroot ?_
  intro w
  refine responseJ_cube_ratio_of_dhFluxForm_bound dimension a g F hlroot hSroot w
    h12 ?_
  intro τ hτ₁ hτ₂
  refine (abs_dhFluxForm_le_cubeGauge a h F hF hRscale hlroot hSroot hS τ w).trans ?_
  have hJnn : (0 : ℝ) ≤ responseJ (cubeDomain S)
      (perturbCoeffOn (cubeDomain S) (F.coeffOn S)
        (descendantField hlroot hSroot g) τ) 0 w :=
    Ch02.responseJ_nonneg _ _ 0 w
  have hgle : K * cubeGauge R a g τ ≤ K * C :=
    mul_le_mul_of_nonneg_left (hC τ hτ₁ hτ₂) hKnn
  nlinarith [hJnn, hgle]

end

end Algsuperdiff.Section24.Sensitivity.Provider.LambdaUnconditional
