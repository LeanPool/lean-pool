/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional.CubeDhPQ
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.LambdaUnconditional.Closure
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.BigLambda.CubeJSensitivity

/-!
# CubeSensitivity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The conditional `J`-sensitivity at a mesoscopic cube, unconditionally

Source: ABK26.

At the mesoscopic depth `H = mesoscaleDepth s (1 + C₀ ‖∇h‖ λ_{s,2}^{-1}(□₀;a))`
the dimensionless quantity `‖∇h‖ |R| λ_{3/8,2}^{-1}(R;a)` is at most `1/C₀` at
*every* triadic descendant `R` of the unit cube of depth `H`, with no hypothesis
whatsoever on `h`.  With `C₀` chosen large enough this gate

* makes the mesoscopic coarse gauge at most double along the perturbation path
  (`cubeGauge_le_two_mul_zero`, the `Provider.Lambda.Bootstrap` engine run at
  `R` exactly as in `Provider.LambdaUnconditional.CubeRatio`), and
* makes the Term BC coefficient of the general-loading `D_h` bound at most
  `1/4`,

so the affine differential inequality of `Provider.BigLambda.PathODE` integrates
at `δ = 1` to the per-cube estimate

```
J(R, a+h, p, q) ≤ 3 J(R, a, p, q)
                + K₁ |p|² λ_{3/8,2}^{-1}(R) (V(R) + 3^{-2H} ‖∇h‖²)
                + K₁ 3^{-2H} λ_{3/8,2}^{-2}(R) ‖∇h‖² |p·q| ,
```

with `V(R)` the cube-local `L²` value budget of
`Provider.ResponseUnconditional.ValueLipschitz`.

Every declaration in this module is an internal helper for the Section 2.4
sensitivity providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.BigLambda
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz
open Algsuperdiff.Section24.Sensitivity.Provider.Lambda
open Algsuperdiff.Section24.Sensitivity.Provider.LambdaUnconditional
open Algsuperdiff.Section24.Sensitivity.Provider.Multiscale
open Algsuperdiff.Section24.Sensitivity.Provider.Response
open Algsuperdiff.Section24.UnitCubeMultiscale
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Two pieces of abstract path arithmetic -/

/-- The pointwise conversion of the general-loading `D_h` bound into the affine
differential inequality, with the path gauge replaced by twice its base value. -/
theorem dhBound_to_path_step {CA CB P G0 Gt Y T : ℝ} (hCAP : 0 ≤ CA * P)
    (hCB : 0 ≤ CB) (hGt : 0 ≤ Gt) (hGle : Gt ≤ 2 * G0) (hY : 0 ≤ Y) (_hT : 0 ≤ T) :
    (1 / 2 : ℝ) * (CA * P * (Real.sqrt Gt * Real.sqrt Y) +
        CB * ((Real.sqrt Gt * Real.sqrt Y) *
          (Real.sqrt Gt * Real.sqrt Y + Real.sqrt Gt * Real.sqrt T))) ≤
      ((1 / 2 : ℝ) * CA * P * (Real.sqrt 2 * Real.sqrt G0)) * Real.sqrt Y +
        ((1 / 2 : ℝ) * CB * (2 * G0)) * Y +
        (((1 / 2 : ℝ) * CB * (2 * G0)) * Real.sqrt T) * Real.sqrt Y := by
  have hGtG : Real.sqrt Gt * Real.sqrt Gt = Gt := Real.mul_self_sqrt hGt
  have hYY : Real.sqrt Y * Real.sqrt Y = Y := Real.mul_self_sqrt hY
  have hexp : (Real.sqrt Gt * Real.sqrt Y) *
      (Real.sqrt Gt * Real.sqrt Y + Real.sqrt Gt * Real.sqrt T) =
      Gt * Y + Gt * (Real.sqrt Y * Real.sqrt T) := by
    calc (Real.sqrt Gt * Real.sqrt Y) *
          (Real.sqrt Gt * Real.sqrt Y + Real.sqrt Gt * Real.sqrt T)
        = (Real.sqrt Gt * Real.sqrt Gt) * (Real.sqrt Y * Real.sqrt Y) +
            (Real.sqrt Gt * Real.sqrt Gt) * (Real.sqrt Y * Real.sqrt T) := by ring
      _ = Gt * Y + Gt * (Real.sqrt Y * Real.sqrt T) := by rw [hGtG, hYY]
  rw [hexp]
  have hG0 : 0 ≤ G0 := by
    have : (0 : ℝ) ≤ 2 * G0 := le_trans hGt hGle
    linarith
  have hsqrtle : Real.sqrt Gt ≤ Real.sqrt 2 * Real.sqrt G0 := by
    have hstep := Real.sqrt_le_sqrt hGle
    rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at hstep
  have hA : CA * P * (Real.sqrt Gt * Real.sqrt Y) ≤
      CA * P * ((Real.sqrt 2 * Real.sqrt G0) * Real.sqrt Y) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hsqrtle (Real.sqrt_nonneg _)) hCAP
  have hinner : (0 : ℝ) ≤ Real.sqrt Y * Real.sqrt T :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hB : CB * (Gt * Y + Gt * (Real.sqrt Y * Real.sqrt T)) ≤
      CB * ((2 * G0) * Y + (2 * G0) * (Real.sqrt Y * Real.sqrt T)) := by
    refine mul_le_mul_of_nonneg_left ?_ hCB
    have h1 : Gt * Y ≤ (2 * G0) * Y := mul_le_mul_of_nonneg_right hGle hY
    have h2 : Gt * (Real.sqrt Y * Real.sqrt T) ≤
        (2 * G0) * (Real.sqrt Y * Real.sqrt T) :=
      mul_le_mul_of_nonneg_right hGle hinner
    linarith
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hA hB)
    (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
  refine hsum.trans (le_of_eq ?_)
  ring

/-- Exact integration of the affine differential inequality at `δ = 1`. -/
theorem path_ode_le {y y' : ℝ → ℝ} {A₁ B₁ T : ℝ}
    (hderiv : ∀ τ, HasDerivAt y (y' τ) τ) (hynn : ∀ τ, 0 ≤ y τ)
    (_hA₁ : 0 ≤ A₁) (hB₁ : 0 ≤ B₁) (hB₁le : B₁ ≤ 1 / 4) (hT : 0 ≤ T)
    (hstep : ∀ τ, (0 : ℝ) ≤ τ → τ ≤ 1 →
      y' τ ≤ A₁ * Real.sqrt (y τ) + B₁ * y τ +
        (B₁ * Real.sqrt T) * Real.sqrt (y τ)) :
    y 1 ≤ 2 * y 0 + 4 * A₁ ^ 2 + 4 * B₁ ^ 2 * T := by
  have hm : (0 : ℝ) ≤ 2 * A₁ ^ 2 + 2 * (B₁ ^ 2 * T) := by positivity
  have hc : (0 : ℝ) ≤ B₁ + 1 / 4 := by linarith
  have hbound : ∀ τ, (0 : ℝ) ≤ τ → τ ≤ 1 →
      y' τ ≤ (2 * A₁ ^ 2 + 2 * (B₁ ^ 2 * T)) + (B₁ + 1 / 4) * y τ := by
    intro τ h0 h1
    have hY1 := mul_sqrt_le_young_div (A := A₁) (y := y τ) (θ := (1 / 4 : ℝ))
      (hynn τ) (by norm_num)
    have hY2 := mul_sqrt_le_young_div (A := B₁ * Real.sqrt T) (y := y τ)
      (θ := (1 / 4 : ℝ)) (hynn τ) (by norm_num)
    have hTsq : (B₁ * Real.sqrt T) ^ 2 = B₁ ^ 2 * T := by
      rw [mul_pow, Real.sq_sqrt hT]
    rw [hTsq] at hY2
    have e1 : A₁ ^ 2 / (2 * (1 / 4 : ℝ)) = 2 * A₁ ^ 2 := by ring
    have e2 : B₁ ^ 2 * T / (2 * (1 / 4 : ℝ)) = 2 * (B₁ ^ 2 * T) := by ring
    rw [e1] at hY1
    rw [e2] at hY2
    linarith [hstep τ h0 h1, hY1, hY2]
  have hint := le_exp_mul_add_of_hasDerivAt_le hderiv hc hm hbound
    (by norm_num : (0 : ℝ) ≤ 1)
  rw [sub_zero, mul_one, mul_one] at hint
  have hcle : B₁ + 1 / 4 ≤ 1 / 2 := by linarith
  have hexp : Real.exp (B₁ + 1 / 4) ≤ 1 + 2 * (B₁ + 1 / 4) :=
    exp_le_one_add_two_mul hc hcle
  have hfac : (0 : ℝ) ≤ y 0 + (2 * A₁ ^ 2 + 2 * (B₁ ^ 2 * T)) := by
    have := hynn 0; linarith
  have hst := hint.trans (mul_le_mul_of_nonneg_right hexp hfac)
  have hco : 1 + 2 * (B₁ + 1 / 4) ≤ 2 := by linarith
  have h2 := mul_le_mul_of_nonneg_right hco hfac
  linarith [hst, h2]

/-- It is large enough both for the mesoscopic pure-flux spine (factor `4 C_flux`)
and for the Term BC coefficient of the general-loading `D_h` bound (factor `4
C_BC`). -/
def jGateConst (d : ℕ) : ℝ  :=
  max 1 (max (4 * fluxCubeConst d) (4 * pqCubeConstB d))

theorem one_le_jGateConst (d : ℕ) : 1 ≤ jGateConst d  := le_max_left _ _

theorem jGateConst_pos (d : ℕ) : 0 < jGateConst d  :=
  lt_of_lt_of_le zero_lt_one (one_le_jGateConst d)

theorem four_mul_fluxCubeConst_le_jGateConst (d : ℕ) : 4 * fluxCubeConst d ≤ jGateConst d  :=
  le_trans (le_max_left _ _) (le_max_right _ _)

theorem four_mul_pqCubeConstB_le_jGateConst (d : ℕ) : 4 * pqCubeConstB d ≤ jGateConst d  :=
  le_trans (le_max_right _ _) (le_max_right _ _)

/-- The mesoscopic depth attached to the base coefficient and the perturbation. -/
def jDepth (d : ℕ) (a : CoeffOn (cubeDomain (originCube d 0)))
    (h : UnitCubeSkewW2Infinity d) (s : ℝ) : ℕ  :=
  Mesoscale.mesoscaleDepth s (1 + jGateConst d *
    (h.gradientW1Infinity * (unitCubeLambda s (.finite 2) a)⁻¹))

/-! ## The unconditional deep-cube gate -/

/-- **The unconditional deep-cube gate.**  At the mesoscopic depth, the
dimensionless quantity governing both the mesoscopic gauge bootstrap and the
Term BC coefficient is at most `1/C₀`, with no hypothesis on `h`. -/
theorem gradient_mul_cubeScaleFactor_mul_lambdaSq_inv_le [NeZero d]
    (a : CoeffOn (cubeDomain (originCube d 0))) (h : UnitCubeSkewW2Infinity d)
    (F : TriadicCoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 4) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d 0) (-((jDepth d a h s : ℕ) : ℤ))) :
    h.gradientW1Infinity *
        (cubeScaleFactor R * (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹) ≤
      (jGateConst d)⁻¹ := by
  classical
  have hgnn : 0 ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
  have hCpos : 0 < jGateConst d := jGateConst_pos d
  have hLnn : (0 : ℝ) ≤ (unitCubeLambda s (.finite 2) a)⁻¹ :=
    unitCubeLambda_inv_nonneg a hs0 isAdmissible_finite_two
  have hu1 : (1 : ℝ) ≤ 1 + jGateConst d *
      (h.gradientW1Infinity * (unitCubeLambda s (.finite 2) a)⁻¹) := by
    have : 0 ≤ jGateConst d *
        (h.gradientW1Infinity * (unitCubeLambda s (.finite 2) a)⁻¹) := by positivity
    linarith
  have hscale0 : ((originCube d 0).scale) = (0 : ℤ) := rfl
  have hkroot : (-((jDepth d a h s : ℕ) : ℤ)) ≤ (originCube d 0).scale := by
    rw [hscale0]
    exact neg_nonpos.mpr (Int.natCast_nonneg _)
  have hLeq : (unitCubeLambda s (.finite 2) a)⁻¹ =
      (Ch02.lambdaSq (originCube d 0) s (.finite 2) F)⁻¹ := by
    rw [unitCubeLambda_characterization s (.finite 2) a F hF]
  have hmono : Ch02.lambdaSq R s (.finite 2) F ≤
      Ch02.lambdaSq R (3 / 8) (.finite 2) F :=
    Ch02.lambdaSq_mono R F hs0 (by linarith) isAdmissible_finite_two
  have hposs : 0 < Ch02.lambdaSq R s (.finite 2) F :=
    Ch02.lambdaSq_pos R F hs0 isAdmissible_finite_two
  have hinv : (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ ≤
      (Ch02.lambdaSq R s (.finite 2) F)⁻¹ := by gcongr
  have hdesc := cubeScaleFactor_mul_lambdaSq_inv_le_rpow F hs0
    isAdmissible_finite_two hkroot hR
  have hWeq : Real.rpow (3 : ℝ)
        ((1 - 2 * s) * (((-((jDepth d a h s : ℕ) : ℤ)) : ℤ) : ℝ)) =
      Real.rpow (3 : ℝ) (-((1 - 2 * s) * ((jDepth d a h s : ℕ) : ℝ))) := by
    congr 1
    push_cast
    ring
  have hWnn : (0 : ℝ) ≤
      Real.rpow (3 : ℝ) (-((1 - 2 * s) * ((jDepth d a h s : ℕ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hchain : cubeScaleFactor R * (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ ≤
      Real.rpow (3 : ℝ) (-((1 - 2 * s) * ((jDepth d a h s : ℕ) : ℝ))) *
        (unitCubeLambda s (.finite 2) a)⁻¹ := by
    calc cubeScaleFactor R * (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹
        ≤ cubeScaleFactor R * (Ch02.lambdaSq R s (.finite 2) F)⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (cubeScaleFactor_pos_cube R).le
      _ ≤ Real.rpow (3 : ℝ)
            ((1 - 2 * s) * (((-((jDepth d a h s : ℕ) : ℤ)) : ℤ) : ℝ)) *
            (Ch02.lambdaSq (originCube d 0) s (.finite 2) F)⁻¹ := hdesc
      _ = _ := by rw [hWeq, hLeq]
  have hkey := Mesoscale.sub_one_mul_three_rpow_neg_mesoscaleDepth_le_one hs0 hs hu1
  have hkey' : jGateConst d *
      (h.gradientW1Infinity * (unitCubeLambda s (.finite 2) a)⁻¹) *
      Real.rpow (3 : ℝ) (-((1 - 2 * s) * ((jDepth d a h s : ℕ) : ℝ))) ≤ 1 := by
    have hsub : (1 + jGateConst d *
        (h.gradientW1Infinity * (unitCubeLambda s (.finite 2) a)⁻¹)) - 1 =
        jGateConst d *
          (h.gradientW1Infinity * (unitCubeLambda s (.finite 2) a)⁻¹) := by ring
    rw [hsub] at hkey
    exact hkey
  have hstep := mul_le_mul_of_nonneg_left hchain hgnn
  refine hstep.trans ?_
  rw [show (jGateConst d)⁻¹ = 1 / jGateConst d from inv_eq_one_div _,
    le_div_iff₀ hCpos]
  linarith only [hkey']

/-! ## The mesoscopic gauge along the path -/

/-- **The mesoscopic coarse gauge at most doubles along the path.** -/
theorem cubeGauge_le_two_mul_zero [NeZero d] (dimension : 2 ≤ d)
    (a : CoeffOn (cubeDomain (originCube d 0))) (h : UnitCubeSkewW2Infinity d)
    (F : TriadicCoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    {k : ℤ} (hk : k ≤ (originCube d 0).scale) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d 0) k)
    (hsmall : 4 * mesoFluxConst d h R *
      cubeGauge R a h.toLInfSkewMatrixFieldOn 0 ≤ 1 / 2)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    cubeGauge R a h.toLInfSkewMatrixFieldOn τ ≤
      2 * cubeGauge R a h.toLInfSkewMatrixFieldOn 0 := by
  classical
  have hΨnn : ∀ t : ℝ, 0 ≤ cubeGauge R a h.toLInfSkewMatrixFieldOn t :=
    fun t => cubeGauge_nonneg R a _ t
  have hKnn : 0 ≤ mesoFluxConst d h R := mesoFluxConst_nonneg d h R
  have hBnn : (0 : ℝ) ≤ 4 * (d : ℝ) * (a.lam)⁻¹ := by
    have := a.lam_pos
    positivity
  have hcrude : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      cubeGauge R a h.toLInfSkewMatrixFieldOn t ≤ 4 * (d : ℝ) * (a.lam)⁻¹ :=
    fun t _ _ => cubeGauge_le_crude R a _ t
  have hengine : ∀ t₁ t₂ C : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ 1 →
      (∀ σ, t₁ ≤ σ → σ ≤ t₂ → cubeGauge R a h.toLInfSkewMatrixFieldOn σ ≤ C) →
      cubeGauge R a h.toLInfSkewMatrixFieldOn t₂ ≤
        Real.exp (mesoFluxConst d h R * C * (t₂ - t₁)) *
          cubeGauge R a h.toLInfSkewMatrixFieldOn t₁ :=
    fun t₁ t₂ C _ h12 _ hC =>
      cubeGauge_ratio_engine dimension a h F hF hk hR t₁ t₂ C h12 hC
  have hΨ0 : 0 ≤ cubeGauge R a h.toLInfSkewMatrixFieldOn 0 := hΨnn 0
  have hstrict : 4 * mesoFluxConst d h R *
      cubeGauge R a h.toLInfSkewMatrixFieldOn 0 < 1 := by linarith
  have hpos : 0 < 1 - 4 * mesoFluxConst d h R *
      cubeGauge R a h.toLInfSkewMatrixFieldOn 0 := by linarith
  have hmain := le_riccati_of_ratio_engine
    (Ψ := fun t => cubeGauge R a h.toLInfSkewMatrixFieldOn t)
    hΨnn hKnn hBnn hcrude hengine hstrict hτ0 hτ1
  refine hmain.trans ?_
  rw [div_le_iff₀ hpos]
  have hnn2 : (0 : ℝ) ≤ 2 * cubeGauge R a h.toLInfSkewMatrixFieldOn 0 := by
    linarith only [hΨ0]
  linarith only [mul_le_mul_of_nonneg_right hsmall hnn2]

/-! ## The two ODE coefficients -/

/-- The Term A coefficient of the path ODE at a mesoscopic cube. -/
def jTermACoeff (d : ℕ) (h : UnitCubeSkewW2Infinity d)
    (F : TriadicCoeffFamily d) (R : TriadicCube d) (p : Vec d) : ℝ :=
  (1 / 2 : ℝ) * pqCubeConstA d *
      (vecNorm p * (Real.sqrt (valueBudget h R) +
        cubeScaleFactor R * h.gradientW1Infinity)) *
    (Real.sqrt 2 * Real.sqrt ((Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹))

/-- The Term BC coefficient of the path ODE at a mesoscopic cube. -/
def jTermBCoeff (d : ℕ) (h : UnitCubeSkewW2Infinity d)
    (F : TriadicCoeffFamily d) (R : TriadicCube d) : ℝ  :=
  (1 / 2 : ℝ) * (pqCubeConstB d * (h.gradientW1Infinity * cubeScaleFactor R)) *
    (2 * (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹)

theorem jTermACoeff_nonneg (h : UnitCubeSkewW2Infinity d)
    (F : TriadicCoeffFamily d) (R : TriadicCube d) (p : Vec d) :
    0 ≤ jTermACoeff d h F R p := by
  have h1 := pqCubeConstA_nonneg d
  have h2 : (0 : ℝ) ≤ vecNorm p := Ch02.vecNorm_nonneg p
  have h3 : (0 : ℝ) ≤ Real.sqrt (valueBudget h R) := Real.sqrt_nonneg _
  have h4 : (0 : ℝ) ≤ cubeScaleFactor R := (cubeScaleFactor_pos_cube R).le
  have h5 : (0 : ℝ) ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
  have h6 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have h7 : (0 : ℝ) ≤
      Real.sqrt ((Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹) := Real.sqrt_nonneg _
  unfold jTermACoeff
  positivity

theorem jTermBCoeff_nonneg [NeZero d] (h : UnitCubeSkewW2Infinity d)
    (F : TriadicCoeffFamily d) (R : TriadicCube d) :
    0 ≤ jTermBCoeff d h F R := by
  have h1 := pqCubeConstB_nonneg d
  have h4 : (0 : ℝ) ≤ cubeScaleFactor R := (cubeScaleFactor_pos_cube R).le
  have h5 : (0 : ℝ) ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
  have h7 : (0 : ℝ) ≤ (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ :=
    lambdaSq_inv_nonneg R F
  unfold jTermBCoeff
  positivity

/-! ## The error constant -/

/-- The error constant of the per-mesoscopic-cube `J`-sensitivity. -/
def jErrorConst (d : ℕ) : ℝ  :=
  max (4 * pqCubeConstA d ^ 2) (4 * pqCubeConstB d ^ 2)

theorem jErrorConst_nonneg (d : ℕ) : 0 ≤ jErrorConst d  :=
  le_trans (by positivity) (le_max_left _ _)

theorem four_mul_jTermACoeff_sq_le [NeZero d] (h : UnitCubeSkewW2Infinity d)
    (F : TriadicCoeffFamily d) (R : TriadicCube d) (p : Vec d) :
    4 * jTermACoeff d h F R p ^ 2 ≤
      jErrorConst d * (vecNormSq p * (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ *
        (valueBudget h R + cubeScaleFactor R ^ 2 * h.gradientW1Infinity ^ 2)) := by
  have hVnn : 0 ≤ valueBudget h R := valueBudget_nonneg h R
  have hΨnn : (0 : ℝ) ≤ (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ :=
    lambdaSq_inv_nonneg R F
  have hgnn : (0 : ℝ) ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
  have hcfnn : (0 : ℝ) ≤ cubeScaleFactor R := (cubeScaleFactor_pos_cube R).le
  have hpnn : (0 : ℝ) ≤ vecNormSq p := vecNormSq_nonneg p
  have hsqV : Real.sqrt (valueBudget h R) ^ 2 = valueBudget h R := Real.sq_sqrt hVnn
  have hsqΨ : Real.sqrt ((Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹) ^ 2 =
      (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ := Real.sq_sqrt hΨnn
  have hs2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hpsq : vecNorm p ^ 2 = vecNormSq p := Ch02.vecNorm_sq_eq_vecNormSq p
  have hexp : 4 * jTermACoeff d h F R p ^ 2 =
      2 * pqCubeConstA d ^ 2 * vecNormSq p *
        ((Real.sqrt (valueBudget h R) +
          cubeScaleFactor R * h.gradientW1Infinity) ^ 2) *
        (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ := by
    unfold jTermACoeff
    calc 4 * ((1 / 2 : ℝ) * pqCubeConstA d *
          (vecNorm p * (Real.sqrt (valueBudget h R) +
            cubeScaleFactor R * h.gradientW1Infinity)) *
          (Real.sqrt 2 *
            Real.sqrt ((Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹))) ^ 2
        = pqCubeConstA d ^ 2 * vecNorm p ^ 2 *
            ((Real.sqrt (valueBudget h R) +
              cubeScaleFactor R * h.gradientW1Infinity) ^ 2) *
            (Real.sqrt 2 ^ 2 *
              Real.sqrt ((Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹) ^ 2) := by ring
      _ = _ := by rw [hs2, hsqΨ, hpsq]; ring
  rw [hexp]
  have hkey : (Real.sqrt (valueBudget h R) +
      cubeScaleFactor R * h.gradientW1Infinity) ^ 2 ≤
      2 * (valueBudget h R + cubeScaleFactor R ^ 2 * h.gradientW1Infinity ^ 2) := by
    calc (Real.sqrt (valueBudget h R) +
          cubeScaleFactor R * h.gradientW1Infinity) ^ 2
        ≤ 2 * (Real.sqrt (valueBudget h R) ^ 2 +
            (cubeScaleFactor R * h.gradientW1Infinity) ^ 2) := by
          linarith only [sq_nonneg (Real.sqrt (valueBudget h R) -
            cubeScaleFactor R * h.gradientW1Infinity)]
      _ = 2 * (valueBudget h R +
            cubeScaleFactor R ^ 2 * h.gradientW1Infinity ^ 2) := by
          rw [hsqV]; ring
  have hKle : 4 * pqCubeConstA d ^ 2 ≤ jErrorConst d := le_max_left _ _
  have hVtot : (0 : ℝ) ≤ valueBudget h R +
      cubeScaleFactor R ^ 2 * h.gradientW1Infinity ^ 2 := by positivity
  have hcoef : (0 : ℝ) ≤ 2 * pqCubeConstA d ^ 2 * vecNormSq p *
      (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ := by positivity
  have hstep := mul_le_mul_of_nonneg_left hkey hcoef
  have hrest : (0 : ℝ) ≤ vecNormSq p *
      (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ *
      (valueBudget h R + cubeScaleFactor R ^ 2 * h.gradientW1Infinity ^ 2) := by
    positivity
  linarith only [hstep, mul_le_mul_of_nonneg_right hKle hrest]

theorem four_mul_jTermBCoeff_sq_le [NeZero d] (h : UnitCubeSkewW2Infinity d)
    (F : TriadicCoeffFamily d) (R : TriadicCube d) {T : ℝ} (hT : 0 ≤ T) :
    4 * jTermBCoeff d h F R ^ 2 * T ≤
      jErrorConst d * (cubeScaleFactor R ^ 2 *
        (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ ^ 2 *
        h.gradientW1Infinity ^ 2 * T) := by
  have hΨnn : (0 : ℝ) ≤ (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ :=
    lambdaSq_inv_nonneg R F
  have hgnn : (0 : ℝ) ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
  have hcfnn : (0 : ℝ) ≤ cubeScaleFactor R := (cubeScaleFactor_pos_cube R).le
  have hexp : 4 * jTermBCoeff d h F R ^ 2 * T =
      (4 * pqCubeConstB d ^ 2) * (cubeScaleFactor R ^ 2 *
        (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ ^ 2 *
        h.gradientW1Infinity ^ 2 * T) := by
    unfold jTermBCoeff
    ring
  rw [hexp]
  have hKle : 4 * pqCubeConstB d ^ 2 ≤ jErrorConst d := le_max_right _ _
  have hrest : (0 : ℝ) ≤ cubeScaleFactor R ^ 2 *
      (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ ^ 2 *
      h.gradientW1Infinity ^ 2 * T := by positivity
  exact mul_le_mul_of_nonneg_right hKle hrest

/-! ## The per-mesoscopic-cube `J`-sensitivity -/

/-- **The per-mesoscopic-cube `J`-sensitivity at a general loading.** -/
theorem responseJ_mesoscale_cube_sensitivity [NeZero d] (dimension : 2 ≤ d)
    (a : CoeffOn (cubeDomain (originCube d 0))) (h : UnitCubeSkewW2Infinity d)
    (F : TriadicCoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 4)
    {k : ℤ} (hk : k ≤ (originCube d 0).scale) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d 0) k)
    (hkeq : k = -((jDepth d a h s : ℕ) : ℤ)) (p q : Vec d) :
    responseJ (cubeDomain R)
        (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
          (descendantField hk hR h.toLInfSkewMatrixFieldOn) 1) p q ≤
      3 * responseJ (cubeDomain R) (F.coeffOn R) p q +
        jErrorConst d * (vecNormSq p *
          (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ *
          (valueBudget h R + cubeScaleFactor R ^ 2 * h.gradientW1Infinity ^ 2)) +
        jErrorConst d * (cubeScaleFactor R ^ 2 *
          (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ ^ 2 *
          h.gradientW1Infinity ^ 2 * |vecDot p q|) := by
  classical
  subst hkeq
  have hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)) :=
    openCubeSet_subset_of_mem_descendantsAtScale hk hR
  have hLone : cubeScaleFactor R ≤ 1 :=
    cubeScaleFactor_le_one_of_mem_descendantsAtScale hk hR
  have hcfnn : (0 : ℝ) ≤ cubeScaleFactor R := (cubeScaleFactor_pos_cube R).le
  have hgnn : (0 : ℝ) ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
  have hΨnn : (0 : ℝ) ≤ (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ :=
    lambdaSq_inv_nonneg R F
  have hCpos : 0 < jGateConst d := jGateConst_pos d
  have hTnn : (0 : ℝ) ≤ |vecDot p q| := abs_nonneg _
  -- the unconditional gate
  have hgate := gradient_mul_cubeScaleFactor_mul_lambdaSq_inv_le a h F hF hs0 hs hR
  have hgauge0 : cubeGauge R a h.toLInfSkewMatrixFieldOn 0 =
      (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ :=
    (cubeGauge_zero_eq_of_family a h.toLInfSkewMatrixFieldOn hk hR F hF).symm
  -- the mesoscopic smallness for the gauge bootstrap
  have hsmall : 4 * mesoFluxConst d h R *
      cubeGauge R a h.toLInfSkewMatrixFieldOn 0 ≤ 1 / 2 := by
    rw [hgauge0]
    have heq : 4 * mesoFluxConst d h R *
        (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ =
        (2 * fluxCubeConst d) * (h.gradientW1Infinity *
          (cubeScaleFactor R * (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹)) := by
      unfold mesoFluxConst
      ring
    rw [heq]
    have hFnn : (0 : ℝ) ≤ 2 * fluxCubeConst d := by
      have := fluxCubeConst_nonneg d
      linarith
    refine (mul_le_mul_of_nonneg_left hgate hFnn).trans ?_
    rw [inv_eq_one_div, mul_one_div, div_le_iff₀ hCpos]
    have h4 : 4 * fluxCubeConst d ≤ jGateConst d :=
      four_mul_fluxCubeConst_le_jGateConst d
    linarith
  -- the gate bounds the Term BC coefficient
  have hB₁le : jTermBCoeff d h F R ≤ 1 / 4 := by
    have heq : jTermBCoeff d h F R = pqCubeConstB d *
        (h.gradientW1Infinity *
          (cubeScaleFactor R * (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹)) := by
      unfold jTermBCoeff
      ring
    rw [heq]
    refine (mul_le_mul_of_nonneg_left hgate (pqCubeConstB_nonneg d)).trans ?_
    rw [inv_eq_one_div, mul_one_div, div_le_iff₀ hCpos]
    have h4 : 4 * pqCubeConstB d ≤ jGateConst d :=
      four_mul_pqCubeConstB_le_jGateConst d
    linarith
  -- the path data
  have hderiv : ∀ τ : ℝ, HasDerivAt
      (fun σ => responseJ (cubeDomain R)
        (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
          (descendantField hk hR h.toLInfSkewMatrixFieldOn) σ) p q)
      ((1 / 2 : ℝ) * dhLoadForm (cubeDomain R)
        (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
          (descendantField hk hR h.toLInfSkewMatrixFieldOn) τ)
        (descendantField hk hR h.toLInfSkewMatrixFieldOn) p q) τ := fun τ =>
    hasDerivAt_responseJ_perturbCoeffOn_pair dimension (cubeDomain R)
      (F.coeffOn R) (descendantField hk hR h.toLInfSkewMatrixFieldOn) p q τ
  have hynn : ∀ τ : ℝ, 0 ≤ responseJ (cubeDomain R)
      (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
        (descendantField hk hR h.toLInfSkewMatrixFieldOn) τ) p q :=
    fun τ => Ch02.responseJ_nonneg _ _ p q
  -- the pointwise derivative bound
  have hstep : ∀ τ : ℝ, (0 : ℝ) ≤ τ → τ ≤ 1 →
      (1 / 2 : ℝ) * dhLoadForm (cubeDomain R)
        (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
          (descendantField hk hR h.toLInfSkewMatrixFieldOn) τ)
        (descendantField hk hR h.toLInfSkewMatrixFieldOn) p q ≤
      jTermACoeff d h F R p * Real.sqrt (responseJ (cubeDomain R)
          (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
            (descendantField hk hR h.toLInfSkewMatrixFieldOn) τ) p q) +
        jTermBCoeff d h F R * responseJ (cubeDomain R)
          (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
            (descendantField hk hR h.toLInfSkewMatrixFieldOn) τ) p q +
        (jTermBCoeff d h F R * Real.sqrt |vecDot p q|) *
          Real.sqrt (responseJ (cubeDomain R)
            (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
              (descendantField hk hR h.toLInfSkewMatrixFieldOn) τ) p q) := by
    intro τ hτ0 hτ1
    have hAR : CoeffOn.AEEq
        ((rootCoeffFamily (perturbCoeffOn (cubeDomain (originCube d 0)) a
          h.toLInfSkewMatrixFieldOn τ)).coeffOn R)
        (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
          (descendantField hk hR h.toLInfSkewMatrixFieldOn) τ) :=
      coeffOn_descendant_aeeq_perturbCoeffOn a h.toLInfSkewMatrixFieldOn τ F _ hF
        (rootCoeffFamily_aeeq _) hk hR
    have hdh := abs_dhLoadForm_cube_le h hsub hLone
      (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
        (descendantField hk hR h.toLInfSkewMatrixFieldOn) τ)
      (rootCoeffFamily (perturbCoeffOn (cubeDomain (originCube d 0)) a
        h.toLInfSkewMatrixFieldOn τ)) hAR p q
    have habs : (1 / 2 : ℝ) * dhLoadForm (cubeDomain R)
        (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
          (descendantField hk hR h.toLInfSkewMatrixFieldOn) τ)
        (descendantField hk hR h.toLInfSkewMatrixFieldOn) p q ≤
        (1 / 2 : ℝ) * |dhLoadForm (cubeDomain R)
          (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
            (descendantField hk hR h.toLInfSkewMatrixFieldOn) τ)
          (descendantField hk hR h.toLInfSkewMatrixFieldOn) p q| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
    have hΨτle : (Ch02.lambdaSq R (3 / 8) (.finite 2)
        (rootCoeffFamily (perturbCoeffOn (cubeDomain (originCube d 0)) a
          h.toLInfSkewMatrixFieldOn τ)))⁻¹ ≤
        2 * (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹ := by
      have hgt : (Ch02.lambdaSq R (3 / 8) (.finite 2)
          (rootCoeffFamily (perturbCoeffOn (cubeDomain (originCube d 0)) a
            h.toLInfSkewMatrixFieldOn τ)))⁻¹ =
          cubeGauge R a h.toLInfSkewMatrixFieldOn τ := rfl
      rw [hgt, ← hgauge0]
      exact cubeGauge_le_two_mul_zero dimension a h F hF hk hR hsmall hτ0 hτ1
    have harith := dhBound_to_path_step
      (CA := pqCubeConstA d)
      (CB := pqCubeConstB d * (h.gradientW1Infinity * cubeScaleFactor R))
      (P := vecNorm p * (Real.sqrt (valueBudget h R) +
        cubeScaleFactor R * h.gradientW1Infinity))
      (G0 := (Ch02.lambdaSq R (3 / 8) (.finite 2) F)⁻¹)
      (Gt := (Ch02.lambdaSq R (3 / 8) (.finite 2)
        (rootCoeffFamily (perturbCoeffOn (cubeDomain (originCube d 0)) a
          h.toLInfSkewMatrixFieldOn τ)))⁻¹)
      (Y := responseJ (cubeDomain R)
        (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
          (descendantField hk hR h.toLInfSkewMatrixFieldOn) τ) p q)
      (T := |vecDot p q|)
      (by
        have h1 := pqCubeConstA_nonneg d
        have h2 : (0 : ℝ) ≤ vecNorm p := Ch02.vecNorm_nonneg p
        have h3 : (0 : ℝ) ≤ Real.sqrt (valueBudget h R) := Real.sqrt_nonneg _
        positivity)
      (by have := pqCubeConstB_nonneg d; positivity)
      (lambdaSq_inv_nonneg R _) hΨτle (hynn τ) hTnn
    have hhalf := mul_le_mul_of_nonneg_left hdh
      (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
    refine habs.trans (hhalf.trans (harith.trans (le_of_eq ?_)))
    unfold jTermACoeff jTermBCoeff
    ring
  -- integrate
  have hmain := path_ode_le hderiv hynn (jTermACoeff_nonneg h F R p)
    (jTermBCoeff_nonneg h F R) hB₁le hTnn hstep
  -- the base point
  have hy0 : responseJ (cubeDomain R)
      (perturbCoeffOn (cubeDomain R) (F.coeffOn R)
        (descendantField hk hR h.toLInfSkewMatrixFieldOn) 0) p q =
      responseJ (cubeDomain R) (F.coeffOn R) p q := by
    refine responseJ_eq_ofAEEq ?_ p q
    refine Filter.Eventually.of_forall fun x => ?_
    change (F.coeffOn R).toCoeffField x +
      (0 : ℝ) • (descendantField hk hR h.toLInfSkewMatrixFieldOn).1.1 x =
      (F.coeffOn R).toCoeffField x
    simp
  rw [hy0] at hmain
  have hYnn : 0 ≤ responseJ (cubeDomain R) (F.coeffOn R) p q :=
    Ch02.responseJ_nonneg _ _ p q
  have hA := four_mul_jTermACoeff_sq_le h F R p
  have hB := four_mul_jTermBCoeff_sq_le h F R (T := |vecDot p q|) hTnn
  linarith [hmain, hA, hB, hYnn]

end

end Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional
