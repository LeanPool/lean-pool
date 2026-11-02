/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseMomentsOperator
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseLegsBudgetEllipticity

/-!
# PrincipalResponseMomentsFourth

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Provider: sub-step (iv) of the principal response, the fourth-moment display

Source display in ABK26, inside Step 3 of the proof of
`l.approximate.recurrence.formula` (label):

```
( avsum_{z in 3^n Zd cap cu_K} E[ | bfAhom_{m-1}^{1/2} P_z |^4 ] )^{1/4}  <=  C .
```

The manuscript proves the same display at the gauge `m - h` earlier in the same
proof ("and we get, by `e.nablaw.in.L.eight`"), and quotes it at the gauge `m
- 1` here.  Two things separate the two readings, and this module supplies both
of them:

* the **gauge transport** from `shom_{m-h}` to `shom_{m-1}`, which costs exactly
  the ratio `max( shom_{m-1}/shom_{m-h} , shom_{m-h}/shom_{m-1} )` on the
  squared length and its square on the fourth power; and
* the **collapse of the normalization**, which is sub-step (ii): because `P_z`
  is by definition `bfAhom_{m-h}^{-1/2}` applied to the raw averaged slope pair,
  `| bfAhom_{m-h}^{1/2} P_z |^2` is the *unnormalized*
  `|e' + (grad w_D)_R|^2 + |e + (grad w_N + shom^{-1} h e')_R|^2`.

## What is proved here, and what is not

Everything below is **pathwise**: an inequality between explicit functions of
the sample and of the two correctors, with no expectation taken.  The
manuscript's own display is an inequality between expectations, so the
statements here are strictly stronger in that respect, and strictly weaker in
another: the final numerical bound by the dimensional constant `C` is **not**
proved.  That bound needs `e.nablaw.in.L.eight` (label) together with the
comparison of the volume-normalized `L^4` and `L^8` norms on `cu_K` and the
second moment of the `Gamma_1` fluctuation it carries; none of those is invoked
below, and no declaration here asserts the display's right-hand side.

The two grid averages that remain on the right-hand side of
`descendantsAverage_sq_annealedSqrtNormSq_principalPz_le` are exactly the two
quantities that `e.nablaw.in.L.eight` is quoted for.  They are named, not
bounded.

## The `eLpNorm` bridges

The companion module `PrincipalResponseLegsBudget` takes the two moments in
seminorm form, as the binders `hBn : ‖B‖_8 <= Cb` and `hVn : ‖V‖_4 <= Cv`.
`eLpNorm_le_ofReal_of_integral_rpow_le` and its two specializations turn a real
moment bound `E[X^p] <= C^p` -- the form in which both displays are printed --
into exactly those binders, so that neither has to be stated twice.

## Main results

* `annealedSqrtNormSq`, `annealedSqrtNormSq_nonneg` -- the integrand
  `| bfAhom^{1/2} P |^2` of the display, and its nonnegativity.
* `gaugeRatio`, `annealedSqrtNormSq_le_gaugeRatio_mul`,
  `sq_annealedSqrtNormSq_le_gaugeRatio_sq_mul` -- the gauge transport.
* `annealedSqrtNormSq_principalPz_eq` -- the collapse, from sub-step (ii).
* `sq_annealedSqrtNormSq_principalPz_le` -- the pathwise fourth power.
* `descendantsAverage_sq_annealedSqrtNormSq_principalPz_le` -- the grid form.
* `eLpNorm_le_ofReal_of_integral_rpow_le`, `eLpNorm_eight_le_ofReal_of_moment`,
  `eLpNorm_four_le_ofReal_of_moment` -- the seminorm bridges.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Observable
open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ}

/-! ## The integrand -/

/-- **`| bfAhom^{1/2} P |^2`.**  The `shom`-weighted squared length of a doubled
load, `shom |P_1|^2 + shom^{-1} |P_2|^2`. -/
def annealedSqrtNormSq (sigma : PositiveScalar) (Y : BlockVec d) : ℝ :=
  (sigma : ℝ) * vecNormSq Y.1 + (sigma : ℝ)⁻¹ * vecNormSq Y.2

theorem annealedSqrtNormSq_nonneg (sigma : PositiveScalar) (Y : BlockVec d) :
    0 ≤ annealedSqrtNormSq sigma Y := by
  have h1 := vecNormSq_nonneg Y.1
  have h2 := vecNormSq_nonneg Y.2
  have hs1 := sigma.2.le
  have hs2 := (inv_pos.2 sigma.2).le
  rw [annealedSqrtNormSq]
  positivity

/-! ## The gauge transport -/

/-- The cost of reading the display at a different gauge: the larger of the two
diffusivity ratios.  At the manuscript's two scales, `e.shom.h.bounds` bounds
it by a dimensional constant, which is why the printed constant `C` does not
change between. -/
def gaugeRatio (sigmaLow sigmaTop : PositiveScalar) : ℝ :=
  max ((sigmaTop : ℝ) / (sigmaLow : ℝ)) ((sigmaLow : ℝ) / (sigmaTop : ℝ))

theorem gaugeRatio_pos (sigmaLow sigmaTop : PositiveScalar) :
    0 < gaugeRatio sigmaLow sigmaTop :=
  lt_of_lt_of_le (div_pos sigmaTop.2 sigmaLow.2) (le_max_left _ _)

/-- **The gauge transport.**  Changing the gauge of the squared length costs at
most the larger of the two diffusivity ratios. -/
theorem annealedSqrtNormSq_le_gaugeRatio_mul (sigmaLow sigmaTop : PositiveScalar)
    (Y : BlockVec d) :
    annealedSqrtNormSq sigmaTop Y ≤
      gaugeRatio sigmaLow sigmaTop * annealedSqrtNormSq sigmaLow Y := by
  have hL : (0 : ℝ) < (sigmaLow : ℝ) := sigmaLow.2
  have hT : (0 : ℝ) < (sigmaTop : ℝ) := sigmaTop.2
  have h1 := vecNormSq_nonneg Y.1
  have h2 := vecNormSq_nonneg Y.2
  have hup : (sigmaTop : ℝ) * vecNormSq Y.1 ≤
      gaugeRatio sigmaLow sigmaTop * ((sigmaLow : ℝ) * vecNormSq Y.1) := by
    have hratio : (sigmaTop : ℝ) / (sigmaLow : ℝ) ≤ gaugeRatio sigmaLow sigmaTop :=
      le_max_left _ _
    have hmul := mul_le_mul_of_nonneg_right hratio
      (mul_nonneg hL.le h1)
    refine le_trans (le_of_eq ?_) hmul
    field_simp
  have hdown : (sigmaTop : ℝ)⁻¹ * vecNormSq Y.2 ≤
      gaugeRatio sigmaLow sigmaTop * ((sigmaLow : ℝ)⁻¹ * vecNormSq Y.2) := by
    have hratio : (sigmaLow : ℝ) / (sigmaTop : ℝ) ≤ gaugeRatio sigmaLow sigmaTop :=
      le_max_right _ _
    have hmul := mul_le_mul_of_nonneg_right hratio
      (mul_nonneg (inv_pos.2 hL).le h2)
    refine le_trans (le_of_eq ?_) hmul
    field_simp
  rw [annealedSqrtNormSq, annealedSqrtNormSq, mul_add]
  linarith

/-- The gauge transport on the fourth power, which is what raises to. -/
theorem sq_annealedSqrtNormSq_le_gaugeRatio_sq_mul
    (sigmaLow sigmaTop : PositiveScalar) (Y : BlockVec d) :
    annealedSqrtNormSq sigmaTop Y ^ 2 ≤
      gaugeRatio sigmaLow sigmaTop ^ 2 * annealedSqrtNormSq sigmaLow Y ^ 2 := by
  have h := annealedSqrtNormSq_le_gaugeRatio_mul sigmaLow sigmaTop Y
  have h0 := annealedSqrtNormSq_nonneg sigmaTop Y
  have hsq := pow_le_pow_left₀ h0 h 2
  rwa [mul_pow] at hsq

/-! ## The collapse of the normalization: sub-step (ii) -/

/-- **The collapse at the load's own gauge.**  `ellipticityBudget_eq` read
through `annealedSqrtNormSq`: at the gauge that defines `P_z` the two
normalizations cancel exactly, leaving the raw averaged slope pair. -/
theorem annealedSqrtNormSq_principalPz_eq (sigma : PositiveScalar)
    (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ) (e e' : Vec d)
    {Q : TriadicCube d} (R : TriadicCube d) (wD : H10Function (openCubeSet Q))
    (wN : H1MeanZeroFunction (openCubeSet Q)) :
    annealedSqrtNormSq sigma
        (principalPz sigma omega lowScale highScale e e' R wD wN) =
      vecNormSq (e' + cubeAverageVec R (fun x => wD.toH1Function.grad x)) +
        vecNormSq
          (e + cubeAverageVec R
            (neumannFluxField sigma omega lowScale highScale e' wN)) := by
  rw [annealedSqrtNormSq]
  exact ellipticityBudget_eq sigma omega lowScale highScale e e' R wD wN

/-! ## The pathwise fourth power -/

private theorem sq_add_le_two_mul (A B : ℝ) :
    (A + B) ^ 2 ≤ 2 * (A ^ 2 + B ^ 2) := by
  nlinarith [sq_nonneg (A - B)]

/-- **The pathwise fourth power, at the display's gauge.**  For the localized load
`P_z` of `e.Pz.def` built at `sigmaLow` and read through the gauge `sigmaTop`,

```
| bfAhom_{sigmaTop}^{1/2} P_z |^4
  <= 2 rho^2 ( |e' + (grad w_D)_R|^4
               + |e + (grad w_N + sigmaLow^{-1} h e')_R|^4 ) ,
```

with `rho = gaugeRatio sigmaLow sigmaTop`. -/
theorem sq_annealedSqrtNormSq_principalPz_le (sigmaLow sigmaTop : PositiveScalar)
    (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ) (e e' : Vec d)
    {Q : TriadicCube d} (R : TriadicCube d) (wD : H10Function (openCubeSet Q))
    (wN : H1MeanZeroFunction (openCubeSet Q)) :
    annealedSqrtNormSq sigmaTop
          (principalPz sigmaLow omega lowScale highScale e e' R wD wN) ^ 2 ≤
      2 * gaugeRatio sigmaLow sigmaTop ^ 2 *
        (vecNormSq (e' + cubeAverageVec R (fun x => wD.toH1Function.grad x)) ^ 2 +
          vecNormSq
            (e + cubeAverageVec R
              (neumannFluxField sigmaLow omega lowScale highScale e' wN)) ^ 2) := by
  have hgauge := sq_annealedSqrtNormSq_le_gaugeRatio_sq_mul sigmaLow sigmaTop
    (principalPz sigmaLow omega lowScale highScale e e' R wD wN)
  rw [annealedSqrtNormSq_principalPz_eq] at hgauge
  have hsplit := sq_add_le_two_mul
    (vecNormSq (e' + cubeAverageVec R (fun x => wD.toH1Function.grad x)))
    (vecNormSq
      (e + cubeAverageVec R
        (neumannFluxField sigmaLow omega lowScale highScale e' wN)))
  have hrho : (0 : ℝ) ≤ gaugeRatio sigmaLow sigmaTop ^ 2 := sq_nonneg _
  have hstep := mul_le_mul_of_nonneg_left hsplit hrho
  refine le_trans hgauge (le_trans hstep (le_of_eq ?_))
  ring

/-! ## The grid form -/

/-- **The grid form.**  Averaging the pathwise fourth power over the triadic
subcubes of `Q = cu_K` at the localization depth `j = K - n`:

```
avsum_R | bfAhom_{sigmaTop}^{1/2} P_R |^4
  <= 2 rho^2 ( avsum_R |e' + (grad w_D)_R|^4
               + avsum_R |e + (grad w_N + sigmaLow^{-1} h e')_R|^4 ) .
``` -/
theorem descendantsAverage_sq_annealedSqrtNormSq_principalPz_le
    (sigmaLow sigmaTop : PositiveScalar) (omega : Cutoff.ShellSeq d)
    (lowScale highScale : ℤ) (e e' : Vec d) (Q : TriadicCube d) (j : ℕ)
    (wD : H10Function (openCubeSet Q))
    (wN : H1MeanZeroFunction (openCubeSet Q)) :
    descendantsAverage Q j
        (fun R =>
          annealedSqrtNormSq sigmaTop
            (principalPz sigmaLow omega lowScale highScale e e' R wD wN) ^ 2) ≤
      2 * gaugeRatio sigmaLow sigmaTop ^ 2 *
        (descendantsAverage Q j
            (fun R =>
              vecNormSq
                (e' + cubeAverageVec R (fun x => wD.toH1Function.grad x)) ^ 2) +
          descendantsAverage Q j
            (fun R =>
              vecNormSq
                (e + cubeAverageVec R
                  (neumannFluxField sigmaLow omega lowScale highScale e' wN))
                ^ 2)) := by
  classical
  have hmono := descendantsAverage_le_descendantsAverage Q j
    (F := fun R =>
      annealedSqrtNormSq sigmaTop
        (principalPz sigmaLow omega lowScale highScale e e' R wD wN) ^ 2)
    (G := fun R =>
      2 * gaugeRatio sigmaLow sigmaTop ^ 2 *
        (vecNormSq (e' + cubeAverageVec R (fun x => wD.toH1Function.grad x)) ^ 2 +
          vecNormSq
            (e + cubeAverageVec R
              (neumannFluxField sigmaLow omega lowScale highScale e' wN)) ^ 2))
    (fun R _ => sq_annealedSqrtNormSq_principalPz_le sigmaLow sigmaTop omega
      lowScale highScale e e' R wD wN)
  refine hmono.trans (le_of_eq ?_)
  rw [descendantsAverage_smul Q j (2 * gaugeRatio sigmaLow sigmaTop ^ 2)
      (fun R =>
        vecNormSq (e' + cubeAverageVec R (fun x => wD.toH1Function.grad x)) ^ 2 +
          vecNormSq
            (e + cubeAverageVec R
              (neumannFluxField sigmaLow omega lowScale highScale e' wN)) ^ 2),
    descendantsAverage_add Q j
      (fun R =>
        vecNormSq (e' + cubeAverageVec R (fun x => wD.toH1Function.grad x)) ^ 2)
      (fun R =>
        vecNormSq
          (e + cubeAverageVec R
            (neumannFluxField sigmaLow omega lowScale highScale e' wN)) ^ 2)]

/-! ## The seminorm bridges -/

section Seminorm

variable {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}

/-- **From a printed moment to the seminorm binder.**  Both displays are printed as
real moment roots `(E[X^p])^{1/p} <= C`; the Hoelder leg consumes them as
`eLpNorm` bounds.  For a nonnegative `X` in `L^p` the two are the same
statement. -/
theorem eLpNorm_le_ofReal_of_integral_rpow_le {X : Omega → ℝ}
    (hX0 : ∀ omega, 0 ≤ X omega) {p : ℝ} (hp : 0 < p)
    (hmem : MemLp X (ENNReal.ofReal p) mu) {C : ℝ} (hC0 : 0 ≤ C)
    (h : ∫ omega, X omega ^ p ∂mu ≤ C ^ p) :
    eLpNorm X (ENNReal.ofReal p) mu ≤ ENNReal.ofReal C := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by simpa using hp
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have htoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  have hrepr := hmem.eLpNorm_eq_integral_rpow_norm hp0 hptop
  rw [htoReal] at hrepr
  have hnorm : (fun omega => ‖X omega‖ ^ p) = fun omega => X omega ^ p := by
    funext omega
    rw [Real.norm_eq_abs, abs_of_nonneg (hX0 omega)]
  rw [hnorm] at hrepr
  rw [hrepr]
  refine ENNReal.ofReal_le_ofReal ?_
  have hint0 : (0 : ℝ) ≤ ∫ omega, X omega ^ p ∂mu :=
    integral_nonneg fun omega => Real.rpow_nonneg (hX0 omega) p
  have hstep : (∫ omega, X omega ^ p ∂mu) ^ p⁻¹ ≤ (C ^ p) ^ p⁻¹ :=
    Real.rpow_le_rpow hint0 h (by positivity)
  refine hstep.trans (le_of_eq ?_)
  rw [← Real.rpow_mul hC0, mul_inv_cancel₀ (ne_of_gt hp), Real.rpow_one]

private theorem ofReal_eight : ENNReal.ofReal (8 : ℝ) = (8 : ℝ≥0∞) := by
  simp

private theorem ofReal_four : ENNReal.ofReal (4 : ℝ) = (4 : ℝ≥0∞) := by
  simp

/-- **The binder `hBn`.**  The eighth moment of the operator norm, in the seminorm
form the Hoelder leg consumes. -/
theorem eLpNorm_eight_le_ofReal_of_moment {X : Omega → ℝ}
    (hX0 : ∀ omega, 0 ≤ X omega) (hmem : MemLp X (8 : ℝ≥0∞) mu) {C : ℝ}
    (hC0 : 0 ≤ C) (h : ∫ omega, X omega ^ (8 : ℝ) ∂mu ≤ C ^ (8 : ℝ)) :
    eLpNorm X (8 : ℝ≥0∞) mu ≤ ENNReal.ofReal C := by
  have hmem' : MemLp X (ENNReal.ofReal (8 : ℝ)) mu := by rwa [ofReal_eight]
  have := eLpNorm_le_ofReal_of_integral_rpow_le hX0 (by norm_num : (0 : ℝ) < 8)
    hmem' hC0 h
  rwa [ofReal_eight] at this

/-- **The binder `hVn`.**  The fourth moment of the normalized load length, in the
seminorm form the Hoelder leg consumes. -/
theorem eLpNorm_four_le_ofReal_of_moment {X : Omega → ℝ}
    (hX0 : ∀ omega, 0 ≤ X omega) (hmem : MemLp X (4 : ℝ≥0∞) mu) {C : ℝ}
    (hC0 : 0 ≤ C) (h : ∫ omega, X omega ^ (4 : ℝ) ∂mu ≤ C ^ (4 : ℝ)) :
    eLpNorm X (4 : ℝ≥0∞) mu ≤ ENNReal.ofReal C := by
  have hmem' : MemLp X (ENNReal.ofReal (4 : ℝ)) mu := by rwa [ofReal_four]
  have := eLpNorm_le_ofReal_of_integral_rpow_le hX0 (by norm_num : (0 : ℝ) < 4)
    hmem' hC0 h
  rwa [ofReal_four] at this

end Seminorm

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
