/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.OneSidedOrlicz

/-!
# PrincipalResponseBudgetMoment

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
Binder descriptions below are an informal inventory only, NOT a source
certification; certification vocabulary is reserved for frozen source-facing
declarations.

# Provider: the second moment of a one-sided two-term weak-Orlicz bound

This module supplies the single probabilistic step of the budget `delta <=^2
|log gamma|^2 gamma` of ABK26, inside the proof of
`e.use.also.for.the.upper.bound`: the passage from the *tail* form of the
induction hypothesis `e.new.induction.for.shom` (`d.mathcalS.def`) to a *second
moment*.

```
  ... <= C 3^{t(m-h-n)} E[ mathcalE_{t,infinity,2}(cu_{m-h}; a_{m-h}, shom_{m-h})^2 ]
      <= C E^2 |log gamma|^2 gamma ,
```

and the last inequality is the only place where the induction state enters.
The induction state is stated as the one-sided two-term weak-Orlicz relation

```
  mathcalE_{s,infinity,2}(cu_m; a_m, shom_m)
    <=  O_{Gamma_2}( E s^{-1} gamma^{1/2} )
      + O_{Gamma_{1/2}}( s^{-2} exp(-E^{-3} gamma^{-1}) ) ,
```

i.e. `Algsuperdiff.Section3.Probability.IsTwoTermBigOWith` at the two
stretched-exponential tail functions `Gamma_2` and `Gamma_{1/2}`.  What is
proved below is the general fact that such a relation for a *nonnegative*
random variable controls its second moment by the two scales:

```
  E[X^2]  <=  c(sigma_1) A_1^2 + c(sigma_2) A_2^2 ,
```

with `c(sigma)` the explicit absolute constant `orliczSecondMomentConst`.

## How the two witnesses are handled

`IsTwoTermBigOWith` supplies measurable witnesses `Y, Z` with `X <= Y + Z`
pointwise and a one-sided tail for each.  The witnesses are *not* assumed
nonnegative, so the layer-cake moment bound of CoarseGraining's
`Homogenization.Probability.IndependentSums.GammaSigma.Basic`
(`integral_rpow_le_of_isBigOWith_gammaSigma`) is applied to their positive
parts `max(Y,0)`, `max(Z,0)`, which carry the same one-sided upper tails
because the tail threshold `A t` is positive for `t >= 1` and `A > 0`.  Since
`0 <= X <= max(Y,0) + max(Z,0)`, the elementary inequality `(u+v)^2 <= 2u^2 +
2v^2` finishes.  No symmetrization and no lower tail is used, matching the
one-sided source notation.

## Scope

Nothing here mentions the manuscript's cube, probe, defect, or scales: the
statements are about an arbitrary nonnegative random variable on a probability
space.  In particular no source node is claimed, and neither the value
`t = |log gamma|^{-1}` nor the window `s in [8 gamma, 1]` of `d.mathcalS.def`
appears.

## Main results

* `orliczSecondMomentConst`: the explicit absolute second-moment constant of
  the stretched-exponential class `Gamma_sigma`, and its positivity.
* `integrable_sq_of_isTwoTermBigOWith_gammaSigma`: square integrability.
* `integral_sq_le_of_isTwoTermBigOWith_gammaSigma`: **the second moment
  bound**.

## References

* ABK26, `d.mathcalS.def`, `e.new.induction.for.shom`.
* ABK26 (the budget of `e.use.also.for.the.upper.bound`).
* ABK26, Appendix (the weak-Orlicz notation).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section3

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-! ## Positive parts and the layer-cake moment at `p = 2` -/

private theorem rpow_two_eq_sq (y : ℝ) : y ^ (2 : ℝ) = y ^ 2 := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The positive part of a variable with a one-sided weak-Orlicz upper tail has
the same tail, the threshold `A t` being positive for `t >= 1`. -/
private theorem isBigOWith_posPart {mu : Measure Omega} {Psi : ℝ → ℝ}
    {X : Omega → ℝ} {A : ℝ} (hA : 0 < A)
    (hX : IndependentSums.IsBigOWith mu Psi X A) :
    IndependentSums.IsBigOWith mu Psi (fun omega => max (X omega) 0) A := by
  simpa only [max_comm] using
    Algsuperdiff.Section3.Probability.isBigOWith_max_zero hA hX

private theorem integral_sq_le_of_isBigOWith_gammaSigma
    {mu : Measure Omega} [IsProbabilityMeasure mu] {Y : Omega → ℝ} {A sigma : ℝ}
    (hsigma : 0 < sigma) (hA : 0 < A) (hYnonneg : ∀ omega, 0 ≤ Y omega)
    (hYm : AEMeasurable Y mu)
    (hY : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sigma) Y A) :
    ∫ omega, Y omega ^ 2 ∂mu ≤
      (IndependentSums.gammaMomentConst sigma * (2 : ℝ) ^ sigma⁻¹ * A) ^ 2 := by
  have h := IndependentSums.integral_rpow_le_of_isBigOWith_gammaSigma
    hsigma hA (by norm_num : (1 : ℝ) ≤ 2) hYnonneg hYm hY
  simpa only [rpow_two_eq_sq] using h

private theorem integrable_sq_of_isBigOWith_gammaSigma
    {mu : Measure Omega} [IsProbabilityMeasure mu] {Y : Omega → ℝ} {A sigma : ℝ}
    (hsigma : 0 < sigma) (hA : 0 < A) (hYnonneg : ∀ omega, 0 ≤ Y omega)
    (hYm : AEMeasurable Y mu)
    (hY : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sigma) Y A) :
    Integrable (fun omega => Y omega ^ 2) mu := by
  have h := IndependentSums.integrable_rpow_of_isBigOWith_gammaSigma
    hsigma hA (by norm_num : (1 : ℝ) ≤ 2) hYnonneg hYm hY
  simpa only [rpow_two_eq_sq] using h

/-! ## The second-moment constant -/

/-- The explicit absolute second-moment constant of the stretched-exponential
class `Gamma_sigma`: an `O_{Gamma_sigma}(A)` variable has second moment at most
`orliczSecondMomentConst sigma * A^2` after the factor `2` of the elementary
inequality `(u+v)^2 <= 2u^2 + 2v^2` is absorbed.  It depends on nothing but
`sigma`. -/
def orliczSecondMomentConst (sigma : ℝ) : ℝ :=
  2 * (IndependentSums.gammaMomentConst sigma * (2 : ℝ) ^ sigma⁻¹) ^ 2

theorem orliczSecondMomentConst_pos {sigma : ℝ} (hsigma : 0 < sigma) :
    0 < orliczSecondMomentConst sigma := by
  have h1 : 0 < IndependentSums.gammaMomentConst sigma :=
    IndependentSums.gammaMomentConst_pos hsigma
  have h2 : (0 : ℝ) < (2 : ℝ) ^ sigma⁻¹ := Real.rpow_pos_of_pos (by norm_num) _
  unfold orliczSecondMomentConst
  positivity

/-! ## The second moment of a two-term weak-Orlicz bound -/

variable {mu : Measure Omega} [IsProbabilityMeasure mu]

private theorem sq_integrable_and_integral_le_of_isTwoTermBigOWith_gammaSigma
    {X : Omega → ℝ} {A1 A2 sig1 sig2 : ℝ} (hsig1 : 0 < sig1) (hsig2 : 0 < sig2)
    (hXnonneg : ∀ omega, 0 ≤ X omega)
    (h : Probability.IsTwoTermBigOWith mu (IndependentSums.gammaSigma sig1)
      (IndependentSums.gammaSigma sig2) X A1 A2) :
    Integrable (fun omega => X omega ^ 2) mu ∧
      ∫ omega, X omega ^ 2 ∂mu ≤
        orliczSecondMomentConst sig1 * A1 ^ 2 +
          orliczSecondMomentConst sig2 * A2 ^ 2 := by
  obtain ⟨Y, Z, _hPsi1, _hPsi2, hA1, hA2, hXm, hYm, hZm, hdom, hYt, hZt⟩ := h
  set Yp : Omega → ℝ := fun omega => max (Y omega) 0 with hYp
  set Zp : Omega → ℝ := fun omega => max (Z omega) 0 with hZp
  have hYpnonneg : ∀ omega, 0 ≤ Yp omega := fun omega => le_max_right _ _
  have hZpnonneg : ∀ omega, 0 ≤ Zp omega := fun omega => le_max_right _ _
  have hYpm : Measurable Yp := hYm.max measurable_const
  have hZpm : Measurable Zp := hZm.max measurable_const
  have hYpt : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sig1) Yp A1 :=
    isBigOWith_posPart hA1 hYt
  have hZpt : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sig2) Zp A2 :=
    isBigOWith_posPart hA2 hZt
  have hIY : Integrable (fun omega => Yp omega ^ 2) mu :=
    integrable_sq_of_isBigOWith_gammaSigma hsig1 hA1 hYpnonneg hYpm.aemeasurable hYpt
  have hIZ : Integrable (fun omega => Zp omega ^ 2) mu :=
    integrable_sq_of_isBigOWith_gammaSigma hsig2 hA2 hZpnonneg hZpm.aemeasurable hZpt
  have hbound : ∀ omega, X omega ^ 2 ≤ 2 * Yp omega ^ 2 + 2 * Zp omega ^ 2 := by
    intro omega
    have h1 : X omega ≤ Yp omega + Zp omega :=
      le_trans (hdom omega) (add_le_add (le_max_left _ _) (le_max_left _ _))
    nlinarith [hXnonneg omega, hYpnonneg omega, hZpnonneg omega,
      sq_nonneg (Yp omega - Zp omega)]
  have hmaj : Integrable (fun omega => 2 * Yp omega ^ 2 + 2 * Zp omega ^ 2) mu :=
    (hIY.const_mul 2).add (hIZ.const_mul 2)
  have hXsqm : AEStronglyMeasurable (fun omega => X omega ^ 2) mu :=
    (hXm.pow_const 2).aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · refine hmaj.mono' hXsqm ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound omega
  · have hstep : ∫ omega, X omega ^ 2 ∂mu ≤
        ∫ omega, (2 * Yp omega ^ 2 + 2 * Zp omega ^ 2) ∂mu :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun omega => sq_nonneg _)
        hmaj (Filter.Eventually.of_forall hbound)
    have hsplit : ∫ omega, (2 * Yp omega ^ 2 + 2 * Zp omega ^ 2) ∂mu =
        2 * (∫ omega, Yp omega ^ 2 ∂mu) + 2 * ∫ omega, Zp omega ^ 2 ∂mu := by
      rw [integral_add (hIY.const_mul 2) (hIZ.const_mul 2), integral_const_mul,
        integral_const_mul]
    have hY2 := integral_sq_le_of_isBigOWith_gammaSigma hsig1 hA1 hYpnonneg
      hYpm.aemeasurable hYpt
    have hZ2 := integral_sq_le_of_isBigOWith_gammaSigma hsig2 hA2 hZpnonneg
      hZpm.aemeasurable hZpt
    have hexp1 : (IndependentSums.gammaMomentConst sig1 * (2 : ℝ) ^ sig1⁻¹ * A1) ^ 2 =
        (IndependentSums.gammaMomentConst sig1 * (2 : ℝ) ^ sig1⁻¹) ^ 2 * A1 ^ 2 := by
      ring
    have hexp2 : (IndependentSums.gammaMomentConst sig2 * (2 : ℝ) ^ sig2⁻¹ * A2) ^ 2 =
        (IndependentSums.gammaMomentConst sig2 * (2 : ℝ) ^ sig2⁻¹) ^ 2 * A2 ^ 2 := by
      ring
    rw [hexp1] at hY2
    rw [hexp2] at hZ2
    rw [hsplit] at hstep
    unfold orliczSecondMomentConst
    nlinarith [hY2, hZ2, hstep]

/-- A nonnegative random variable obeying the one-sided two-term weak-Orlicz
relation of `d.mathcalS.def` at two stretched-exponential classes is square
integrable. -/
theorem integrable_sq_of_isTwoTermBigOWith_gammaSigma
    {X : Omega → ℝ} {A1 A2 sig1 sig2 : ℝ} (hsig1 : 0 < sig1) (hsig2 : 0 < sig2)
    (hXnonneg : ∀ omega, 0 ≤ X omega)
    (h : Probability.IsTwoTermBigOWith mu (IndependentSums.gammaSigma sig1)
      (IndependentSums.gammaSigma sig2) X A1 A2) :
    Integrable (fun omega => X omega ^ 2) mu :=
  (sq_integrable_and_integral_le_of_isTwoTermBigOWith_gammaSigma hsig1 hsig2
    hXnonneg h).1

/-- **The Orlicz-to-moment step of ABK26.**

A nonnegative random variable satisfying
`X <= O_{Gamma_{sig1}}(A_1) + O_{Gamma_{sig2}}(A_2)` in the one-sided sense of
the ABK26 Appendix has second moment at most
`c(sig1) A_1^2 + c(sig2) A_2^2`, with `c = orliczSecondMomentConst` an explicit
absolute constant.

Applied to `X = mathcalE_{s,infinity,2}(cu_m; a_m, shom_m)` with the two scales
of `e.new.induction.for.shom`, this is the only consumption of the induction
state in the budget of `e.use.also.for.the.upper.bound`.  No cube, probe or
scale of the manuscript appears here. -/
theorem integral_sq_le_of_isTwoTermBigOWith_gammaSigma
    {X : Omega → ℝ} {A1 A2 sig1 sig2 : ℝ} (hsig1 : 0 < sig1) (hsig2 : 0 < sig2)
    (hXnonneg : ∀ omega, 0 ≤ X omega)
    (h : Probability.IsTwoTermBigOWith mu (IndependentSums.gammaSigma sig1)
      (IndependentSums.gammaSigma sig2) X A1 A2) :
    ∫ omega, X omega ^ 2 ∂mu ≤
      orliczSecondMomentConst sig1 * A1 ^ 2 + orliczSecondMomentConst sig2 * A2 ^ 2 :=
  (sq_integrable_and_integral_le_of_isTwoTermBigOWith_gammaSigma hsig1 hsig2
    hXnonneg h).2

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
