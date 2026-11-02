/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# PrincipalResponseLegsHolder

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Provider: sub-step (iv) of the principal response, the Hoelder leg

Source displays in ABK26:

* The first moment of Step 3's bad-event estimate,
  ```
  E[ | bfAhom_{m-1}^{-1/2} bfA_m(cu_n) bfAhom_{m-1}^{-1/2} |^8 ]^{1/8} <= C gamma^{-1} ,
  ```

* The second moment,
  ```
  ( avsum_{z} E[ | bfAhom_{m-1}^{1/2} P_z |^4 ] )^{1/4} <= C ,
  ```

* The conclusion
  ```
  avsum_z E[ P_z . bfA_m(z+cu_n) P_z 1_{not Q_z} ] <= C gamma^{-2} exp(-gamma^{-1})
                                                  <= (1/2) gamma^6 .
  ```

This module supplies the **Hoelder arithmetic** of that chain and nothing else.
Write `B` for the normalized matrix size of the first display and `V` for the
normalized load length of the second, so that the energy observable obeys the
pointwise domination `X <= B . V^2` used in the conclusion display.  Then the
printed four-way split `1/8 + 1/4 + 1/4 + 3/8 = 1` is realized here as two
nested two-factor Hoelder inequalities: an inner one at the conjugate pair
`(8, 2)` bounding `‖B
V^2‖_{8/5}` by `‖B‖_8 ‖V‖_4^2`, and an outer one at the conjugate pair `(8/5,
8/3)` separating the energy from the indicator of the bad event.

## The tail exponent is `3/8`, not `1`

Every statement below carries the honest exponent `3/8`; the printed exponent
`1` occurs nowhere.

## Main results

* `holderConjugate_eightFifths_eightThirds`, `holderTriple_eight_two_eightFifths`
* `eLpNorm_energy_le_of_moments` -- the inner split's energy factor.
* `integral_rpow_le_of_eLpNorm_le` -- descent from the seminorm to the source's
  own real moment root.
* `integral_mul_indicator_le_of_moment` -- the outer split at the exponent `3/8`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-! ## The two conjugate pairs -/

/-- **The outer conjugate pair**: `1/(8/5) + 1/(8/3) = 1`. -/
theorem holderConjugate_eightFifths_eightThirds :
    (8 / 5 : ℝ).HolderConjugate (8 / 3) := by
  rw [Real.holderConjugate_iff]
  constructor <;> norm_num

/-- **The inner conjugate pair**: `1/8 + 1/2 = 1/(8/5)`, which is the printed `1/8
+ 1/4 + 1/4` with the two load factors kept together as `V^2`. -/
instance holderTriple_eight_two_eightFifths :
    ENNReal.HolderTriple 8 2 (8 / 5) := by
  refine ⟨?_⟩
  rw [ENNReal.inv_div (by norm_num) (by norm_num)]
  rw [show (8 : ℝ≥0∞) = ((8 : ℝ≥0) : ℝ≥0∞) by norm_cast,
    show (2 : ℝ≥0∞) = ((2 : ℝ≥0) : ℝ≥0∞) by norm_cast,
    show (5 : ℝ≥0∞) = ((5 : ℝ≥0) : ℝ≥0∞) by norm_cast]
  rw [← ENNReal.coe_inv (by norm_num), ← ENNReal.coe_inv (by norm_num),
    ← ENNReal.coe_add, ← ENNReal.coe_div (by norm_num)]
  norm_cast
  norm_num

/-! ## The inner split: the energy factor -/

variable {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}

private theorem eLpNorm_sq_eq (V : Omega → ℝ) (hV0 : ∀ omega, 0 ≤ V omega) :
    eLpNorm (fun omega => V omega ^ (2 : ℕ)) 2 mu =
      eLpNorm V 4 mu ^ (2 : ℕ) := by
  by_cases hVm : AEStronglyMeasurable V mu
  swap
  · have hVsq : ¬ AEStronglyMeasurable (fun omega => V omega ^ (2 : ℕ)) mu := by
      intro h
      refine hVm ((Real.continuous_sqrt.comp_aestronglyMeasurable h).congr
        (Filter.Eventually.of_forall fun omega => ?_))
      exact Real.sqrt_sq (hV0 omega)
    rw [eLpNorm_of_not_aestronglyMeasurable hVsq, eLpNorm_of_not_aestronglyMeasurable hVm]
    simp
  have hfun : (fun omega => ‖V omega‖ ^ (2 : ℝ)) =
      fun omega => V omega ^ (2 : ℕ) := by
    funext omega
    rw [Real.norm_eq_abs, abs_of_nonneg (hV0 omega),
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hexp : (2 : ℝ≥0∞) * ENNReal.ofReal (2 : ℝ) = 4 := by
    rw [show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by simp]
    norm_num
  have hbase := eLpNorm_norm_rpow (μ := mu) (p := (2 : ℝ≥0∞)) V hVm (by norm_num : (0 : ℝ) < 2)
  rw [hfun, hexp] at hbase
  rw [hbase, ← ENNReal.rpow_natCast (eLpNorm V 4 mu) 2]
  norm_num

/-- **The energy factor.**  If the energy observable `X` is dominated pointwise by
`B . V^2`, then its `L^{8/5}` seminorm is at most the product `‖B‖_8 ‖V‖_4^2`
of the two moments printed.

This is the manuscript's four-way Hoelder `1/8 + 1/4 + 1/4 + 3/8 = 1` with the
two load factors kept together, so that only the two-factor inequality at the
pair `(8, 2)` is needed. -/
theorem eLpNorm_energy_le_of_moments {B V X : Omega → ℝ}
    (hB0 : ∀ omega, 0 ≤ B omega) (hV0 : ∀ omega, 0 ≤ V omega)
    (hX0 : ∀ omega, 0 ≤ X omega)
    (hdom : ∀ omega, X omega ≤ B omega * V omega ^ (2 : ℕ))
    (hXm : AEStronglyMeasurable X mu)
    (hBm : AEStronglyMeasurable B mu) (hVm : AEStronglyMeasurable V mu)
    {Cb Cv : ℝ} (hCb0 : 0 ≤ Cb) (hCv0 : 0 ≤ Cv)
    (hBn : eLpNorm B 8 mu ≤ ENNReal.ofReal Cb)
    (hVn : eLpNorm V 4 mu ≤ ENNReal.ofReal Cv) :
    eLpNorm X (8 / 5) mu ≤ ENNReal.ofReal (Cb * Cv ^ (2 : ℕ)) := by
  have hVsqm : AEStronglyMeasurable (fun omega => V omega ^ (2 : ℕ)) mu :=
    hVm.pow 2
  have hmono : eLpNorm X (8 / 5) mu ≤
      eLpNorm (fun omega => B omega * V omega ^ (2 : ℕ)) (8 / 5) mu := by
    refine eLpNorm_mono hXm fun omega => ?_
    have hprod : (0 : ℝ) ≤ B omega * V omega ^ (2 : ℕ) := by
      have := hB0 omega
      positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hX0 omega),
      abs_of_nonneg hprod]
    exact hdom omega
  have hholder :
      eLpNorm (fun omega => B omega * V omega ^ (2 : ℕ)) (8 / 5) mu ≤
        ((1 : ℝ≥0) : ℝ≥0∞) * eLpNorm B 8 mu *
          eLpNorm (fun omega => V omega ^ (2 : ℕ)) 2 mu := by
    refine eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (fun a b : ℝ => a * b) 1 continuous_mul
      hBm hVsqm (Filter.Eventually.of_forall fun omega => ?_)
    rw [norm_mul]
    simp
  rw [eLpNorm_sq_eq V hV0] at hholder
  refine le_trans hmono (le_trans hholder ?_)
  have hstep : ((1 : ℝ≥0) : ℝ≥0∞) * eLpNorm B 8 mu * eLpNorm V 4 mu ^ (2 : ℕ) ≤
      ENNReal.ofReal Cb * ENNReal.ofReal Cv ^ (2 : ℕ) := by
    rw [ENNReal.coe_one, one_mul]
    exact mul_le_mul' hBn (pow_le_pow_left' hVn 2)
  refine le_trans hstep (le_of_eq ?_)
  rw [← ENNReal.ofReal_pow hCv0, ← ENNReal.ofReal_mul hCb0]

/-! ## Descent to the source's real moment root -/

/-- The source writes its moments as real moment roots `(E[X^p])^{1/p}`.  A
seminorm bound descends to that form; when the moment fails to be integrable the
real integral takes its junk value and the bound is vacuous, so no integrability
hypothesis beyond `MemLp` is needed. -/
theorem integral_rpow_le_of_eLpNorm_le {X : Omega → ℝ}
    (hX0 : ∀ omega, 0 ≤ X omega) {p : ℝ} (hp : 0 < p)
    (hmem : MemLp X (ENNReal.ofReal p) mu) {R : ℝ} (hR : 0 ≤ R)
    (h : eLpNorm X (ENNReal.ofReal p) mu ≤ ENNReal.ofReal R) :
    (∫ omega, X omega ^ p ∂mu) ^ (1 / p) ≤ R := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    simpa using hp
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have htoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  have hrepr := hmem.eLpNorm_eq_integral_rpow_norm hp0 hptop
  rw [htoReal] at hrepr
  have hnorm : (fun omega => ‖X omega‖ ^ p) = fun omega => X omega ^ p := by
    funext omega
    rw [Real.norm_eq_abs, abs_of_nonneg (hX0 omega)]
  rw [hnorm] at hrepr
  rw [hrepr] at h
  have hnn : (0 : ℝ) ≤ (∫ omega, X omega ^ p ∂mu) ^ p⁻¹ :=
    Real.rpow_nonneg (integral_nonneg fun omega => Real.rpow_nonneg (hX0 omega) p) _
  have := (ENNReal.ofReal_le_ofReal_iff hR).1 h
  rwa [one_div]

/-! ## The outer split at the exponent `3/8` -/

/-- **The outer Hoelder split, at the honest tail exponent.**  For a nonnegative
energy observable in `L^{8/5}` and a measurable bad event `E`,

```
  E[ X 1_E ]  <=  ( E[ X^{8/5} ] )^{5/8} . P[E]^{3/8} .
``` -/
theorem integral_mul_indicator_le_moment_mul_measure [IsFiniteMeasure mu]
    {X : Omega → ℝ} {E : Set Omega} (hX0 : 0 ≤ᵐ[mu] X)
    (hmem : MemLp X (ENNReal.ofReal (8 / 5 : ℝ)) mu) (hE : MeasurableSet E) :
    ∫ omega, X omega * E.indicator (fun _ => (1 : ℝ)) omega ∂mu ≤
      (∫ omega, X omega ^ (8 / 5 : ℝ) ∂mu) ^ (5 / 8 : ℝ) *
        mu.real E ^ (3 / 8 : ℝ) := by
  have hgmem : MemLp (E.indicator fun _ => (1 : ℝ))
      (ENNReal.ofReal (8 / 3 : ℝ)) mu :=
    memLp_indicator_const (ENNReal.ofReal (8 / 3 : ℝ)) hE 1
      (Or.inr (measure_ne_top mu E))
  have hg0 : 0 ≤ᵐ[mu] E.indicator fun _ => (1 : ℝ) :=
    Filter.Eventually.of_forall fun omega =>
      Set.indicator_nonneg (fun _ _ => zero_le_one) omega
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    holderConjugate_eightFifths_eightThirds hX0 hg0 hmem hgmem
  have hgpow : ∀ omega,
      (E.indicator (fun _ => (1 : ℝ)) omega) ^ (8 / 3 : ℝ) =
        E.indicator (fun _ => (1 : ℝ)) omega := by
    intro omega
    by_cases homega : omega ∈ E
    · rw [Set.indicator_of_mem homega, Real.one_rpow]
    · rw [Set.indicator_of_notMem homega, Real.zero_rpow (by norm_num)]
  have hintg : ∫ omega, (E.indicator (fun _ => (1 : ℝ)) omega) ^ (8 / 3 : ℝ) ∂mu =
      mu.real E := by
    simp_rw [hgpow]
    simpa using integral_indicator_const (1 : ℝ) hE
  rw [hintg] at hholder
  have h1 : (1 : ℝ) / (8 / 5 : ℝ) = (5 / 8 : ℝ) := by norm_num
  have h2 : (1 : ℝ) / (8 / 3 : ℝ) = (3 / 8 : ℝ) := by norm_num
  rwa [h1, h2] at hholder

/-- **The one-cube bad-event energy bound.**  Composing the outer split with a
moment budget `Emom` and a probability tail `tail` gives

```
  E[ X 1_E ]  <=  Emom . tail^{3/8} .
```
-/
theorem integral_mul_indicator_le_of_moment [IsFiniteMeasure mu]
    {X : Omega → ℝ} {E : Set Omega} (hX0 : 0 ≤ᵐ[mu] X)
    (hmem : MemLp X (ENNReal.ofReal (8 / 5 : ℝ)) mu) (hE : MeasurableSet E)
    {Emom tail : ℝ}
    (hmom : (∫ omega, X omega ^ (8 / 5 : ℝ) ∂mu) ^ (5 / 8 : ℝ) ≤ Emom)
    (hEmom0 : 0 ≤ Emom) (htail : mu.real E ≤ tail) :
    ∫ omega, X omega * E.indicator (fun _ => (1 : ℝ)) omega ∂mu ≤
      Emom * tail ^ (3 / 8 : ℝ) := by
  refine le_trans
    (integral_mul_indicator_le_moment_mul_measure hX0 hmem hE) ?_
  have hpow : mu.real E ^ (3 / 8 : ℝ) ≤ tail ^ (3 / 8 : ℝ) :=
    Real.rpow_le_rpow measureReal_nonneg htail (by norm_num)
  have hpow0 : (0 : ℝ) ≤ mu.real E ^ (3 / 8 : ℝ) :=
    Real.rpow_nonneg measureReal_nonneg _
  exact mul_le_mul hmom hpow hpow0 hEmom0

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
