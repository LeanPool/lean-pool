/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# MinkowskiLp

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Countable Minkowski in `L^q`, on `ℝ≥0∞`

Nothing here imports that file, and nothing here claims the anchor.  Everything
below is abstract measure theory on `ℝ≥0∞`: no model, no carrier, no cube
occurs.

## What is here

Mathlib supplies Minkowski's inequality in `L^q` on `ℝ≥0∞` for TWO functions
(`ENNReal.lintegral_Lp_add_le`).  This module supplies exactly that, and nothing else:

* `lintegral_rpow_finsetSum_le` — the finite-sum form, by induction on the
  index `Finset` from Mathlib's two-function inequality;
* `lintegral_rpow_tsum_le_tsum_rpow` — the countable form, by monotone
  convergence (`lintegral_iSup'`) along the partial sums;
* `lintegral_rpow_tsum_le_rpow_tsum` — the same with both sides raised to the
  `q`-th power, which is the shape the transport consumes.

No sign or summability side condition is needed anywhere: on `ℝ≥0∞` a `tsum`
is the supremum of its partial sums, so a divergent family simply makes both
sides `⊤`.

## References

* ABK26, `l.bounds.mathcal.E.aL`, Step 5.
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open MeasureTheory
open scoped ENNReal

variable {Omega : Type*} [MeasurableSpace Omega]

/-- A positive `ℝ≥0∞` power commutes with suprema.  Disclosed re-derivation of
`AeMeasurableTransport.lean`'s `private iSup_rpow_of_pos'`, made public here
because the Minkowski-ordered transport consumes it at the anchor's `sup_L`. -/
theorem iSup_rpow_of_pos {iota : Sort*} (f : iota → ℝ≥0∞) {q : ℝ} (hq : 0 < q) :
    (⨆ i, f i) ^ q = ⨆ i, f i ^ q := by
  have h := (ENNReal.orderIsoRpow q hq).map_iSup f
  simp only [ENNReal.orderIsoRpow_apply] at h
  exact h

/-- **Minkowski in `L^q` for a finite family of `ℝ≥0∞`-valued functions.**

For `q ≥ 1` and a.e. measurable `F i`,

```
( ∫⁻ (∑_{i ∈ t} F i)^q )^{1/q}  ≤  ∑_{i ∈ t} ( ∫⁻ (F i)^q )^{1/q} .
```

The induction step is Mathlib's two-function `ENNReal.lintegral_Lp_add_le`. -/
theorem lintegral_rpow_finsetSum_le {iota : Type*} {mu : Measure Omega} {q : ℝ}
    (hq : 1 ≤ q) (F : iota → Omega → ℝ≥0∞) (hF : ∀ i, AEMeasurable (F i) mu)
    (t : Finset iota) :
    (∫⁻ omega, (∑ i ∈ t, F i omega) ^ q ∂mu) ^ (1 / q) ≤
      ∑ i ∈ t, (∫⁻ omega, F i omega ^ q ∂mu) ^ (1 / q) := by
  classical
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  induction t using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      rw [ENNReal.zero_rpow_of_pos hq0, lintegral_zero,
        ENNReal.zero_rpow_of_pos (one_div_pos.mpr hq0)]
  | insert a t ha ih =>
      have hsumM : AEMeasurable (fun omega => ∑ i ∈ t, F i omega) mu :=
        Finset.aemeasurable_fun_sum t fun i _ => hF i
      have hmink := ENNReal.lintegral_Lp_add_le (μ := mu) (f := F a)
        (g := fun omega => ∑ i ∈ t, F i omega) (hF a) hsumM hq
      simp only [Pi.add_apply] at hmink
      simp only [Finset.sum_insert ha]
      exact le_trans hmink (add_le_add le_rfl ih)

/-- For `q ≥ 1` and a.e. measurable `F l`,

```
( ∫⁻ (∑'_l F l)^q )^{1/q}  ≤  ∑'_l ( ∫⁻ (F l)^q )^{1/q} .
```

Both sides are suprema of their partial-sum truncations -- the left one by
monotone convergence, the right one by the `ℝ≥0∞` `tsum` -- so the finite form
above passes to the limit with no summability hypothesis. -/
theorem lintegral_rpow_tsum_le_tsum_rpow {mu : Measure Omega} {q : ℝ} (hq : 1 ≤ q)
    (F : ℕ → Omega → ℝ≥0∞) (hF : ∀ l, AEMeasurable (F l) mu) :
    (∫⁻ omega, (∑' l : ℕ, F l omega) ^ q ∂mu) ^ (1 / q) ≤
      ∑' l : ℕ, (∫⁻ omega, F l omega ^ q ∂mu) ^ (1 / q) := by
  classical
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have hq1 : (0 : ℝ) < 1 / q := one_div_pos.mpr hq0
  have hpt : ∀ omega : Omega, (∑' l : ℕ, F l omega) ^ q =
      ⨆ N : ℕ, (∑ l ∈ Finset.range N, F l omega) ^ q := by
    intro omega
    rw [ENNReal.tsum_eq_iSup_nat, iSup_rpow_of_pos _ hq0]
  have hmeasN : ∀ N : ℕ,
      AEMeasurable (fun omega => (∑ l ∈ Finset.range N, F l omega) ^ q) mu := fun N =>
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (Finset.aemeasurable_fun_sum (Finset.range N) fun l _ => hF l)
  have hmonoN : ∀ᵐ omega ∂mu,
      Monotone fun N : ℕ => (∑ l ∈ Finset.range N, F l omega) ^ q :=
    Filter.Eventually.of_forall fun omega N1 N2 hN =>
      ENNReal.rpow_le_rpow
        (Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hN)) hq0.le
  have hkey : (∫⁻ omega, (∑' l : ℕ, F l omega) ^ q ∂mu) =
      ⨆ N : ℕ, ∫⁻ omega, (∑ l ∈ Finset.range N, F l omega) ^ q ∂mu := by
    rw [lintegral_congr hpt]
    exact lintegral_iSup' hmeasN hmonoN
  rw [hkey, iSup_rpow_of_pos _ hq1, ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N => ?_
  exact le_trans (lintegral_rpow_finsetSum_le hq F hF (Finset.range N))
    (le_iSup (fun N : ℕ =>
      ∑ l ∈ Finset.range N, (∫⁻ omega, F l omega ^ q ∂mu) ^ (1 / q)) N)

/-- **The countable Minkowski inequality, in the shape the Step-5 transport
consumes**: both sides raised to the `q`-th power. -/
theorem lintegral_rpow_tsum_le_rpow_tsum {mu : Measure Omega} {q : ℝ} (hq : 1 ≤ q)
    (F : ℕ → Omega → ℝ≥0∞) (hF : ∀ l, AEMeasurable (F l) mu) :
    (∫⁻ omega, (∑' l : ℕ, F l omega) ^ q ∂mu) ≤
      (∑' l : ℕ, (∫⁻ omega, F l omega ^ q ∂mu) ^ (1 / q)) ^ q := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have h := ENNReal.rpow_le_rpow (lintegral_rpow_tsum_le_tsum_rpow hq F hF) hq0.le
  rwa [← ENNReal.rpow_mul, one_div_mul_cancel (ne_of_gt hq0), ENNReal.rpow_one] at h

end Algsuperdiff.Section4.Provider.BoundsEaL
