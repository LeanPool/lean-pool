/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.MacaulayModified
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Clean price and accrued interest, on- and between-coupon dates

A coupon bond's quoted **clean price** omits the interest that has accrued
since the last coupon date; the **dirty (invoiced) price** is what actually
changes hands. Writing `f ∈ [0, 1)` for the fraction of the current coupon
period elapsed since the last coupon date, the street-convention dirty price
is the flat-compounded present value of the remaining cashflows, carried
forward by `f` periods:

  `Dirty(y, f) = (1 + y)^f · Σ c_i / (1 + y)^{t_i}`     (`bondPriceDisc` from
  `MacaulayModified`, with `t_i` the number of whole periods from the *last*
  coupon date to each cashflow, so the next coupon has `t_i = 1`): the
  `(1 + y)^f` factor carries the last-coupon-date present value forward by
  the elapsed fraction `f` of the period that has since run. `(1 + y)^f`
  here is `Real.rpow`, a compound-interest carry only for `1 + y > 0`; for
  `1 + y < 0` and `f ∈ (0, 1)` the value is junk. The on-coupon-date results
  fix `f = 0`, where `Real.rpow_zero` gives `1` for every `y`; the
  across-a-coupon-date limits assume `1 + y > 0`.

Accrued interest on the next coupon (its amount supplied separately as
`c1`, since it is not tied to the cashflow map `c`) is the simple-interest
share of that coupon already earned,

  `Accrued(f) = f · c₁`,

with **clean price** `Clean(y, f) = Dirty(y, f) - Accrued(f)`. On a coupon
date (`f = 0`) this collapses to the ordinary `bondPriceDisc` with zero
accrued interest — the two pricing conventions agree exactly where they must.

## Main definitions

* `dirtyPrice`: the flat-compounded present value of the remaining cashflows, carried forward by
  the elapsed fraction `f` of the current coupon period.
* `accruedInterest`: the simple-interest share of the next coupon accrued over the fraction `f`.
* `cleanPrice`: the dirty price minus the accrued interest.

## Main results

* `cleanPrice_eq_dirty_sub_accrued`: `Clean = Dirty - Accrued` by definition.
* `dirtyPrice_on_coupon_date`: `Dirty(y, 0) = bondPriceDisc s t c y`.
* `accruedInterest_on_coupon_date`: `Accrued(0) = 0`.
* `cleanPrice_on_coupon_date`: on a coupon date, clean price equals
  `bondPriceDisc` (equivalently, equals dirty price).

## Across a coupon date

At the end of a period (`f ↑ 1`) the next coupon `j ∈ s` (`t j = 1`) is paid and a
new period starts: the remaining cashflows are `s.erase j`, each one period
closer (`t i - 1`), and `f` restarts at `0`. With `1 + y > 0` and every
cashflow at least one period out (`∀ i ∈ s, 1 ≤ t i`, so `t i - 1` is the true
remaining tenor, not an `ℕ`-truncated `0`):

* `dirtyPrice_one_eq`: at `f = 1` the dirty price is the new period's dirty
  price plus `c j` (this one needs only `1 + y ≠ 0`).
* `tendsto_dirtyPrice_coupon_date`: the dirty price tends to the new period's
  dirty price **plus the coupon** `c j` — it drops by exactly the coupon paid.
* `tendsto_cleanPrice_coupon_date`: the clean price, with accrued interest
  on `c j`, tends to the new period's clean price — it is continuous across
  the coupon date. The full accrued coupon is what the dirty price sheds.

## References

* [Fabozzi, *Bond Markets, Analysis and Strategies*][FabozziBMAS]
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull]

## Tags

clean price, dirty price, accrued interest, coupon bond, bond quotation, day count fraction,
MSC 91G30, JEL G12
-/

@[expose] public section

namespace MathFin

open Filter Topology

variable {ι : Type*}

/-- Dirty price between coupon dates: the flat-compounded present value of
remaining cashflows, carried forward by the elapsed fraction `f` of the
current period. -/
noncomputable def dirtyPrice (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) (y f : ℝ) : ℝ :=
  (1 + y) ^ f * bondPriceDisc s t c y

/-- Accrued interest on the next coupon, as a simple-interest share of the
elapsed fraction `f` of the current period. `c1` is the next coupon's
amount, supplied directly by the caller rather than read off `c`. -/
def accruedInterest (c1 f : ℝ) : ℝ := f * c1

/-- Clean (quoted) price: dirty price minus accrued interest. As with
`accruedInterest`, `c1` is caller-supplied and not tied to `c`. -/
noncomputable def cleanPrice (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) (y f c1 : ℝ) : ℝ :=
  dirtyPrice s t c y f - accruedInterest c1 f

/-- Clean price is dirty price minus accrued interest, by construction. -/
theorem cleanPrice_eq_dirty_sub_accrued (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) (y f c1 : ℝ) :
    cleanPrice s t c y f c1 = dirtyPrice s t c y f - accruedInterest c1 f := rfl

/-- On a coupon date (`f = 0`), the dirty price collapses to the ordinary
discrete-compounding bond price. -/
theorem dirtyPrice_on_coupon_date (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) (y : ℝ) :
    dirtyPrice s t c y 0 = bondPriceDisc s t c y := by
  rw [dirtyPrice, Real.rpow_zero, one_mul]

/-- On a coupon date, no interest has accrued. -/
theorem accruedInterest_on_coupon_date (c1 : ℝ) : accruedInterest c1 0 = 0 :=
  zero_mul c1

/-- On a coupon date, clean price equals dirty price (equivalently, equals
the ordinary `bondPriceDisc`): the two conventions agree exactly on coupon
dates, where there is nothing left to accrue. -/
theorem cleanPrice_on_coupon_date (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) (y c1 : ℝ) :
    cleanPrice s t c y 0 c1 = bondPriceDisc s t c y := by
  rw [cleanPrice_eq_dirty_sub_accrued, dirtyPrice_on_coupon_date,
    accruedInterest_on_coupon_date, sub_zero]

/-- At the end of a period (`f = 1`), the dirty price is the new period's dirty
price plus the next coupon `c j` (`j ∈ s`) paid on that date: carrying the
last-coupon-date value one full period forward discounts every cashflow one
period less. -/
theorem dirtyPrice_one_eq [DecidableEq ι] (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) {y : ℝ}
    (hy : 1 + y ≠ 0) {j : ι} (hj : j ∈ s) (htj : t j = 1) (ht : ∀ i ∈ s, 1 ≤ t i) :
    dirtyPrice s t c y 1 = dirtyPrice (s.erase j) (fun i ↦ t i - 1) c y 0 + c j := by
  rw [dirtyPrice_on_coupon_date, dirtyPrice, Real.rpow_one, bondPriceDisc, Finset.mul_sum,
    bondPriceDisc, ← Finset.add_sum_erase s _ hj, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' (ht i (Finset.mem_of_mem_erase hi))
    rw [hn, Nat.add_sub_cancel, pow_succ]
    field_simp
  · rw [htj, pow_one]
    field_simp

/-- **The dirty price drops by the coupon at a coupon date.** As the elapsed
fraction `f` of the period rises to `1`, the dirty price tends to the new
period's dirty price (remaining cashflows `s.erase j`, each one period closer,
`f = 0`) plus the next coupon `c j` (`j ∈ s`) paid on the date. -/
theorem tendsto_dirtyPrice_coupon_date [DecidableEq ι] (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ)
    {y : ℝ} (hy : 0 < 1 + y) {j : ι} (hj : j ∈ s) (htj : t j = 1) (ht : ∀ i ∈ s, 1 ≤ t i) :
    Tendsto (fun f ↦ dirtyPrice s t c y f) (𝓝[<] 1)
      (𝓝 (dirtyPrice (s.erase j) (fun i ↦ t i - 1) c y 0 + c j)) := by
  rw [← dirtyPrice_one_eq s t c hy.ne' hj htj ht]
  exact ((Real.continuousAt_const_rpow hy.ne').mul continuousAt_const).continuousWithinAt

/-- **The clean price is continuous across a coupon date.** With accrued
interest on the next coupon `c j` (`j ∈ s`) being paid, the clean price tends, as `f ↑ 1`, to
the clean price at the start of the new period, whatever coupon `c1'` accrues
next: the coupon the dirty price sheds (`tendsto_dirtyPrice_coupon_date`) is
exactly the accrued interest that has built up to it. -/
theorem tendsto_cleanPrice_coupon_date [DecidableEq ι] (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ)
    {y : ℝ} (hy : 0 < 1 + y) {j : ι} (hj : j ∈ s) (htj : t j = 1) (ht : ∀ i ∈ s, 1 ≤ t i)
    (c1' : ℝ) :
    Tendsto (fun f ↦ cleanPrice s t c y f (c j)) (𝓝[<] 1)
      (𝓝 (cleanPrice (s.erase j) (fun i ↦ t i - 1) c y 0 c1')) := by
  have hacc : Tendsto (fun f ↦ accruedInterest (c j) f) (𝓝[<] 1) (𝓝 (c j)) := by
    simpa [accruedInterest] using
      ((continuous_mul_const (c j)).tendsto 1).mono_left nhdsWithin_le_nhds
  simpa [cleanPrice, accruedInterest_on_coupon_date] using
    (tendsto_dirtyPrice_coupon_date s t c hy hj htj ht).sub hacc

end MathFin
