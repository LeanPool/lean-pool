/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.DurationSensitivity
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Key-rate partials sum to the parallel-shift derivative

`MacaulayModified` prices a bond off a single flat yield, `P(y) = Σ cᵢ / (1 + y)^{tᵢ}`
(`bondPriceDisc`), and `DurationSensitivity` differentiates it: `P'(y) = -ModNum(y)`
(`hasDerivAt_bondPriceDisc`).
Key-rate analysis refines the flat yield to a curve: cashflow `i` is discounted at its own rate
`kᵢ` (one node per cashflow, not a tenor-indexed curve),

  `P(k) = Σ cᵢ / (1 + kᵢ)^{tᵢ}`     (`bondPriceKeyRate`).

The key-rate sensitivity to node `j` is the partial derivative `∂P/∂kⱼ`, the derivative of `P`
along the curve that moves `kⱼ` alone (`Function.update k j`). The key-rate duration is
`KRDⱼ = -(1/P)·∂P/∂kⱼ`; this module states its results for the partials and does not define
the durations.

The identity that makes key rates a decomposition of duration: the partials sum to the
derivative under a parallel shift `k ↦ k + ε·1`. On a flat curve `k ≡ y` the parallel shift is
a move of the flat yield, so the sum is `dP/dy`, the derivative `hasDerivAt_bondPriceDisc`
computes.

## Main definitions

* `bondPriceKeyRate`: the bond price with cashflow `i` discounted at its own rate `k i`, with
  annual compounding.

## Main results

* `bondPriceKeyRate_update_eq`: moving the spot rate of node `j ∈ s` to `x` leaves every other
  cashflow's term unchanged (used to prove both results below).
* `hasDerivAt_bondPriceKeyRate_update`: for `1 + kⱼ ≠ 0`, `∂P/∂kⱼ = -tⱼ·cⱼ / (1 + kⱼ)^{tⱼ+1}`,
  as a `HasDerivAt`.
* `hasDerivAt_bondPriceKeyRate_parallel`: on any curve, the parallel-shift derivative is
  `Σⱼ ∂P/∂kⱼ`, for any choice of witnesses `∂P/∂kⱼ`.
* `sum_keyRate_partials_eq_deriv_bondPriceDisc`, `sum_deriv_keyRate_eq_deriv_bondPriceDisc`:
  on a flat curve `k ≡ y` (`1 + y ≠ 0`), `Σⱼ ∂P/∂kⱼ = dP/dy` (`deriv (bondPriceDisc s t c) y`),
  for given partial-derivative witnesses and for the `deriv`s themselves.

## References

* [Ho, *Key rate durations: measures of interest rate risks*][Ho1992]

## Tags

key rate duration, partial duration, parallel shift, yield curve sensitivity, bond risk,
spot rate node, MSC 91G30, JEL G12
-/

@[expose] public section

namespace MathFin

variable {ι : Type*}

/-- Bond price with cashflow `i` discounted at its own rate `k i` (one node per cashflow),
annual compounding. On a flat curve it is `bondPriceDisc`. -/
noncomputable def bondPriceKeyRate (s : Finset ι) (t : ι → ℕ) (c k : ι → ℝ) : ℝ :=
  ∑ i ∈ s, c i / (1 + k i) ^ t i

/-- On a flat curve the key-rate price is the flat-yield price `bondPriceDisc`. -/
theorem bondPriceKeyRate_const (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) (y : ℝ) :
    bondPriceKeyRate s t c (fun _ ↦ y) = bondPriceDisc s t c y := rfl

/-- Moving the spot rate of node `j ∈ s` to `x` changes only cashflow `j`'s discount term; the
rest of the curve's contribution is unchanged. -/
theorem bondPriceKeyRate_update_eq [DecidableEq ι] (s : Finset ι) (t : ι → ℕ) (c k : ι → ℝ)
    {j : ι} (hj : j ∈ s) (x : ℝ) :
    bondPriceKeyRate s t c (Function.update k j x) =
      c j / (1 + x) ^ t j + ∑ i ∈ s.erase j, c i / (1 + k i) ^ t i := by
  rw [bondPriceKeyRate, ← Finset.add_sum_erase s _ hj, Function.update_self]
  congr 1
  exact Finset.sum_congr rfl fun i hi ↦ by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- **Key-rate partial derivative.** Moving the spot rate of node `j ∈ s` alone moves only
cashflow `j`'s discount term, so, for `1 + kⱼ ≠ 0`, `∂P/∂kⱼ = -tⱼ·cⱼ / (1 + kⱼ)^{tⱼ+1}`: the
per-cashflow derivative `hasDerivAt_coupon_term` that `hasDerivAt_bondPriceDisc` sums. -/
theorem hasDerivAt_bondPriceKeyRate_update [DecidableEq ι] (s : Finset ι) (t : ι → ℕ)
    (c k : ι → ℝ) {j : ι} (hj : j ∈ s) (hk : 1 + k j ≠ 0) :
    HasDerivAt (fun x ↦ bondPriceKeyRate s t c (Function.update k j x))
      (-((t j : ℝ) * c j / (1 + k j) ^ (t j + 1))) (k j) := by
  simpa only [bondPriceKeyRate_update_eq s t c k hj] using
    (hasDerivAt_coupon_term (c j) (t j) hk).add_const _

/-- **Key-rate partials sum to the parallel-shift derivative.** On any curve `k`, if `D j` is
the partial derivative `∂P/∂kⱼ` for every node `j ∈ s`, then the price along the parallel shift
`ε ↦ P(k + ε·1)` has derivative `Σⱼ D j` at `ε = 0`. The partials are taken as hypotheses, so
the statement holds for whatever `∂P/∂kⱼ` is — `hasDerivAt_bondPriceKeyRate_update` computes one
such witness in closed form. -/
theorem hasDerivAt_bondPriceKeyRate_parallel [DecidableEq ι] (s : Finset ι) (t : ι → ℕ)
    (c k : ι → ℝ) {D : ι → ℝ}
    (hD : ∀ j ∈ s,
      HasDerivAt (fun x ↦ bondPriceKeyRate s t c (Function.update k j x)) (D j) (k j)) :
    HasDerivAt (fun ε ↦ bondPriceKeyRate s t c (fun i ↦ k i + ε)) (∑ j ∈ s, D j) 0 := by
  unfold bondPriceKeyRate
  refine HasDerivAt.fun_sum fun j hj ↦ ?_
  have h0 : HasDerivAt (fun x ↦ bondPriceKeyRate s t c (Function.update k j x)) (D j)
      (k j + 0) := by simpa using hD j hj
  simpa only [bondPriceKeyRate_update_eq s t c k hj, add_sub_cancel_right] using
    (h0.comp_const_add (k j) 0).sub_const (∑ i ∈ s.erase j, c i / (1 + k i) ^ t i)

/-- **`Σⱼ ∂P/∂kⱼ = dP/dy`.** On a flat curve `k ≡ y` (with `1 + y ≠ 0`), the key-rate partials
`D j = ∂P/∂kⱼ` sum to the derivative of the flat-yield price `bondPriceDisc` at `y`: a
parallel shift of a flat curve is a move of the yield, so `hasDerivAt_bondPriceKeyRate_parallel`
and `hasDerivAt_bondPriceDisc` compute the same derivative. -/
theorem sum_keyRate_partials_eq_deriv_bondPriceDisc [DecidableEq ι] (s : Finset ι) (t : ι → ℕ)
    (c : ι → ℝ) {y : ℝ} (hy : 1 + y ≠ 0) {D : ι → ℝ}
    (hD : ∀ j ∈ s, HasDerivAt
      (fun x ↦ bondPriceKeyRate s t c (Function.update (fun _ ↦ y) j x)) (D j) y) :
    ∑ j ∈ s, D j = deriv (bondPriceDisc s t c) y := by
  have hpar := hasDerivAt_bondPriceKeyRate_parallel s t c (fun _ ↦ y) hD
  have hflat : HasDerivAt (fun ε ↦ bondPriceKeyRate s t c (fun _ ↦ y + ε))
      (-modifiedNumerator s t c y) 0 := by
    have := (hasDerivAt_bondPriceDisc s t c (y := y + 0) (by simpa using hy)).comp_const_add y 0
    rwa [add_zero] at this
  rw [hpar.unique hflat, (hasDerivAt_bondPriceDisc s t c hy).deriv]

/-- **`Σⱼ ∂P/∂kⱼ = dP/dy`, with the partials as `deriv`s.** On a flat curve `k ≡ y`
(`1 + y ≠ 0`), the key-rate partial derivatives sum to the derivative of the flat-yield price
`bondPriceDisc` at `y`. Each partial exists by `hasDerivAt_bondPriceKeyRate_update`. -/
theorem sum_deriv_keyRate_eq_deriv_bondPriceDisc [DecidableEq ι] (s : Finset ι) (t : ι → ℕ)
    (c : ι → ℝ) {y : ℝ} (hy : 1 + y ≠ 0) :
    ∑ j ∈ s, deriv (fun x ↦ bondPriceKeyRate s t c (Function.update (fun _ ↦ y) j x)) y =
      deriv (bondPriceDisc s t c) y :=
  sum_keyRate_partials_eq_deriv_bondPriceDisc s t c hy fun _ hj ↦
    (hasDerivAt_bondPriceKeyRate_update s t c _ hj hy).differentiableAt.hasDerivAt

end MathFin
