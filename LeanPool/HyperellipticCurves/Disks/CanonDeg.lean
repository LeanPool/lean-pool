/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Curve.PointValuation
public import LeanPool.HyperellipticCurves.Disks.CurvePoint
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import LeanPool.HyperellipticCurves.ForMathlib.Polynomial

/-!
# The degree of the canonical divisor, and the total vanishing budget

The divisor-degree / point-sum framework for `ω_bar = h_bar dx/y` on the residue curve.

* `cor:sum-ord` (`sum_ord_le`): over the residue field `F_p` (not necessarily algebraically
  closed), the point-sum `∑_{x₀} ∑_{y₀ : y₀²=f(x₀)} ord_{(x₀,y₀)}(h_bar)` plus the order at `∞`
  is `≤ 2g-2`. Each `x`-fiber has `0/1/2` points, so contributes `≤ 2·rootMult`, and
  `∑ rootMult ≤ deg h_bar`.

The `x`-fiber contribution is `fiber_sum_of_sq` (given a square root of `f(x₀)`); `fiber_sum_le`
(general, `≤ 2·rootMult`) specialises it. (The alg-closed *equality* version and the exact
canonical degree `2g-2` — `lem:canon-deg` — are formalized in
`upstream HyperellipticCurves.Archive.CanonDegExact`; the count needs only the one-sided bound.)
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

variable {κ : Type*} [Field κ] {f : κ[X]}
  [NeZero (2 : κ)] [Fact (Odd f.natDegree)] [Fact (Squarefree f)]

/-- Given a square root `b` of `f(x₀)`, the total order over the fiber `{y : y²=f(x₀)}` is
`2·rootMultiplicity x₀ h`: the fiber is `{±b}` (two points, generic) or `{0}` (one point,
Weierstrass), and both give `2·rootMult`. -/
theorem fiber_sum_of_sq {x₀ b : κ} (hb : b ^ 2 = f.eval x₀) {h : κ[X]} (hh : h ≠ 0) :
    ∑ᶠ y₀ ∈ {y : κ | y ^ 2 = f.eval x₀},
        (emultiplicity (pointIdeal f x₀ y₀)
          (Ideal.span {algebraMap κ[X] (HypRing κ f) h})).toNat
      = 2 * rootMultiplicity x₀ h := by
  classical
  rcases eq_or_ne b 0 with rfl | hbne
  · have hc : f.eval x₀ = 0 := by rw [← hb]; ring
    have hset : {y : κ | y ^ 2 = f.eval x₀} = {0} := by ext y; simp [hc, pow_eq_zero_iff]
    rw [hset, finsum_mem_singleton, emultiplicity_pointIdeal_weierstrass (by rw [hc]; ring) hh,
      nsmul_eq_mul]
    simp [mul_comm]
  · have hset : {y : κ | y ^ 2 = f.eval x₀} = ↑({b, -b} : Finset κ) := by
      ext y; rw [Set.mem_ofPred_eq, ← hb, sq_eq_sq_iff_eq_or_eq_neg]; simp
    have hbne' : b ≠ -b := fun heq ↦ hbne <|
      (mul_eq_zero.mp (show (2 : κ) * b = 0 by linear_combination heq)).resolve_left two_ne_zero
    rw [hset, finsum_mem_coe_finset, Finset.sum_pair hbne',
      emultiplicity_pointIdeal_generic hb hbne hh,
      emultiplicity_pointIdeal_generic (show (-b) ^ 2 = f.eval x₀ by rw [neg_pow]; simpa using hb)
        (neg_ne_zero.mpr hbne) hh]
    simp [two_mul]

/-- The fiber above `x₀` contributes at most `2·rootMult` (over any field): if `f(x₀)` is a square
the fiber sum equals `2·rootMult` (`fiber_sum_of_sq`); otherwise the fiber is empty and the sum is
`0`. -/
theorem fiber_sum_le {x₀ : κ} {h : κ[X]} (hh : h ≠ 0) :
    ∑ᶠ y₀ ∈ {y : κ | y ^ 2 = f.eval x₀},
        (emultiplicity (pointIdeal f x₀ y₀)
          (Ideal.span {algebraMap κ[X] (HypRing κ f) h})).toNat
      ≤ 2 * rootMultiplicity x₀ h := by
  by_cases hsq : ∃ b : κ, b ^ 2 = f.eval x₀
  · obtain ⟨b, hb⟩ := hsq
    exact (fiber_sum_of_sq hb hh).le
  · have hset : {y : κ | y ^ 2 = f.eval x₀} = ∅ := by
      ext y; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hy ↦ hsq ⟨y, hy⟩
    rw [hset, finsum_mem_empty]
    exact Nat.zero_le _

/-- The affine point-sum is at most `2·deg h` over any field: each `x`-fibre contributes
`≤ 2·rootMult` (`fiber_sum_le`), the support is finite (contained in the roots of `h`), and
`∑ rootMult ≤ deg h` (`finsum_rootMultiplicity_le`). -/
theorem finsum_fiber_sum_le {h : κ[X]} (hh : h ≠ 0) :
    (∑ᶠ x₀ : κ, ∑ᶠ y₀ ∈ {y : κ | y ^ 2 = f.eval x₀},
        (emultiplicity (pointIdeal f x₀ y₀)
          (Ideal.span {algebraMap κ[X] (HypRing κ f) h})).toNat)
      ≤ 2 * h.natDegree := by
  classical
  have hsub : (Function.support fun x₀ : κ ↦ ∑ᶠ y₀ ∈ {y : κ | y ^ 2 = f.eval x₀},
      (emultiplicity (pointIdeal f x₀ y₀)
        (Ideal.span {algebraMap κ[X] (HypRing κ f) h})).toNat) ⊆ ↑h.roots.toFinset := by
    intro x hx
    simp only [Function.mem_support] at hx
    rw [Finset.mem_coe, Multiset.mem_toFinset]
    have := lt_of_lt_of_le (Nat.pos_of_ne_zero hx) (fiber_sum_le (f := f) (x₀ := x) hh)
    exact Multiset.count_pos.mp (by rw [count_roots]; lia)
  have hR : ∑ x ∈ h.roots.toFinset, rootMultiplicity x h ≤ h.natDegree := by
    rw [← finsum_eq_finsetSum_of_support_subset _ (support_rootMultiplicity_subset h)]
    exact finsum_rootMultiplicity_le h
  rw [finsum_eq_finsetSum_of_support_subset _ hsub]
  calc ∑ x ∈ h.roots.toFinset, ∑ᶠ y₀ ∈ {y : κ | y ^ 2 = f.eval x},
          (emultiplicity (pointIdeal f x y₀)
            (Ideal.span {algebraMap κ[X] (HypRing κ f) h})).toNat
      ≤ ∑ x ∈ h.roots.toFinset, 2 * rootMultiplicity x h :=
        Finset.sum_le_sum fun x _ ↦ fiber_sum_le hh
    _ = 2 * ∑ x ∈ h.roots.toFinset, rootMultiplicity x h := by rw [Finset.mul_sum]
    _ ≤ 2 * h.natDegree := by lia

/-- **Total vanishing budget (`cor:sum-ord`).** Over the residue field `F_p` (not necessarily
algebraically closed), the sum of the orders over the affine points plus the order at `∞` is at
most `2g-2`. Each `x`-fibre contributes `≤ 2·rootMult` and `∑ rootMult ≤ deg h`. -/
theorem sum_ord_le {h : κ[X]} (hh : h ≠ 0) (hdeg : h.natDegree ≤ genus f - 1) :
    (∑ᶠ x₀ : κ, ∑ᶠ y₀ ∈ {y : κ | y ^ 2 = f.eval x₀},
        (emultiplicity (pointIdeal f x₀ y₀)
          (Ideal.span {algebraMap κ[X] (HypRing κ f) h})).toNat)
        + (2 * (genus f - 1) - 2 * h.natDegree)
      ≤ 2 * genus f - 2 := by
  lia [finsum_fiber_sum_le (f := f) hh]

end ChabautyColeman

end
