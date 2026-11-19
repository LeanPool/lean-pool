/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-!
# A factor of a homogeneous polynomial is homogeneous

A candidate for `Mathlib.RingTheory.MvPolynomial.Homogeneous`: over a commutative semiring without
zero divisors, a factor `φ` of a homogeneous polynomial `φ * ψ` with `ψ ≠ 0` is homogeneous, of
degree its total degree (`MvPolynomial.IsHomogeneous.of_mul_left`).

The proof compares the least and the largest degree of the monomials of a polynomial: its order as
a power series, which is additive in a product (`MvPowerSeries.order_mul`), and its total degree,
which is additive too (`MvPolynomial.totalDegree_mul_of_isDomain`). In a homogeneous product the two
sums agree, so each factor has its least degree equal to its largest. Mathlib's file imports
neither of the two additivity results.
-/

@[expose] public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R] {φ ψ : MvPolynomial σ R} {n : ℕ}

-- The least degree of the monomials of `φ ≠ 0` is at most the largest.
private theorem order_coe_le_totalDegree (hφ : φ ≠ 0) :
    (φ : MvPowerSeries σ R).order ≤ φ.totalDegree := by
  obtain ⟨d, hd⟩ := exists_coeff_ne_zero hφ
  exact (MvPowerSeries.order_le (by rwa [coeff_coe])).trans
    (mod_cast le_totalDegree (mem_support_iff.mpr hd))

-- A polynomial homogeneous of degree `n` has no monomial of a degree below `n`.
private theorem IsHomogeneous.le_order_coe (h : φ.IsHomogeneous n) :
    (n : ℕ∞) ≤ (φ : MvPowerSeries σ R).order :=
  MvPowerSeries.le_order fun d hd ↦ by
    rw [coeff_coe]
    exact h.coeff_eq_zero (mod_cast hd.ne)

-- A polynomial whose least degree is at least its largest is homogeneous.
private theorem isHomogeneous_totalDegree_of_le_order
    (h : (φ.totalDegree : ℕ∞) ≤ (φ : MvPowerSeries σ R).order) :
    φ.IsHomogeneous φ.totalDegree := fun d hd ↦ by
  rw [Pi.one_def, ← Finsupp.degree_eq_weight_one]
  refine le_antisymm (le_totalDegree (mem_support_iff.mpr hd)) ?_
  exact_mod_cast h.trans (MvPowerSeries.order_le (by rwa [coeff_coe]))

/-- A factor `φ` of a homogeneous polynomial `φ * ψ` with `ψ ≠ 0`, over a semiring without zero
divisors, is homogeneous: in a product the least degrees of the monomials add up, and so do the
largest. -/
theorem IsHomogeneous.of_mul_left [NoZeroDivisors R] (h : (φ * ψ).IsHomogeneous n)
    (hψ : ψ ≠ 0) : φ.IsHomogeneous φ.totalDegree := by
  obtain rfl | hφ := eq_or_ne φ 0
  · exact isHomogeneous_zero ..
  refine isHomogeneous_totalDegree_of_le_order <|
    (ENat.add_le_add_iff_right (ENat.natCast_ne_top ψ.totalDegree)).mp ?_
  calc (φ.totalDegree + ψ.totalDegree : ℕ∞)
      ≤ n := mod_cast totalDegree_mul_of_isDomain hφ hψ ▸ h.totalDegree_le
    _ ≤ (φ : MvPowerSeries σ R).order + (ψ : MvPowerSeries σ R).order := by
      rw [← MvPowerSeries.order_mul, ← coe_mul]
      exact h.le_order_coe
    _ ≤ _ := add_le_add_right (order_coe_le_totalDegree hψ) _

end MvPolynomial

end
