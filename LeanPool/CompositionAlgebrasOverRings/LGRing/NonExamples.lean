/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.LGRing.Defs
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Tactic.NormNum

/-!
# Non-examples of LG rings

`ℤ` and `R[t]` (`R` a nonzero commutative domain) are not LG-rings (`GPR Exercise 11.42`). These
are cheap, high-value negative results: they stop `IsLGRing` being silently assumed for the two
most familiar base rings, and mark exactly where the classification in this project stops
applying.

## Main results

* `not_isLGRing_int` : `ℤ` is not an LG-ring.
* `not_isLGRing_polynomial` : `R[t]` is not an LG-ring, for `R` a nonzero commutative domain.

## Implementation notes

Both proofs go through `exists_isUnit_of_isUnit_quotient` (`LGRing/Defs.lean`) instead of `GPR`
Exercise 11.42's `X² + c` argument: if `R` is LG, `Rˣ → (R ⧸ (b))ˣ` is surjective for *every*
`b : R`, so exhibiting one `b` and one unit of `R ⧸ (b)` with no lift in `Rˣ` refutes `IsLGRing R`
directly, with no case analysis on fields needed at the application site (all of that is bundled
once, inside `exists_isUnit_of_isUnit_quotient` itself).

* `ℤ`, `b = 5`: `2` is a unit mod `5` (inverse `3`), but neither `1` nor `-1` — the only units of
  `ℤ` (`Int.units_eq_one_or`) — is `≡ 2 mod 5`.
* `R[t]`, `b = t²`: `1 + t` is a unit mod `t²` (inverse `1 - t`, since `(1+t)(1-t) = 1 - t²`), but
  the units of `R[t]` are exactly `C r` for `r ∈ Rˣ` (`Polynomial.isUnit_iff`, needs `R` a domain)
  — degree `0` — while anything `≡ 1 + t mod t²` has `t`-coefficient `1 ≠ 0`
  (`Polynomial.X_pow_dvd_iff`), hence is not of that form.

`GPR`'s discrete-valuation extension of the `R[t]` argument (any ring with a discrete valuation
admitting an element of odd negative valuation is not LG) is not formalized here.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, Exercise Exc. 11.42.
-/

@[expose] public section

open Polynomial

/-- `ℤ` is not an LG-ring (`GPR Exercise 11.42`): `2` is a unit mod `5`, but no unit of `ℤ` is
`≡ 2 mod 5` (the units of `ℤ` are `±1`, and neither is `≡ 2 mod 5`). -/
theorem not_isLGRing_int : ¬ IsLGRing ℤ := by
  intro hLG
  have hu2 : IsUnit (Ideal.Quotient.mk (Ideal.span {(5 : ℤ)}) 2) := by
    apply IsUnit.of_mul_eq_one (Ideal.Quotient.mk (Ideal.span {(5 : ℤ)}) 3)
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (Ideal.span {(5 : ℤ)})), Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton.mpr (by norm_num)
  obtain ⟨u', hu'⟩ := exists_isUnit_of_isUnit_quotient hLG 5 hu2.unit
  simp only [IsUnit.unit_spec] at hu'
  rcases Int.units_eq_one_or u' with rfl | rfl
  · simp only [Units.val_one] at hu'
    have hdvd : (5 : ℤ) ∣ (1 - 2) := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hu')
    norm_num at hdvd
  · simp only [Units.val_neg, Units.val_one] at hu'
    have hdvd : (5 : ℤ) ∣ (-1 - 2) := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hu')
    norm_num at hdvd

/-- `R[t]` is not an LG-ring, for `R` a nonzero commutative domain (`GPR Exercise 11.42`(b)):
`1 + t` is a unit mod `t²`, but no unit of `R[t]` — all of which have
degree `0` — is `≡ 1 + t mod t²`, since that congruence class has `t`-coefficient `1 ≠ 0`. -/
theorem not_isLGRing_polynomial (R : Type*) [CommRing R] [IsDomain R] :
    ¬ IsLGRing (Polynomial R) := by
  intro hLG
  have hu2 : IsUnit (Ideal.Quotient.mk (Ideal.span {(X : R[X]) ^ 2}) (1 + X)) := by
    apply IsUnit.of_mul_eq_one (Ideal.Quotient.mk (Ideal.span {(X : R[X]) ^ 2}) (1 - X))
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (Ideal.span {(X : R[X]) ^ 2})),
      Ideal.Quotient.eq]
    have heq : (1 + X) * (1 - X) - 1 = -(X ^ 2 : R[X]) := by ring
    rw [heq]
    exact Submodule.neg_mem _ (Ideal.mem_span_singleton_self _)
  obtain ⟨u', hu'⟩ := exists_isUnit_of_isUnit_quotient hLG (X ^ 2) hu2.unit
  simp only [IsUnit.unit_spec] at hu'
  obtain ⟨r, -, hr⟩ := Polynomial.isUnit_iff.mp u'.isUnit
  rw [← hr] at hu'
  have hdvd : (X : R[X]) ^ 2 ∣ (C r - (1 + X)) :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hu')
  rw [Polynomial.X_pow_dvd_iff] at hdvd
  have h1 := hdvd 1 (by norm_num)
  simp only [coeff_sub, coeff_C, coeff_add, coeff_one, coeff_X_one] at h1
  norm_num at h1
