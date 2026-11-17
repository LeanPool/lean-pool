/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation

/-!
# Additions to the Weierstrass preparation API

Mathlib-gap facts about Weierstrass factorization of power series:

* the reduction of a distinguished polynomial modulo the ideal, which is `X ^ natDegree` by
  `Polynomial.IsDistinguishedAt.map_eq_X_pow`, has order equal to its degree
  (`Polynomial.IsDistinguishedAt.order_map_coe`);
* if a *polynomial* has a Weierstrass factorization `F = W·u` as a power series over a complete
  local ring, the unit cofactor `u` is itself the polynomial `F /ₘ W`
  (`PowerSeries.IsWeierstrassFactorization.polynomial_cofactor`).
-/

@[expose] public section

open Polynomial PowerSeries IsLocalRing

/-! ### The unit cofactor of a polynomial's Weierstrass factorization is a polynomial -/

/-- The reduction of a distinguished polynomial has order equal to its degree — it is
`X ^ natDegree` there. -/
theorem Polynomial.IsDistinguishedAt.order_map_coe {R : Type*} [CommRing R] {W : R[X]}
    {I : Ideal R} (hI : I ≠ ⊤) (hW : W.IsDistinguishedAt I) :
    ((W : PowerSeries R).map (Ideal.Quotient.mk I)).order = W.natDegree := by
  have := Ideal.Quotient.nontrivial_iff.mpr hI
  rw [← Polynomial.polynomial_map_coe, hW.map_eq_X_pow]
  push_cast
  exact PowerSeries.order_X_pow _

/-- If a *polynomial* `F` has a Weierstrass factorization `F = W·u` (as power series over a
complete local ring), then the unit `u` is itself a polynomial: the polynomial division
`F = W·(F /ₘ W) + (F %ₘ W)` is also a Weierstrass division, so by uniqueness `u = F /ₘ W` and
`F %ₘ W = 0`. Consequently root-counting for `F` needs no power-series evaluation. -/
theorem PowerSeries.IsWeierstrassFactorization.polynomial_cofactor {O : Type*} [CommRing O]
    [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O] {F W : O[X]} {u : O⟦X⟧}
    (hfac : (F : O⟦X⟧).IsWeierstrassFactorization W u) :
    F = W * (F /ₘ W) ∧ IsUnit ((F /ₘ W).coeff 0) ∧ ((F /ₘ W : O[X]) : O⟦X⟧) = u := by
  have hmon : W.Monic := hfac.isDistinguishedAt.monic
  have hWmap : (W : O⟦X⟧).map (residue O) ≠ 0 := by
    rw [← Polynomial.polynomial_map_coe, ne_eq, Polynomial.coe_eq_zero_iff]
    exact (hmon.map (residue O)).ne_zero
  have hord : ((W : O⟦X⟧).map (Ideal.Quotient.mk (maximalIdeal O))).order.toNat
      = W.natDegree := by
    rw [hfac.isDistinguishedAt.order_map_coe (IsLocalRing.maximalIdeal.isMaximal O).ne_top]
    exact ENat.toNat_natCast _
  have hA : (F : O⟦X⟧).IsWeierstrassDivision W u 0 := by
    constructor
    · rw [Polynomial.degree_zero]
      exact WithBot.bot_lt_coe _
    · rw [hfac.eq_mul, Polynomial.coe_zero, add_zero]
  have hB : (F : O⟦X⟧).IsWeierstrassDivision W (↑(F /ₘ W)) (F %ₘ W) := by
    constructor
    · rw [hord]
      exact lt_of_lt_of_le (degree_modByMonic_lt F hmon) (degree_le_natDegree)
    · rw [← Polynomial.coe_mul, ← Polynomial.coe_add]
      norm_cast
      rw [add_comm, modByMonic_add_div F W]
  obtain ⟨hqu, hr⟩ := hA.elim hWmap hB
  have hF : F = W * (F /ₘ W) := by
    nth_rw 1 [← modByMonic_add_div F W]
    rw [← hr, zero_add]
  refine ⟨hF, ?_, hqu.symm⟩
  have hcc := isUnit_iff_constantCoeff.mp hfac.isUnit
  rwa [hqu, Polynomial.constantCoeff_coe] at hcc

end
