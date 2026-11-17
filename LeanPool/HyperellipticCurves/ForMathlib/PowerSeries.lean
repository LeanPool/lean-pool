/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Order

import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# General facts about power series

Mathlib-gap lemmas about `PowerSeries`: the constant coefficient of a reduced series; the
constant coefficient and reduction of a polynomial evaluated at a power series; and the order of a
series with nonzero constant coefficient.
-/

@[expose] public section

open Polynomial

namespace PowerSeries

/-- The univariate counterpart of `MvPowerSeries.constantCoeff_map`. -/
@[simp]
theorem constantCoeff_map {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) (φ : R⟦X⟧) :
    constantCoeff (map f φ) = f (constantCoeff φ) :=
  rfl

variable {O : Type*} [CommRing O]

/-! ### Constant coefficient, reduction, and order -/

/-- The constant coefficient of `aeval x p` (a polynomial evaluated at a power series) is the
value of `p` at the constant coefficient of `x`. -/
theorem constantCoeff_aeval (p : O[X]) (x : O⟦X⟧) :
    constantCoeff (Polynomial.aeval x p) = p.eval (constantCoeff x) := by
  have h1 : (constantCoeff : O⟦X⟧ →+* O).comp (algebraMap O (O⟦X⟧)) = RingHom.id O :=
    RingHom.ext fun r ↦ constantCoeff_C r
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, h1, Polynomial.eval₂_id]

/-- A power series with nonzero constant coefficient has order `0`. -/
theorem order_eq_zero_of_constantCoeff_ne_zero {κ : Type*} [Semiring κ] {φ : κ⟦X⟧}
    (h : constantCoeff φ ≠ 0) : φ.order = 0 := by
  by_contra hne
  exact h (order_ne_zero_iff_constCoeff_eq_zero.mp hne)

/-- Reduction commutes with evaluation of a polynomial at a power series. -/
theorem map_aeval {O κ' : Type*} [CommRing O] [CommRing κ'] (ρ : O →+* κ') (s : O⟦X⟧) (p : O[X]) :
    (PowerSeries.map ρ) (Polynomial.aeval s p)
      = Polynomial.aeval ((PowerSeries.map ρ) s) (p.map ρ) := by
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.aeval_def, eval₂_map]
  congr 1
  ext a
  simp [PowerSeries.algebraMap_eq, PowerSeries.map_C]

/-- The formal derivative commutes with coefficientwise base change. -/
theorem map_derivative {K : Type*} [CommRing K] (ψ : O →+* K) (s : O⟦X⟧) :
    PowerSeries.map ψ (PowerSeries.derivative s)
      = PowerSeries.derivative (PowerSeries.map ψ s) := by
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_derivative, PowerSeries.coeff_derivative,
    PowerSeries.coeff_map, map_mul, map_add, map_natCast, map_one]

/-- Division in the power series ring by a series with unit constant coefficient. -/
theorem exists_mul_eq_of_constantCoeff_isUnit {O : Type*} [CommRing O] {D : PowerSeries O}
    (hD : IsUnit (PowerSeries.constantCoeff D)) (R : PowerSeries O) :
    ∃ m : PowerSeries O, m * D = R := by
  obtain ⟨v, hv⟩ := (PowerSeries.isUnit_iff_constantCoeff.mpr hD).exists_left_inv
  exact ⟨R * v, by rw [mul_assoc, hv, mul_one]⟩

end PowerSeries

end
