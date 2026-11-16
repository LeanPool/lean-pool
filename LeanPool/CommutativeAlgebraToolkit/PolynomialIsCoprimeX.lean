/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.Coprime.Basic

/-!
# Coprimality with `X - C a`

Over a commutative ring, `X - C a` is coprime to `p` if and only if `p.eval a` is a unit.

## Main statements

* `Polynomial.isCoprime_X_sub_C_iff`: `IsCoprime (X - C a) p ↔ IsUnit (p.eval a)`.
* `Polynomial.isCoprime_X_sub_C_iff_isUnit_sub`: `IsCoprime (X - C a) (X - C b) ↔ IsUnit (a - b)`.
* `Polynomial.isCoprime_X_iff`: `IsCoprime X p ↔ IsUnit (p.coeff 0)`.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R] {a b : R}

theorem isCoprime_X_sub_C_iff {p : R[X]} :
    IsCoprime (X - C a) p ↔ IsUnit (p.eval a) := by
  refine ⟨fun h ↦ by simpa [isCoprime_zero_left] using h.map (evalRingHom a), fun h ↦ ?_⟩
  have ⟨q, hq⟩ := X_sub_C_dvd_sub_C_eval (a := a) (p := p)
  rw [eq_add_of_sub_eq' hq]
  exact (isCoprime_one_right.of_isCoprime_of_dvd_right
    (isUnit_iff_dvd_one.1 (h.map C))).add_mul_left_right q

@[simp]
theorem isCoprime_X_sub_C_iff_isUnit_sub :
    IsCoprime (X - C a) (X - C b) ↔ IsUnit (a - b) := by
  simp [isCoprime_X_sub_C_iff]

theorem isCoprime_X_iff {p : R[X]} : IsCoprime X p ↔ IsUnit (p.coeff 0) := by
  simpa [coeff_zero_eq_eval_zero] using isCoprime_X_sub_C_iff (a := 0) (p := p)

end Polynomial
