/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Tactic.LinearCombination

/-! # Lifting a square root of −1 through a nilpotent

Part of the SVI polynomial-sign certificate (#174).

In a commutative ring in which `2` is invertible, if `x² + 1` is nilpotent then `−1` has an exact
square root (`exists_sq_neg_one_of_nilpotent`).

## Main results

* `exists_sq_neg_one_of_nilpotent`: in a nontrivial commutative ring with `2 * half = 1`, if
  `x ^ 2 + 1` is nilpotent for some `x`, then there is `u` with `u ^ 2 = -1`.

## Tags

nilpotent lifting, square root of minus one, Hensel-type lifting, SVI, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI

/-- Lift a square root of -1 through a nilpotent error. Each correction
squares the error, so the construction terminates after finitely many steps.
No reducedness assumption is needed. -/
theorem exists_sq_neg_one_of_nilpotent {A : Type*} [CommRing A] [Nontrivial A]
    (half : A) (hh : 2 * half = 1) (x : A) (hx : IsNilpotent (x ^ 2 + 1)) :
    ∃ u : A, u^2 = -1 := by
  obtain ⟨r, hr⟩ := hx
  induction r using Nat.strong_induction_on generalizing x with
  | ind r ih =>
    rcases r with _ | (_ | n)
    · norm_num at hr
    · exact ⟨x, by simpa only [Nat.zero_add, pow_one, add_eq_zero_iff_eq_neg] using hr⟩
    · let e := x^2+1
      let y := x*(1+e*half)
      have he : y^2+1 = e^2*(e+3)*half^2 := by
        dsimp [y, e]
        linear_combination -(x^2+1+2*(x^2+1)^2*half) * hh
      have hy : (y^2+1)^(n+1) = 0 := by
        rw [he, mul_pow, mul_pow, ← pow_mul]
        have hz : e^(2*(n+1)) = 0 := pow_eq_zero_of_le (by omega) hr
        rw [hz, zero_mul, zero_mul]
      exact ih (n+1) (by omega) y hy

end SVI
end MathFin
