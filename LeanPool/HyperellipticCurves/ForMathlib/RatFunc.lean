/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.FieldTheory.RatFunc.Degree

/-!
# Complements to the `RatFunc` API

Results about rational function fields intended for eventual upstreaming to Mathlib:

* `RatFunc.not_isSquare_of_odd_intDegree`: a rational function of odd degree is not
  a square;
* `RatFunc.exists_algebraMap_eq_of_sq_mul_squarefree`: if `b² · f` is a polynomial with
  `f` squarefree, then `b` is a polynomial (by clearing denominators in lowest terms);
* `RatFunc.instNeZeroTwo`: `K(x)` has characteristic ≠ 2 when `K` does.
-/

@[expose] public section

open Polynomial

namespace RatFunc

variable {K : Type*} [Field K]

/-- A rational function of odd degree is not a square. -/
theorem not_isSquare_of_odd_intDegree {x : RatFunc K} (h : Odd x.intDegree) :
    ¬IsSquare x := by
  rintro ⟨r, rfl⟩
  rcases eq_or_ne r 0 with rfl | hr
  · simp at h
  · rw [intDegree_mul hr hr] at h
    obtain ⟨k, hk⟩ := h
    lia

/-- If `b² · f` is a polynomial and `f` is squarefree, then `b` is a polynomial. -/
theorem exists_algebraMap_eq_of_sq_mul_squarefree {f c : K[X]} (hf : Squarefree f)
    {b : RatFunc K} (hb : b ^ 2 * algebraMap K[X] _ f = algebraMap K[X] _ c) :
    ∃ p : K[X], algebraMap K[X] (RatFunc K) p = b := by
  have hd : algebraMap K[X] (RatFunc K) b.denom ≠ 0 := algebraMap_ne_zero b.denom_ne_zero
  have hnum : algebraMap K[X] (RatFunc K) b.num = b * algebraMap K[X] _ b.denom :=
    (div_eq_iff hd).mp b.num_div_denom
  have hpoly : b.num ^ 2 * f = c * b.denom ^ 2 := by
    apply algebraMap_injective K
    rw [map_mul, map_mul, map_pow, map_pow, hnum]
    linear_combination (algebraMap K[X] (RatFunc K) b.denom) ^ 2 * hb
  have hcop : IsCoprime (b.denom ^ 2) (b.num ^ 2) := (isCoprime_num_denom b).symm.pow
  have hdvd : b.denom ^ 2 ∣ f := hcop.dvd_of_dvd_mul_left ⟨c, by linear_combination hpoly⟩
  have hu : IsUnit b.denom := hf b.denom (by rwa [← sq])
  rw [(monic_denom b).eq_one_of_isUnit hu, map_one, mul_one] at hnum
  exact ⟨b.num, hnum⟩

/-- `K(x)` inherits `2 ≠ 0` from `K`. -/
instance instNeZeroTwo [NeZero (2 : K)] : NeZero (2 : RatFunc K) :=
  ⟨fun h ↦ NeZero.ne (2 : K)
    ((algebraMap K (RatFunc K)).injective (by rw [map_ofNat, map_zero]; exact h))⟩

end RatFunc

end
