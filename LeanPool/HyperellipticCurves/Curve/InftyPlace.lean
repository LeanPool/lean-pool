/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Curve.IntegralClosure
public import Mathlib.RingTheory.Norm.Basic

/-!
# The infinite place of the hyperelliptic function field

For odd `deg f` the function field `F_K` has a unique place above the infinite place of `K(x)`
(totally ramified, `e = 2`). Its additive order is defined via the norm to `K(x)`:
`ord_∞(g) = -intDegree(N_{F_K/K(x)}(g))` (`ChabautyColeman.inftyOrd`). This is additive
(`inftyOrd_mul`), and on a polynomial function `h(x)` — embedded through `K(x)` — it gives
`ord_∞(h) = -2·deg h` (`inftyOrd_algebraMap`): a pole of order `2·deg h`, since `N(h) = h²` and
`intDegree(h²) = 2·deg h`. (Sanity: for the uniformizer `t = xᵍ/y`, `N(t) = x^{2g}/(-f)`, so
`intDegree = -1` and `ord_∞(t) = 1`.)

This is the function-order half of the intrinsic order at `∞` used in `lem:ord-match`; the
differential order `ord_∞(dx/y) = 2g-2` is developed separately.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

variable {K : Type*} [Field K] {f : K[X]} [Fact (Odd f.natDegree)]

/-- The additive order at the infinite place of `F_K`, via the norm to `K(x)`:
`ord_∞(g) = -intDegree(N(g))`. -/
noncomputable def inftyOrd (g : HypField K f) : ℤ := -(Algebra.norm (RatFunc K) g).intDegree

/-- `ord_∞` of a polynomial function `h(x)` is `-2·deg h` (a pole of order `2·deg h`), since
`N(h) = h²`. -/
@[simp]
theorem inftyOrd_algebraMap (h : K[X]) :
    inftyOrd (algebraMap (RatFunc K) (HypField K f) (algebraMap K[X] (RatFunc K) h))
      = -2 * (h.natDegree : ℤ) := by
  rw [inftyOrd, Algebra.norm_algebraMap, QuadraticAlgebra.finrank_eq_two]
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  · have hr : algebraMap K[X] (RatFunc K) h ≠ 0 := RatFunc.algebraMap_ne_zero hh
    rw [sq, RatFunc.intDegree_mul hr hr, RatFunc.intDegree_polynomial]
    ring

/-- `ord_∞` of a coordinate-ring function `P + Q·y` is `-deg(P² - f·Q²)`, the negated degree of
the norm (which is a polynomial). Both `= 0` in the degenerate `P² - f·Q² = 0` case (`z = 0`). -/
theorem inftyOrd_toHypField (P Q : K[X]) :
    inftyOrd (HypRing.toHypField f (⟨P, Q⟩ : HypRing K f))
      = -((P ^ 2 - f * Q ^ 2).natDegree : ℤ) := by
  have hnorm : Algebra.norm (RatFunc K) (HypRing.toHypField f (⟨P, Q⟩ : HypRing K f))
      = algebraMap K[X] (RatFunc K) (P ^ 2 - f * Q ^ 2) := by
    rw [QuadraticAlgebra.algebraNorm_eq_norm, QuadraticAlgebra.norm_def,
      HypRing.re_toHypField, HypRing.im_toHypField, map_sub, map_mul, map_pow, map_pow]
    ring
  rw [inftyOrd, hnorm, RatFunc.intDegree_polynomial]

/-- `ord_∞` is additive on products (it is the additive infinite-place valuation). -/
theorem inftyOrd_mul {g g' : HypField K f} (hg : g ≠ 0) (hg' : g' ≠ 0) :
    inftyOrd (g * g') = inftyOrd g + inftyOrd g' := by
  have hn : Algebra.norm (RatFunc K) g ≠ 0 := Algebra.norm_ne_zero_iff.mpr hg
  have hn' : Algebra.norm (RatFunc K) g' ≠ 0 := Algebra.norm_ne_zero_iff.mpr hg'
  rw [inftyOrd, inftyOrd, inftyOrd, map_mul, RatFunc.intDegree_mul hn hn']
  ring

end ChabautyColeman
