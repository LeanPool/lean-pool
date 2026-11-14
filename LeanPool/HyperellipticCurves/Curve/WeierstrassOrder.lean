/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Curve.PointValuation

import LeanPool.HyperellipticCurves.ForMathlib.Multiplicity

/-!
# Intrinsic order of a function element at a Weierstrass point (individual)

At a Weierstrass point `(x₀, 0)` the conjugate point coincides with the point, so the norm
decomposition (`emultiplicity_pointIdeal_element_weierstrass`) only gives the *sum*
`emult(z) + emult(star z) = 2·rootMult`. The two summands are equal by the `star`-symmetry (the
involution fixes the Weierstrass point ideal, `map_star_pointIdeal_zero`, and `emultiplicity` is
invariant under ring automorphisms, `Ideal.emultiplicity_map_ringEquiv`), so the individual
intrinsic order is `emult(z) = rootMult` of the norm — the algebraic `ord_{P_bar}(h_bar)` at a
Weierstrass point, matching the generic-chart `emultiplicity_pointIdeal_element_generic`.
-/

@[expose] public section

open Polynomial QuadraticAlgebra

namespace ChabautyColeman

variable {K : Type*} [Field K] {f : K[X]}

/-- The `star` involution fixes the Weierstrass point ideal (the two point ideals above `x₀`
coincide there). -/
theorem map_star_pointIdeal_zero {x₀ : K} :
    Ideal.map (starAlgEquiv (S := K) (R := K[X]) (a := f) (b := 0)).toRingEquiv
        (pointIdeal f x₀ 0) = pointIdeal f x₀ 0 := by
  simp only [pointIdeal, map_zero, sub_zero, Ideal.map_span, Set.image_pair,
    AlgEquiv.coe_toRingEquiv, starAlgEquiv_apply, star_algebraMap, HypRing.star_y]
  exact Ideal.span_pair_neg _ _

variable [NeZero (2 : K)] [Fact (Odd f.natDegree)] [Fact (Squarefree f)]

/-- **Intrinsic order of a function element (Weierstrass chart), individual.** At a Weierstrass
point the intrinsic order of `z` equals `rootMult` of the norm — the two branches contribute
equally by the `star`-symmetry. This is the algebraic `ord_{P_bar}(h_bar)` at a Weierstrass point.
-/
theorem emultiplicity_pointIdeal_element_weierstrass_eq {x₀ : K} (hb : (0 : K) ^ 2 = f.eval x₀)
    {z : HypRing K f} (hN : z.re ^ 2 - f * z.im ^ 2 ≠ 0) :
    emultiplicity (pointIdeal f x₀ 0) (Ideal.span {z})
      = rootMultiplicity x₀ (z.re ^ 2 - f * z.im ^ 2) := by
  have hspan : Ideal.span {star z} = Ideal.map
      (starAlgEquiv (S := K) (R := K[X]) (a := f) (b := 0)).toRingEquiv (Ideal.span {z}) := by
    rw [Ideal.map_span, Set.image_singleton, AlgEquiv.coe_toRingEquiv, starAlgEquiv_apply]
  have hsym : emultiplicity (pointIdeal f x₀ 0) (Ideal.span {star z})
      = emultiplicity (pointIdeal f x₀ 0) (Ideal.span {z}) := by
    rw [hspan]
    nth_rw 1 [← map_star_pointIdeal_zero (x₀ := x₀)]
    exact Ideal.emultiplicity_map_ringEquiv _ _ _
  have hsum := emultiplicity_pointIdeal_element_weierstrass hb hN
  have hrhs : rootMultiplicity x₀ (z.re ^ 2 - f * z.im ^ 2) • (2 : ℕ∞)
      = ((rootMultiplicity x₀ (z.re ^ 2 - f * z.im ^ 2) * 2 : ℕ) : ℕ∞) := by
    rw [nsmul_eq_mul]; push_cast; ring
  have hle : emultiplicity (pointIdeal f x₀ 0) (Ideal.span {z})
      ≤ ((rootMultiplicity x₀ (z.re ^ 2 - f * z.im ^ 2) * 2 : ℕ) : ℕ∞) := by
    rw [← hrhs, ← hsum]; exact le_self_add
  have hfin := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle
  rw [hsym] at hsum
  lift emultiplicity (pointIdeal f x₀ 0) (Ideal.span {z}) to ℕ using hfin with m hm
  rw [← Nat.cast_add, hrhs, Nat.cast_inj] at hsum
  rw [Nat.cast_inj]; lia

end ChabautyColeman
