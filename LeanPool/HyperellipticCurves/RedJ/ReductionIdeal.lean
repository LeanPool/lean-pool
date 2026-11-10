/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Curve.PointFactorization

/-!
# Products of point ideals over an algebraically closed field

Over an algebraically closed field `κ`, every effective divisor supported on affine points
of `y² = g(x)` is encoded by a multiplicity function `n` on the affine points; here we
define the corresponding ideal `ChabautyColeman.pointIdealProd n = ∏ₚ m_p^{n(p)}` of the
coordinate ring and record its formal properties: it is nonzero, multiplicative in `n`, and
— the key point, via the Nullstellensatz `ChabautyColeman.exists_pointIdeal_eq_of_isPrime` —
*every principal ideal is recovered from its multiplicity function*
(`ChabautyColeman.pointIdealProd_span`).

This is the target-side bookkeeping for the reduction map on the Jacobian (`def:redJ`): the
reduction of a class is defined by a multiplicity function on the reduced curve, and
`pointIdealProd_span` is what makes reduced principal divisors principal.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

/-- The affine points of the curve `y² = g(x)`, as a subtype of coordinate pairs. -/
abbrev AffinePair {κ : Type*} [CommRing κ] (g : κ[X]) : Type _ :=
  {p : κ × κ // p.2 ^ 2 = g.eval p.1}

variable {κ : Type*} [Field κ] {g : κ[X]}

/-- The ideal `∏ₚ m_p^{n(p)}` of the coordinate ring attached to a multiplicity function
`n` on the affine points: the ideal of the effective divisor with multiplicities `n`. -/
noncomputable def pointIdealProd (n : AffinePair g → ℕ) : Ideal (HypRing κ g) :=
  ∏ᶠ p : AffinePair g, pointIdeal g p.1.1 p.1.2 ^ n p

theorem mulSupport_pointIdeal_pow_subset (n : AffinePair g → ℕ) :
    (Function.mulSupport fun p : AffinePair g ↦ pointIdeal g p.1.1 p.1.2 ^ n p)
      ⊆ Function.support n := fun p hp ↦
  Function.mem_support.mpr fun h0 ↦
    Function.mem_mulSupport.mp hp (by rw [h0, pow_zero])

/-- `pointIdealProd` turns pointwise sums of multiplicity functions into products. -/
theorem pointIdealProd_add {n m : AffinePair g → ℕ} (hn : (Function.support n).Finite)
    (hm : (Function.support m).Finite) :
    pointIdealProd (fun p ↦ n p + m p) = pointIdealProd n * pointIdealProd m := by
  simp only [pointIdealProd, pow_add]
  exact finprod_mul_distrib (hn.subset (mulSupport_pointIdeal_pow_subset n))
    (hm.subset (mulSupport_pointIdeal_pow_subset m))

/-- A multiplicity function concentrated at one point gives a power of its point ideal. -/
theorem pointIdealProd_eq_pow (p₀ : AffinePair g) {n : AffinePair g → ℕ}
    (hn : ∀ p ≠ p₀, n p = 0) :
    pointIdealProd n = pointIdeal g p₀.1.1 p₀.1.2 ^ n p₀ :=
  finprod_eq_single _ p₀ fun p hp ↦ by rw [hn p hp, pow_zero]

/-- The zero multiplicity function gives the unit ideal. -/
theorem pointIdealProd_eq_top {n : AffinePair g → ℕ} (hn : ∀ p, n p = 0) :
    pointIdealProd (g := g) n = ⊤ := by
  rw [← Ideal.one_eq_top]
  exact finprod_eq_one_of_forall_eq_one fun p ↦ by rw [hn p, pow_zero]

theorem pointIdealProd_ne_zero [Fact (Odd g.natDegree)] (n : AffinePair g → ℕ) :
    pointIdealProd n ≠ 0 := by
  rw [pointIdealProd]
  by_cases hfin : (Function.mulSupport
      fun p : AffinePair g ↦ pointIdeal g p.1.1 p.1.2 ^ n p).Finite
  · rw [finprod_eq_prod _ hfin]
    exact Finset.prod_ne_zero_iff.mpr fun p _ ↦ pow_ne_zero _
      (pointIdeal_ne_zero g p.1.1 p.1.2)
  · rw [finprod_of_infinite_mulSupport hfin]
    exact one_ne_zero

variable [IsAlgClosed κ] [NeZero (2 : κ)] [Fact (Odd g.natDegree)] [Fact (Squarefree g)]

/-- Over an algebraically closed field, the affine points biject with the height-one primes
of the coordinate ring (Nullstellensatz + the point ideal determines the point). -/
theorem bijective_pointSpectrum :
    Function.Bijective fun p : AffinePair g ↦ pointSpectrum (f := g) p.2 := by
  constructor
  · intro p q hpq
    have h := congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hpq
    obtain ⟨h1, h2⟩ := (pointIdeal_eq_pointIdeal_iff p.2).mp h
    exact Subtype.ext (Prod.ext h1 h2)
  · intro v
    obtain ⟨x₀, y₀, h, hv⟩ := exists_pointIdeal_eq_of_isPrime v.isPrime v.ne_bot
    exact ⟨⟨(x₀, y₀), h⟩, IsDedekindDomain.HeightOneSpectrum.ext hv.symm⟩

/-- **Every principal ideal is the point-ideal product of its multiplicity function**: over
an algebraically closed field, `(z) = ∏ₚ m_p^{emult(m_p, (z))}`. -/
theorem pointIdealProd_span {z : HypRing κ g} (hz : z ≠ 0) :
    pointIdealProd (fun p : AffinePair g ↦
        (emultiplicity (pointIdeal g p.1.1 p.1.2) (Ideal.span {z})).toNat)
      = Ideal.span {z} := by
  rw [pointIdealProd]
  conv_rhs => rw [span_singleton_eq_finprod_heightOneSpectrum hz,
    ← finprod_comp (fun p : AffinePair g ↦ pointSpectrum (f := g) p.2) bijective_pointSpectrum]
  exact finprod_congr fun p ↦ rfl

end ChabautyColeman

end
