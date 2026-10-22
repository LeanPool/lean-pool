/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.UFD
import Mathlib.RingTheory.IntegralClosure.GoingDown

/-!
# Krull heights of contracted primes and of two-equation intersections

## Main results

* `Ideal.height_under_eq_one_of_height_le_one`: a nonzero prime of height at most one in an
  integral extension of a normal Noetherian domain contracts to a prime of height one.
* `Ideal.isPrincipal_under_of_height_le_one`: over a unique factorization domain, that
  contraction is principal.
* `Ideal.height_eq_two_of_mem_minimalPrimes_span_pair`: if `f` is prime and does not divide
  `g`, every minimal prime of `(f, g)` has height two.
-/

@[expose] public section

namespace Ideal

/-- A nonzero prime of height at most one in an integral extension of a normal Noetherian domain
contracts to a prime of height one. -/
theorem height_under_eq_one_of_height_le_one
    (R A : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Algebra R A] [FaithfulSMul R A] [Algebra.IsIntegral R A]
    (Q : Ideal A) [Q.IsPrime] (hQ : Q ≠ ⊥) (hheight : Q.height ≤ 1) :
    (Q.under R).height = 1 := by
  have hne : Q.under R ≠ ⊥ := fun h => hQ (Ideal.eq_bot_of_under_eq_bot h)
  have hupper : (Q.under R).height ≤ 1 := by
    have he := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (Q.under R) Q
    exact (le_self_add.trans he.symm.le).trans hheight
  apply le_antisymm hupper
  by_contra! h
  have hz : (Q.under R).height = 0 := Order.lt_one_iff.mp h
  exact hne (Ideal.height_eq_zero_iff_eq_bot.mp hz)

/-- A nonzero prime of height at most one in an integral extension of a normal Noetherian unique
factorization domain contracts to a principal prime. -/
theorem isPrincipal_under_of_height_le_one
    (R A : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [UniqueFactorizationMonoid R]
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Algebra R A] [FaithfulSMul R A] [Algebra.IsIntegral R A]
    (Q : Ideal A) [Q.IsPrime] (hQ : Q ≠ ⊥) (hheight : Q.height ≤ 1) :
    (Q.under R).IsPrincipal :=
  UniqueFactorizationMonoid.isPrincipal_of_height_eq_one
    (height_under_eq_one_of_height_le_one R A Q hQ hheight)

/-- A nontrivial two-equation intersection with prime first equation is purely
of codimension two: all its minimal primes have height two. -/
theorem height_eq_two_of_mem_minimalPrimes_span_pair {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] {f g : R} (hf : Prime f) (hfg : ¬ f ∣ g)
    {p : Ideal R} (hp : p ∈ (Ideal.span ({f, g} : Set R)).minimalPrimes) :
    p.height = 2 := by
  classical
  have : p.IsPrime := hp.isPrime
  let : (Ideal.span ({f} : Set R)).IsPrime := (Ideal.span_singleton_prime hf.ne_zero).mpr hf
  have hpf : Ideal.span ({f} : Set R) ≤ p :=
    (Ideal.span_mono (by simp : ({f} : Set R) ⊆ {f, g})).trans hp.le
  have hpg : g ∈ p := hp.le (Ideal.subset_span (by simp))
  have hlt : Ideal.span ({f} : Set R) < p := by
    apply lt_of_le_of_ne hpf
    intro he
    exact hfg (Ideal.mem_span_singleton.mp (he ▸ hpg))
  have h1 := Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr hf.ne_zero) hf.not_isUnit
  have hlo := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  rw [h1] at hlo
  have hhi : p.height ≤ 2 := by
    have h := Ideal.height_le_card_of_mem_minimalPrimes_span_finset
      (s := ({f, g} : Finset R)) (by simpa using hp)
    exact h.trans (by exact_mod_cast (Finset.card_le_two : ({f, g} : Finset R).card ≤ 2))
  norm_num at hlo
  exact le_antisymm hhi hlo

end Ideal
