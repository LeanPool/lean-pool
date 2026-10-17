/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

module

public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.FieldTheory.SeparableClosure

/-!
# Relative norms in finite separable extensions

The relative norm formula requires separability of the particular fraction-field extension,
which suffices also for function fields with imperfect base fields. This file retains the
project's separable-extension interface to Mathlib's `Ideal.relNorm_eq_pow_of_isMaximal` and
records its consequence for weighted sums of prime factors.
-/

@[expose] public section

open Module
open UniqueFactorizationMonoid
open scoped nonZeroDivisors

namespace MarkoffRiemannRoch

open _root_.Ideal

namespace Ideal


variable {R S : Type*} [CommRing R] [CommRing S]
  [IsDedekindDomain R] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [IsTorsionFree R S]

/-- The relative norm of a maximal ideal in a finite separable extension is the corresponding
prime below, raised to the inertia degree. This is the project's interface to
`Ideal.relNorm_eq_pow_of_isMaximal`. -/
theorem relNorm_eq_pow_of_isMaximal_of_isSeparable
    [@Algebra.IsSeparable (FractionRing R) (FractionRing S) _ _
      (FractionRing.liftAlgebra R (FractionRing S))]
    (P : Ideal S) (p : Ideal R) [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
    relNorm R P = p ^ P.inertiaDeg R := by
  exact _root_.Ideal.relNorm_eq_pow_of_isMaximal P p

/-- Relative norm preserves the weighted sum of prime factors, with each prime upstairs weighted
by its inertia degree over the prime below. -/
theorem sum_normalizedFactors_relNorm_of_isSeparable
    [@Algebra.IsSeparable (FractionRing R) (FractionRing S) _ _
      (FractionRing.liftAlgebra R (FractionRing S))]
    (I : Ideal S) (hI : I ≠ ⊥) (w : Ideal R → ℕ) :
    ((normalizedFactors (relNorm R I)).map w).sum =
      ((normalizedFactors I).map fun P =>
        P.inertiaDeg R * w (P.under R)).sum := by
  classical
  let : Algebra (FractionRing R) (FractionRing S) :=
    FractionRing.liftAlgebra R (FractionRing S)
  have aux : ∀ s : Multiset (Ideal S), (∀ P ∈ s, Prime P) →
      ((normalizedFactors (relNorm R s.prod)).map w).sum =
        (s.map fun P => P.inertiaDeg R * w (P.under R)).sum := by
    intro s hs
    induction s using Multiset.induction_on with
    | empty =>
        rw [Multiset.prod_zero, map_one]
        simp only [normalizedFactors_one, Multiset.map_zero, Multiset.sum_zero]
    | @cons P s ih =>
        have hP : Prime P := hs P (Multiset.mem_cons_self P s)
        have hs' : ∀ Q ∈ s, Prime Q := fun Q hQ => hs Q (Multiset.mem_cons_of_mem hQ)
        have hP0 : P ≠ ⊥ := hP.ne_zero
        have hs0 : s.prod ≠ ⊥ := Multiset.prod_ne_zero fun h =>
          (hs' ⊥ h).ne_zero rfl
        let p : Ideal R := P.under R
        let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP0
        let : p.IsMaximal := Ideal.IsMaximal.under R P
        let : P.LiesOver p := ⟨rfl⟩
        have hp0 : p ≠ ⊥ := by
          intro hp
          have : P.LiesOver (⊥ : Ideal R) := hp ▸ (inferInstance : P.LiesOver p)
          exact hP0 (Ideal.eq_bot_of_liesOver_bot R P)
        have hnorm : relNorm R P = p ^ P.inertiaDeg R :=
          relNorm_eq_pow_of_isMaximal_of_isSeparable P p
        have hnormP0 : relNorm R P ≠ ⊥ := (relNorm_eq_bot_iff.not.mpr hP0)
        have hnorms0 : relNorm R s.prod ≠ ⊥ :=
          relNorm_eq_bot_iff.not.mpr hs0
        rw [Multiset.prod_cons, map_mul, normalizedFactors_mul hnormP0 hnorms0,
          Multiset.map_add, Multiset.sum_add, hnorm, normalizedFactors_pow,
          UniqueFactorizationMonoid.normalizedFactors_irreducible
            (Ideal.prime_of_isPrime hp0
              (inferInstance : p.IsMaximal).isPrime).irreducible,
          normalize_eq, Multiset.nsmul_singleton]
        simp [ih hs', p]
  let s := normalizedFactors I
  have hsprod : s.prod = I := _root_.Ideal.prod_normalizedFactors_eq_self hI
  calc
    ((normalizedFactors (relNorm R I)).map w).sum =
        ((normalizedFactors (relNorm R s.prod)).map w).sum := by rw [hsprod]
    _ = (s.map fun P => P.inertiaDeg R * w (P.under R)).sum := by
      apply aux s
      intro P hP
      exact UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    _ = ((normalizedFactors I).map fun P =>
        P.inertiaDeg R * w (P.under R)).sum := rfl

end Ideal

end MarkoffRiemannRoch
