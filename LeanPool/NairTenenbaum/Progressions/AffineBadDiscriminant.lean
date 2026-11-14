/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Polynomials.PolynomialLocal
public import LeanPool.NairTenenbaum.Progressions.AffineDiscriminant

/-! # The restricted discriminant after progression substitution -/

@[expose] public section

namespace NairTenenbaum.PolynomialSystem

open Polynomial

variable {k r : ℕ} (P : PolynomialSystem k r)

/-- Absolute-value form of equation (38). -/
theorem affine_discriminant (q : ℕ) (a : ℤ) (hq : q ≠ 0)
    (hqa : q.Coprime (P.total.eval a).natAbs) :
    (P.affine q a hq hqa).discriminant =
      q ^ (P.radical.natDegree * (P.radical.natDegree - 1)) * P.discriminant := by
  rw [PolynomialSystem.discriminant, P.affine_radical, discr_comp_affine _ _ _ hq,
    Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  rfl

/-- The new powers of primes dividing `q` do not enter the restricted
bad discriminant, since the transformed polynomial has no roots there. -/
theorem affine_badDiscriminant_factorization (q : ℕ) (a : ℤ) (hq : q ≠ 0)
    (hqa : q.Coprime (P.total.eval a).natAbs) (p : ℕ) :
    (P.affine q a hq hqa).badDiscriminant.factorization p =
      if p ∣ q then 0 else P.badDiscriminant.factorization p := by
  by_cases hp : p.Prime
  · rw [(P.affine q a hq hqa).badDiscriminant_factorization, P.affine_total,
      rootCount_comp_affine P.total q a p hqa]
    have H : q.Coprime p ↔ ¬p ∣ q := Nat.coprime_comm.trans hp.coprime_iff_not_dvd
    by_cases hpq : p ∣ q
    · simp only [ite_eq_left hpq, ite_eq_right (fun h => H.mp h hpq), ite_true]
    · rw [ite_eq_right hpq, ite_eq_left (H.mpr hpq), P.affine_discriminant,
        Nat.factorization_mul (pow_ne_zero _ hq) P.discriminant_pos.ne',
        Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply,
        Nat.factorization_eq_zero_of_not_dvd hpq, smul_zero, zero_add,
        P.badDiscriminant_factorization]
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp, Nat.factorization_eq_zero_of_not_prime _ hp]
    split_ifs <;> rfl

/-- The transformed restricted discriminant divides the original one. Thus a
finite divisor envelope of the Theorem 1 constants is uniform in `q` and `a`. -/
theorem affine_badDiscriminant_dvd (q : ℕ) (a : ℤ) (hq : q ≠ 0)
    (hqa : q.Coprime (P.total.eval a).natAbs) :
    (P.affine q a hq hqa).badDiscriminant ∣ P.badDiscriminant := by
  apply (Nat.factorization_le_iff_dvd (P.affine q a hq hqa).badDiscriminant_pos.ne'
    P.badDiscriminant_pos.ne').mp
  intro p
  rw [P.affine_badDiscriminant_factorization]
  split_ifs
  · exact Nat.zero_le _
  · exact le_rfl

end NairTenenbaum.PolynomialSystem
