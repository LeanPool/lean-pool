/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Progressions.AffinePolynomialContent

/-! # Removing fixed prime divisors on finitely many progressions

For a polynomial with nonzero discriminant, the primitive part of every
restriction modulo `degree! * |discriminant|` has no fixed prime divisor.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial

theorem affineRestriction_natDegree_le (Q : ℤ[X]) (M a : ℤ) :
    (affineRestriction Q M a).natDegree ≤ Q.natDegree := by
  exact natDegree_comp_le.trans ((Nat.mul_le_mul_left _ natDegree_linear_le).trans_eq (Nat.mul_one
      _))

theorem affineRestriction_primPart_reduction_degree_le_one {Q : ℤ[X]}
    (hdeg : 2 ≤ Q.natDegree) {p : ℕ} (hp : p.Prime) {M a : ℤ} {m : ℕ}
    (hMp : (p : ℤ) ^ m ∣ M) (hM : ¬ (p : ℤ) ^ (m + 1) ∣ M)
    (hD : ¬ (p : ℤ) ^ m ∣ Q.discr) :
    ((affineRestriction Q M a).primPart.map (Int.castRingHom (ZMod p))).natDegree ≤ 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [coeff_map]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    (affineRestriction_primPart_high_coeff_dvd hdeg hp hMp hM hD (by omega))

/-- The progression modulus used to remove fixed prime divisors. -/
noncomputable def fixedPrimeRemovalModulus (Q : ℤ[X]) : ℕ :=
  Q.natDegree.factorial * Q.discr.natAbs

theorem fixedPrimeRemovalModulus_pos {Q : ℤ[X]} (hD : Q.discr ≠ 0) :
    0 < fixedPrimeRemovalModulus Q :=
  Nat.mul_pos (Nat.factorial_pos _) (Int.natAbs_pos.mpr hD)

theorem affine_primPart_noFixedPrimeDivisor {Q : ℤ[X]} (hD : Q.discr ≠ 0) (a : ℤ) :
    NoFixedPrimeDivisor (affineRestriction Q (fixedPrimeRemovalModulus Q) a).primPart := by
  let M := fixedPrimeRemovalModulus Q
  let R := affineRestriction Q (M : ℤ) a
  have hR : R.primPart.IsPrimitive := R.isPrimitive_primPart
  have hRdeg : R.primPart.natDegree ≤ Q.natDegree :=
    (natDegree_primPart R).trans_le (affineRestriction_natDegree_le Q M a)
  by_cases hdeg : 2 ≤ Q.natDegree
  · intro p hp
    by_cases hsmall : p ≤ Q.natDegree
    · have hM₀ : M ≠ 0 := (fixedPrimeRemovalModulus_pos hD).ne'
      have hD₀ : Q.discr.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD
      let m := M.factorization p
      have hm : Q.discr.natAbs.factorization p < m := by
        have H := hp.factorization_pos_of_dvd (Nat.factorial_ne_zero Q.natDegree)
          (Nat.dvd_factorial hp.pos hsmall)
        dsimp [m, M, fixedPrimeRemovalModulus]
        rw [Nat.factorization_mul (Nat.factorial_ne_zero _) hD₀, Finsupp.add_apply]
        omega
      have hMp : (p : ℤ) ^ m ∣ (M : ℤ) := by
        simpa only [← Nat.cast_pow, Int.natCast_dvd, Int.natAbs_natCast] using Nat.ordProj_dvd M p
      have hM : ¬ (p : ℤ) ^ (m + 1) ∣ (M : ℤ) := by
        simpa only [← Nat.cast_pow, Int.natCast_dvd, Int.natAbs_natCast] using
            Nat.pow_succ_factorization_not_dvd hM₀ hp
      have hDp : ¬ (p : ℤ) ^ m ∣ Q.discr := by
        rw [← Nat.cast_pow, Int.natCast_dvd, hp.pow_dvd_iff_le_factorization hD₀]
        omega
      exact (rootCount_le_reduction_degree hp (primitive_map_zmod_ne_zero hR hp)).trans_lt
        ((affineRestriction_primPart_reduction_degree_le_one hdeg hp hMp hM hDp).trans_lt hp.one_lt)
    · exact primitive_rootCount_lt_of_degree_lt hR hp (hRdeg.trans_lt (by omega))
  · exact primitive_noFixedPrimeDivisor_of_degree_le_one hR (hRdeg.trans (by omega))

end NairTenenbaum
