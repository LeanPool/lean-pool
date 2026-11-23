/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.FamilyRotations

/-!
# Fermat-type curves

The polynomials `X^d + Y^d - 2`: irreducibility, degree and infinite real locus.
-/

@[expose] public section

namespace CurveSymmetry

open Polynomial

/-- The Fermat-type polynomial `X^d + Y^d - 2` in nested form. -/
noncomputable def fermatNested (d : ℕ) : NPoly := X ^ d + C (X ^ d - C 2)

theorem fermatNested_irreducible {d : ℕ} (hd : 0 < d) : Irreducible (fermatNested d) := by
  obtain ⟨η, hη⟩ := IsAlgClosed.exists_pow_nat_eq (2 : ℂ) hd
  have hn : η ≠ 0 := by intro h; simp [h, hd.ne'] at hη
  have hmonic : (fermatNested d).Monic := monic_X_pow_add_C _ hd.ne'
  have hdeg : (fermatNested d).natDegree = d := by
    simp only [fermatNested, natDegree_add_C, natDegree_X_pow]
  have hprime : (Ideal.span ({X - C η} : Set UPoly)).IsPrime :=
    (Ideal.span_singleton_prime (X_sub_C_ne_zero η)).mpr (prime_X_sub_C η)
  apply irreducible_of_eisenstein_criterion hprime
  · rw [hmonic.leadingCoeff]
    exact fun h => hprime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  · intro n hnd
    have hnd' : n < d := by simpa [hdeg] using coe_lt_degree.mp hnd
    rw [Ideal.mem_span_singleton]
    by_cases h0 : n = 0
    · subst n
      simp only [fermatNested, coeff_add, coeff_X_pow, hd.ne, ite_false, coeff_C_zero, zero_add]
      apply dvd_iff_isRoot.mpr
      simp [IsRoot, hη]
    · simp only [fermatNested, coeff_add, coeff_X_pow, ite_eq_right (Nat.ne_of_lt hnd'),
        coeff_C, ite_eq_right h0, add_zero, dvd_zero]
  · exact natDegree_pos_iff_degree_pos.mp (by omega)
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hs
    have hc : (fermatNested d).coeff 0 = X ^ d - C 2 := by
      simp only [fermatNested, coeff_add, coeff_X_pow, ite_eq_right hd.ne, coeff_C_zero, zero_add]
    rw [hc] at hs
    have ht := pow_sub_one_dvd_derivative_of_pow_dvd hs
    simp only [show 2 - 1 = 1 by decide, pow_one] at ht
    have he := dvd_iff_isRoot.mp ht
    have hdn : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    simp [IsRoot, derivative_X_pow, hdn, hn] at he
  · exact hmonic.isPrimitive

/-- The Fermat-type polynomial `X^d + Y^d - 2`, whose real locus is `Re(z^d) = 1`. -/
noncomputable def fermatPolynomial (d : ℕ) : BPoly :=
  MvPolynomial.X 0 ^ d + MvPolynomial.X 1 ^ d - MvPolynomial.C 2

lemma fermat_toNested (d : ℕ) : toNested (fermatPolynomial d) = fermatNested d := by
  simp [fermatPolynomial, fermatNested, toNested_X_zero, toNested_X_one, toNested_C]
  ring

theorem fermat_irreducible {d : ℕ} (hd : 0 < d) : Irreducible (fermatPolynomial d) := by
  have h := (fermatNested_irreducible hd).map toNested.symm.toMulEquiv
  change Irreducible (toNested.symm (fermatNested d)) at h
  rwa [← fermat_toNested, toNested.symm_apply_apply] at h

lemma eval_fermat (d : ℕ) (z : ℂ) :
    MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z else star z) (fermatPolynomial d) =
      z ^ d + star (z ^ d) - 2 := by
  simp [fermatPolynomial, star_pow]

theorem fermat_realLocus_infinite {d : ℕ} (hd : 0 < d) :
    (realLocus (fermatPolynomial d)).Infinite := by
  have hex : ∀ n : ℕ, ∃ z : ℂ, z ^ d = 1 + (n : ℂ) * Complex.I :=
    fun n => IsAlgClosed.exists_pow_nat_eq _ hd
  choose f hf using hex
  have hi : Function.Injective f := by
    intro n k h
    have he := congrArg (fun z : ℂ => z ^ d) h
    rw [hf, hf] at he
    have he' := congrArg Complex.im he
    simpa using he'
  apply (Set.infinite_range_of_injective hi).mono
  rintro _ ⟨n, rfl⟩
  change MvPolynomial.eval _ (fermatPolynomial d) = 0
  rw [eval_fermat, hf]
  simp [star_add, star_mul]
  ring

theorem fermat_degree {d : ℕ} (hd : 0 < d) : (fermatPolynomial d).totalDegree = d := by
  open MvPolynomial in
  have h0 : (fermatPolynomial d).coeff (exponent d 0) = 1 := by
    have h10 : (Finsupp.single (1 : Fin 2) d : Exponent) ≠ Finsupp.single 0 d := by
      intro h
      have he := congrArg (fun s : Exponent => s 0) h
      simp [hd.ne] at he
    have hzero : (0 : Exponent) ≠ Finsupp.single 0 d := by
      intro h
      have he := congrArg (fun s : Exponent => s 0) h
      simp [hd.ne] at he
    simp [fermatPolynomial, exponent, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.coeff_monomial, h10, hzero]
  have hlo := support_degree (MvPolynomial.mem_support_iff.mpr (by rw [h0]; exact one_ne_zero))
  simp only [exponent_zero, exponent_one, Nat.add_zero] at hlo
  have hsum := MvPolynomial.totalDegree_add (MvPolynomial.X 0 ^ d : BPoly) (MvPolynomial.X 1 ^ d)
  have hsub := MvPolynomial.totalDegree_sub_C_le
    (MvPolynomial.X 0 ^ d + MvPolynomial.X 1 ^ d : BPoly) 2
  simp only [MvPolynomial.totalDegree_X_pow, max_self] at hsum
  change (MvPolynomial.X 0 ^ d + MvPolynomial.X 1 ^ d - MvPolynomial.C 2 : BPoly).totalDegree = d
  change d ≤ (MvPolynomial.X 0 ^ d + MvPolynomial.X 1 ^ d - MvPolynomial.C 2 : BPoly).totalDegree
    at hlo
  omega

end CurveSymmetry
