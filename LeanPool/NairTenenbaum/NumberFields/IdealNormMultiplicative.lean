/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.NumberFields.PrimeIdealNormBounds

/-! # Coprime multiplicativity of the ideal norm counting function

A nonzero ideal whose norm is `m * n`, with `m` and `n` coprime, has a
unique factorization into ideals of norms `m` and `n`.
-/

@[expose] public section

namespace NairTenenbaum

open Finset NumberField Ideal UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K]

theorem ideals_isRelPrime_of_coprime_norm {I J : Ideal (𝓞 K)}
    (h : (absNorm I).Coprime (absNorm J)) : IsRelPrime I J := by
  intro D hDI hDJ
  apply Ideal.isUnit_iff.mpr
  apply Ideal.absNorm_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes h (map_dvd absNorm hDI) (map_dvd absNorm hDJ)

theorem ideal_factorization_unique_of_coprime_norm
    {I J I' J' : Ideal (𝓞 K)}
    (hI : absNorm I = absNorm I') (hJ : absNorm J = absNorm J')
    (hcop : (absNorm I).Coprime (absNorm J)) (h : I * J = I' * J') :
    I = I' ∧ J = J' := by
  have hIJ' : IsRelPrime I J' := ideals_isRelPrime_of_coprime_norm (hJ ▸ hcop)
  have hI'J : IsRelPrime I' J := ideals_isRelPrime_of_coprime_norm (hI ▸ hcop)
  have hII' : I = I' := le_antisymm
    (Ideal.dvd_iff_le.mp (hI'J.dvd_of_dvd_mul_right (h ▸ dvd_mul_right I' J')))
    (Ideal.dvd_iff_le.mp (hIJ'.dvd_of_dvd_mul_right (h.symm ▸ dvd_mul_right I J)))
  have hJJ' : J = J' := le_antisymm
    (Ideal.dvd_iff_le.mp (hIJ'.symm.dvd_of_dvd_mul_left (h ▸ dvd_mul_left J' I')))
    (Ideal.dvd_iff_le.mp (hI'J.symm.dvd_of_dvd_mul_left (h.symm ▸ dvd_mul_left J I)))
  exact ⟨hII', hJJ'⟩

theorem exists_ideal_factors_of_coprime_norm {I : Ideal (𝓞 K)} {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hcop : m.Coprime n) (hI : absNorm I = m * n) :
    ∃ A B : Ideal (𝓞 K), A * B = I ∧ absNorm A = m ∧ absNorm B = n := by
  classical
  have hI0 : I ≠ ⊥ := by
    intro h
    have := hI
    rw [h, absNorm_bot] at this
    exact (Nat.mul_pos hm hn).ne' this.symm
  let S := (normalizedFactors I).toFinset
  let A : Ideal (𝓞 K) := ∏ P ∈ S.filter (fun P => rationalPrimeBelow P ∣ m),
    P ^ (normalizedFactors I).count P
  let B : Ideal (𝓞 K) := ∏ P ∈ S.filter (fun P => ¬ rationalPrimeBelow P ∣ m),
    P ^ (normalizedFactors I).count P
  have hAB : A * B = I := by
    dsimp [A, B]
    rw [prod_filter_mul_prod_filter_not]
    exact (ideal_eq_prod_factor_counts hI0 S (Subset.refl _)).symm
  have hnorm : absNorm A * absNorm B = m * n := by
    rw [← map_mul, hAB, hI]
  have hAn : (absNorm A).Coprime n := by
    dsimp [A]
    rw [map_prod]
    apply Nat.coprime_prod_left_iff.mpr
    intro P hP
    obtain ⟨hPS, hPm⟩ := mem_filter.mp hP
    have hprime := prime_of_normalized_factor P (Multiset.mem_toFinset.mp hPS)
    rw [map_pow, idealNorm_eq_primeBelow_pow hprime]
    exact ((hcop.of_dvd_left hPm).pow_left _).pow_left _
  have hBm : (absNorm B).Coprime m := by
    dsimp [B]
    rw [map_prod]
    apply Nat.coprime_prod_left_iff.mpr
    intro P hP
    obtain ⟨hPS, hPm⟩ := mem_filter.mp hP
    have hprime := prime_of_normalized_factor P (Multiset.mem_toFinset.mp hPS)
    rw [map_pow, idealNorm_eq_primeBelow_pow hprime]
    exact (((rationalPrimeBelow_prime hprime).coprime_iff_not_dvd.mpr hPm).pow_left _).pow_left _
  have hAm : absNorm A = m := Nat.dvd_antisymm
    (hAn.dvd_of_dvd_mul_right (hnorm ▸ dvd_mul_right (absNorm A) (absNorm B)))
    (hBm.symm.dvd_of_dvd_mul_right (hnorm.symm ▸ dvd_mul_right m n))
  have hBn : absNorm B = n := by
    rw [hAm] at hnorm
    exact Nat.eq_of_mul_eq_mul_left hm hnorm
  exact ⟨A, B, hAB, hAm, hBn⟩

/-- Multiplication identifies ideals of coprime product norm with pairs of ideals. -/
noncomputable def idealNormMulEquiv {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hcop : m.Coprime n) :
    ({I : Ideal (𝓞 K) // absNorm I = m} × {J : Ideal (𝓞 K) // absNorm J = n}) ≃
      {L : Ideal (𝓞 K) // absNorm L = m * n} := by
  let f : ({I : Ideal (𝓞 K) // absNorm I = m} ×
      {J : Ideal (𝓞 K) // absNorm J = n}) →
      {L : Ideal (𝓞 K) // absNorm L = m * n} :=
    fun IJ => ⟨IJ.1.1 * IJ.2.1, by rw [map_mul, IJ.1.2, IJ.2.2]⟩
  apply Equiv.ofBijective f
  constructor
  · intro IJ I'J' h
    have H := ideal_factorization_unique_of_coprime_norm
      (IJ.1.2.trans I'J'.1.2.symm) (IJ.2.2.trans I'J'.2.2.symm)
      (by simpa only [IJ.1.2, IJ.2.2] using hcop)
      (show IJ.1.1 * IJ.2.1 = I'J'.1.1 * I'J'.2.1 from congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext H.1) (Subtype.ext H.2)
  · intro L
    obtain ⟨A, B, hAB, hA, hB⟩ := exists_ideal_factors_of_coprime_norm hm hn hcop L.2
    exact ⟨(⟨A, hA⟩, ⟨B, hB⟩), Subtype.ext hAB⟩

@[simp] theorem idealNormCount_one : idealNormCount K 1 = 1 := by
  simp [idealNormCount, Ideal.absNorm_eq_one_iff]

theorem idealNormCount_mul_of_coprime {m n : ℕ} (hcop : m.Coprime n) :
    idealNormCount K (m * n) = idealNormCount K m * idealNormCount K n := by
  by_cases hm : m = 0
  · subst m
    have hn : n = 1 := by simpa using hcop
    simp [hn]
  by_cases hn : n = 0
  · subst n
    have hm : m = 1 := by simpa using hcop
    simp [hm]
  exact (Nat.card_congr (idealNormMulEquiv (K := K) (Nat.pos_of_ne_zero hm)
    (Nat.pos_of_ne_zero hn) hcop)).symm.trans (Nat.card_prod _ _)

end NairTenenbaum
