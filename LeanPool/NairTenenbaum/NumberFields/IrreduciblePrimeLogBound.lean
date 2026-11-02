/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.NumberFields.IntegralRootNormalization
public import LeanPool.NairTenenbaum.NumberFields.MinpolyPrimeLogBound

/-! # The sharp prime-root logarithmic bound for irreducible polynomials

For every integer polynomial irreducible over the rationals,
`Σ_p ρ_Q(p)/p^σ ≤ −log(σ−1)+O_Q(1)` near `σ=1`.
Both convergence and the bound are proved from the Dedekind zeta residue.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Real Polynomial NumberField

theorem primeRootPowerWeight_le_one (Q : ℤ[X]) {p : ℕ} (hp : p.Prime)
    {σ : ℝ} (hσ : 1 ≤ σ) :
    (rootCount Q p : ℝ) * (p : ℝ) ^ (-σ) ≤ 1 := by
  calc
    _ ≤ (p : ℝ) * (p : ℝ) ^ (-σ) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast rootCount_le Q hp.ne_zero) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ (p : ℝ) * (p : ℝ) ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by
        exact_mod_cast hp.one_le) (by linarith)) (Nat.cast_nonneg _)
    _ = 1 := by rw [Real.rpow_neg_one, mul_inv_cancel₀ (by exact_mod_cast hp.ne_zero)]

theorem primeRootSum_le_integralNormalization_add {Q : ℤ[X]} (hdeg : 1 ≤ Q.natDegree)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {σ : ℝ} (hσ : 1 ≤ σ) :
    (∑ p ∈ S, (rootCount Q p : ℝ) * (p : ℝ) ^ (-σ)) ≤
      (∑ p ∈ S, (rootCount Q.integralNormalization p : ℝ) * (p : ℝ) ^ (-σ)) +
        Q.leadingCoeff.natAbs.primeFactors.card := by
  classical
  have hQ : Q ≠ 0 := by intro h; simp [h] at hdeg
  have hc : Q.leadingCoeff.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (leadingCoeff_ne_zero.mpr hQ)
  have hbad : S.filter (fun p => p ∣ Q.leadingCoeff.natAbs) ⊆ Q.leadingCoeff.natAbs.primeFactors
      := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨hS p (mem_filter.mp hp).1, (mem_filter.mp hp).2, hc⟩
  have Hbad : (∑ p ∈ S.filter (fun p => p ∣ Q.leadingCoeff.natAbs),
      (rootCount Q p : ℝ) * (p : ℝ) ^ (-σ)) ≤ Q.leadingCoeff.natAbs.primeFactors.card := by
    calc
      _ ≤ ∑ _p ∈ S.filter (fun p => p ∣ Q.leadingCoeff.natAbs), (1 : ℝ) :=
        sum_le_sum (fun p hp => primeRootPowerWeight_le_one Q (hS p (mem_filter.mp hp).1) hσ)
      _ = ((S.filter (fun p => p ∣ Q.leadingCoeff.natAbs)).card : ℝ) := by simp
      _ ≤ _ := by exact_mod_cast card_le_card hbad
  have Hgood : (∑ p ∈ S.filter (fun p => ¬p ∣ Q.leadingCoeff.natAbs),
      (rootCount Q p : ℝ) * (p : ℝ) ^ (-σ)) ≤
      ∑ p ∈ S, (rootCount Q.integralNormalization p : ℝ) * (p : ℝ) ^ (-σ) := by
    calc
      _ ≤ ∑ p ∈ S.filter (fun p => ¬p ∣ Q.leadingCoeff.natAbs),
          (rootCount Q.integralNormalization p : ℝ) * (p : ℝ) ^ (-σ) := by
        apply sum_le_sum
        intro p hp
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        exact_mod_cast rootCount_le_integralNormalization hdeg (hS p (mem_filter.mp hp).1)
          (mem_filter.mp hp).2
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun p _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have Hsplit := sum_filter_add_sum_filter_not S (fun p => p ∣ Q.leadingCoeff.natAbs)
    (fun p => (rootCount Q p : ℝ) * (p : ℝ) ^ (-σ))
  linarith

theorem exists_irreducible_primeSum_log_bound {Q : ℤ[X]}
    (hQ : Irreducible (Q.map (Int.castRingHom ℚ))) :
    ∃ C b : ℝ, 0 ≤ C ∧ 1 < b ∧ ∀ σ : ℝ, 1 < σ → σ < b →
      ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
        (∑ p ∈ S, (rootCount Q p : ℝ) * (p : ℝ) ^ (-σ)) ≤ C - Real.log (σ - 1) := by
  let : Fact (Irreducible (Q.map (Int.castRingHom ℚ))) := ⟨hQ⟩
  have hQ0 : Q ≠ 0 := by intro h; simp [h] at hQ
  let B : PowerBasis ℚ (AdjoinRoot (Q.map (Int.castRingHom ℚ))) := AdjoinRoot.powerBasis hQ.ne_zero
  have hroot : aeval B.gen Q = 0 := by
    rw [← aeval_map_algebraMap ℚ]
    change aeval (AdjoinRoot.root (Q.map (Int.castRingHom ℚ)))
      (Q.map (Int.castRingHom ℚ)) = 0
    exact (AdjoinRoot.aeval_eq (f := Q.map (Int.castRingHom ℚ)) _).trans AdjoinRoot.mk_self
  have hdeg : Q.natDegree = B.dim := by
    exact (natDegree_map_eq_of_injective (f := Int.castRingHom ℚ) Int.cast_injective Q).symm
  obtain ⟨θ, B', hB', hmin⟩ := exists_integralGenerator_of_polynomial hQ0 B hroot hdeg
  obtain ⟨C, b, hC, hb, hbound⟩ := exists_minpoly_primeSum_log_bound θ B' hB'
  rw [hmin] at hbound
  refine ⟨C + Q.leadingCoeff.natAbs.primeFactors.card, b,
    add_nonneg hC (Nat.cast_nonneg _), hb, fun σ hσ hσb S hS => ?_⟩
  have hdegpos : 1 ≤ Q.natDegree := by
    rw [← natDegree_map_eq_of_injective (f := Int.castRingHom ℚ) Int.cast_injective Q]
    exact hQ.natDegree_pos
  have H := primeRootSum_le_integralNormalization_add hdegpos S hS hσ.le
  have H' := hbound σ hσ hσb S hS
  linarith

theorem exists_irreducible_rootPrimePowerSum_log_bound {Q : ℤ[X]}
    (hQ : Irreducible (Q.map (Int.castRingHom ℚ))) :
    ∃ C b : ℝ, 0 ≤ C ∧ 1 < b ∧ ∀ σ : ℝ, 1 < σ → σ < b →
      Summable (fun p : Nat.Primes => (rootCount Q p.1 : ℝ) * (p.1 : ℝ) ^ (-σ)) ∧
      rootPrimePowerSum Q σ ≤ C - Real.log (σ - 1) := by
  classical
  obtain ⟨C, b, hC, hb, hbound⟩ := exists_irreducible_primeSum_log_bound hQ
  refine ⟨C, b, hC, hb, fun σ hσ hσb => ?_⟩
  have H (S : Finset Nat.Primes) :
      (∑ p ∈ S, (rootCount Q p.1 : ℝ) * (p.1 : ℝ) ^ (-σ)) ≤ C - Real.log (σ - 1) := by
    have H := hbound σ hσ hσb (S.image Subtype.val) (by
      intro p hp
      obtain ⟨r, _, rfl⟩ := mem_image.mp hp
      exact r.2)
    apply le_trans _ H
    exact le_of_eq (sum_image (s := S)
      (f := fun p : ℕ => (rootCount Q p : ℝ) * (p : ℝ) ^ (-σ))
      (fun _ _ _ _ h => Subtype.val_injective h)).symm
  have hn (p : Nat.Primes) : 0 ≤ (rootCount Q p.1 : ℝ) * (p.1 : ℝ) ^ (-σ) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  exact ⟨summable_of_sum_le hn H, Real.tsum_le_of_sum_le hn H⟩

end NairTenenbaum
