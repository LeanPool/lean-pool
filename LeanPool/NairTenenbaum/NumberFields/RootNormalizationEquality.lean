/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.NumberFields.IrreduciblePrimeLogBound

/-! # Equality of residue-root counts under integral normalization -/

@[expose] public section

namespace NairTenenbaum

open Finset Real Polynomial

theorem rootCount_integralNormalization_le {Q : ℤ[X]} (hdeg : 1 ≤ Q.natDegree)
    {p : ℕ} (hp : p.Prime) (hgood : ¬p ∣ Q.leadingCoeff.natAbs) :
    rootCount Q.integralNormalization p ≤ rootCount Q p := by
  let : Fact p.Prime := ⟨hp⟩
  have hc : (Q.leadingCoeff : ZMod p) ≠ 0 := by
    simpa only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd] using hgood
  let f : ResidueRoots Q.integralNormalization p → ResidueRoots Q p := fun a =>
    ⟨(Q.leadingCoeff : ZMod p)⁻¹ * a.1, by
      have H := integralNormalization_eval₂_leadingCoeff_mul hdeg (Int.castRingHom (ZMod p))
        ((Q.leadingCoeff : ZMod p)⁻¹ * a.1)
      change Polynomial.eval₂ (Int.castRingHom (ZMod p))
        ((Q.leadingCoeff : ZMod p) * ((Q.leadingCoeff : ZMod p)⁻¹ * a.1)) Q.integralNormalization =
        (Q.leadingCoeff : ZMod p) ^ (Q.natDegree - 1) *
          Polynomial.eval₂ (Int.castRingHom (ZMod p)) ((Q.leadingCoeff : ZMod p)⁻¹ * a.1) Q at H
      rw [mul_inv_cancel_left₀ hc] at H
      have HH := H.symm.trans a.2
      exact (mul_eq_zero.mp HH).resolve_left (pow_ne_zero _ hc)⟩
  apply Nat.card_le_card_of_injective f
  intro a b h
  apply Subtype.ext
  exact mul_left_cancel₀ (inv_ne_zero hc) (congrArg Subtype.val h)

theorem rootCount_integralNormalization_eq {Q : ℤ[X]} (hdeg : 1 ≤ Q.natDegree)
    {p : ℕ} (hp : p.Prime) (hgood : ¬p ∣ Q.leadingCoeff.natAbs) :
    rootCount Q.integralNormalization p = rootCount Q p :=
  Nat.le_antisymm (rootCount_integralNormalization_le hdeg hp hgood)
    (rootCount_le_integralNormalization hdeg hp hgood)

theorem primeRootSum_integralNormalization_le_add {Q : ℤ[X]} (hdeg : 1 ≤ Q.natDegree)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {σ : ℝ} (hσ : 1 ≤ σ) :
    (∑ p ∈ S, (rootCount Q.integralNormalization p : ℝ) * (p : ℝ) ^ (-σ)) ≤
      (∑ p ∈ S, (rootCount Q p : ℝ) * (p : ℝ) ^ (-σ)) +
        Q.leadingCoeff.natAbs.primeFactors.card := by
  classical
  have hQ : Q ≠ 0 := by intro h; simp [h] at hdeg
  have hc : Q.leadingCoeff.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (leadingCoeff_ne_zero.mpr hQ)
  have hbad : S.filter (fun p => p ∣ Q.leadingCoeff.natAbs) ⊆ Q.leadingCoeff.natAbs.primeFactors
      := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨hS p (mem_filter.mp hp).1, (mem_filter.mp hp).2, hc⟩
  have Hbad : (∑ p ∈ S.filter (fun p => p ∣ Q.leadingCoeff.natAbs),
      (rootCount Q.integralNormalization p : ℝ) * (p : ℝ) ^ (-σ)) ≤
          Q.leadingCoeff.natAbs.primeFactors.card := by
    calc
      _ ≤ ∑ _p ∈ S.filter (fun p => p ∣ Q.leadingCoeff.natAbs), (1 : ℝ) :=
        sum_le_sum (fun p hp => primeRootPowerWeight_le_one Q.integralNormalization (hS p
            (mem_filter.mp hp).1) hσ)
      _ = ((S.filter (fun p => p ∣ Q.leadingCoeff.natAbs)).card : ℝ) := by simp
      _ ≤ _ := by exact_mod_cast card_le_card hbad
  have Hgood : (∑ p ∈ S.filter (fun p => ¬p ∣ Q.leadingCoeff.natAbs),
      (rootCount Q.integralNormalization p : ℝ) * (p : ℝ) ^ (-σ)) ≤
      ∑ p ∈ S, (rootCount Q p : ℝ) * (p : ℝ) ^ (-σ) := by
    calc
      _ = ∑ p ∈ S.filter (fun p => ¬p ∣ Q.leadingCoeff.natAbs),
          (rootCount Q p : ℝ) * (p : ℝ) ^ (-σ) := by
        apply sum_congr rfl
        intro p hp
        rw [rootCount_integralNormalization_eq hdeg (hS p (mem_filter.mp hp).1) (mem_filter.mp
            hp).2]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun p _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have Hsplit := sum_filter_add_sum_filter_not S (fun p => p ∣ Q.leadingCoeff.natAbs)
    (fun p => (rootCount Q.integralNormalization p : ℝ) * (p : ℝ) ^ (-σ))
  linarith

theorem rootPrimePowerSum_integralNormalization_le {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (hdeg : 1 ≤ Q.natDegree) {σ : ℝ} (hσ : 1 < σ) :
    rootPrimePowerSum Q.integralNormalization σ ≤
      rootPrimePowerSum Q σ + Q.leadingCoeff.natAbs.primeFactors.card := by
  classical
  apply Real.tsum_le_of_sum_le (fun p => mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg
      (Nat.cast_nonneg _) _))
  intro S
  have HS : ∀ p ∈ S.image Subtype.val, p.Prime := by
    intro p hp
    obtain ⟨r, _, rfl⟩ := mem_image.mp hp
    exact r.2
  have H := primeRootSum_integralNormalization_le_add hdeg (S.image Subtype.val) HS hσ.le
  have HR := prime_finset_sum_le_tsum (fun p : ℕ => (rootCount Q p : ℝ) * (p : ℝ) ^ (-σ))
    (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (summable_rootPrimePowerWeight hQ hσ) (S.image Subtype.val) HS
  apply le_trans _ (H.trans (add_le_add HR le_rfl))
  exact le_of_eq (sum_image (s := S)
    (f := fun p : ℕ => (rootCount Q.integralNormalization p : ℝ) * (p : ℝ) ^ (-σ))
    (fun _ _ _ _ h => Subtype.val_injective h)).symm

end NairTenenbaum
