/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.PrimeDirichletPoleBound
public import LeanPool.NairTenenbaum.NumberFields.IrreduciblePrimeLowerBound

/-! # A lower bound for the truncated prime-root reciprocal sum -/

@[expose] public section

namespace NairTenenbaum

open Finset Real Polynomial

/-- The reciprocal-prime sum weighted by polynomial root counts. -/
noncomputable def primeRootReciprocalSum (Q : ℤ[X]) (x : ℝ) : ℝ :=
  ∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, (rootCount Q p : ℝ) / p

theorem primeRootPowerWeight_le_logWeight_div {Q : ℤ[X]} {p : ℕ} (_hp : p.Prime)
    {x σ : ℝ} (hx : 1 < x) (hpx : x ≤ p) :
    (rootCount Q p : ℝ) * (p : ℝ) ^ (-σ) ≤ rootPrimeLogWeight Q σ p / Real.log x := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have hlog : Real.log x ≤ Real.log p := Real.log_le_log (by linarith) hpx
  have HE : rootPrimeLogWeight Q σ p = ((rootCount Q p : ℝ) * (p : ℝ) ^ (-σ)) * Real.log p := by
    simp only [rootPrimeLogWeight, Real.rpow_neg (Nat.cast_nonneg p), div_eq_mul_inv]
    ring
  rw [HE]
  exact (le_div_iff₀ hl).mpr (mul_le_mul_of_nonneg_left hlog
    (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)))

theorem finite_primeRootPowerSum_le_reciprocal_add_tail {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {x σ : ℝ} (hx : 1 < x) (hσ : 1 < σ) :
    (∑ p ∈ S, (rootCount Q p : ℝ) * (p : ℝ) ^ (-σ)) ≤
      primeRootReciprocalSum Q x + rootPrimeDirichletSum Q σ / Real.log x := by
  classical
  have hl : 0 < Real.log x := Real.log_pos hx
  have Hsmall : (∑ p ∈ S.filter (fun p : ℕ => (p : ℝ) ≤ x),
      (rootCount Q p : ℝ) * (p : ℝ) ^ (-σ)) ≤ primeRootReciprocalSum Q x := by
    calc
      _ ≤ ∑ p ∈ S.filter (fun p : ℕ => (p : ℝ) ≤ x), (rootCount Q p : ℝ) / p := by
        apply sum_le_sum
        intro p hp
        have hp' := hS p (mem_filter.mp hp).1
        have H := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ (p : ℝ) by
            exact_mod_cast hp'.one_le) (show -σ ≤ (-1 : ℝ) by linarith))
          (Nat.cast_nonneg (rootCount Q p))
        simpa only [Real.rpow_neg_one, div_eq_mul_inv] using H
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (by
        intro p hp
        exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_floor_iff (by
          linarith : 0 ≤ x)).mpr (mem_filter.mp hp).2)),
          hS p (mem_filter.mp hp).1⟩) (fun p _ _ => by positivity)
  have Hlarge : (∑ p ∈ S.filter (fun p : ℕ => ¬(p : ℝ) ≤ x),
      (rootCount Q p : ℝ) * (p : ℝ) ^ (-σ)) ≤ rootPrimeDirichletSum Q σ / Real.log x := by
    calc
      _ ≤ ∑ p ∈ S.filter (fun p : ℕ => ¬(p : ℝ) ≤ x), rootPrimeLogWeight Q σ p / Real.log x :=
        sum_le_sum (fun p hp => primeRootPowerWeight_le_logWeight_div (hS p (mem_filter.mp hp).1) hx
          (le_of_lt (not_le.mp (mem_filter.mp hp).2)))
      _ ≤ ∑ p ∈ S, rootPrimeLogWeight Q σ p / Real.log x :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p hp _ =>
          div_nonneg (rootPrimeLogWeight_nonneg Q σ (hS p hp)) hl.le)
      _ = (∑ p ∈ S, rootPrimeLogWeight Q σ p) / Real.log x := (sum_div _ _ _).symm
      _ ≤ _ := div_le_div_of_nonneg_right
        (prime_finset_sum_le_tsum (rootPrimeLogWeight Q σ) (fun p hp => rootPrimeLogWeight_nonneg
            Q σ hp)
          (summable_rootPrimeLogWeight hQ hσ) S hS) hl.le
  have HE := sum_filter_add_sum_filter_not S (fun p : ℕ => (p : ℝ) ≤ x)
    (fun p => (rootCount Q p : ℝ) * (p : ℝ) ^ (-σ))
  linarith

theorem rootPrimePowerSum_le_reciprocal_add_tail {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {x σ : ℝ} (hx : 1 < x) (hσ : 1 < σ) :
    rootPrimePowerSum Q σ ≤ primeRootReciprocalSum Q x + rootPrimeDirichletSum Q σ / Real.log x :=
        by
  classical
  apply Real.tsum_le_of_sum_le (fun p => mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg
      (Nat.cast_nonneg _) _))
  intro S
  have H := finite_primeRootPowerSum_le_reciprocal_add_tail hQ (S.image Subtype.val)
    (by intro p hp; obtain ⟨r, _, rfl⟩ := mem_image.mp hp; exact r.2) hx hσ
  apply le_trans _ H
  exact le_of_eq (sum_image (s := S)
    (f := fun p : ℕ => (rootCount Q p : ℝ) * (p : ℝ) ^ (-σ))
    (fun _ _ _ _ h => Subtype.val_injective h)).symm

theorem exists_primeRootReciprocalSum_lower_bound {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (hirr : Irreducible (Q.map (Int.castRingHom ℚ))) :
    ∃ C x₀ : ℝ, 1 < x₀ ∧ ∀ x : ℝ, x₀ < x →
      Real.log (Real.log x) - C ≤ primeRootReciprocalSum Q x := by
  obtain ⟨C, b, hb, H⟩ := exists_irreducible_rootPrimePowerSum_lower_bound hQ hirr
  let G := 2 * (Q.natDegree : ℝ) * (Real.log 4 * Real.exp 2)
  let x₀ := Real.exp (1 / (b - 1) + 2)
  have hd : 0 < b - 1 := by linarith
  have hx₀ : 1 < x₀ := Real.one_lt_exp_iff.mpr (by positivity)
  refine ⟨C + G, x₀, hx₀, fun x hx => ?_⟩
  have hx₁ : 1 < x := hx₀.trans hx
  have hl : 0 < Real.log x := Real.log_pos hx₁
  have hlbig : 1 / (b - 1) + 2 < Real.log x := by
    have HH := Real.log_lt_log (Real.exp_pos (1 / (b - 1) + 2)) hx
    rwa [Real.log_exp] at HH
  have hl₁ : 1 < Real.log x := by linarith [one_div_pos.mpr hd]
  have hσ : 1 < 1 + 1 / Real.log x := by linarith [one_div_pos.mpr hl]
  have hσ₂ : 1 + 1 / Real.log x ≤ 2 := by
    have HH := (div_le_one hl).mpr hl₁.le
    linarith
  have hσb : 1 + 1 / Real.log x < b := by
    have H₁ : 1 / (b - 1) < Real.log x := by linarith
    have H₂ := (div_lt_iff₀ hd).mp H₁
    have H₃ := (div_lt_iff₀ hl).mpr (show 1 < (b - 1) * Real.log x by nlinarith)
    linarith
  have HL := H (1 + 1 / Real.log x) hσ hσb
  simp only [add_sub_cancel_left, one_div, Real.log_inv, neg_neg] at HL
  have HU := rootPrimePowerSum_le_reciprocal_add_tail hQ hx₁ hσ
  have HP := div_le_div_of_nonneg_right (rootPrimeDirichletSum_le_pole hQ hσ hσ₂) hl.le
  have HE : (G / ((1 + 1 / Real.log x) - 1)) / Real.log x = G := by field_simp; ring
  change rootPrimeDirichletSum Q (1 + 1 / Real.log x) / Real.log x ≤
    (G / ((1 + 1 / Real.log x) - 1)) / Real.log x at HP
  rw [HE] at HP
  simp only [one_div] at HU HP
  linarith

end NairTenenbaum
