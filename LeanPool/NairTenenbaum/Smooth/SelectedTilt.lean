/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Smooth.SelectedMoment

/-! # Admissibility of the small-prime tilt used in Corollary 6 -/

@[expose] public section

namespace NairTenenbaum

open Finset

theorem selectedMoment_eq_prod (s : Finset ℕ) (β : ℝ) (n : ℕ) :
    selectedMoment s β n = ∏ p ∈ s, ((p : ℝ) ^ n.factorization p) ^ β := by
  classical
  unfold selectedMoment primePowerProduct
  rw [← Finset.prod_filter]
  apply Finset.prod_subset
  · exact fun p hp => (mem_filter.mp hp).2
  · intro p hp hnot
    have hp' : p ∉ n.primeFactors := fun h => hnot (mem_filter.mpr ⟨h, hp⟩)
    have hν : n.factorization p = 0 := by
      simpa only [← Nat.support_factorization, Finsupp.mem_support_iff, not_not] using hp'
    simp only [hν, pow_zero, Real.one_rpow]

/-- The selected moment is completely multiplicative on positive integers. -/
theorem selectedMoment_mul_of_ne_zero (s : Finset ℕ) (β : ℝ) {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) :
    selectedMoment s β (m * n) = selectedMoment s β m * selectedMoment s β n := by
  simp only [selectedMoment_eq_prod, Nat.factorization_mul hm hn, Finsupp.add_apply,
    pow_add, Real.mul_rpow (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (Nat.cast_nonneg _) _),
    Finset.prod_mul_distrib]

theorem selectedMoment_pow (s : Finset ℕ) (β : ℝ) (n e : ℕ) :
    selectedMoment s β (n ^ e) = selectedMoment s ((e : ℝ) * β) n := by
  simp only [selectedMoment_eq_prod, Nat.factorization_pow, Finsupp.smul_apply,
    smul_eq_mul]
  apply Finset.prod_congr rfl
  intro p hp
  rw [mul_comm e, pow_mul, ← Real.rpow_natCast_mul (by positivity)]

theorem selectedMoment_prod {ι : Type*} (s : Finset ℕ) (β : ℝ) (t : Finset ι)
    (f : ι → ℕ) (hf : ∀ i ∈ t, f i ≠ 0) :
    selectedMoment s β (∏ i ∈ t, f i) = ∏ i ∈ t, selectedMoment s β (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      selectedMoment_mul_of_ne_zero s β (hf i (mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hf j (mem_insert_of_mem hj))),
      ih (fun j hj => hf j (mem_insert_of_mem hj))]

theorem selectedMoment_mono_exponent (s : Finset ℕ) {β β' : ℝ} (hβ : β ≤ β') (n : ℕ) :
    selectedMoment s β n ≤ selectedMoment s β' n := by
  unfold selectedMoment primePowerProduct
  apply Finset.prod_le_prod₀
  · intro p hp
    dsimp only
    split_ifs <;> positivity
  · intro p hp
    dsimp only
    split_ifs
    · exact Real.rpow_le_rpow_of_exponent_le
        (one_le_pow₀ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)) hβ
    · exact le_rfl

theorem selectedMoment_le_exp_bigOmega {z κ : ℝ} (hz : 2 ≤ z) (hκ : 0 ≤ κ) (n : ℕ) :
    selectedMoment (Icc 0 ⌊z⌋₊) (κ / Real.log z) n ≤ (Real.exp κ) ^ bigOmega n := by
  unfold selectedMoment primePowerProduct
  calc
    _ ≤ ∏ p ∈ n.primeFactors, (Real.exp κ) ^ n.factorization p := by
      apply Finset.prod_le_prod₀
      · intro p hp
        dsimp only
        split_ifs <;> positivity
      · intro p hp
        dsimp only
        split_ifs with hpz
        · rw [← Real.rpow_pow_comm (Nat.cast_nonneg p)]
          apply pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg p) _)
          have H := rpow_log_cutoff_le_exp hz hκ 1 (Nat.prime_of_mem_primeFactors hp)
            ((Nat.le_floor_iff (by linarith : 0 ≤ z)).mp (mem_Icc.mp hpz).2)
          simpa only [Nat.cast_one, one_mul] using H
        · exact one_le_pow₀ (Real.one_le_exp_iff.mpr hκ)
    _ = _ := by
      rw [Finset.prod_pow_eq_pow_sum]
      congr 1
      exact (ArithmeticFunction.cardFactors_eq_sum_factorization (n := n)).symm

theorem bigOmega_coordinate_le {k : ℕ} (n : Tuple k) (j : Fin k) :
    bigOmega (n j) ≤ bigOmega (mass n) := by
  obtain ⟨d, hd⟩ := coordinate_dvd_mass n j
  have hd₀ : d ≠ 0 := by
    rintro rfl
    exact (mass_pos n).ne' (by simpa only [mul_zero] using hd)
  rw [hd, bigOmega_mul (n j).ne_zero hd₀]
  omega

/-- The multiplicative tilt associated with the selected coordinates. -/
noncomputable def selectedTilt {k : ℕ} (F : ArithmeticMap k) (j : Fin k)
    (s : Finset ℕ) (β : ℝ) : ArithmeticMap k :=
  fun n => F n * selectedMoment s β (n j)

/-- The shift in the polynomial-growth exponent is exactly `κ/log(z)`;
the prime-factor growth parameter is multiplied by `exp(κ)`. -/
theorem Admissible.selectedTilt {k : ℕ} {A B ε κ z : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hκ : 0 ≤ κ) (hz : 2 ≤ z) (j : Fin k) :
    Admissible (A * Real.exp κ) B (ε + κ / Real.log z)
      (selectedTilt F j (Icc 0 ⌊z⌋₊) (κ / Real.log z)) := by
  let s := Icc 0 ⌊z⌋₊
  let β := κ / Real.log z
  have hβ : 0 ≤ β := div_nonneg hκ (Real.log_pos (by linarith : 1 < z)).le
  refine ⟨fun n => mul_nonneg (hF.nonneg n) (selectedMoment_nonneg _ _ _), ?_⟩
  intro m n hmn
  have Hprime : selectedMoment s β (m j) ≤ (Real.exp κ) ^ bigOmega (mass m) :=
    (selectedMoment_le_exp_bigOmega hz hκ _).trans
      (pow_le_pow_right₀ (Real.one_le_exp_iff.mpr hκ) (bigOmega_coordinate_le m j))
  have Hpower : selectedMoment s β (m j) ≤ (mass m : ℝ) ^ β :=
    (selectedMoment_le_rpow s hβ (m j)).trans
      (Real.rpow_le_rpow (by positivity)
        (by exact_mod_cast Nat.le_of_dvd (mass_pos m) (coordinate_dvd_mass m j)) hβ)
  have Hgrowth : growthBound A B ε m * selectedMoment s β (m j) ≤
      growthBound (A * Real.exp κ) B (ε + β) m := by
    apply le_min
    · calc
        _ ≤ A ^ bigOmega (mass m) * (Real.exp κ) ^ bigOmega (mass m) :=
          mul_le_mul (min_le_left _ _) Hprime (selectedMoment_nonneg _ _ _) (pow_nonneg hA _)
        _ = _ := (mul_pow _ _ _).symm
    · calc
        _ ≤ (B * (mass m : ℝ) ^ ε) * (mass m : ℝ) ^ β :=
          mul_le_mul (min_le_right _ _) Hpower (selectedMoment_nonneg _ _ _) (by positivity)
        _ = _ := by rw [mul_assoc, ← Real.rpow_add (by exact_mod_cast mass_pos m)]
  change F (m * n) * selectedMoment s β ((m * n) j) ≤ _
  rw [show ((m * n) j : ℕ) = (m j : ℕ) * (n j : ℕ) from rfl,
    selectedMoment_mul_of_ne_zero s β (m j).ne_zero (n j).ne_zero]
  calc
    _ ≤ (growthBound A B ε m * F n) * (selectedMoment s β (m j) * selectedMoment s β (n j)) :=
      mul_le_mul_of_nonneg_right (hF.growth m n hmn)
        (mul_nonneg (selectedMoment_nonneg _ _ _) (selectedMoment_nonneg _ _ _))
    _ = (growthBound A B ε m * selectedMoment s β (m j)) * NairTenenbaum.selectedTilt F j s β n :=
        by
      unfold NairTenenbaum.selectedTilt
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right Hgrowth
      (mul_nonneg (hF.nonneg n) (selectedMoment_nonneg _ _ _))

end NairTenenbaum
