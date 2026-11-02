/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Smooth.GeneralSmoothTail

/-! # Lemma 2: smooth tails with weights in the scalar class M

The constant precedes the arithmetic function and both real cutoffs. The
statement keeps the paper's sum of factor multiplicities in `4^(γκ)` and
covers the full range `x > z > 4^(γκ)`, including `z < 2`.
-/

@[expose] public section

namespace NairTenenbaum

open Finset

/-- Below two, a smooth positive integer must be one. -/
theorem factored_eq_one_of_cutoff_lt_two {n : ℕ} {z : ℝ} (hz : z < 2)
    (hn : n ∈ Nat.factoredNumbers (Finset.Icc 0 ⌊z⌋₊)) : n = 1 := by
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp hpn
  have H := (Finset.mem_Icc.mp (Nat.mem_factoredNumbers'.mp hn p hp hpn)).2
  have hz' : ⌊z⌋₊ < 2 := (Nat.floor_lt' (by decide)).mpr hz
  have := hp.two_le
  omega

/-- A class-M family admits one constant for all admissible `F`, discriminants,
and cutoffs. The exponent condition is weaker than Theorem 1's hypotheses. -/
theorem exists_classM_smooth_tail_bound {k r : ℕ} {A B ε κ : ℝ}
    {θ : Fin r → ℕ → ℝ} (hθ : ∀ i, ScalarClassM (θ i))
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hκ : 0 ≤ κ)
    (γ : Fin k → Fin r → ℕ) (hγ : ∀ i, 0 < totalExponent γ i)
    (hγε : ∀ i, (totalExponent γ i : ℝ) * ε ≤ 1 / 16)
    (G : ℕ) (hG : ∀ i, totalExponent γ i ≤ G) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ArithmeticMap k), Admissible A B ε F →
      ∀ (D : ℕ) (x z : ℝ), z < x → (4 : ℝ) ^ ((G : ℝ) * κ) < z →
        let f := fun m : ℕ+ =>
          if (m : ℕ) ∈ Nat.factoredNumbers (Finset.Icc 0 ⌊z⌋₊) ∧ x < (m : ℝ)
          then weight γ D F θ m else 0
        Summable f ∧ (∑' m, f m) ≤
          C * Real.exp (-κ * Real.log x / Real.log z) *
            ∑ m ∈ positiveUpTo z, weight γ D F θ m := by
  classical
  obtain ⟨Aθ, T, hAθ, hT, Hθ⟩ := scalarClassM_common hθ hε
  let A' := max A Aθ
  have hA' : 1 ≤ A' := hA.trans (le_max_left _ _)
  have Hθ' (i) : Admissible A' T ε (fun n : Tuple 1 => θ i (n 0)) :=
    (Hθ i).mono (zero_le_one.trans hAθ) (zero_le_one.trans hT) (le_max_right _ _) le_rfl le_rfl
  refine ⟨generalSmoothTailBound A' B T κ γ G,
    generalSmoothTailBound_pos (zero_le_one.trans hB) (zero_le_one.trans hT) γ G, ?_⟩
  intro F hF D x z hzx hzκ
  have hF' : Admissible A' B ε F :=
    hF.mono (zero_le_one.trans hA) (zero_le_one.trans hB) (le_max_left _ _) le_rfl le_rfl
  have hz₁ : 1 < z := (Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 4)
    (mul_nonneg (Nat.cast_nonneg _) hκ)).trans_lt hzκ
  by_cases hz : 2 ≤ z
  · exact general_weight_smooth_tail hF' Hθ' hA' hB hT hε hκ hz
      (lt_trans zero_lt_one (hz₁.trans hzx)) γ hγ hγε G hG hzκ.le D
  · have hf : (fun m : ℕ+ =>
        if (m : ℕ) ∈ Nat.factoredNumbers (Finset.Icc 0 ⌊z⌋₊) ∧ x < (m : ℝ)
        then weight γ D F θ m else 0) = 0 := by
      funext m
      apply ite_eq_right
      rintro ⟨hm, hx⟩
      have hm₁ := factored_eq_one_of_cutoff_lt_two (lt_of_not_ge hz) hm
      have hmR : (m : ℝ) = 1 := by exact_mod_cast hm₁
      rw [hmR] at hx
      linarith
    change Summable _ ∧ _ ≤ _
    rw [hf]
    refine ⟨summable_zero, ?_⟩
    change (∑' _ : ℕ+, (0 : ℝ)) ≤ _
    rw [tsum_zero]
    apply mul_nonneg
    · exact mul_nonneg (generalSmoothTailBound_pos (zero_le_one.trans hB)
        (zero_le_one.trans hT) γ G).le (Real.exp_pos _).le
    · exact Finset.sum_nonneg (fun m _ => weight_nonneg_of_positive γ D hF.nonneg
        (fun i n => (Hθ i).nonneg (fun _ => n)) m)

/-- The growth restriction used in the general tail estimate follows from the
original parameters of Theorem 1, which are assumed throughout §4. -/
theorem lemmaTwo_exponent_bound {g : ℕ} (hg : 0 < g) {ε δ : ℝ}
    (hε : 0 < ε) (hεg : ε < 1 / (8 * (g : ℝ) ^ 2))
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) {a : ℕ} (ha : a ≤ g) :
    (a : ℝ) * (ε * δ / 3) ≤ 1 / 16 := by
  have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hg₂ : (g : ℝ) ≤ (g : ℝ) ^ 2 := by nlinarith
  have H := (lt_div_iff₀ (by positivity : 0 < 8 * (g : ℝ) ^ 2)).mp hεg
  have H' : (g : ℝ) * ε < 1 / 8 := by
    nlinarith [mul_le_mul_of_nonneg_right hg₂ hε.le]
  calc
    (a : ℝ) * (ε * δ / 3) ≤ (g : ℝ) * (ε * δ / 3) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast ha) (by positivity)
    _ ≤ (g : ℝ) * (ε / 3) := mul_le_mul_of_nonneg_left
      (by nlinarith : ε * δ / 3 ≤ ε / 3) (by positivity)
    _ ≤ 1 / 16 := by nlinarith

/-- Lemma 2, equation (26), under the hypotheses stipulated at the start of §4.
No multiplicativity is required of the scalar weights. -/
def LemmaTwo : Prop :=
  ∀ (k r g : ℕ), 0 < g →
    ∀ (γ : Fin k → Fin r → ℕ), (∀ i, 0 < totalExponent γ i) →
      (∀ i, totalExponent γ i ≤ g) →
    ∀ (A B ε δ κ : ℝ), 1 ≤ A → 1 ≤ B → 0 < ε → ε < 1 / (8 * (g : ℝ) ^ 2) →
      0 < δ → δ ≤ 1 → 0 < κ →
    ∀ (θ : Fin r → ℕ → ℝ), (∀ i, ScalarClassM (θ i)) →
      ∃ C : ℝ, 0 < C ∧ ∀ (F : ArithmeticMap k), Admissible A B (ε * δ / 3) F →
        ∀ (D : ℕ) (x z : ℝ), z < x →
          (4 : ℝ) ^ (((∑ i, totalExponent γ i : ℕ) : ℝ) * κ) < z →
          let f := fun m : ℕ+ =>
            if (m : ℕ) ∈ Nat.factoredNumbers (Finset.Icc 0 ⌊z⌋₊) ∧ x < (m : ℝ)
            then weight γ D F θ m else 0
          Summable f ∧ (∑' m, f m) ≤
            C * Real.exp (-κ * Real.log x / Real.log z) *
              ∑ m ∈ positiveUpTo z, weight γ D F θ m

theorem lemmaTwo : LemmaTwo := by
  intro k r g hg γ hγ hγg A B ε δ κ hA hB hε hεg hδ hδ₁ hκ θ hθ
  exact exists_classM_smooth_tail_bound hθ hA hB (by positivity) hκ.le γ hγ
    (fun i => lemmaTwo_exponent_bound hg hε hεg hδ hδ₁ (hγg i))
    (∑ i, totalExponent γ i)
    (fun i => Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i))

end NairTenenbaum
