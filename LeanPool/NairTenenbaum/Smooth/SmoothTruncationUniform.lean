/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Smooth.SmoothTruncation

/-! # Uniform truncation for every smoothness cutoff

The large-cutoff absorption argument is supplemented by a fixed Euler product
for the bounded range. The resulting constant is independent of both cutoffs,
the arithmetic function, and the polynomial coefficients apart from their
supplied uniform root bounds.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

/-- Uniform bound for a whole local auxiliary series. -/
theorem rootAuxiliary_local_tsum_uniform {A B ε σ : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (hσ : σ < 1) (γ : ℕ) (hγ : (γ : ℝ) * ε ≤ σ)
    (Q : ℤ[X]) {p : ℕ} (hp : p.Prime) (C : ℕ)
    (hρ : ∀ ν, rootCount Q (p ^ ν) ≤ C) :
    (∑' ν : ℕ, rootAuxiliary A B ε γ Q (p ^ ν)) ≤
      (C : ℝ) * B / (1 - (2 : ℝ) ^ (σ - 1)) := by
  have hr : auxiliaryRatio ε γ p ≤ (2 : ℝ) ^ (σ - 1) := by
    apply (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le)
      (show (γ : ℝ) * ε - 1 ≤ σ - 1 by linarith)).trans
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp.two_le) (by linarith)
  have hd : 0 < 1 - (2 : ℝ) ^ (σ - 1) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  exact (rootAuxiliary_prime_pow_tsum_le hA hB hε γ (hγ.trans_lt hσ) Q hp C hρ).trans
    (div_le_div_of_nonneg_left (by positivity) hd (by linarith))

/-- A finite smooth tuple sum is bounded by its coordinate auxiliary products. -/
theorem rootTupleWeight_sum_le_euler {k r : ℕ} {A B ε : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (γ : Fin k → Fin r → ℕ) (hγε : ∀ i, (totalExponent γ i : ℝ) * ε < 1)
    (Q : Fin r → ℤ[X]) (C : Fin r → ℕ)
    (hρ : ∀ i p, p.Prime → ∀ ν, rootCount (Q i) (p ^ ν) ≤ C i)
    (s : Finset ℕ) (S : Finset (Tuple r)) (N : ℕ+)
    (hbox : ∀ n ∈ S, ∀ i, n i ≤ N)
    (hsmooth : ∀ n ∈ S, ∀ i, (n i : ℕ) ∈ Nat.factoredNumbers s) :
    (∑ n ∈ S, rootTupleWeight γ F Q n) ≤ F 1 *
      ∏ i, ∏ p ∈ s.filter Nat.Prime, ∑' ν : ℕ, rootAuxiliary A B ε (totalExponent γ i) (Q i) (p ^
          ν) := by
  classical
  let T := (Finset.Icc 1 N).filter (fun n : ℕ+ => (n : ℕ) ∈ Nat.factoredNumbers s)
  let U := fun i (n : ℕ+) => rootAuxiliary A B ε (totalExponent γ i) (Q i) n
  have hU : ∀ i n, 0 ≤ U i n := fun i n => rootAuxiliary_nonneg hA (zero_le_one.trans hB) _ _ n
  have hsub : S ⊆ Fintype.piFinset (fun _ : Fin r => T) := by
    intro n hn
    exact Fintype.mem_piFinset.mpr (fun i => Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨one_le, hbox n hn i⟩, hsmooth n hn i⟩)
  calc
    _ ≤ ∑ n ∈ S, F 1 * ∏ i, U i (n i) :=
      Finset.sum_le_sum (fun n _ => hF.pullback_root_weight_le hA hB γ Q n)
    _ = F 1 * ∑ n ∈ S, ∏ i, U i (n i) := by rw [Finset.mul_sum]
    _ ≤ F 1 * ∑ n ∈ Fintype.piFinset (fun _ : Fin r => T), ∏ i, U i (n i) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n _ _ => Finset.prod_nonneg (fun i _ => hU i (n i)))) (hF.nonneg 1)
    _ = F 1 * ∏ i, ∑ n ∈ T, U i n := by rw [Finset.prod_univ_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (hF.nonneg 1)
      apply Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg (fun n _ => hU i n))
      intro i _
      exact rootAuxiliary_sum_le_product hA hB hε _ (hγε i) _ (C i) (hρ i) s T
        (fun _ hn => (Finset.mem_filter.mp hn).2)

/-- The uniform threshold for comparing the two smooth-weight cutoffs. -/
noncomputable def smoothTruncationThreshold {k r : ℕ} (A B : ℝ)
    (γ : Fin k → Fin r → ℕ) (C : Fin r → ℕ) (G : ℕ) : ℝ :=
  (max 2 ((4 : ℝ) ^ G)) ^ smoothTruncationScale A B γ C

/-- The constant in the uniform smooth-weight truncation comparison. -/
noncomputable def smoothTruncationBound {k r : ℕ} (A B : ℝ)
    (γ : Fin k → Fin r → ℕ) (C : Fin r → ℕ) (G : ℕ) : ℝ :=
  (2 * ∏ i, primeBandBound A B (1 / 8) (smoothTruncationScale A B γ C) (totalExponent γ i) (C i)) +
    ∏ i, (((C i : ℝ) * B) / (1 - (2 : ℝ) ^ ((1 / 8 : ℝ) - 1))) ^
      ((Finset.Icc 0 ⌊smoothTruncationThreshold A B γ C G⌋₊).filter Nat.Prime).card

theorem smoothTruncationBound_pos {k r : ℕ} {A B : ℝ} (hB : 0 ≤ B)
    (γ : Fin k → Fin r → ℕ) (C : Fin r → ℕ) (G : ℕ) :
    0 < smoothTruncationBound A B γ C G := by
  have hd : 0 ≤ 1 - (2 : ℝ) ^ ((1 / 8 : ℝ) - 1) := sub_nonneg.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)).le
  apply add_pos_of_pos_of_nonneg
  · exact mul_pos (by norm_num) (Finset.prod_pos (fun _ _ => Real.exp_pos _))
  · exact Finset.prod_nonneg (fun i _ => pow_nonneg
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hB) hd) _)

/-- The tuple `1` contributes `F(1)` to every nonempty mass truncation. -/
theorem one_le_truncated_rootTupleWeight_sum {k r : ℕ} {F : ArithmeticMap k}
    (hF : ∀ n, 0 ≤ F n) (γ : Fin k → Fin r → ℕ) (hγ : ∀ i, 0 < totalExponent γ i)
    (Q : Fin r → ℤ[X]) (D : ℕ) (N : ℕ+) {z : ℝ} (hz : 1 ≤ z) :
    F 1 ≤ ∑ n ∈ (weightUpTo γ D N).filter (fun n => (weightedMass γ n : ℝ) ≤ z),
      rootTupleWeight γ F Q n := by
  classical
  have hmem : (1 : Tuple r) ∈ (weightUpTo γ D N).filter
      (fun n => (weightedMass γ n : ℝ) ≤ z) := by
    apply Finset.mem_filter.mpr
    constructor
    · apply (mem_weightUpTo γ hγ D N 1).mpr
      exact ⟨by rw [weightedMass_one]; exact Nat.succ_le_iff.mpr N.pos, by simp [Dagger]⟩
    · simpa using hz
  have H := Finset.single_le_sum (fun n _ => rootTupleWeight_nonneg γ hF Q n) hmem
  simpa [rootTupleWeight, pullback] using H

/-- Uniform finite smooth truncation for every `z ≥ 2`. -/
theorem smoothWeightUpTo_truncation_uniform {k r : ℕ} {A B ε z : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hz : 2 ≤ z)
    (γ : Fin k → Fin r → ℕ) (hγ : ∀ i, 0 < totalExponent γ i)
    (hγε : ∀ i, (totalExponent γ i : ℝ) * ε ≤ 1 / 8)
    (Q : Fin r → ℤ[X]) (C : Fin r → ℕ)
    (hρ : ∀ i p, p.Prime → ∀ ν, rootCount (Q i) (p ^ ν) ≤ C i)
    (G : ℕ) (hG : ∀ i, totalExponent γ i ≤ G) (D : ℕ) (N : ℕ+) :
    (∑ n ∈ smoothWeightUpTo γ D (Finset.Icc 0 ⌊z⌋₊) N, rootTupleWeight γ F Q n) ≤
      smoothTruncationBound A B γ C G *
        ∑ n ∈ (weightUpTo γ D N).filter (fun n => (weightedMass γ n : ℝ) ≤ z),
          rootTupleWeight γ F Q n := by
  classical
  let Z := smoothTruncationThreshold A B γ C G
  let E := ∏ i, (((C i : ℝ) * B) / (1 - (2 : ℝ) ^ ((1 / 8 : ℝ) - 1))) ^
    ((Finset.Icc 0 ⌊Z⌋₊).filter Nat.Prime).card
  have hd : 0 ≤ 1 - (2 : ℝ) ^ ((1 / 8 : ℝ) - 1) := sub_nonneg.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)).le
  have hE : 0 ≤ E := Finset.prod_nonneg (fun i _ => pow_nonneg
    (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hB)) hd) _)
  have hlo : 0 ≤ ∑ n ∈ (weightUpTo γ D N).filter (fun n => (weightedMass γ n : ℝ) ≤ z),
      rootTupleWeight γ F Q n := Finset.sum_nonneg (fun n _ => rootTupleWeight_nonneg γ hF.nonneg
          Q n)
  by_cases hzZ : Z ≤ z
  · refine (smoothWeightUpTo_truncation_large hF hA hB hε γ hγ hγε Q C hρ G hG hzZ D N).trans ?_
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hE) hlo
  · have hzZ' : z ≤ Z := (lt_of_not_ge hzZ).le
    have hsupport : Finset.Icc 0 ⌊z⌋₊ ⊆ Finset.Icc 0 ⌊Z⌋₊ :=
      Finset.Icc_subset_Icc_right (Nat.floor_mono hzZ')
    have H := rootTupleWeight_sum_le_euler hF hA hB hε γ
      (fun i => (hγε i).trans_lt (by norm_num)) Q C hρ (Finset.Icc 0 ⌊Z⌋₊)
      (smoothWeightUpTo γ D (Finset.Icc 0 ⌊z⌋₊) N) N
      (fun _ hn => weightUpTo_coordinate_le γ D N (Finset.mem_filter.mp hn).1)
      (fun _ hn i => Nat.factoredNumbers_mono hsupport ((Finset.mem_filter.mp hn).2 i))
    have hprod : (∏ i, ∏ p ∈ (Finset.Icc 0 ⌊Z⌋₊).filter Nat.Prime,
        ∑' ν : ℕ, rootAuxiliary A B ε (totalExponent γ i) (Q i) (p ^ ν)) ≤ E := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Finset.prod_nonneg (fun _ _ => tsum_nonneg
          (fun _ => rootAuxiliary_nonneg hA (zero_le_one.trans hB) _ _ _))
      · intro i _
        rw [← Finset.prod_const]
        apply Finset.prod_le_prod₀
        · exact fun _ _ => tsum_nonneg (fun _ => rootAuxiliary_nonneg hA (zero_le_one.trans hB) _
            _ _)
        · intro p hp
          exact rootAuxiliary_local_tsum_uniform hA hB hε (by norm_num) _ (hγε i) _
            (Finset.mem_filter.mp hp).2 (C i) (hρ i p (Finset.mem_filter.mp hp).2)
    calc
      _ ≤ F 1 * E := H.trans (mul_le_mul_of_nonneg_left hprod (hF.nonneg 1))
      _ ≤ E * ∑ n ∈ (weightUpTo γ D N).filter (fun n => (weightedMass γ n : ℝ) ≤ z),
          rootTupleWeight γ F Q n := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left
          (one_le_truncated_rootTupleWeight_sum hF.nonneg γ hγ Q D N (by linarith)) hE
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left
        (mul_nonneg (by norm_num) (Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le)))) hlo

end NairTenenbaum
