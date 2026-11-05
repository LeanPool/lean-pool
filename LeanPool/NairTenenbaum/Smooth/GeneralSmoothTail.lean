/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Smooth.LiftedWeightSums

/-! # Smooth tails for general scalar admissible weights

This extends the root-vector smooth-tail bound to the scalar class `M` in
Lemma 2. The proof lifts the weights into additional arithmetic coordinates,
squares the weighted mass, and halves the decay parameter.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial

/-- Uniform constant in the smooth-tail estimate for a general admissible weight. -/
noncomputable def generalSmoothTailBound {k r : ℕ} (A B T κ : ℝ)
    (γ : Fin k → Fin r → ℕ) (G : ℕ) : ℝ :=
  rootSmoothTailBound A (B * T ^ r) (κ / 2) (liftedExponents γ) (fun _ => 1) (2 * G)

theorem generalSmoothTailBound_pos {k r : ℕ} {A B T κ : ℝ}
    (hB : 0 ≤ B) (hT : 0 ≤ T) (γ : Fin k → Fin r → ℕ) (G : ℕ) :
    0 < generalSmoothTailBound A B T κ γ G :=
  rootSmoothTailBound_pos (mul_nonneg hB (pow_nonneg hT _)) _ _ _

/-- Finite general-weight smooth tail, with the same cutoff and decay as in
Lemma 2. Its slightly stronger growth bound is implied by Theorem 1's parameters. -/
theorem general_weight_smooth_tail_finite {k r : ℕ} {A B T ε κ z x : ℝ}
    {F : ArithmeticMap k} {θ : Fin r → ℕ → ℝ}
    (hF : Admissible A B ε F) (hθ : ∀ i, Admissible A T ε (fun n : Tuple 1 => θ i (n 0)))
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hT : 1 ≤ T) (hε : 0 < ε)
    (hκ : 0 ≤ κ) (hz : 2 ≤ z) (hx : 0 < x)
    (γ : Fin k → Fin r → ℕ) (hγ : ∀ i, 0 < totalExponent γ i)
    (hγε : ∀ i, (totalExponent γ i : ℝ) * ε ≤ 1 / 16)
    (G : ℕ) (hG : ∀ i, totalExponent γ i ≤ G) (hzκ : (4 : ℝ) ^ ((G : ℝ) * κ) ≤ z)
    (D : ℕ) (N : ℕ+) :
    (∑ m ∈ (Finset.Icc 1 N).filter (fun m : ℕ+ =>
        (m : ℕ) ∈ Nat.factoredNumbers (Finset.Icc 0 ⌊z⌋₊) ∧ x < (m : ℝ)),
      weight γ D F θ m) ≤
      generalSmoothTailBound A B T κ γ G * Real.exp (-κ * Real.log x / Real.log z) *
        ∑ m ∈ positiveUpTo z, weight γ D F θ m := by
  classical
  have hL := admissible_liftedArithmeticMap hF hθ hA (zero_le_one.trans hB)
    (zero_le_one.trans hT) hε.le γ hγ
  have hBT : 1 ≤ B * T ^ r := one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ hT)
  have hθ₀ (i : Fin r) (n : ℕ+) : 0 ≤ θ i n := (hθ i).nonneg (fun _ => n)
  have hΓ := liftedExponents_pos hγ
  have hΓε (i : Fin r) : (totalExponent (liftedExponents γ) i : ℝ) * ε ≤ 1 / 8 := by
    simp only [totalExponent_lifted, Nat.cast_mul, Nat.cast_ofNat]
    linarith [hγε i]
  have hΓG (i : Fin r) : totalExponent (liftedExponents γ) i ≤ 2 * G := by
    simpa only [totalExponent_lifted] using Nat.mul_le_mul_left 2 (hG i)
  have hκ₂ : 0 ≤ κ / 2 := by positivity
  have hzκ₂ : (4 : ℝ) ^ ((2 * G : ℕ) * (κ / 2)) ≤ z := by
    have he : ((2 * G : ℕ) : ℝ) * (κ / 2) = (G : ℝ) * κ := by
      push_cast
      ring
    rwa [he]
  have hshift (i : Fin r) :
      (totalExponent (liftedExponents γ) i : ℝ) * (ε + (κ / 2) / Real.log z) ≤ 7 / 8 := by
    apply moment_exponent_gap _ (hΓε i) hκ₂ hz
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hΓG i) hκ₂)).trans hzκ₂
  have hρ : ∀ (i : Fin r) p, p.Prime → ∀ ν, rootCount (X : ℤ[X]) (p ^ ν) ≤ 1 := by
    simp
  have H := smoothWeightUpTo_tail_uniform hL (zero_le_one.trans hA) hBT hε hκ₂
    (by norm_num : (7 / 8 : ℝ) < 1) hz (pow_pos hx 2) (liftedExponents γ) hΓ hshift
    (fun _ => X) (fun _ => 1) hρ D (N ^ 2)
  have HT := (smoothWeightUpTo_truncation_uniform hL (zero_le_one.trans hA) hBT hε hz
    (liftedExponents γ) hΓ hΓε (fun _ => X) (fun _ => 1) hρ (2 * G) hΓG D (N ^ 2)).trans
    (mul_le_mul_of_nonneg_left (truncated_liftedTupleWeight_sum_le hF.nonneg hθ₀ γ hγ D (N ^ 2) z)
      (smoothTruncationBound_pos (zero_le_one.trans hBT) _ _ _).le)
  have H' := H.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left HT (Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le)))
    (Real.exp_pos _).le)
  refine (smooth_weight_tail_le_lifted hF.nonneg hθ₀ γ hγ D N _ hx.le).trans (H'.trans_eq ?_)
  have he : -(κ / 2) * Real.log (x ^ 2) / Real.log z = -κ * Real.log x / Real.log z := by
    rw [Real.log_pow]
    ring
  rw [he]
  unfold generalSmoothTailBound rootSmoothTailBound
  ring

/-- The convergent infinite tail for arbitrary scalar admissible weights. -/
theorem general_weight_smooth_tail {k r : ℕ} {A B T ε κ z x : ℝ}
    {F : ArithmeticMap k} {θ : Fin r → ℕ → ℝ}
    (hF : Admissible A B ε F) (hθ : ∀ i, Admissible A T ε (fun n : Tuple 1 => θ i (n 0)))
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hT : 1 ≤ T) (hε : 0 < ε)
    (hκ : 0 ≤ κ) (hz : 2 ≤ z) (hx : 0 < x)
    (γ : Fin k → Fin r → ℕ) (hγ : ∀ i, 0 < totalExponent γ i)
    (hγε : ∀ i, (totalExponent γ i : ℝ) * ε ≤ 1 / 16)
    (G : ℕ) (hG : ∀ i, totalExponent γ i ≤ G) (hzκ : (4 : ℝ) ^ ((G : ℝ) * κ) ≤ z) (D : ℕ) :
    let f := fun m : ℕ+ => if (m : ℕ) ∈ Nat.factoredNumbers (Finset.Icc 0 ⌊z⌋₊) ∧ x < (m : ℝ)
      then weight γ D F θ m else 0
    Summable f ∧ (∑' m, f m) ≤
      generalSmoothTailBound A B T κ γ G * Real.exp (-κ * Real.log x / Real.log z) *
        ∑ m ∈ positiveUpTo z, weight γ D F θ m := by
  classical
  apply pnat_summable_and_tsum_le
  · intro m
    split_ifs
    · exact weight_nonneg_of_positive γ D hF.nonneg (fun i n => (hθ i).nonneg (fun _ => n)) m
    · rfl
  · intro N
    rw [← Finset.sum_filter]
    exact general_weight_smooth_tail_finite hF hθ hA hB hT hε hκ hz hx γ hγ hγε G hG hzκ D N

end NairTenenbaum
