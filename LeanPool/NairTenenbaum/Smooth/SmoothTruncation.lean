/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Smooth.SmoothCutoffComparison

/-! # Absorbing the smooth tail

The smaller smoothness cutoff is chosen so that the moment bound makes its
tail at most half of the full sum. The prime-band comparison then reduces the
original smooth sum to a sum with weighted mass at most `z`.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

/-- An explicit constant for choosing the smaller smoothness cutoff. -/
noncomputable def smoothTruncationScale {k r : ℕ} (A B : ℝ)
    (γ : Fin k → Fin r → ℕ) (C : Fin r → ℕ) : ℝ :=
  1 + |∑ i, momentPrimeBound A B 1 (7 / 8) (totalExponent γ i) (C i)| + Real.log 2

theorem smoothTruncationScale_one_le {k r : ℕ} (A B : ℝ)
    (γ : Fin k → Fin r → ℕ) (C : Fin r → ℕ) : 1 ≤ smoothTruncationScale A B γ C := by
  unfold smoothTruncationScale
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith [abs_nonneg (∑ i, momentPrimeBound A B 1 (7 / 8) (totalExponent γ i) (C i))]

/-- This choice of scale makes the moment correction times the Rankin saving
at most one half. No sign assumption on the written correction constant is needed. -/
theorem smoothTruncationScale_absorb {k r : ℕ} (A B : ℝ)
    (γ : Fin k → Fin r → ℕ) (C : Fin r → ℕ) :
    Real.exp (-smoothTruncationScale A B γ C) *
      (∏ i, Real.exp (momentPrimeBound A B 1 (7 / 8) (totalExponent γ i) (C i))) ≤ 1 / 2 := by
  rw [← Real.exp_sum, ← Real.exp_add]
  calc
    _ ≤ Real.exp (-Real.log 2) := by
      apply Real.exp_le_exp.mpr
      unfold smoothTruncationScale
      linarith [le_abs_self (∑ i, momentPrimeBound A B 1 (7 / 8) (totalExponent γ i) (C i))]
    _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num

/-- The finite absorption step. Its hypotheses expose exactly what is required
of the smaller cutoff; the following theorem supplies it explicitly. -/
theorem smoothWeightUpTo_truncation_of_cutoff {k r : ℕ} {A B ε L w z : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (hw : 2 ≤ w) (hz : 2 ≤ z) (hlog : Real.log z / Real.log w = L)
    (γ : Fin k → Fin r → ℕ) (hγ : ∀ i, 0 < totalExponent γ i)
    (hγε : ∀ i, (totalExponent γ i : ℝ) * ε ≤ 1 / 8)
    (hshift : ∀ i, (totalExponent γ i : ℝ) * (ε + 1 / Real.log w) ≤ 7 / 8)
    (Q : Fin r → ℤ[X]) (C : Fin r → ℕ)
    (hρ : ∀ i p, p.Prime → ∀ ν, rootCount (Q i) (p ^ ν) ≤ C i)
    (habsorb : Real.exp (-L) *
      (∏ i, Real.exp (momentPrimeBound A B 1 (7 / 8) (totalExponent γ i) (C i))) ≤ 1 / 2)
    (D : ℕ) (N : ℕ+) :
    (∑ n ∈ smoothWeightUpTo γ D (Finset.Icc 0 ⌊z⌋₊) N, rootTupleWeight γ F Q n) ≤
      (2 * ∏ i, primeBandBound A B (1 / 8) L (totalExponent γ i) (C i)) *
        ∑ n ∈ (weightUpTo γ D N).filter (fun n => (weightedMass γ n : ℝ) ≤ z),
          rootTupleWeight γ F Q n := by
  classical
  let S := smoothWeightUpTo γ D (Finset.Icc 0 ⌊w⌋₊) N
  let W := fun n => rootTupleWeight γ F Q n
  have hW : ∀ n, 0 ≤ W n := rootTupleWeight_nonneg γ hF.nonneg Q
  have htail : (∑ n ∈ S.filter (fun n => z < (weightedMass γ n : ℝ)), W n) ≤
      (1 / 2) * ∑ n ∈ S, W n := by
    have H := smoothWeightUpTo_tail_uniform hF hA hB hε (κ := 1) (by norm_num)
      (σ := 7 / 8) (by norm_num) hw (show 0 < z by linarith) γ hγ hshift Q C hρ D N
    have heq : -1 * Real.log z / Real.log w = -L := by rw [neg_one_mul, neg_div, hlog]
    rw [heq, ← mul_assoc] at H
    exact H.trans (mul_le_mul_of_nonneg_right habsorb (Finset.sum_nonneg (fun n _ => hW n)))
  have hlow : (∑ n ∈ S.filter (fun n => (weightedMass γ n : ℝ) ≤ z), W n) ≤
      ∑ n ∈ (weightUpTo γ D N).filter (fun n => (weightedMass γ n : ℝ) ≤ z), W n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      obtain ⟨hn, hm⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1, hm⟩
    · exact fun n _ _ => hW n
  have hsplit : (∑ n ∈ S.filter (fun n => (weightedMass γ n : ℝ) ≤ z), W n) +
      (∑ n ∈ S.filter (fun n => z < (weightedMass γ n : ℝ)), W n) = ∑ n ∈ S, W n := by
    simpa only [not_le] using Finset.sum_filter_add_sum_filter_not S
      (fun n => (weightedMass γ n : ℝ) ≤ z) W
  have hsmall : (∑ n ∈ S, W n) ≤
      2 * ∑ n ∈ (weightUpTo γ D N).filter (fun n => (weightedMass γ n : ℝ) ≤ z), W n := by
    linarith
  have H := smoothWeightUpTo_cutoff_uniform hF hA hB hε (σ := 1 / 8) (by norm_num)
    hw hz hlog.le γ hγ hγε Q C hρ D N
  refine H.trans ?_
  calc
    _ ≤ (∏ i, primeBandBound A B (1 / 8) L (totalExponent γ i) (C i)) *
        (2 * ∑ n ∈ (weightUpTo γ D N).filter (fun n => (weightedMass γ n : ℝ) ≤ z), W n) :=
      mul_le_mul_of_nonneg_left hsmall (Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le))
    _ = _ := by ring

/-- A fixed large-cutoff threshold supplies the smaller smoothness cutoff.
The bound is uniform in the mass cutoff and the arithmetic function. -/
theorem smoothWeightUpTo_truncation_large {k r : ℕ} {A B ε z : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (γ : Fin k → Fin r → ℕ) (hγ : ∀ i, 0 < totalExponent γ i)
    (hγε : ∀ i, (totalExponent γ i : ℝ) * ε ≤ 1 / 8)
    (Q : Fin r → ℤ[X]) (C : Fin r → ℕ)
    (hρ : ∀ i p, p.Prime → ∀ ν, rootCount (Q i) (p ^ ν) ≤ C i)
    (G : ℕ) (hG : ∀ i, totalExponent γ i ≤ G)
    (hz : (max 2 ((4 : ℝ) ^ G)) ^ smoothTruncationScale A B γ C ≤ z) (D : ℕ) (N : ℕ+) :
    (∑ n ∈ smoothWeightUpTo γ D (Finset.Icc 0 ⌊z⌋₊) N, rootTupleWeight γ F Q n) ≤
      (2 * ∏ i, primeBandBound A B (1 / 8) (smoothTruncationScale A B γ C)
        (totalExponent γ i) (C i)) *
          ∑ n ∈ (weightUpTo γ D N).filter (fun n => (weightedMass γ n : ℝ) ≤ z),
            rootTupleWeight γ F Q n := by
  let L := smoothTruncationScale A B γ C
  let V : ℝ := max 2 ((4 : ℝ) ^ G)
  let w := z ^ L⁻¹
  have hL₁ : 1 ≤ L := smoothTruncationScale_one_le A B γ C
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hL₁
  have hV : 2 ≤ V := le_max_left _ _
  have hVz : V ≤ z := (by
    calc
      V = V ^ (1 : ℝ) := (Real.rpow_one V).symm
      _ ≤ V ^ L := Real.rpow_le_rpow_of_exponent_le (by linarith) hL₁
      _ ≤ z := hz)
  have hz₂ : 2 ≤ z := hV.trans hVz
  have hz₀ : 0 < z := by linarith
  have hwV : V ≤ w := (Real.le_rpow_inv_iff_of_pos (by linarith) hz₀.le hL).mpr hz
  have hw : 2 ≤ w := hV.trans hwV
  have hlog : Real.log z / Real.log w = L := by
    have hlz : Real.log z ≠ 0 := (Real.log_pos (by linarith : 1 < z)).ne'
    dsimp only [w]
    rw [Real.log_rpow hz₀]
    field_simp
  apply smoothWeightUpTo_truncation_of_cutoff hF hA hB hε hw hz₂ hlog γ hγ hγε
  · intro i
    apply moment_exponent_gap _ (hγε i) (by norm_num) hw
    have hpow : (4 : ℝ) ^ ((totalExponent γ i : ℝ) * 1) ≤ (4 : ℝ) ^ G := by
      rw [mul_one, Real.rpow_natCast]
      exact pow_le_pow_right₀ (by norm_num) (hG i)
    exact hpow.trans ((le_max_right _ _).trans hwV)
  · exact hρ
  · exact smoothTruncationScale_absorb A B γ C

end NairTenenbaum
