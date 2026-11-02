/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Smooth.SmoothLogExpansion

/-! # Prime-power divisibility counts in the smooth logarithmic mass -/

@[expose] public section

namespace NairTenenbaum

open Finset Real

theorem factorization_eq_card_primePowers {n p L : ℕ} (hn : n ≠ 0) (hp : p.Prime)
    (hL : n.factorization p ≤ L) :
    n.factorization p = ((Icc 1 L).filter (fun ν => p ^ ν ∣ n)).card := by
  have HE : (Icc 1 L).filter (fun ν => p ^ ν ∣ n) = Icc 1 (n.factorization p) := by
    ext ν
    simp only [mem_filter, mem_Icc, hp.pow_dvd_iff_le_factorization hn]
    omega
  rw [HE, Nat.card_Icc]
  omega

theorem sum_factorization_eq_primePower_counts {ι : Type*} (S : Finset ι) (n : ι → ℕ)
    (hn : ∀ i ∈ S, n i ≠ 0) {p L : ℕ} (hp : p.Prime)
    (hL : ∀ i ∈ S, (n i).factorization p ≤ L) :
    (∑ i ∈ S, ((n i).factorization p : ℝ)) =
      ∑ ν ∈ Icc 1 L, ((S.filter (fun i => p ^ ν ∣ n i)).card : ℝ) := by
  classical
  have H (i : ι) (hi : i ∈ S) : ((n i).factorization p : ℝ) =
      ∑ ν ∈ Icc 1 L, if p ^ ν ∣ n i then (1 : ℝ) else 0 := by
    rw [factorization_eq_card_primePowers (hn i hi) hp (hL i hi)]
    simp only [sum_boole]
  calc
    _ = ∑ i ∈ S, ∑ ν ∈ Icc 1 L, if p ^ ν ∣ n i then (1 : ℝ) else 0 := sum_congr rfl H
    _ = ∑ ν ∈ Icc 1 L, ∑ i ∈ S, if p ^ ν ∣ n i then (1 : ℝ) else 0 := sum_comm
    _ = _ := by simp only [sum_boole]

theorem sum_log_smoothPart_eq_primePower_counts {ι : Type*} (S : Finset ι) (n : ι → ℕ+)
    {z : ℝ} (hz : 0 ≤ z) (L : ℕ → ℕ)
    (hL : ∀ p ∈ (range (⌊z⌋₊ + 1)).filter Nat.Prime, ∀ i ∈ S,
      (n i : ℕ).factorization p ≤ L p) :
    (∑ i ∈ S, Real.log (smoothPart (n i) z : ℕ)) =
      ∑ p ∈ (range (⌊z⌋₊ + 1)).filter Nat.Prime,
        (∑ ν ∈ Icc 1 (L p), ((S.filter (fun i => p ^ ν ∣ (n i : ℕ))).card : ℝ)) * Real.log p := by
  rw [sum_log_smoothPart_eq_prime_sum S n hz]
  apply sum_congr rfl
  intro p hp
  rw [sum_factorization_eq_primePower_counts S (fun i => (n i : ℕ)) (fun i _ => (n i).ne_zero)
    (mem_filter.mp hp).2 (hL p hp)]

end NairTenenbaum
