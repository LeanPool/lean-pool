/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Surface.CongruencePrimeWindow
import LeanPool.CCDN.Analysis.SmallDegreeSurfaceNumerics

/-! The number of subsets and edges of a common logarithmic prime window
costs only an arbitrarily small positive power of the box radius. Constants
are fixed before the radius, including the bounded range near B = 1. -/

@[expose] public section
namespace CCDN
noncomputable section
open Finset

/-- For `L ≥ 1`, the number of primes in `congruencePrimeWindow L`, multiplied by `log 2`, is
at most `(log 4 + 4) c L`, where `c` is `scalingPrimeRatio`. -/
theorem congruencePrimeWindow_card_log_two {L : ℝ} (hL : 1 ≤ L) :
    (congruencePrimeWindow L).card * Real.log 2 ≤
      (Real.log 4 + 4) * scalingPrimeRatio * L := by
  calc
    _ = ∑ _p ∈ congruencePrimeWindow L, Real.log 2 := by simp
    _ ≤ ∑ p ∈ congruencePrimeWindow L, Real.log p := by
      apply sum_le_sum
      intro p hp
      exact Real.log_le_log (by norm_num)
        (by exact_mod_cast ((mem_congruencePrimeWindow hL).mp hp).1.two_le)
    _ ≤ _ := congruencePrimeWindow_log_upper hL

/-- A uniform bound for any fixed exponential in the size of the window.
This retains the arbitrary epsilon needed to absorb residue multiplicities. -/
private theorem congruencePrimeWindow_pow_subpower {K R ε : ℝ}
    (hK : 1 ≤ K) (hR : 1 ≤ R) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 1 ≤ B →
      R ^ (congruencePrimeWindow (K * (Real.log B + 1))).card ≤ C * B ^ ε := by
  let A := (Real.log 4 + 4) * scalingPrimeRatio
  have hA : 0 < A := by
    have ha := scalingPrimeRatio_one_le
    have hl := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp only [A]
    positivity
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let D := A * K * Real.log R / ε + 1
  let E := A * Real.exp D / Real.log 2 * Real.log R
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  refine ⟨Real.exp (E + ε), Real.exp_pos _, ?_⟩
  intro B hB
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  let L := K * (Real.log B + 1)
  let m := (congruencePrimeWindow L).card
  have hL : 1 ≤ L := by dsimp only [L]; nlinarith
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hcard : (m : ℝ) * Real.log L ≤ A * L :=
    congruencePrimeWindow_card_log_bound hL
  have hcard2 : (m : ℝ) * Real.log 2 ≤ A * L :=
    congruencePrimeWindow_card_log_two hL
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hbound : (m : ℝ) * Real.log R ≤ E + ε * (Real.log B + 1) := by
    by_cases hlarge : D ≤ Real.log L
    · have hd : A * K * Real.log R / ε ≤ Real.log L := by
        dsimp only [D] at hlarge
        linarith
      have hd' : A * K * Real.log R ≤ ε * Real.log L := by
        have hh := (div_le_iff₀ hε).mp hd
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left hd' hm
      have hupper := mul_le_mul_of_nonneg_left hcard hε.le
      have hmain : (m : ℝ) * Real.log R ≤ ε * (Real.log B + 1) := by
        apply (mul_le_mul_iff_left₀ (mul_pos hA hK0)).mp
        dsimp only [L] at hupper
        nlinarith
      nlinarith
    · have hLbound : L ≤ Real.exp D := by
        have hh := Real.exp_le_exp.mpr (le_of_not_ge hlarge)
        rwa [Real.exp_log hL0] at hh
      have hm' : (m : ℝ) ≤ A * Real.exp D / Real.log 2 := by
        apply (le_div_iff₀ hlog2).mpr
        exact hcard2.trans (mul_le_mul_of_nonneg_left hLbound hA.le)
      have hh := mul_le_mul_of_nonneg_right hm' hlogR
      change (m : ℝ) * Real.log R ≤ E at hh
      nlinarith
  have hexp := Real.exp_le_exp.mpr hbound
  rw [← Real.log_pow, Real.exp_log (pow_pos hR0 _)] at hexp
  have heq : Real.exp (E + ε * (Real.log B + 1)) =
      Real.exp (E + ε) * B ^ ε := by
    rw [Real.rpow_def_of_pos hB0, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at hexp
  exact hexp

/-- The edge count of the subset lattice, together with a fixed cost per
selected prime, also has arbitrarily small power growth. -/
private theorem congruencePrimeWindow_edge_subpower {K R ε : ℝ}
    (hK : 1 ≤ K) (hR : 1 ≤ R) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 1 ≤ B →
      (congruencePrimeWindow (K * (Real.log B + 1))).card *
        R ^ (congruencePrimeWindow (K * (Real.log B + 1))).card ≤ C * B ^ ε := by
  obtain ⟨C, hC, hpow⟩ := congruencePrimeWindow_pow_subpower hK
    (show 1 ≤ 2 * R by linarith) hε
  refine ⟨C, hC, ?_⟩
  intro B hB
  let m := (congruencePrimeWindow (K * (Real.log B + 1))).card
  have hm : (m : ℝ) ≤ 2 ^ m := by exact_mod_cast (Nat.le_of_lt m.lt_two_pow_self)
  calc
    _ ≤ (2 : ℝ) ^ m * R ^ m := mul_le_mul_of_nonneg_right hm (by positivity)
    _ = (2 * R) ^ m := (mul_pow _ _ _).symm
    _ ≤ _ := hpow B hB

/-- Both prime-subset multiplicities and any fixed logarithmic power fit
inside the exponent gap used by the surface argument. -/
private theorem congruencePrimeWindow_edge_polylog_linear {K R : ℝ}
    (hK : 1 ≤ K) (hR : 1 ≤ R) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α B : ℝ, α ≤ 19 / 20 → 1 ≤ B →
      ((congruencePrimeWindow (K * (Real.log B + 1))).card *
        R ^ (congruencePrimeWindow (K * (Real.log B + 1))).card) *
        B ^ α * (Real.log B + 1) ^ k ≤ C * B := by
  obtain ⟨C₁, hC₁, h₁⟩ := congruencePrimeWindow_edge_subpower hK hR
    (by norm_num : (0 : ℝ) < 1 / 40)
  let C₂ := (k.factorial : ℝ) / (1 / 40 : ℝ) ^ k * Real.exp (1 / 40)
  have hC₂ : 0 < C₂ := by dsimp only [C₂]; positivity
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, ?_⟩
  intro α B hα hB
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have h₂ := logarithm_add_one_pow_le_rpow k (by norm_num : (0 : ℝ) < 1 / 40) hB
  change (Real.log B + 1) ^ k ≤ C₂ * B ^ (1 / 40 : ℝ) at h₂
  calc
    _ ≤ (C₁ * B ^ (1 / 40 : ℝ)) * B ^ α * (C₂ * B ^ (1 / 40 : ℝ)) := by
      apply mul_le_mul
        (mul_le_mul_of_nonneg_right (h₁ B hB) (Real.rpow_nonneg hB0.le _)) h₂
      · positivity
      · positivity
    _ = (C₁ * C₂) * B ^ (α + 1 / 20) := by
      rw [Real.rpow_add hB0]
      have hh : B ^ (1 / 20 : ℝ) = B ^ (1 / 40 : ℝ) * B ^ (1 / 40 : ℝ) := by
        rw [← Real.rpow_add hB0]
        norm_num
      rw [hh]
      ring
    _ ≤ (C₁ * C₂) * B ^ (1 : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hB (by linarith))
        (mul_pos hC₁ hC₂).le
    _ = _ := by rw [Real.rpow_one]

/-- For `K, R ≥ 1` and `k : ℕ`, there is a constant `C` such that, for every degree `d ≥ 5` and
every `B ≥ 1`, the prime window `W` of logarithmic size `K (log B + 1)` satisfies
`#W R^#W B^(2/√d) (log B + 1)^k ≤ C B`. -/
theorem congruencePrimeWindow_surface_residual_bound {K R : ℝ}
    (hK : 1 ≤ K) (hR : 1 ≤ R) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 5 ≤ d → ∀ B : ℝ, 1 ≤ B →
      ((congruencePrimeWindow (K * (Real.log B + 1))).card *
        R ^ (congruencePrimeWindow (K * (Real.log B + 1))).card) *
        B ^ (2 / Real.sqrt (d : ℝ)) * (Real.log B + 1) ^ k ≤ C * B := by
  obtain ⟨C, hC, hbound⟩ := congruencePrimeWindow_edge_polylog_linear hK hR k
  refine ⟨C, hC, fun d hd B hB => hbound _ B ?_ hB⟩
  have hh := surface_inverse_sqrt_le_nine_twentieths hd
  have he : 2 / Real.sqrt (d : ℝ) = 2 * (1 / Real.sqrt (d : ℝ)) := by ring
  rw [he]
  linarith

end
end CCDN
