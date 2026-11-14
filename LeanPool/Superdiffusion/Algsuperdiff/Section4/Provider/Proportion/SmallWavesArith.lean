/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.G1AtomTails
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.G1Engine
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.LatticeCount

/-!
# SmallWavesArith

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Arithmetic and combinatorics for the small-waves lane

1. Its cardinality and the resulting `(1 + log N)^{1/σ}` penalty are produced
   exactly as `LatticeCount` does for the annulus.
2. **The interchange** `Σ_{n ≤ m} Σ_{k=n-1}^{m} = Σ_{k ≤ m} Σ_{n ≤ (k+1) ∧ m}`,
   an identity in `ℝ≥0∞` (Tonelli, no side condition).
3. **The geometric partial weight**, the manuscript's `4 s^{-1}`.
4. That absorption is proved here, explicitly.

## References

* ABK26, `l.ratio.of.good.scales.for.k`, Step 2.
* ABK26, `e.maxy.bound` and `e.powerofGammasigma`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability.ScalesConcentration
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The lattice cube as a `Finset`, and its penalty -/

open Classical in
/-- **The lattice cube as a `Finset`**: the proved set `Support.latticeCubeSet` cut
out of the enclosing index box.  This is the `𝒢₁b` maximum's index set. -/
def latticeCubeFinset (d : ℕ) (j outer : ℤ) : Finset (Fin d → ℤ) :=
  (boxIndexFinset d ((3 : ℤ) ^ (outer - j).toNat)).filter fun v =>
    Support.triadicLatticePoint j v ∈ openCubeSet (originCube d outer)

theorem mem_latticeCubeFinset_iff {j outer : ℤ} (hj : j ≤ outer) {v : Fin d → ℤ} :
    v ∈ latticeCubeFinset d j outer ↔ v ∈ Support.latticeCubeSet d j outer := by
  classical
  rw [latticeCubeFinset, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨mem_boxIndexFinset_iff.2 fun i => abs_le_of_mem_latticeCubeSet hj h i, h⟩

/-- **The count.**  `#(3^j ℤ^d ∩ □_outer) ≤ 3^{d(outer−j+1)}`. -/
theorem card_latticeCubeFinset_le (d : ℕ) {j outer : ℤ} :
    (latticeCubeFinset d j outer).card ≤ 3 ^ (d * ((outer - j).toNat + 1)) := by
  classical
  have hsub : (latticeCubeFinset d j outer).card
      ≤ (boxIndexFinset d ((3 : ℤ) ^ (outer - j).toNat)).card :=
    Finset.card_filter_le _ _
  rw [card_boxIndexFinset d ((3 : ℤ) ^ (outer - j).toNat)] at hsub
  refine le_trans hsub ?_
  have hstep : (2 * (3 : ℤ) ^ (outer - j).toNat + 1).toNat ≤ 3 ^ ((outer - j).toNat + 1) := by
    rw [Int.toNat_le]
    push_cast
    have h3 : (1 : ℤ) ≤ (3 : ℤ) ^ (outer - j).toNat := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    linarith only [h3]
  calc (2 * (3 : ℤ) ^ (outer - j).toNat + 1).toNat ^ d
      ≤ (3 ^ ((outer - j).toNat + 1)) ^ d := Nat.pow_le_pow_left hstep d
    _ = 3 ^ (d * ((outer - j).toNat + 1)) := by
        rw [← pow_mul, Nat.mul_comm]

theorem log_card_latticeCubeFinset_le (d : ℕ) {j outer : ℤ} :
    Real.log ((latticeCubeFinset d j outer).card : ℝ)
      ≤ (d : ℝ) * (((outer - j).toNat : ℝ) + 1) * Real.log 3 := by
  classical
  have hlog3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hRHS : (0 : ℝ) ≤ (d : ℝ) * (((outer - j).toNat : ℝ) + 1) * Real.log 3 := by
    positivity
  rcases Nat.eq_zero_or_pos (latticeCubeFinset d j outer).card with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact hRHS
  · have hcardpos : (0 : ℝ) < ((latticeCubeFinset d j outer).card : ℝ) := by
      exact_mod_cast hpos
    have hle : ((latticeCubeFinset d j outer).card : ℝ)
        ≤ (3 : ℝ) ^ (d * ((outer - j).toNat + 1)) := by
      have hcard := card_latticeCubeFinset_le d (j := j) (outer := outer)
      calc ((latticeCubeFinset d j outer).card : ℝ)
          ≤ ((3 ^ (d * ((outer - j).toNat + 1)) : ℕ) : ℝ) := by exact_mod_cast hcard
        _ = (3 : ℝ) ^ (d * ((outer - j).toNat + 1)) := by push_cast; ring
    refine le_trans (Real.log_le_log hcardpos hle) ?_
    rw [Real.log_pow]
    have hcast : ((d * ((outer - j).toNat + 1) : ℕ) : ℝ)
        = (d : ℝ) * (((outer - j).toNat : ℝ) + 1) := by push_cast; ring
    rw [hcast]

/-- The `isBigOWith_fmax` interface `log(#S) ≤ c^σ − 1`, discharged at the
lattice cube by the same penalty `LatticeCount` uses for the annulus. -/
theorem log_card_cube_le_annulusPenalty_rpow_sub_one (d : ℕ) {sigma : ℝ}
    (hsigma : 0 < sigma) (j outer : ℤ) :
    Real.log ((latticeCubeFinset d j outer).card : ℝ)
      ≤ annulusPenalty d sigma (outer - j).toNat ^ sigma - 1 := by
  rw [annulusPenalty_rpow d hsigma]
  have h := log_card_latticeCubeFinset_le d (j := j) (outer := outer)
  linarith only [h]

/-! ## 2. The `ℝ≥0∞` interchange -/

/-- A finite `Finset.Icc` block written as a guarded `tsum`. -/
theorem finsetIcc_sum_eq_tsum (g : ℤ → ℝ≥0∞) (a b : ℤ) :
    (∑ k ∈ Finset.Icc a b, g k) = ∑' k : ℤ, (if a ≤ k ∧ k ≤ b then g k else 0) := by
  classical
  rw [tsum_eq_sum (s := Finset.Icc a b) (f := fun k => if a ≤ k ∧ k ≤ b then g k else 0)]
  · refine (Finset.sum_congr rfl fun k hk => ?_).symm
    rw [ite_eq_left (Finset.mem_Icc.1 hk)]
  · intro k hk
    rw [ite_eq_right]
    intro hc
    exact hk (Finset.mem_Icc.2 hc)

/-- **The `𝒢₁b` interchange, as an identity.**  Tonelli in `ℝ≥0∞` does the swap
unconditionally: everything is nonnegative, so there is no summability side
condition. -/
theorem tsum_block_comm (w g : ℤ → ℝ≥0∞) (m : ℤ) :
    (∑' n : ℤ, (if n ≤ m then w n * ∑ k ∈ Finset.Icc (n - 1) m, g k else 0))
      = ∑' k : ℤ,
          (if k ≤ m then (∑' n : ℤ, (if n ≤ min (k + 1) m then w n else 0)) * g k
            else 0) := by
  classical
  have hstep : ∀ n : ℤ,
      (if n ≤ m then w n * ∑ k ∈ Finset.Icc (n - 1) m, g k else 0)
        = ∑' k : ℤ, (if n ≤ m ∧ n - 1 ≤ k ∧ k ≤ m then w n * g k else 0) := by
    intro n
    by_cases hn : n ≤ m
    · rw [ite_eq_left hn, finsetIcc_sum_eq_tsum, ← ENNReal.tsum_mul_left]
      refine tsum_congr fun k => ?_
      by_cases hk : n - 1 ≤ k ∧ k ≤ m
      · rw [ite_eq_left hk, ite_eq_left ⟨hn, hk.1, hk.2⟩]
      · rw [ite_eq_right hk, ite_eq_right (fun hc : n ≤ m ∧ n - 1 ≤ k ∧ k ≤ m => hk ⟨hc.2.1,
        hc.2.2⟩),
          mul_zero]
    · have hz : ∀ k : ℤ, (if n ≤ m ∧ n - 1 ≤ k ∧ k ≤ m then w n * g k else 0)
          = (0 : ℝ≥0∞) := fun k => ite_eq_right (fun hc => hn hc.1)
      rw [ite_eq_right hn, tsum_congr hz, tsum_zero]
  rw [tsum_congr hstep, ENNReal.tsum_comm]
  refine tsum_congr fun k => ?_
  by_cases hk : k ≤ m
  · rw [ite_eq_left hk, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun n => ?_
    by_cases hn : n ≤ min (k + 1) m
    · have h1 : n ≤ m ∧ n - 1 ≤ k ∧ k ≤ m := by
        refine ⟨le_trans hn (min_le_right _ _), ?_, hk⟩
        have := le_trans hn (min_le_left _ _)
        omega
      rw [ite_eq_left h1, ite_eq_left hn]
    · have h1 : ¬ (n ≤ m ∧ n - 1 ≤ k ∧ k ≤ m) := by
        rintro ⟨ha, hb, _⟩
        exact hn (le_min (by omega) ha)
      rw [ite_eq_right h1, ite_eq_right hn, zero_mul]
  · have hz : ∀ n : ℤ, (if n ≤ m ∧ n - 1 ≤ k ∧ k ≤ m then w n * g k else 0)
        = (0 : ℝ≥0∞) := by
      intro n
      rw [ite_eq_right]
      rintro ⟨_, _, hc⟩
      exact hk hc
    rw [ite_eq_right hk, tsum_congr hz, tsum_zero]

/-! ## 3. The geometric partial weight -/

/-- The event's own geometric weight `3^{-s(m-n)/4}`, in `ℝ≥0∞` and in the exact
spelling of the frozen `𝒢₁` definition. -/
def gwG1b (s : ℝ) (t : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * s * (t : ℝ)))

/-- The manuscript's interchange constant `4 s^{-1}`, in the explicit form the
`ℝ≥0∞` proof produces. -/
def g1bConst (s : ℝ) : ℝ := Real.rpow (3 : ℝ) (s / 2) * (12 / s)

theorem g1bConst_pos {s : ℝ} (hs : 0 < s) : 0 < g1bConst s := by
  unfold g1bConst
  have h2 : (0 : ℝ) < 12 / s := by positivity
  exact mul_pos (rpow_pos_three _) h2

private theorem gwG1b_split (s : ℝ) (m k n : ℤ) :
    Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * s * ((m - n : ℤ) : ℝ)) =
      Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * s * ((k - n : ℤ) : ℝ)) *
        Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * s * ((m - k : ℤ) : ℝ)) := by
  rw [← rpow_add_three]
  congr 1
  push_cast
  ring

/-- **The partial weight bound, proved.**  For `n ≤ k + 1` the weight
`3^{-s(m-n)/4}` is at most `3^{s/2}` times the two-sided Appendix-D weight at
rate `s/4`, so the guarded `n`-sum is `O(s^{-1})` times `3^{-s(m-k)/4}`. -/
theorem tsum_partialWeight_le {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (m k : ℤ) :
    (∑' n : ℤ, (if n ≤ min (k + 1) m then gwG1b s (m - n) else 0)) ≤
      ENNReal.ofReal (g1bConst s) * gwG1b s (m - k) := by
  classical
  have hterm : ∀ n : ℤ,
      (if n ≤ min (k + 1) m then gwG1b s (m - n) else 0) ≤
        ENNReal.ofReal (Real.rpow (3 : ℝ) (s / 2) * wt (s / 4) k n) * gwG1b s (m - k) := by
    intro n
    by_cases hn : n ≤ min (k + 1) m
    · have hnk : n ≤ k + 1 := le_trans hn (min_le_left _ _)
      rw [ite_eq_left hn, gwG1b, gwG1b_split s m k n,
        ENNReal.ofReal_mul
          (rpow_nonneg_three (-(1 / 4 : ℝ) * s * ((k - n : ℤ) : ℝ)))]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      have hexp : -(1 / 4 : ℝ) * s * ((k - n : ℤ) : ℝ) ≤
          s / 2 + -(s / 4 * idist k n) := by
        have habs : |((k : ℤ) : ℝ) - ((n : ℤ) : ℝ)| ≤ ((k - n : ℤ) : ℝ) + 2 := by
          rcases le_or_gt (n : ℤ) k with hle | hgt
          · have hc : ((n : ℤ) : ℝ) ≤ ((k : ℤ) : ℝ) := by exact_mod_cast hle
            rw [abs_of_nonneg (by linarith only [hc])]
            push_cast
            linarith only [hc]
          · have hc : ((k : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ) := by exact_mod_cast hgt.le
            have hk1 : ((n : ℤ) : ℝ) ≤ ((k : ℤ) : ℝ) + 1 := by
              exact_mod_cast (by omega : (n : ℤ) ≤ k + 1)
            rw [abs_of_nonpos (by linarith only [hc])]
            push_cast
            linarith only [hk1]
        have hid : idist k n = |((k : ℤ) : ℝ) - ((n : ℤ) : ℝ)| := rfl
        rw [hid]
        nlinarith only [habs, hs0]
      calc Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * s * ((k - n : ℤ) : ℝ))
          ≤ Real.rpow (3 : ℝ) (s / 2 + -(s / 4 * idist k n)) :=
            rpow_le_rpow_three hexp
        _ = Real.rpow (3 : ℝ) (s / 2) * wt (s / 4) k n := by
            rw [rpow_add_three]
            rfl
    · rw [ite_eq_right hn]
      exact zero_le
  refine le_trans (ENNReal.tsum_le_tsum hterm) ?_
  rw [ENNReal.tsum_mul_right]
  refine mul_le_mul' ?_ le_rfl
  have hsum : Summable fun n : ℤ => Real.rpow (3 : ℝ) (s / 2) * wt (s / 4) k n :=
    (summable_wtRow (by linarith only [hs0]) (by linarith only [hs1]) k).mul_left _
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (f := fun n : ℤ => Real.rpow (3 : ℝ) (s / 2) * wt (s / 4) k n)
    (fun n => mul_nonneg (rpow_nonneg_three _) (wt_nonneg _ _ _)) hsum]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [tsum_mul_left, g1bConst]
  refine mul_le_mul_of_nonneg_left ?_ (rpow_nonneg_three _)
  have h := tsum_wtRow_le (sprime := s / 4) (by linarith only [hs0])
    (by linarith only [hs1]) k
  refine h.trans (le_of_eq ?_)
  field_simp
  norm_num

/-! ## 4. Absorbing the lattice-max penalty into the discount -/

/-- The abstract-real core of the absorption.  Stated with an opaque `L` so that
no numeric tactic ever sees `Real.log`. -/
private theorem penalty_core {L a x D : ℝ} (hL1 : 1 ≤ L) (ha0 : 0 < a)
    (haL : a * L ≤ 1) (hx : 0 ≤ x) (hD : 0 ≤ D) :
    a * (1 + D * (x + 1) * L) ≤ (1 + 2 * D * L) * (1 + a * x * L) := by
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL1
  have ha1 : a ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hL1 ha0.le
    rw [mul_one] at h
    linarith only [h, haL]
  have hDL : (0 : ℝ) ≤ D * L := mul_nonneg hD hL0.le
  have haDxL : (0 : ℝ) ≤ a * D * x * L :=
    mul_nonneg (mul_nonneg (mul_nonneg ha0.le hD) hx) hL0.le
  have e1 : a * (D * L) ≤ 2 * (D * L) :=
    mul_le_mul_of_nonneg_right (by linarith only [ha1]) hDL
  have e2 : a * D * x * L ≤ 2 * (D * L) * (a * x * L) := by
    have h2L : (0 : ℝ) ≤ 2 * L - 1 := by linarith only [hL1]
    have hkey : 0 ≤ a * D * x * L * (2 * L - 1) := mul_nonneg haDxL h2L
    nlinarith only [hkey]
  have e3 : (0 : ℝ) ≤ a * x * L :=
    mul_nonneg (mul_nonneg ha0.le hx) hL0.le
  nlinarith only [ha1, e1, e2, e3]

/-- **The uniform tail scale of the `𝒢₁b` array.**  The lattice-max penalty at `σ =
2`, squared, is `1 + d(p+1)log 3`, which grows linearly in the scale gap `p = m
- k`; the array's built-in discount `3^{-s p/8}` absorbs it at the cost of one
power of `s^{-1}`. -/
theorem rpow_mul_penalty_sq_le (d : ℕ) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (p : ℕ) :
    Real.rpow (3 : ℝ) (-(s / 8 * (p : ℝ))) *
        (1 + (d : ℝ) * ((p : ℝ) + 1) * Real.log 3) ≤
      8 / s * (1 + 2 * (d : ℝ) * Real.log 3) := by
  have hL1 : (1 : ℝ) ≤ Real.log 3 := le_of_lt log_three_gt_one
  have hL2 : Real.log 3 < 2 := log_three_lt_two
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have ha0 : (0 : ℝ) < s / 8 := by linarith only [hs0]
  have hL0 : (0 : ℝ) ≤ Real.log 3 := le_trans zero_le_one hL1
  have haL : s / 8 * Real.log 3 ≤ 1 := by
    have h1 : s / 8 * Real.log 3 ≤ (1 / 8 : ℝ) * Real.log 3 :=
      mul_le_mul_of_nonneg_right (by linarith only [hs1]) hL0
    have h2 : (1 / 8 : ℝ) * Real.log 3 ≤ (1 / 8 : ℝ) * 2 :=
      mul_le_mul_of_nonneg_left hL2.le (by norm_num)
    linarith only [h1, h2]
  have hnn : (0 : ℝ) ≤ s / 8 * (p : ℝ) * Real.log 3 :=
    mul_nonneg (mul_nonneg ha0.le hp0) hL0
  have hbase : (0 : ℝ) < 1 + s / 8 * (p : ℝ) * Real.log 3 := by linarith only [hnn]
  have hexp : (1 : ℝ) + s / 8 * (p : ℝ) * Real.log 3 ≤
      Real.rpow (3 : ℝ) (s / 8 * (p : ℝ)) := by
    rw [rpow_def_three,
      show Real.log 3 * (s / 8 * (p : ℝ)) = s / 8 * (p : ℝ) * Real.log 3 from by ring]
    linarith only [Real.add_one_le_exp (s / 8 * (p : ℝ) * Real.log 3)]
  have hinv : Real.rpow (3 : ℝ) (-(s / 8 * (p : ℝ))) ≤
      (1 + s / 8 * (p : ℝ) * Real.log 3)⁻¹ := by
    rw [rpow_neg_three]
    exact inv_anti₀ hbase hexp
  have hpen : (0 : ℝ) ≤ 1 + (d : ℝ) * ((p : ℝ) + 1) * Real.log 3 :=
    annulusPenalty_base_nonneg d p
  have hstep : Real.rpow (3 : ℝ) (-(s / 8 * (p : ℝ))) *
      (1 + (d : ℝ) * ((p : ℝ) + 1) * Real.log 3) ≤
      (1 + s / 8 * (p : ℝ) * Real.log 3)⁻¹ *
        (1 + (d : ℝ) * ((p : ℝ) + 1) * Real.log 3) :=
    mul_le_mul_of_nonneg_right hinv hpen
  refine hstep.trans ?_
  have hcore := penalty_core (L := Real.log 3) (a := s / 8) (x := (p : ℝ))
    (D := (d : ℝ)) hL1 ha0 haL hp0 (Nat.cast_nonneg d)
  have h2 := mul_le_mul_of_nonneg_left hcore (inv_pos.2 ha0).le
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt ha0), one_mul] at h2
  have hs8 : (8 : ℝ) / s = (s / 8)⁻¹ := by
    rw [inv_div]
  rw [inv_mul_le_iff₀ hbase, hs8]
  exact le_trans h2 (le_of_eq (by ring))

end

end Algsuperdiff.Section4.Provider.Proportion
