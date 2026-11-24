/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.PermutationGeometry
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Algebra.BigOperators.Intervals

/-! Binary transcripts of deterministic comparisons on a finite input space. -/
@[expose] public noncomputable section
namespace Shellsort.ComparisonTranscriptBound
open scoped BigOperators

/-- Two distinct inputs cannot terminate at comparable nodes of the comparison tree. -/
def Separates {α : Type*} (trace : α → List Bool) : Prop :=
  ∀ x y, List.IsPrefix (trace x) (trace y) → x = y

/-- Pad each transcript to a common length. All resulting sets of words are disjoint. -/
theorem kraft {α : Type*} [Fintype α] (trace : α → List Bool)
    (separates : Separates trace) :
    (∑ x, ((2 : ℝ) ^ (trace x).length)⁻¹) ≤ 1 := by
  classical
  let d := ∑ x, (trace x).length
  have maxlen (x) : (trace x).length ≤ d :=
    Finset.single_le_sum (f := fun i => (trace i).length)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ x)
  let pad : (Σ x, List.Vector Bool (d - (trace x).length)) → List.Vector Bool d :=
    fun ⟨x, s⟩ => ⟨trace x ++ s.val, by simp [s.property, Nat.add_sub_of_le (maxlen x)]⟩
  have injective : Function.Injective pad := by
    rintro ⟨x, s⟩ ⟨y, t⟩ eq
    have common : trace x ++ s.val = trace y ++ t.val := congrArg Subtype.val eq
    have px : List.IsPrefix (trace x) (trace x ++ s.val) := ⟨_, rfl⟩
    have py : List.IsPrefix (trace y) (trace x ++ s.val) := ⟨t.val, common.symm⟩
    have xy : x = y := (List.prefix_or_prefix_of_prefix px py).elim (separates x y)
      (fun h => (separates y x h).symm)
    subst y
    have st : s = t := Subtype.ext (List.append_cancel_left common)
    cases st
    rfl
  have count : (∑ x, 2 ^ (d - (trace x).length)) ≤ 2 ^ d := by
    simpa [Fintype.card_sigma] using Fintype.card_le_of_injective pad injective
  have countR : (∑ x, (2 : ℝ) ^ (d - (trace x).length)) ≤ (2 : ℝ) ^ d := by exact_mod_cast count
  apply (mul_le_mul_iff_left₀ (show 0 < (2 : ℝ) ^ d by positivity)).mp
  rw [Finset.sum_mul, one_mul]
  convert countR using 1
  apply Finset.sum_congr rfl
  intro x _
  have exp := Nat.sub_add_cancel (maxlen x)
  have powers := congrArg (fun k => (2 : ℝ) ^ k) exp
  rw [pow_add] at powers
  rw [← powers]
  field_simp

/-- The mean length of separating binary comparison outcomes over equiprobable rank inputs. -/
theorem uniform_transcript_mean_lower {n : ℕ} (trace : RankPlacement n → List Bool)
    (separates : Separates trace) :
    Real.logb 2 (n.factorial : ℝ) ≤ uniformAverage (fun p => ((trace p).length : ℝ)) := by
  classical
  let m : ℝ := n.factorial
  have hm : 0 < m := by dsimp [m]; exact_mod_cast Nat.factorial_pos n
  have card : (Fintype.card (RankPlacement n) : ℝ) = m := by
    simp [RankPlacement, Fintype.card_perm, m]
  have cap := kraft trace separates
  have term (p : RankPlacement n) :
      Real.log m - (trace p).length * Real.log 2 ≤ m * ((2 : ℝ) ^ (trace p).length)⁻¹ - 1 := by
    have h := Real.log_le_sub_one_of_pos
      (show 0 < m * ((2 : ℝ) ^ (trace p).length)⁻¹ by positivity)
    rw [Real.log_mul hm.ne' (by positivity), Real.log_inv, Real.log_pow] at h
    linarith
  have total := Finset.sum_le_sum (s := (Finset.univ : Finset (RankPlacement n)))
    (fun p _ => term p)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    card, ← Finset.sum_mul, ← Finset.mul_sum, mul_one] at total
  have capM := mul_le_mul_of_nonneg_left cap hm.le
  change Real.log m / Real.log 2 ≤ (∑ p, ((trace p).length : ℝ)) / m
  apply (div_le_div_iff₀ (Real.log_pos (by norm_num)) hm).2
  nlinarith

/-- This version accepts an upper bound on transcript lengths, so equality to the cost
is sufficient as well. Both premises must hold for the actual execution model. -/
theorem uniform_cost_lower {n : ℕ} (trace : RankPlacement n → List Bool)
    (cost : RankPlacement n → ℕ) (separates : Separates trace)
    (budget : ∀ p, (trace p).length ≤ cost p) :
    Real.logb 2 (n.factorial : ℝ) ≤ uniformAverage (fun p => (cost p : ℝ)) := by
  refine (uniform_transcript_mean_lower trace separates).trans ?_
  unfold uniformAverage
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Finset.sum_le_sum fun p _ => by exact_mod_cast budget p




/-- Pair each factorial factor with the reflected factor. This yields a finite
comparison lower bound in units of n log₂ n without any asymptotic estimates. -/
theorem half_nlog_le_log_factorial {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * Real.logb 2 n / 2 ≤ Real.logb 2 (n.factorial : ℝ) := by
  have paired : n ^ n ≤ n.factorial ^ 2 := by
    have h (i : ℕ) (hi : i ∈ Finset.range n) : n ≤ (i + 1) * (n - 1 - i + 1) := by
      have lt := Finset.mem_range.mp hi
      have hi' : n = i + 1 + (n - 1 - i) := by omega
      nlinarith [Nat.zero_le (i * (n - 1 - i))]
    have b := Finset.prod_le_prod h
    simpa [Finset.prod_mul_distrib, Finset.prod_range_reflect (fun i => i + 1),
      Finset.prod_range_add_one_eq_factorial, pow_two] using b
  have r : (n : ℝ) ^ n ≤ (n.factorial : ℝ) ^ 2 := by exact_mod_cast paired
  have pos : 0 < (n : ℝ) ^ n := pow_pos (by exact_mod_cast hn) _
  have l := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) pos r
  rw [Real.logb_pow, Real.logb_pow] at l
  push_cast at l
  linarith

end Shellsort.ComparisonTranscriptBound
