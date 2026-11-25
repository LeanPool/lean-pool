/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.HarvestBlockIteration
public import LeanPool.ShellsortMean.HarvestWordCost

/-! Sum ordinary comparison counts along a certified sequence of actual
blocks. Positive words describe the same transitions as the certificate. -/
@[expose] public noncomputable section
namespace Shellsort.HarvestBlockIteration
open Actual214
/-- Match each realized stage to its typed positive execution word and
bound the ratio of its entry scale to the smallest gap in that word. -/
def Covers (R : ℕ) : ℕ → List Stage → List ℕ → List PositiveWord → Prop
  | _, [], [], [] => True
  | prev, s::ss, h::hs, w::ws =>
      w.map Subtype.val = stageWord s h ∧
      (∃ H : ℕ, 0 < H ∧ prev ≤ R * H ∧ ∀ k ∈ w, H ≤ k.val) ∧
      Covers R (gap s.j) ss hs ws
  | _, _, _, _ => False

theorem comparisons_append {n : ℕ} (p : RankPlacement n) (u v : PositiveWord) :
    ordinaryWordComparisons p (u++v) =
      ordinaryWordComparisons p u + ordinaryWordComparisons (sortWord p (u.map Subtype.val)) v := by
  induction u generalizing p with
  | nil => simp [ordinaryWordComparisons, sortWord]
  | cons h t ih =>
    simp only [List.cons_append, ordinaryWordComparisons, List.map_cons, sortWord, ih,
      Nat.add_assoc]

/-- On each fixed original input, costs compose on the actual previous
checkpoint. The only averaging below is over that original input. -/
theorem certified_comparison_sum {n : ℕ} (hn : 0 < n) (ss : List Stage)
    (hs : List ℕ) (ws : List PositiveWord) (P : RankPlacement n → RankPlacement n)
    (prev R : ℕ) (initial : meanEnergy P ≤ scaleBound prev)
    (cert : Certified P ss hs) (fit : Covers R prev ss hs ws) :
    uniformAverage (fun p => (ordinaryWordComparisons (P p) ws.flatten : ℝ)) ≤
      (ws.flatten.length : ℝ) * ((1 + 2 * ((2 : ℝ) ^ 115 * R)) * n) := by
  induction ss generalizing hs ws P prev with
  | nil =>
    obtain rfl : hs = [] := cert
    cases ws with
    | nil => simp [ordinaryWordComparisons, uniformAverage]
    | cons => exact False.elim fit
  | cons s ss ih =>
    cases hs with
    | nil => exact False.elim cert
    | cons h hs =>
      cases ws with
      | nil => exact False.elim fit
      | cons w ws =>
        obtain ⟨agree, ⟨H, Hpos, ratio, lower⟩, fittail⟩ := fit
        have r : (prev : ℝ) ≤ (R : ℝ) * H := by exact_mod_cast ratio
        have cap : meanEnergy P ≤ (((2 : ℝ) ^ 115 * R) * H) ^ 2 := by
          apply initial.trans
          apply pow_le_pow_left₀ (by positivity)
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left r (by positivity)
        have one := HarvestWordCost.actual_word_from_square hn Hpos P w lower
          ((2 : ℝ) ^ 115 * R) (by positivity) cap
        have tail := ih hs ws (fun p => sortWord (P p) (stageWord s h)) (gap s.j)
          cert.2.2.1 cert.2.2.2 fittail
        simp only [List.flatten_cons, comparisons_append, Nat.cast_add, uniformAverage_add, agree,
          List.length_append]
        rw [add_mul]
        exact add_le_add one tail

/-- The remaining input to this endpoint is a deterministic schedule fact:
every menu realization can be listed as positive gaps at the declared scales. -/
theorem select_comparison_words {n : ℕ} (hn : 0 < n) (ss : List Stage)
    (P : RankPlacement n → RankPlacement n) (R : ℕ) (centers : Centers n ss)
    (covers : ∀ hs, List.Forall₂ (fun s h => h ∈ HarvestMenuBlock.choices s.j) ss hs →
      ∃ ws, Covers R n ss hs ws) :
    ∃ hs ws, Certified P ss hs ∧ Covers R n ss hs ws ∧
      uniformAverage (fun p => (ordinaryWordComparisons (P p) ws.flatten : ℝ)) ≤
        (ws.flatten.length : ℝ) * ((1 + 2 * ((2 : ℝ) ^ 115 * R)) * n) := by
  obtain ⟨hs, hc⟩ := select_blocks_from_size hn ss centers P
  obtain ⟨ws, fit⟩ := covers hs (certified_choices hc)
  exact ⟨hs, ws, hc, fit, certified_comparison_sum hn ss hs ws P n R (initial_bound hn P) hc fit⟩

end Shellsort.HarvestBlockIteration
