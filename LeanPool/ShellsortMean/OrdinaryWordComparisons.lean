/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.RankBandCost
public import LeanPool.ShellsortMean.NaturalComparisonBounds

/-!
Comparisons on actual insertion executions. A strict record minimum is a key
smaller than every earlier key in its chain; the first key is included. The
record count is computed from the input list, independently of the counters.
-/

@[expose] public noncomputable section
namespace Shellsort
open scoped BigOperators

def prefixMinima {α : Type*} [LinearOrder α] (l : List α) : ℕ :=
  List.reverseRec (motive := fun _ => ℕ) 0
    (fun pre a count => count + if pre.all (fun b => decide (a < b)) then 1 else 0) l

theorem insertCompared_exact {α : Type*} [LinearOrder α] (a : α) (l : List α) :
    (insertCompared a l).comparisons + (if l.all (fun b => decide (a < b)) then 1 else 0) =
      (insertCompared a l).shifts + 1 := by
  induction l with
  | nil => simp [insertCompared]
  | cons b l ih =>
    by_cases hab : a < b <;> simp [insertCompared, hab] at *
    omega

theorem insertionComparedBack_records {α : Type*} [LinearOrder α] (l : List α) :
    (insertionComparedBack l).comparisons + prefixMinima l =
      (insertionComparedBack l).shifts + l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [prefixMinima, insertionComparedBack_nil]
  | append_singleton l a ih =>
    have hp := congrArg Prod.fst (insertionComparedBack_projection l)
    simp only at hp
    have he := (insertionBack_perm l)
    have ha : (insertionComparedBack l).output.all (fun b => decide (a < b)) =
        l.all (fun b => decide (a < b)) := by
      rw [hp]
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, decide_eq_true_eq]
      constructor <;> intro h b hb
      · exact h b (he.mem_iff.mpr hb)
      · exact h b (he.mem_iff.mp hb)
    have step := insertCompared_exact a (insertionComparedBack l).output
    rw [ha] at step
    simp only [insertionComparedBack_append, prefixMinima, List.reverseRec_concat,
      List.length_append, List.length_singleton] at *
    omega

theorem insertionComparedExecution_scan {α : Type*} [LinearOrder α] (l : List α) :
    l.length - 1 ≤ (insertionComparedExecution l).comparisons := by
  change _ ≤ (insertionComparedBack l).comparisons
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    rw [insertionComparedBack_append]
    by_cases hl : l = []
    · subst l; simp
    · have hp := congrArg Prod.fst (insertionComparedBack_projection l)
      simp only at hp
      have hn : (insertionComparedBack l).output ≠ [] := by
        intro hz
        apply hl
        exact (List.length_eq_zero_iff.mp (by simpa [← hp, hz] using
          (insertionBack_perm l).length_eq.symm))
      have hs : 0 < (insertCompared a (insertionComparedBack l).output).comparisons := by
        cases hx : (insertionComparedBack l).output with
        | nil => contradiction
        | cons b bs => by_cases hab : a < b <;> simp [insertCompared, hab]
      simp only [List.length_append, List.length_singleton]
      have hlen := List.length_pos_iff.mpr hl
      omega

def gapPrefixMinima {n : ℕ} (p : RankPlacement n) (k : ℕ) (hk : 0 < k) : ℕ :=
  ∑ s : Fin k, prefixMinima (List.ofFn (chainKeys p k hk s))

theorem gapComparisonCost_records {n : ℕ} (p : RankPlacement n) (k : ℕ) (hk : 0 < k) :
    gapComparisonCost p k hk + gapPrefixMinima p k hk = gapInsertionCost p k hk + n := by
  unfold gapComparisonCost gapPrefixMinima gapInsertionCost
  conv_rhs => rhs; rw [← sum_actual_chain_lengths n k hk]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  let l := List.ofFn (chainKeys p k hk s)
  have hr := insertionComparedBack_records l
  have hs := insertionComparedExecution_shifts l
  change (insertionComparedBack l).shifts = _ at hs
  rw [hs] at hr
  simpa only [l, insertionComparedExecution, List.length_ofFn] using hr

theorem chainScanVisits_eq (n k : ℕ) (hk : 0 < k) :
    (∑ s : Fin k, (sourceTrialLength (n / k) (n % k) s.val - 1)) = n - k := by
  by_cases hkn : k ≤ n
  · have hpos : 0 < n / k := Nat.div_pos hkn hk
    have each (s : Fin k) : sourceTrialLength (n / k) (n % k) s.val - 1 + 1 =
        sourceTrialLength (n / k) (n % k) s.val := by
      unfold sourceTrialLength
      split <;> omega
    have he := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin k))) rfl (fun s _ => each s)
    have hadd : (∑ s : Fin k, (sourceTrialLength (n / k) (n % k) s.val - 1)) + k = n := by
      simpa [Finset.sum_add_distrib, sum_actual_chain_lengths n k hk] using he
    exact Nat.eq_sub_of_add_eq hadd
  · have hnk : n < k := by omega
    simp only [Nat.div_eq_of_lt hnk, sourceTrialLength]
    rw [Nat.sub_eq_zero_of_le hnk.le]
    apply Finset.sum_eq_zero
    intro s _
    split <;> decide

theorem gapComparisonCost_scan_bounds {n : ℕ} (p : RankPlacement n) (k : ℕ) (hk : 0 < k) :
    max (gapInsertionCost p k hk) (n - k) ≤ gapComparisonCost p k hk ∧
      gapComparisonCost p k hk ≤ gapInsertionCost p k hk + (n - k) := by
  constructor
  · apply max_le (gapComparisonCost_lower p k hk)
    rw [← chainScanVisits_eq n k hk]
    apply Finset.sum_le_sum
    intro s _
    simpa only [List.length_ofFn] using insertionComparedExecution_scan
      (List.ofFn (chainKeys p k hk s))
  · simpa only [chainScanVisits_eq n k hk] using gapComparisonCost_upper_chains p k hk

def ordinaryWordComparisons {n : ℕ} (p : RankPlacement n) : List {k : ℕ // 0 < k} → ℕ
  | [] => 0
  | k :: ks => gapComparisonCost p k.val k.property +
      ordinaryWordComparisons (gapSort p k.val) ks

def wordPrefixMinima {n : ℕ} (p : RankPlacement n) : List {k : ℕ // 0 < k} → ℕ
  | [] => 0
  | k :: ks => gapPrefixMinima p k.val k.property + wordPrefixMinima (gapSort p k.val) ks

theorem ordinaryWord_records_eq {n : ℕ} (p : RankPlacement n) (ks : List {k : ℕ // 0 < k}) :
    ordinaryWordComparisons p ks + wordPrefixMinima p ks =
      ordinaryWordShifts p ks + n * ks.length := by
  induction ks generalizing p with
  | nil => simp [ordinaryWordComparisons, ordinaryWordShifts, wordPrefixMinima]
  | cons k ks ih =>
    have hi := ih (gapSort p k.val)
    have hk := gapComparisonCost_records p k.val k.property
    simp only [ordinaryWordComparisons, ordinaryWordShifts, wordPrefixMinima, List.length_cons,
      Nat.mul_succ]
    omega

theorem ordinaryWord_scan_bounds {n : ℕ} (p : RankPlacement n) (ks : List {k : ℕ // 0 < k}) :
    max (ordinaryWordShifts p ks) ((ks.map (fun k => n - k.val)).sum) ≤ ordinaryWordComparisons p
      ks ∧
    ordinaryWordComparisons p ks ≤ ordinaryWordShifts p ks + (ks.map (fun k => n - k.val)).sum := by
  induction ks generalizing p with
  | nil => simp [ordinaryWordComparisons, ordinaryWordShifts]
  | cons k ks ih =>
    have hi := ih (gapSort p k.val)
    have hk := gapComparisonCost_scan_bounds p k.val k.property
    simp only [ordinaryWordComparisons, ordinaryWordShifts, List.map_cons, List.sum_cons,
      max_le_iff] at *
    omega

/-- The small-first-gap branch of the unrestricted three-pass problem needs
no coprimality and uses only the actual uniform first-pass counter. -/
theorem uniform_smallFirst_threePass_lower (n h g : ℕ) (hh : 0 < h) (hg : 0 < g)
    (hn : 4 ≤ n) (hsmall : (h : ℝ) ≤ Real.sqrt n) :
    (n : ℝ) * Real.sqrt n / 8 ≤
      uniformAverage (fun p : RankPlacement n => (threePassInsertionCost p h g hh hg : ℝ)) := by
  have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq0 := Real.sqrt_nonneg (n : ℝ)
  have hsq2 : (2 : ℝ) ≤ Real.sqrt n := by nlinarith
  have hhpos : (0 : ℝ) < h := by exact_mod_cast hh
  have hlow : (n : ℝ) * Real.sqrt n / 8 ≤ (n : ℝ) ^ 2 / (4 * h) - n / 4 := by
    rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]
    have bound1 := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ (n : ℝ) * Real.sqrt n by positivity)
    have bound2 := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      (mul_nonneg hsq0 (sub_nonneg.mpr hsq2)), congrArg (fun t : ℝ => (n : ℝ) * t) hs]
  apply (hlow.trans (uniform_firstPassCost_lower n h hh)).trans
  apply uniformAverage_mono
  intro p
  exact_mod_cast (show gapInsertionCost p h hh ≤ threePassInsertionCost p h g hh hg by
    unfold threePassInsertionCost; omega)

end Shellsort
end
