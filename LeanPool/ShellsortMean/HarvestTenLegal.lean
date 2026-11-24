/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.HarvestTenSchedule

/-! All realisations of the ten-center schedule form legal ordinary gap
words. Compare adjacent complete windows before choosing any menu entries. -/
@[expose] public section

namespace Shellsort.HarvestTenLegal
open Actual214 HarvestBlockIteration HarvestTenSchedule HarvestMenuBlock

private def allowed (i x : ℕ) := gap i - gap i / 100 ≤ x ∧ x ≤ gap i + gap i / 100
private inductive Shape : ℕ → List ℕ → Prop
  | nil : Shape 0 []
  | cons {k x xs} : allowed k x → Shape k xs → Shape (k + 1) (x::xs)

private theorem center_allowed (i : ℕ) : allowed i (gap i) := by unfold allowed; omega

private theorem centers_increase : StrictMono gap := by
  apply strictMono_nat_of_lt_succ
  intro i
  change gap i < nextGap (gap i)
  have z := scaled_next_bounds (gap i)
  omega

private theorem window_separation {i j x y : ℕ} (ij : i < j) (hx : allowed i x) (hy : allowed j y) :
    x < y := by
  have h := centers_increase.monotone (Nat.succ_le_of_lt ij)
  change nextGap (gap i) ≤ gap j at h
  have z := scaled_next_bounds (gap i)
  unfold allowed at *
  omega

private theorem shape_mem {k w} (t : Shape k w) {x : ℕ} (hx : x ∈ w) :
    ∃ i < k, allowed i x := by
  induction t with
  | nil => simp at hx
  | @cons k v vs hv _ ih =>
    rcases List.mem_cons.mp hx with eq|hrest
    · exact ⟨k, Nat.lt_succ_self _, eq ▸ hv⟩
    · obtain ⟨i, hi, a⟩ := ih hrest
      exact ⟨i, by omega, a⟩

private theorem shape_pairwise {k w} (t : Shape k w) : w.Pairwise (· > ·) := by
  induction t with
  | nil => exact .nil
  | cons h rest ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih⟩
    intro y hy
    obtain ⟨i, hi, a⟩ := shape_mem rest hy
    exact window_separation hi a h

private theorem shape_last {k w} (t : Shape k w) (hk : 0 < k) : w.getLast? = some 1 := by
  induction t with
  | nil => omega
  | @cons k x xs hx rest ih =>
    cases xs with
    | nil =>
      cases rest
      have xeq : x = 1 := by norm_num [allowed, gap] at hx; omega
      simp [xeq]
    | cons y ys =>
      rw [List.getLast?_cons_cons]
      apply ih
      cases rest
      omega

private theorem tail_shape (k : ℕ) : Shape k ((List.range k).reverse.map gap) := by
  induction k with
  | zero => exact .nil
  | succ k ih =>
    simpa [List.range_succ] using Shape.cons (center_allowed k) ih

private theorem chunk_shape {k h : ℕ} {w : List ℕ} (hk : 10 ≤ k) (hh : h ∈ choices (chunk k).j)
    (tail : Shape (k - 10) w) : Shape k (stageWord (chunk k) h ++ w) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hk
  have near := Finset.mem_Icc.mp (Finset.mem_filter.mp hh).1
  have choice : allowed (l + 7) h := by
    simpa [allowed, chunk, show 10 + l - 3 = l + 7 by omega] using near
  have t : Shape l w := by simpa using tail
  have build := Shape.cons (center_allowed (l + 9))
    (Shape.cons (center_allowed (l + 8)) (Shape.cons choice
      (Shape.cons (center_allowed (l + 6)) (Shape.cons (center_allowed (l + 5))
      (Shape.cons (center_allowed (l + 4)) (Shape.cons (center_allowed (l + 3))
      (Shape.cons (center_allowed (l + 2)) (Shape.cons (center_allowed (l + 1))
      (Shape.cons (center_allowed l) t)))))))))
  have index : l + 10 - 3 = l + 7 := by omega
  have suffix : (List.range 7).reverse = [6, 5, 4, 3, 2, 1, 0] := by decide
  simpa only [stageWord, chunk, index, Nat.add_sub_cancel, List.map_cons, List.map_nil,
    suffix, List.cons_append, List.nil_append, Nat.add_zero, show 10 + l = l + 10 by omega] using
      build

private theorem full_shape (k : ℕ) (hs : List ℕ)
    (picks : List.Forall₂ (fun s h => h ∈ choices s.j) (stages k) hs) :
    Shape k (realizedWord (stages k) hs ++ tailWord k) := by
  induction k using Nat.strong_induction_on generalizing hs with
  | _ k ih =>
    by_cases eligibleNow : eligible k
    · have ss : stages k = chunk k :: stages (k - 10) := by rw [stages_eq]; simp [eligibleNow]
      have tail : tailWord k = tailWord (k - 10) := by
        unfold tailWord
        rw [tailCount_eq k]; simp [eligibleNow]
      rw [ss] at picks ⊢
      cases picks with
      | cons pick rest =>
        rw [realizedWord, List.append_assoc, tail]
        exact chunk_shape eligibleNow.1 pick (ih (k - 10) (by have := eligibleNow.1; omega) _ rest)
    · have ss : stages k = [] := by rw [stages_eq]; simp [eligibleNow]
      rw [ss] at picks ⊢
      cases picks
      have tail : tailCount k = k := by rw [tailCount_eq]; simp [eligibleNow]
      simpa [realizedWord, tailWord, tail] using tail_shape k

/-- For every allowed choice word, the input size determines the full sequence,
which is decreasing, positive, strictly below n, and ends at gap one. -/
theorem full_word_legal {n : ℕ} (hn : 2 ≤ n) (hs : List ℕ)
    (picks : List.Forall₂ (fun s h => h ∈ choices s.j) (stages (count n)) hs) :
    let w := realizedWord (stages (count n)) hs ++ tailWord (count n)
    w.Pairwise (· > ·) ∧ (∀ h ∈ w, 0 < h ∧ h < n) ∧ w.getLast? = some 1 := by
  intro w
  have shape : Shape (count n) w := full_shape _ _ picks
  refine ⟨shape_pairwise shape, ?_, shape_last shape (count_positive _)⟩
  intro h hh
  obtain ⟨i, hi, allowed_i⟩ := shape_mem shape hh
  have small := centers_increase.monotone (show i ≤ top n from Nat.le_of_lt_succ hi)
  have kept := top_kept hn
  have pos := gap_pos i
  unfold allowed at allowed_i
  omega

private theorem sorted_if_last_one {n : ℕ} (w : List ℕ) (p : RankPlacement n)
    (h : w.getLast? = some 1) : sortWord p w = Equiv.refl _ := by
  induction w generalizing p with
  | nil => simp at h
  | cons a as ih =>
    cases as with
    | nil =>
      have eq : a = 1 := by simpa using h
      subst a
      change gapSort p 1 = _
      exact gapSort_one p
    | cons b bs =>
      have last : (b::bs).getLast? = some 1 := h
      change sortWord (gapSort p a) (b::bs) = Equiv.refl _
      exact ih (gapSort p a) last

theorem full_word_sorts {n : ℕ} (hn : 2 ≤ n) (hs : List ℕ)
    (picks : List.Forall₂ (fun s h => h ∈ choices s.j) (stages (count n)) hs)
    (p : RankPlacement n) :
    sortWord p (realizedWord (stages (count n)) hs ++ tailWord (count n)) = Equiv.refl _ :=
  sorted_if_last_one _ p (full_word_legal hn hs picks).2.2


end Shellsort.HarvestTenLegal
