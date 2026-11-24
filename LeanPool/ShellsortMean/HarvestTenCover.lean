/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.HarvestTenSchedule
public import LeanPool.ShellsortMean.HarvestBlockComparisonSum

/-! Positive execution words and their cost covers for the concrete ten-gap
schedule. The emitted words use the very same h as the selection certificate. -/
@[expose] public noncomputable section
namespace Shellsort.HarvestTenCover
open Actual214 HarvestMenuBlock HarvestBlockIteration HarvestTenSchedule HarvestStageArithmetic

def positiveTail (l : ℕ) : PositiveWord :=
  (List.range l).reverse.map (fun t => ⟨gap t, gap_pos t⟩)

@[simp] theorem positiveTail_length (l : ℕ) : (positiveTail l).length = l := by
  simp [positiveTail]

theorem positiveTail_values (l : ℕ) : (positiveTail l).map Subtype.val =
    (List.range l).reverse.map gap := by simp [positiveTail, List.map_map]

private def positiveWord (w : List ℕ) (pos : ∀ k ∈ w, 0 < k) : PositiveWord :=
  w.attach.map (fun k => ⟨k.val, pos k.val k.property⟩)

private theorem positiveWord_values (w : List ℕ) (pos : ∀ k ∈ w, 0 < k) :
    (positiveWord w pos).map Subtype.val = w := by simp [positiveWord, List.map_map]

theorem chunk_lower {k h : ℕ} (ok : eligible k) (choice : h ∈ choices (chunk k).j) :
    ∀ g ∈ stageWord (chunk k) h, gap (k - 10) ≤ g := by
  have big : 10 ≤ k := ok.1
  have stronger : k - 10 + 1 ≤ k - 3 := by omega
  have htwo := (step (k - 10)).1.trans_le (gap_strict.monotone stronger)
  have hlo : gap (k - 3) - gap (k - 3) / 100 ≤ h := (Finset.mem_Icc.mp (Finset.mem_filter.mp
    choice).1).1
  intro g hg
  simp only [stageWord, chunk, List.mem_cons, List.mem_map, List.mem_reverse, List.mem_range] at hg
  rcases hg with rfl | rfl | rfl | ⟨t, _, rfl⟩
  · exact gap_strict.monotone (by omega)
  · exact gap_strict.monotone (by omega)
  · omega
  · exact gap_strict.monotone (Nat.le_add_right _ _)

theorem menu_covers {k prev : ℕ} {hs : List ℕ} (growth : Centers prev (stages k))
    (menus : List.Forall₂ (fun s h => h ∈ choices s.j) (stages k) hs) :
    ∃ ws, Covers (2 ^ 28) prev (stages k) hs ws := by
  induction k using Nat.strong_induction_on generalizing prev hs with
  | ind k ih =>
    by_cases ok : eligible k
    · rw [stages_eq, ite_eq_left ok] at menus growth ⊢
      cases menus with
      | cons good more =>
        rename_i h hs
        obtain ⟨_, prevBound, rest⟩ := growth
        obtain ⟨ws, fit⟩ := ih (k - 10) (by have h10 := ok.1; omega) rest more
        let w := stageWord (chunk k) h
        have low : ∀ g ∈ w, gap (k - 10) ≤ g := chunk_lower ok good
        have pos : ∀ g ∈ w, 0 < g := fun g hg => (gap_pos _).trans_le (low g hg)
        have ck := (bottom_to_center (k - 10) ok.2).2
        have big := ok.1
        rw [show k - 10 + 7 = k - 3 by omega] at ck
        change prev ≤ 2 ^ 16 * gap (k - 3) at prevBound
        have ratio : prev ≤ 2 ^ 28 * gap (k - 10) := by omega
        refine ⟨positiveWord w pos :: ws, positiveWord_values w pos, ⟨gap (k - 10), gap_pos _,
          ratio, ?_⟩, fit⟩
        intro x hx
        apply low
        rw [←positiveWord_values w pos]
        exact List.mem_map_of_mem hx
    · rw [stages_eq, ite_eq_right ok] at menus ⊢
      cases menus
      exact ⟨[], trivial⟩

theorem covers_word {R prev : ℕ} {ss : List Stage} {hs : List ℕ} {ws : List PositiveWord}
    (fit : Covers R prev ss hs ws) :
    ws.flatten.map Subtype.val = realizedWord ss hs := by
  induction ss generalizing prev hs ws with
  | nil =>
    cases hs <;> cases ws <;> first | rfl | exact False.elim fit
  | cons s ss ih =>
    cases hs with
    | nil => cases ws <;> exact False.elim fit
    | cons h hs =>
      cases ws with
      | nil => exact False.elim fit
      | cons w ws =>
        simp only [List.flatten_cons, List.map_append, fit.1, realizedWord, ih fit.2.2]

theorem covers_state {n R prev : ℕ} {ss : List Stage} {hs : List ℕ} {ws : List PositiveWord}
    (fit : Covers R prev ss hs ws) (p : RankPlacement n) :
    sortWord p (ws.flatten.map Subtype.val) = sortWord p (realizedWord ss hs) := by
  rw [covers_word fit]

theorem covers_length {k prev R : ℕ} {hs : List ℕ} {ws : List PositiveWord}
    (fit : Covers R prev (stages k) hs ws) :
    ws.flatten.length + (positiveTail (tailCount k)).length = k := by
  rw [positiveTail_length]
  induction k using Nat.strong_induction_on generalizing prev hs ws with
  | ind k ih =>
    by_cases ok : eligible k
    · rw [stages_eq, ite_eq_left ok] at fit
      rw [tailCount_eq, ite_eq_left ok]
      cases hs with
      | nil => cases ws <;> exact False.elim fit
      | cons h hs =>
        cases ws with
        | nil => exact False.elim fit
        | cons w ws =>
          have h10 := ok.1
          have rem := ih (k - 10) (by omega) fit.2.2
          have len := congrArg List.length fit.1
          simp [stageWord, chunk] at len
          simp only [List.flatten_cons, List.length_append]
          omega
    · rw [stages_eq, ite_eq_right ok] at fit
      rw [tailCount_eq, ite_eq_right ok]
      cases hs <;> cases ws <;> first | exact False.elim fit | simp

end Shellsort.HarvestTenCover
