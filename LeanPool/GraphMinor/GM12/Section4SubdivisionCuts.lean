/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith

/-!
# Subdivision cuts between consecutive crossings

XII (4.5), page 252, subdivides an edge with `k` crossings `k - 1`
times so that every resulting edge has one crossing. In an arc
parametrization, list the crossing parameters in increasing order.
Use their consecutive midpoints as cuts, together with zero and
one at the ends. Each crossing lies strictly between its two cuts.
-/

public section

namespace GraphMinor.GM12

/-- The endpoint parameters and the midpoints between consecutive
crossing parameters in the subdivision step of XII (4.5), page 252. -/
@[expose] noncomputable def subdivisionCut {k : ℕ} (t : Fin k → ℝ) (i : Fin (k + 1)) : ℝ :=
  if hzero : i.val = 0 then 0 else
    if hlast : i.val = k then 1 else
      (t ⟨i.val - 1, by have := i.isLt; omega⟩ +
        t ⟨i.val, by have := i.isLt; omega⟩) / 2

/-- The first subdivision cut is the first end of the arc. -/
theorem subdivisionCut_zero {k : ℕ} (t : Fin k → ℝ) : subdivisionCut t 0 = 0 := by
  simp only [subdivisionCut, Fin.val_zero, ↓reduceDIte]

/-- With at least one crossing, the last subdivision cut is the
last end of the arc. -/
theorem subdivisionCut_last {k : ℕ} (hk : 0 < k) (t : Fin k → ℝ) :
    subdivisionCut t (Fin.last k) = 1 := by
  simp only [subdivisionCut, Fin.val_last, Nat.ne_of_gt hk, ↓reduceDIte]

/-- Each crossing lies strictly between its neighboring cuts.
This proves that cutting at the selected midpoints retains the
crossing in its own edge in XII (4.5), page 252. -/
theorem crossing_between_subdivisionCuts {k : ℕ} (t : Fin k → ℝ)
    (ht : StrictMono t) (ht01 : ∀ i, 0 < t i ∧ t i < 1) (i : Fin k) :
    subdivisionCut t i.castSucc < t i ∧ t i < subdivisionCut t i.succ := by
  constructor
  · unfold subdivisionCut
    simp only [Fin.val_castSucc]
    split_ifs with hzero hlast
    · exact (ht01 i).1
    · exact False.elim ((Nat.ne_of_lt i.isLt) hlast)
    · have hpre : t ⟨i.val - 1, by omega⟩ < t i := by
        apply ht
        change i.val - 1 < i.val
        omega
      linarith
  · have hzero : i.val + 1 ≠ 0 := by omega
    have hkzero : k ≠ 0 := by omega
    by_cases hlast : i.val + 1 = k
    · simp only [subdivisionCut, Fin.val_succ, hlast, hkzero, ↓reduceDIte]
      exact (ht01 i).2
    · simp only [subdivisionCut, Fin.val_succ, hzero, hlast, ↓reduceDIte]
      have hback : (⟨i.val + 1 - 1, by omega⟩ : Fin k) = i := by
        apply Fin.ext
        change i.val + 1 - 1 = i.val
        omega
      rw [hback]
      have hnext : t i < t ⟨i.val + 1, by omega⟩ := ht (by change i.val < i.val + 1; omega)
      linarith

/-- The subdivision cuts occur in strict order along the arc. -/
theorem subdivisionCut_strictMono {k : ℕ} (t : Fin k → ℝ)
    (ht : StrictMono t) (ht01 : ∀ i, 0 < t i ∧ t i < 1) :
    StrictMono (subdivisionCut t) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  exact (crossing_between_subdivisionCuts t ht ht01 i).1.trans
    (crossing_between_subdivisionCuts t ht ht01 i).2

/-- All subdivision cuts stay in the parameter interval of the
original edge arc. -/
theorem subdivisionCut_mem_Icc {k : ℕ} (hk : 0 < k) (t : Fin k → ℝ)
    (ht : StrictMono t) (ht01 : ∀ i, 0 < t i ∧ t i < 1) (i : Fin (k + 1)) :
    subdivisionCut t i ∈ Set.Icc (0 : ℝ) 1 := by
  have hmono := (subdivisionCut_strictMono t ht ht01).monotone
  have hlo := hmono (show (0 : Fin (k + 1)) ≤ i from Nat.zero_le i.val)
  have hhi := hmono (show i ≤ Fin.last k from Nat.le_of_lt_succ i.isLt)
  rw [subdivisionCut_zero] at hlo
  rw [subdivisionCut_last hk] at hhi
  exact ⟨hlo, hhi⟩

/-- Each closed subdivision interval contains exactly its assigned
crossing parameter. This is the one-crossing-per-edge assertion
in the subdivision step of XII (4.5), page 252. -/
theorem crossing_mem_subdivisionInterval_iff {k : ℕ} (t : Fin k → ℝ)
    (ht : StrictMono t) (ht01 : ∀ i, 0 < t i ∧ t i < 1) (i j : Fin k) :
    t i ∈ Set.Icc (subdivisionCut t j.castSucc) (subdivisionCut t j.succ) ↔ i = j := by
  have hcuts := (subdivisionCut_strictMono t ht ht01).monotone
  constructor
  · intro hmem
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · have hsep := hcuts (show i.succ ≤ j.castSucc by change i.val + 1 ≤ j.val; omega)
      have hlt := (crossing_between_subdivisionCuts t ht ht01 i).2.trans_le hsep
      exact (not_le_of_gt hlt) hmem.1
    · have hsep := hcuts (show j.succ ≤ i.castSucc by change j.val + 1 ≤ i.val; omega)
      have hlt := hsep.trans_lt (crossing_between_subdivisionCuts t ht ht01 i).1
      exact (not_le_of_gt hlt) hmem.2
  · rintro rfl
    exact ⟨(crossing_between_subdivisionCuts t ht ht01 i).1.le,
      (crossing_between_subdivisionCuts t ht ht01 i).2.le⟩

/-- No new subdivision vertex is a crossing. The cuts lie strictly
between consecutive crossing parameters in XII (4.5), page 252. -/
theorem subdivisionCut_ne_crossing {k : ℕ} (t : Fin k → ℝ)
    (ht : StrictMono t) (ht01 : ∀ i, 0 < t i ∧ t i < 1)
    (i : Fin (k + 1)) (j : Fin k) : subdivisionCut t i ≠ t j := by
  intro heq
  have hmono := (subdivisionCut_strictMono t ht ht01).monotone
  have hlo : j.castSucc < i := by
    by_contra hnot
    have hle := hmono (le_of_not_gt hnot)
    have hlt := hle.trans_lt (crossing_between_subdivisionCuts t ht ht01 j).1
    exact hlt.ne heq
  have hhi : i < j.succ := by
    by_contra hnot
    have hle := hmono (le_of_not_gt hnot)
    have hlt := (crossing_between_subdivisionCuts t ht ht01 j).2.trans_le hle
    exact hlt.ne heq.symm
  change j.val < i.val at hlo
  change i.val < j.val + 1 at hhi
  omega

end GraphMinor.GM12
