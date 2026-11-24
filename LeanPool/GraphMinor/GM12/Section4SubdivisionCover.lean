/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4SubdivisionCuts
import Mathlib.Data.Nat.Find

/-!
# The subdivision intervals cover the edge

In XII (4.5), page 252, subdivision keeps the whole original
edge arc. For a parameter between zero and one, choose the first
cut at or above it. The preceding cut is below it, unless the
first cut is zero, in which case the first interval contains it.
Thus the closed intervals between consecutive cuts cover `[0,1]`.
-/

public section

namespace GraphMinor.GM12

/-- Every point of the original parameter interval belongs to a
subdivision interval. This proves that the subdivision of XII
(4.5), page 252, retains the entire edge arc. -/
theorem exists_subdivisionInterval_of_mem_Icc {k : ℕ} (hk : 0 < k)
    (t : Fin k → ℝ) (ht : StrictMono t) (ht01 : ∀ i, 0 < t i ∧ t i < 1)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ i : Fin k, x ∈ Set.Icc (subdivisionCut t i.castSucc) (subdivisionCut t i.succ) := by
  classical
  let P : ℕ → Prop := fun r => ∃ hr : r < k + 1, x ≤ subdivisionCut t ⟨r, hr⟩
  have hex : ∃ r, P r := by
    refine ⟨k, Nat.lt_succ_self k, ?_⟩
    change x ≤ subdivisionCut t (Fin.last k)
    rw [subdivisionCut_last hk]
    exact hx.2
  let r := Nat.find hex
  obtain ⟨hrbound, hupper⟩ := Nat.find_spec hex
  change x ≤ subdivisionCut t ⟨r, hrbound⟩ at hupper
  by_cases hrzero : r = 0
  · have hrfin : (⟨r, hrbound⟩ : Fin (k + 1)) = 0 := Fin.ext hrzero
    rw [hrfin, subdivisionCut_zero] at hupper
    refine ⟨⟨0, hk⟩, ?_, ?_⟩
    · change subdivisionCut t 0 ≤ x
      rw [subdivisionCut_zero]
      exact hx.1
    · exact hupper.trans (subdivisionCut_mem_Icc hk t ht ht01 _).1
  · let i : Fin k := ⟨r - 1, by omega⟩
    have hright : i.succ = (⟨r, hrbound⟩ : Fin (k + 1)) := by
      apply Fin.ext
      change r - 1 + 1 = r
      omega
    refine ⟨i, ?_, ?_⟩
    · by_contra hnot
      have hlt : x < subdivisionCut t i.castSucc := lt_of_not_ge hnot
      have hcand : P (r - 1) := ⟨by omega, hlt.le⟩
      have hmin := Nat.find_min' hex hcand
      change r ≤ r - 1 at hmin
      omega
    · rw [hright]
      exact hupper

/-- The union of the closed subdivision intervals is exactly the
parameter interval of the original edge in XII (4.5), page 252. -/
theorem iUnion_subdivisionIntervals {k : ℕ} (hk : 0 < k)
    (t : Fin k → ℝ) (ht : StrictMono t) (ht01 : ∀ i, 0 < t i ∧ t i < 1) :
    (⋃ i : Fin k, Set.Icc (subdivisionCut t i.castSucc) (subdivisionCut t i.succ)) =
      Set.Icc (0 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨(subdivisionCut_mem_Icc hk t ht ht01 i.castSucc).1.trans hi.1,
      hi.2.trans (subdivisionCut_mem_Icc hk t ht ht01 i.succ).2⟩
  · intro x hx
    obtain ⟨i, hi⟩ := exists_subdivisionInterval_of_mem_Icc hk t ht ht01 hx
    exact Set.mem_iUnion.mpr ⟨i, hi⟩

end GraphMinor.GM12
