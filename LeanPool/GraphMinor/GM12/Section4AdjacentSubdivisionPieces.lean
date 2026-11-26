/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4SubdivisionArcIncidence
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# The two pieces at an internal cut

At a new vertex of the subdivision in XII (4.5), page 252,
the two adjacent pieces are portions of the same simple arc.
Any intersection is a cut, and each piece contains only its two
endpoint cuts. Injectivity of the cut map leaves exactly their
shared endpoint as the intersection.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Two different adjacent pieces meet exactly at each internal
cut. This gives the noncrossing pair at each new vertex required
by XII (4.5)(vii), page 252. -/
theorem exists_adjacent_pieces_at_internal_cut {k : ℕ}
    (w : Fin (k + 1) → ℂ) (P : Fin k → Set ℂ) (hw : Function.Injective w)
    (hline : ∀ i, IsLineWithEnds (P i) (w i.castSucc) (w i.succ))
    (hinter : ∀ i j, i ≠ j → P i ∩ P j ⊆ range w)
    (hvertex : ∀ i, P i ∩ range w = {w i.castSucc, w i.succ}) (j : Fin (k - 1)) :
    ∃ i l : Fin k, i ≠ l ∧ P i ∩ P l = {w ⟨j.val + 1, by have := j.isLt; omega⟩} := by
  let i : Fin k := ⟨j.val, by have := j.isLt; omega⟩
  let l : Fin k := ⟨j.val + 1, by have := j.isLt; omega⟩
  let r : Fin (k + 1) := ⟨j.val + 1, by have := j.isLt; omega⟩
  have hil : i ≠ l := by
    intro h
    have hval := congrArg Fin.val h
    change j.val = j.val + 1 at hval
    omega
  refine ⟨i, l, hil, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨q, rfl⟩ := hinter i l hil hx
    have hend : ∀ s, w q ∈ P s → q.val = s.val ∨ q.val = s.val + 1 := by
      intro s hs
      have hends : w q ∈ ({w s.castSucc, w s.succ} : Set ℂ) :=
        hvertex s ▸ And.intro hs (mem_range_self q)
      exact hends.elim (fun h => Or.inl (congrArg Fin.val (hw h)))
        (fun h => Or.inr (congrArg Fin.val (hw h)))
    have hqi := hend i hx.1
    have hql := hend l hx.2
    change q.val = j.val ∨ q.val = j.val + 1 at hqi
    change q.val = j.val + 1 ∨ q.val = j.val + 1 + 1 at hql
    have hqr : q = r := by
      apply Fin.ext
      change q.val = j.val + 1
      omega
    exact congrArg w hqr
  · rintro rfl
    have heq1 : i.succ = r := Fin.ext rfl
    have heq2 : l.castSucc = r := Fin.ext rfl
    have hi := (hline i).right_mem
    have hl := (hline l).left_mem
    rw [heq1] at hi
    rw [heq2] at hl
    exact ⟨hi, hl⟩

end GraphMinor.GM12
