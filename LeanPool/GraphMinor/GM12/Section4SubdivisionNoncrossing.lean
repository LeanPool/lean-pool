/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4AdjacentSubdivisionPieces

/-!
# Noncrossing incident edges after subdivision

XII (4.5), page 252, retains the property that every vertex has
two incident edges that do not cross. At an old vertex, select
pieces of its two original noncrossing edges that contain it.
At a new cut vertex, use the two adjacent pieces of the original
edge. Their intersections are exactly the selected vertex.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Every vertex of the subdivided arc family has two different
edge arcs meeting exactly there. This preserves condition (vii)
in the subdivision step of XII (4.5), page 252. -/
theorem subdivision_has_two_noncrossing_arcs {m n : ℕ}
    (V : Fin m → ℂ) (E : Fin n → Set ℂ) (k : Fin n → ℕ)
    (w : ∀ e, Fin (k e + 1) → ℂ) (P : ∀ e, Fin (k e) → Set ℂ)
    (hw : ∀ e, Function.Injective (w e))
    (hline : ∀ e i, IsLineWithEnds (P e i) (w e i.castSucc) (w e i.succ))
    (hcover : ∀ e, (⋃ i, P e i) = E e)
    (hinter : ∀ e i j, i ≠ j → P e i ∩ P e j ⊆ range (w e))
    (hvertex : ∀ e i, P e i ∩ range (w e) = {w e i.castSucc, w e i.succ})
    (htwo : ∀ v, ∃ e f, e ≠ f ∧ E e ∩ E f = {V v})
    (z : SubdivisionVertex m n k) :
    ∃ q r : Σ e : Fin n, Fin (k e), q ≠ r ∧
      subdivisionEdgeArc k P q ∩ subdivisionEdgeArc k P r = {subdivisionPosition V k w z} := by
  have hsub : ∀ e i, P e i ⊆ E e := by
    intro e i x hx
    rw [← hcover e]
    exact mem_iUnion.mpr ⟨i, hx⟩
  cases z with
  | inl v =>
    obtain ⟨e, f, hef, hcross⟩ := htwo v
    have hpoint : V v ∈ E e ∩ E f := hcross ▸ (show V v ∈ ({V v} : Set ℂ) from rfl)
    have hxe : V v ∈ ⋃ i, P e i := (hcover e).symm ▸ hpoint.1
    have hxf : V v ∈ ⋃ j, P f j := (hcover f).symm ▸ hpoint.2
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxe
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hxf
    refine ⟨⟨e, i⟩, ⟨f, j⟩, (fun h => hef (congrArg Sigma.fst h)), ?_⟩
    apply Subset.antisymm
    · intro x hx
      exact hcross ▸ And.intro (hsub e i hx.1) (hsub f j hx.2)
    · rintro x rfl
      exact ⟨hxi, hxj⟩
  | inr q =>
    obtain ⟨e, j⟩ := q
    obtain ⟨i, l, hil, hint⟩ := exists_adjacent_pieces_at_internal_cut
      (w e) (P e) (hw e) (hline e) (hinter e) (hvertex e) j
    refine ⟨⟨e, i⟩, ⟨e, l⟩, ?_, hint⟩
    intro h
    have hval := congrArg (fun q : Σ e : Fin n, Fin (k e) => q.2.val) h
    exact hil (Fin.ext hval)

end GraphMinor.GM12
