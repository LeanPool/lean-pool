/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4SubdivisionArcIncidence

/-!
# Subdivision preserves the source meeting points

In XII (4.5), pages 252--253, subdividing between crossings
keeps the same crossing points. Two pieces of one old edge can
meet only at cut vertices. Pieces of different old edges meet
away from new vertices only at old meetings. Conversely each old
meeting remains on pieces of its two old edges, and no cut was
chosen there.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Subdivision between the meetings creates no new meeting point
and removes none of the old ones. This identifies the crossing
points before and after the subdivision in XII (4.5), pages 252--253. -/
theorem edgeMeetingPoints_subdivision_eq {m n : ℕ}
    (V : Fin m → ℂ) (κ : Fin n × Bool → Fin m) (E : Fin n → Set ℂ)
    (k : Fin n → ℕ) (hk : ∀ e, 0 < k e)
    (w : ∀ e, Fin (k e + 1) → ℂ) (P : ∀ e, Fin (k e) → Set ℂ)
    (hw0 : ∀ e, w e 0 = V (κ (e, false)))
    (hwlast : ∀ e, w e (Fin.last (k e)) = V (κ (e, true)))
    (hline : ∀ e i, IsLineWithEnds (P e i) (w e i.castSucc) (w e i.succ))
    (hcover : ∀ e, (⋃ i, P e i) = E e)
    (havoid : ∀ e i, w e i ∉ E e ∩ edgeMeetingPoints V E)
    (hinter : ∀ e i j, i ≠ j → P e i ∩ P e j ⊆ range (w e)) :
    edgeMeetingPoints (subdivisionPosition V k w) (subdivisionEdgeArc k P) = edgeMeetingPoints V E
      := by
  have hmem := family_cut_mem_original_edge E k hk w P hline hcover
  have hdisj := disjoint_subdivisionPositions_meetings V E k w hmem havoid
  have hcutrange : ∀ e, range (w e) ⊆ range (subdivisionPosition V k w) := by
    rintro e x ⟨r, rfl⟩
    exact ⟨subdivisionVertexAt κ k e r, subdivisionPosition_vertexAt V κ k hk w hw0 hwlast e r⟩
  have hsub : ∀ e i, P e i ⊆ E e := by
    intro e i x hx
    rw [← hcover e]
    exact mem_iUnion.mpr ⟨i, hx⟩
  ext x
  constructor
  · rintro ⟨⟨e, i⟩, ⟨f, j⟩, hne, hx, hxV⟩
    by_cases hef : e = f
    · subst f
      have hij : i ≠ j := fun h => hne (by subst j; rfl)
      exact False.elim (hxV (hcutrange e (hinter e i j hij hx)))
    · refine ⟨e, f, hef, ⟨hsub e i hx.1, hsub f j hx.2⟩, ?_⟩
      rintro ⟨v, hv⟩
      exact hxV ⟨Sum.inl v, hv⟩
  · intro hx
    obtain ⟨e, f, hef, hxEf, hxV⟩ := hx
    have hxe : x ∈ ⋃ i, P e i := (hcover e).symm ▸ hxEf.1
    have hxf : x ∈ ⋃ j, P f j := (hcover f).symm ▸ hxEf.2
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxe
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hxf
    refine ⟨⟨e, i⟩, ⟨f, j⟩, (fun h => hef (congrArg Sigma.fst h)), ⟨hxi, hxj⟩, ?_⟩
    intro hxnewV
    exact disjoint_left.mp hdisj hxnewV ⟨e, f, hef, hxEf, hxV⟩

/-- Each new edge has exactly one of the unchanged meeting points.
This is the one-crossing-per-edge conclusion in XII (4.5), page 252. -/
theorem subdivisionEdgeArc_one_meeting {m n : ℕ}
    (V : Fin m → ℂ) (κ : Fin n × Bool → Fin m) (E : Fin n → Set ℂ)
    (k : Fin n → ℕ) (hk : ∀ e, 0 < k e)
    (w : ∀ e, Fin (k e + 1) → ℂ) (P : ∀ e, Fin (k e) → Set ℂ)
    (hw0 : ∀ e, w e 0 = V (κ (e, false)))
    (hwlast : ∀ e, w e (Fin.last (k e)) = V (κ (e, true)))
    (hline : ∀ e i, IsLineWithEnds (P e i) (w e i.castSucc) (w e i.succ))
    (hcover : ∀ e, (⋃ i, P e i) = E e)
    (havoid : ∀ e i, w e i ∉ E e ∩ edgeMeetingPoints V E)
    (hinter : ∀ e i j, i ≠ j → P e i ∩ P e j ⊆ range (w e))
    (hmeet : ∀ e i, ∃ x ∈ E e ∩ edgeMeetingPoints V E, P e i ∩ (E e ∩ edgeMeetingPoints V E) = {x})
    (q : Σ e : Fin n, Fin (k e)) :
    ∃ x ∈ edgeMeetingPoints (subdivisionPosition V k w) (subdivisionEdgeArc k P),
      subdivisionEdgeArc k P q ∩
        edgeMeetingPoints (subdivisionPosition V k w) (subdivisionEdgeArc k P) = {x} := by
  rw [edgeMeetingPoints_subdivision_eq V κ E k hk w P hw0 hwlast hline hcover havoid hinter]
  obtain ⟨x, hx, hPx⟩ := hmeet q.1 q.2
  refine ⟨x, hx.2, ?_⟩
  have hsub : P q.1 q.2 ⊆ E q.1 := by
    intro y hy
    rw [← hcover q.1]
    exact mem_iUnion.mpr ⟨q.2, hy⟩
  rw [← inter_assoc, inter_eq_self_of_subset_left hsub] at hPx
  exact hPx

end GraphMinor.GM12
