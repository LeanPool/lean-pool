/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4SubdivisionArcIncidence
import Mathlib.Data.Set.Finite.Range

/-!
# Intersections after subdivision

The source subdivision in XII (4.5), page 252, preserves finite
pairwise intersections and excludes triple meetings away from
vertices. Pieces of different old edges inherit the old finite
intersections. Pieces of one old edge meet only at cuts. For a
triple meeting, either two pieces belong to the same old edge,
or the three old edges already meet at an old vertex.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Distinct new edge arcs meet finitely, preserving condition
(ii) of XII (4.5)'s source construction, page 252. -/
theorem finite_subdivisionEdgeArc_inter {n : ℕ}
    (E : Fin n → Set ℂ) (k : Fin n → ℕ)
    (w : ∀ e, Fin (k e + 1) → ℂ) (P : ∀ e, Fin (k e) → Set ℂ)
    (hcover : ∀ e, (⋃ i, P e i) = E e)
    (hinter : ∀ e i j, i ≠ j → P e i ∩ P e j ⊆ range (w e))
    (hfinite : ∀ e f, e ≠ f → (E e ∩ E f).Finite)
    {q r : Σ e : Fin n, Fin (k e)} (hqr : q ≠ r) :
    (subdivisionEdgeArc k P q ∩ subdivisionEdgeArc k P r).Finite := by
  obtain ⟨e, i⟩ := q
  obtain ⟨f, j⟩ := r
  by_cases hef : e = f
  · subst f
    have hij : i ≠ j := fun h => hqr (by subst j; rfl)
    exact (finite_range (w e)).subset (hinter e i j hij)
  · apply (hfinite e f hef).subset
    intro x hx
    constructor
    · rw [← hcover e]
      exact mem_iUnion.mpr ⟨i, hx.1⟩
    · rw [← hcover f]
      exact mem_iUnion.mpr ⟨j, hx.2⟩

/-- Triple meetings of new edge arcs occur only at subdivision
vertices. This preserves condition (iv) of XII (4.5)'s source
construction, page 252. -/
theorem subdivisionEdgeArcs_triple_subset_vertices {m n : ℕ}
    (V : Fin m → ℂ) (κ : Fin n × Bool → Fin m) (E : Fin n → Set ℂ)
    (k : Fin n → ℕ) (hk : ∀ e, 0 < k e)
    (w : ∀ e, Fin (k e + 1) → ℂ) (P : ∀ e, Fin (k e) → Set ℂ)
    (hw0 : ∀ e, w e 0 = V (κ (e, false)))
    (hwlast : ∀ e, w e (Fin.last (k e)) = V (κ (e, true)))
    (hcover : ∀ e, (⋃ i, P e i) = E e)
    (hinter : ∀ e i j, i ≠ j → P e i ∩ P e j ⊆ range (w e))
    (htriple : ∀ e f g, e ≠ f → f ≠ g → e ≠ g → E e ∩ E f ∩ E g ⊆ range V) :
    ∀ q r s : Σ e : Fin n, Fin (k e), q ≠ r → r ≠ s → q ≠ s →
      subdivisionEdgeArc k P q ∩ subdivisionEdgeArc k P r ∩ subdivisionEdgeArc k P s ⊆
        range (subdivisionPosition V k w) := by
  have hcutrange : ∀ e, range (w e) ⊆ range (subdivisionPosition V k w) := by
    rintro e x ⟨i, rfl⟩
    exact ⟨subdivisionVertexAt κ k e i, subdivisionPosition_vertexAt V κ k hk w hw0 hwlast e i⟩
  have hsub : ∀ e i, P e i ⊆ E e := by
    intro e i x hx
    rw [← hcover e]
    exact mem_iUnion.mpr ⟨i, hx⟩
  rintro ⟨e, i⟩ ⟨f, j⟩ ⟨g, l⟩ hqr hrs hqs x hx
  by_cases hef : e = f
  · subst f
    have hij : i ≠ j := fun h => hqr (by subst j; rfl)
    exact hcutrange e (hinter e i j hij hx.1)
  by_cases heg : e = g
  · subst g
    have hil : i ≠ l := fun h => hqs (by subst l; rfl)
    exact hcutrange e (hinter e i l hil ⟨hx.1.1, hx.2⟩)
  by_cases hfg : f = g
  · subst g
    have hjl : j ≠ l := fun h => hrs (by subst l; rfl)
    exact hcutrange f (hinter f j l hjl ⟨hx.1.2, hx.2⟩)
  · obtain ⟨v, hv⟩ := htriple e f g hef hfg heg
      ⟨⟨hsub e i hx.1.1, hsub f j hx.1.2⟩, hsub g l hx.2⟩
    exact ⟨Sum.inl v, hv⟩

end GraphMinor.GM12
