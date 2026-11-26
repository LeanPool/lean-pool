/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4FamilyCuts
public import LeanPool.GraphMinor.GM12.Section4SubdivisionIncidence
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# Incidence of the global subdivision arc family

In XII (4.5), page 252, the arc portions must represent the
edges of the subdivision graph. The global vertices on an old
edge are exactly its own cuts, and each portion contains exactly
its two endpoint cuts. Injectivity of the global position map
therefore identifies membership in an arc with graph incidence.
-/

public section

namespace GraphMinor.GM12

open Set Surface Graph

/-- A new edge arc is its indexed portion of an original edge,
in the subdivision of XII (4.5), page 252. -/
@[expose] def subdivisionEdgeArc {n : ℕ} (k : Fin n → ℕ)
    (P : ∀ e, Fin (k e) → Set ℂ) (e : Σ f : Fin n, Fin (k f)) : Set ℂ := P e.1 e.2

/-- The vertex-position map and arc portions give the exact
incidence of the subdivision graph in XII (4.5), page 252. -/
theorem subdivisionEdgeArc_vertex_inc_iff {m n : ℕ}
    (V : Fin m → ℂ) (κ : Fin n × Bool → Fin m) (E : Fin n → Set ℂ)
    (k : Fin n → ℕ) (hk : ∀ e, 0 < k e)
    (w : ∀ e, Fin (k e + 1) → ℂ) (P : ∀ e, Fin (k e) → Set ℂ)
    (hV : Function.Injective V) (hw : ∀ e, Function.Injective (w e))
    (hw0 : ∀ e, w e 0 = V (κ (e, false)))
    (hwlast : ∀ e, w e (Fin.last (k e)) = V (κ (e, true)))
    (hline : ∀ e i, IsLineWithEnds (P e i) (w e i.castSucc) (w e i.succ))
    (hcover : ∀ e, (⋃ i, P e i) = E e)
    (havoid : ∀ e i, w e i ∉ E e ∩ edgeMeetingPoints V E)
    (hPvertices : ∀ e i, P e i ∩ range (w e) = {w e i.castSucc, w e i.succ})
    (hvertex : ∀ e v, V v ∈ E e ↔ v = κ (e, false) ∨ v = κ (e, true))
    (e : Σ f : Fin n, Fin (k f)) (z : SubdivisionVertex m n k) :
    subdivisionPosition V k w z ∈ subdivisionEdgeArc k P e ↔ (subdivisionGraph κ k).Inc e z := by
  have hmem := family_cut_mem_original_edge E k hk w P hline hcover
  have hinterior := internal_family_cut_not_mem_vertices V κ E k w hw hw0 hwlast hmem hvertex
  have hinj := subdivisionPosition_injective V E k w hV hw hmem havoid hinterior
  have hglobal := original_edge_inter_subdivisionPositions V κ E k hk w hw0 hwlast
    hmem havoid hvertex hinterior e.1
  have hsub : P e.1 e.2 ⊆ E e.1 := by
    intro x hx
    rw [← hcover e.1]
    exact mem_iUnion.mpr ⟨e.2, hx⟩
  have hcut : P e.1 e.2 ∩ range (subdivisionPosition V k w) =
      {w e.1 e.2.castSucc, w e.1 e.2.succ} := by
    calc
      P e.1 e.2 ∩ range (subdivisionPosition V k w) =
          P e.1 e.2 ∩ (E e.1 ∩ range (subdivisionPosition V k w)) := by
        ext x
        exact ⟨fun h => ⟨h.1, hsub h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
      _ = P e.1 e.2 ∩ range (w e.1) := by rw [hglobal]
      _ = {w e.1 e.2.castSucc, w e.1 e.2.succ} := hPvertices e.1 e.2
  have hleft := subdivisionPosition_vertexAt V κ k hk w hw0 hwlast e.1 e.2.castSucc
  have hright := subdivisionPosition_vertexAt V κ k hk w hw0 hwlast e.1 e.2.succ
  rw [subdivisionGraph_inc_iff]
  constructor
  · intro hz
    have hends : subdivisionPosition V k w z = w e.1 e.2.castSucc ∨
        subdivisionPosition V k w z = w e.1 e.2.succ :=
      show subdivisionPosition V k w z ∈ ({w e.1 e.2.castSucc, w e.1 e.2.succ} : Set ℂ) from
        hcut ▸ And.intro hz (mem_range_self z)
    exact hends.elim (fun h => Or.inl (hinj (h.trans hleft.symm)))
      (fun h => Or.inr (hinj (h.trans hright.symm)))
  · rintro (rfl | rfl)
    · rw [hleft]
      exact (hline e.1 e.2).left_mem
    · rw [hright]
      exact (hline e.1 e.2).right_mem

/-- Each new edge arc is a line with the positions of its graph
endpoints as ends. -/
theorem subdivisionEdgeArc_isLine {m n : ℕ}
    (V : Fin m → ℂ) (κ : Fin n × Bool → Fin m) (k : Fin n → ℕ) (hk : ∀ e, 0 < k e)
    (w : ∀ e, Fin (k e + 1) → ℂ) (P : ∀ e, Fin (k e) → Set ℂ)
    (hw0 : ∀ e, w e 0 = V (κ (e, false)))
    (hwlast : ∀ e, w e (Fin.last (k e)) = V (κ (e, true)))
    (hline : ∀ e i, IsLineWithEnds (P e i) (w e i.castSucc) (w e i.succ))
    (e : Σ f : Fin n, Fin (k f)) :
    IsLineWithEnds (subdivisionEdgeArc k P e)
      (subdivisionPosition V k w (subdivisionVertexAt κ k e.1 e.2.castSucc))
      (subdivisionPosition V k w (subdivisionVertexAt κ k e.1 e.2.succ)) := by
  rw [subdivisionPosition_vertexAt V κ k hk w hw0 hwlast,
    subdivisionPosition_vertexAt V κ k hk w hw0 hwlast]
  exact hline e.1 e.2

end GraphMinor.GM12
