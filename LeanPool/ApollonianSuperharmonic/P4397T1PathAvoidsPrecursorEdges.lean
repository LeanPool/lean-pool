/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4397T1ReflectedEdgeNotBoundary

-- [TABLET NODE: P4397T1PathAvoidsPrecursorEdges]

/-!
# P4397T1PathAvoidsPrecursorEdges

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4397T1PathAvoidsPrecursorEdges :
    ∀ (O : ProtoTile), ∀ (c : Real × Real), (CentrallyReflectedAt c O O) → (∀ (a : GaussianInt),
        ∀ (b : GaussianInt), (a ≠ b) → ((GaussianRealPoint b =
      (2 * c.1 - (GaussianRealPoint a).1,
        2 * c.2 - (GaussianRealPoint a).2)) → (∀ (g : List GaussianInt), (g.Nodup) → ((g.head? =
            some a) → ((g.getLast? = some b) → ((∀ u, ∀ v, (u, v) ∈ g.zip g.tail →
            FourNeighborAdjacent u v) → ((∀ u ∈ g, u ∈ FootprintVertices O → u = a ∨ u = b) → ((∀
            u, ∀ v, (u, v) ∈ g.zip g.tail →
      u ∈ FootprintVertices O → v ∈ FootprintVertices O →
      ¬ OpenLatticeEdge u v ⊆ interior (TileRealization O)) → (∀ u, ∀ v, (u, v) ∈ g.zip g.tail →
      ({u, v} : Finset GaussianInt) ∉ FootprintEdges O))))))))) := by
  intro O c hsym a b hab hreflect g hnd hhead hlast hsteps hroots hnochord
-- BODY
  have first_dropLast (l : List GaussianInt) (u v : GaussianInt)
      (he : (u, v) ∈ l.zip l.tail) : u ∈ l.dropLast := by
    induction l with
    | nil => simp at he
    | cons x l ih =>
      cases l with
      | nil => simp at he
      | cons y ys =>
        simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at he
        simp only [List.dropLast_cons_cons, List.mem_cons]
        rcases he with he | he
        · cases he
          exact Or.inl rfl
        · exact Or.inr (ih he)
  have ha_tail : a ∉ g.tail := by
    obtain ⟨l, hl⟩ := List.head?_eq_some_iff.mp hhead
    subst g
    exact (List.nodup_cons.mp hnd).1
  have hb_dropLast : b ∉ g.dropLast := by
    have hl : g.dropLast ++ [b] = g :=
      List.dropLast_append_getLast? b (by simp [hlast])
    have hn : (g.dropLast ++ [b]).Nodup := hl.symm ▸ hnd
    intro hb
    exact (List.nodup_append.mp hn).2.2 b hb b (by simp) rfl
  intro u v he hfoot
  obtain ⟨z, w, hs⟩ := P4397T1UnitEdgeCells.1 u v (hsteps u v he)
  have hgeom := P4397T1UnitEdgeCells.2 u v z w hs O
  have hsome := hgeom.1.mp hfoot
  have hraw := hgeom.2.2.1 hsome
  have hua : u = a := by
    rcases hroots u (List.of_mem_zip he).1 hraw.1 with hu | hu
    · exact hu
    · exact (hb_dropLast (hu ▸ first_dropLast g u v he)).elim
  have hvb : v = b := by
    rcases hroots v (List.mem_of_mem_tail (List.of_mem_zip he).2) hraw.2.1 with hv | hv
    · exact (ha_tail (hv ▸ (List.of_mem_zip he).2)).elim
    · exact hv
  have hnotboth : ¬ (z ∈ O.cells ∧ w ∈ O.cells) := by
    intro hb
    exact hnochord u v he hraw.1 hraw.2.1 (hgeom.2.2.2.1 hb)
  have hboundary : ({u, v} : Finset GaussianInt) ∈ BoundaryFootprintEdges O := by
    apply hgeom.2.1.mpr
    rcases hsome with hz | hw
    · exact Or.inl ⟨hz, fun hw => hnotboth ⟨hz, hw⟩⟩
    · exact Or.inr ⟨fun hz => hnotboth ⟨hz, hw⟩, hw⟩
  subst u
  subst v
  exact P4397T1ReflectedEdgeNotBoundary O c hsym a b (hsteps a b he)
    hreflect hboundary

end ApollonianSuperharmonic

end
