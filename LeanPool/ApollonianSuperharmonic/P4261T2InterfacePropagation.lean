/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4261T2LiteralInterface
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain
public import Mathlib.Data.List.Chain

-- [TABLET NODE: P4261T2InterfacePropagation]

/-!
# P4261T2InterfacePropagation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4261T2InterfacePropagation
    (D C : BandCircle) (T T' : ProtoTile) (h h' : PartialOdometer)
    (hh : TileOdometer C.1.1 T h) (hh' : TileOdometer C.1.1 T' h')
    (pkg : P4261T2LiteralInterface D C T T' h h')
    (hcompat : ∀ (U V : ProtoTile) (g k : PartialOdometer),
      (U, g) ∈ pkg.tiles.zip pkg.functions →
      (V, k) ∈ pkg.reverseTiles.zip pkg.reverseFunctions →
      (FootprintEdges U ∩ FootprintEdges V).Nonempty → OdometerCompatibility g k) :
    OdometerCompatibility h h' := by
-- BODY
  classical
  have vertex_of_edge : ∀ (U : ProtoTile) (edge : Finset GaussianInt),
      edge ∈ FootprintEdges U → ∀ z ∈ edge, z ∈ FootprintVertices U := by
    intro U edge he z hz
    rcases he with ⟨a, ha, he | he | he | he⟩
    all_goals
      rw [he] at hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rw [FootprintVertices, ite_eq_left (show U.cells.Nonempty from ⟨a, ha⟩)]
      refine ⟨a, ha, ?_⟩
      rcases hz with hz | hz <;> simp [hz]
  let diff := fun z : GaussianInt => h'.value z - h.value z
  let rel := fun x y : GaussianInt => diff x = diff y
  have hchain : pkg.path.IsChain rel := by
    apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
    intro x y pre post he
    obtain ⟨U, V, g, k, hU, hV, hedge, ha, hb⟩ := pkg.restrictions x y pre post he
    have memg : ∀ z, z = x ∨ z = y → z ∈ g.domain := by
      intro z hz
      change z ∈ (g.domain : Set GaussianInt)
      rw [show (g.domain : Set GaussianInt) = FootprintVertices U from ha.2.2.1]
      exact vertex_of_edge U {x, y} hedge.1 z (by simpa using hz)
    have memk : ∀ z, z = x ∨ z = y → z ∈ k.domain := by
      intro z hz
      change z ∈ (k.domain : Set GaussianInt)
      rw [show (k.domain : Set GaussianInt) = FootprintVertices V from hb.2.2.1]
      exact vertex_of_edge V {x, y} hedge.2 z (by simpa using hz)
    have hxg := memg x (Or.inl rfl)
    have hxk := memk x (Or.inl rfl)
    have hyg := memg y (Or.inr rfl)
    have hyk := memk y (Or.inr rfl)
    rcases hcompat U V g k hU hV ⟨{x, y}, hedge⟩ with hd | ⟨c, hc⟩
    · exact (Set.disjoint_left.mp hd hxg hxk).elim
    · change h'.value x - h.value x = h'.value y - h.value y
      rw [← ha.2.2.2.2 x hxg, ← hb.2.2.2.2 x hxk,
        ← ha.2.2.2.2 y hyg, ← hb.2.2.2.2 y hyk]
      exact (hc x hxg hxk).trans (hc y hyg hyk).symm
  let : Trans rel rel rel := ⟨by
    intro a b c hab hbc
    exact hab.trans hbc⟩
  let : Std.Refl rel := ⟨fun _ => rfl⟩
  have hpair := List.isChain_iff_pairwise.mp hchain
  have hd := PositiveCurvatureTileOdometerDomain C.1.1 T h C.2 hh
  have hd' := PositiveCurvatureTileOdometerDomain C.1.1 T' h' C.2 hh'
  cases heq : pkg.path with
  | nil =>
      have hl := pkg.length
      simp [heq] at hl
  | cons x xs =>
      right
      refine ⟨diff x, ?_⟩
      intro z hz hz'
      have hzf : z ∈ FootprintVertices T ∩ FootprintVertices T' := by
        exact ⟨by rwa [← hd], by rwa [← hd']⟩
      rw [pkg.vertices] at hzf
      have hzl : z ∈ pkg.path := by simpa using hzf
      rw [heq] at hpair hzl
      exact (hpair.rel_head hzl).symm

end ApollonianSuperharmonic

end
