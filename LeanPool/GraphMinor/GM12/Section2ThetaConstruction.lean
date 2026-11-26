/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2MinimalChord
public import LeanPool.GraphMinor.GM12.Section2RegionComponents
import LeanPool.GraphMinor.Surface.SurfaceGraph
import LeanPool.GraphMinor.Surface.DiscMerge
import LeanPool.GraphMinor.GM11.RadialBasics

/-!
# The theta graph in Case 2 of XII (2.1)

On page 244, the proof cuts the original circle along a minimal chord
in a region visited more than once. The chord and the two original
arcs form a theta graph. The two new circles are normal, and each
original arc contains a drawing vertex because the chord ends lie in
different components of the region intersection.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The complete theta-graph construction of XII (2.1), Case 2, page
244. The two original arcs each contain vertices, while the chord lies
in a region and hence misses the drawing. -/
theorem exists_theta_of_disconnected_region_intersection {S : Type*} [TopologicalSpace S]
    [T2Space S] (hS : IsClosedSurface S) {Γ : Drawing S} {r F : Set S}
    (hr : r ∈ Γ.R) (hF : IsOArc F) (hnormal : Γ.IsNormal F)
    (hdisconn : ¬ IsPreconnected (F ∩ r)) :
    ∃ (L A B : Set S) (a b : S),
      IsLineWithEnds L a b ∧ IsLineWithEnds A a b ∧ IsLineWithEnds B a b ∧
      A ∪ B = F ∧ L ∩ A = {a, b} ∧ L ∩ B = {a, b} ∧ A ∩ B = {a, b} ∧
      L ⊆ r ∧ IsOArc (L ∪ A) ∧ IsOArc (L ∪ B) ∧
      Γ.IsNormal (L ∪ A) ∧ Γ.IsNormal (L ∪ B) ∧
      (A ∩ Γ.V).Nonempty ∧ (B ∩ Γ.V).Nonempty := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hrpath : IsPathConnected r := isPathConnected_of_isOpen hS
    (region_isOpen hr) (region_isPreconnected hr) (region_nonempty hr)
  obtain ⟨L, a, b, hL, hLr, ha, hb, hgap, hdiff⟩ :=
    exists_minimal_chord_between_components hrpath hF.isCompact.isClosed hdisconn
  have hab : a ≠ b := by
    intro heq
    exact hdiff (congrArg (connectedComponentIn (F ∩ r)) heq)
  obtain ⟨f, g, hfg, hf0, hf1, hfgF⟩ := hF.exists_arcs ha.1 hb.1 hab
  let A := range f
  let B := range g
  have hA : IsLineWithEnds A a b := by
    have hh := isLine_range hfg.arc_left.1 hfg.arc_left.2
    rw [hf0, hf1] at hh
    exact hh
  have hB : IsLineWithEnds B a b := by
    have hh := isLine_range hfg.arc_right.1 hfg.arc_right.2
    rw [hfg.zero, hfg.one, hf0, hf1] at hh
    exact hh
  have hAF : A ⊆ F := fun x hx => hfgF ▸ Or.inl hx
  have hBF : B ⊆ F := fun x hx => hfgF ▸ Or.inr hx
  have hAB : A ∩ B = {a, b} := by
    have hh := hfg.inter
    rwa [hf0, hf1] at hh
  have hend : ∀ {C : Set S}, IsLineWithEnds C a b → ({a, b} : Set S) ⊆ C := by
    intro C hC
    obtain ⟨p, hp0, hp1⟩ := hC
    rintro x (rfl | rfl)
    · exact hp0 ▸ (p 0).property
    · exact hp1 ▸ (p 1).property
  have hcap : ∀ C : Set S, C ⊆ F → ({a, b} : Set S) ⊆ C → L ∩ C = {a, b} := by
    intro C hCF hendC
    apply Subset.antisymm
    · intro x hx
      by_contra hxends
      exact Set.disjoint_left.mp hgap ⟨hx.1, hxends⟩ (hCF hx.2)
    · intro x hx
      exact ⟨hend hL hx, hendC hx⟩
  have hLA : L ∩ A = {a, b} := hcap A hAF (hend hA)
  have hLB : L ∩ B = {a, b} := hcap B hBF (hend hB)
  have hnorm : ∀ C : Set S, C ⊆ F → Γ.IsNormal (L ∪ C) := by
    intro C hCF x hx
    rcases hx.1 with hxL | hxC
    · exact (region_subset hr (hLr hxL) hx.2).elim
    · exact hnormal ⟨hCF hxC, hx.2⟩
  obtain ⟨hAV, hBV⟩ := both_arcs_meet_vertices hr hnormal hA hB hAF hBF ha.2 hdiff
  exact ⟨L, A, B, a, b, hL, hA, hB, hfgF, hLA, hLB, hAB, hLr,
    isOArc_union hL hA hLA.subset, isOArc_union hL hB hLB.subset,
    hnorm A hAF, hnorm B hBF, hAV, hBV⟩

end GraphMinor.GM12
