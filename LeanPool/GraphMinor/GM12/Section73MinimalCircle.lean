/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73ThetaNull
public import LeanPool.GraphMinor.GM12.Section2ThetaConstruction
import LeanPool.GraphMinor.GM12.Section2CurveCounts

/-!
# A shortest non-null normal circle visits each region once

To justify the representativity step in XII (7.3), page 261, choose
a non-null normal circle meeting as few drawing vertices as possible.
If its intersection with a region is disconnected, a chord produces
two normal circles with fewer vertices, as in XII (2.1). Minimality
makes both new circles null-homotopic. The theta-circle lemma then
makes the original circle null-homotopic, a contradiction.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A non-null normal circle can be chosen with no more vertices
and with connected intersection with every region. This is the
minimal-circle reduction in the representativity step of XII (7.3). -/
theorem exists_minimal_nonNull_normal_circle
    {S : Type*} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    {Γ : Drawing S} {F : Set S} (hF : IsOArc F) (hn : Γ.IsNormal F)
    (hnon : ¬ IsNullHomotopicOArc F) :
    ∃ G : Set S, IsOArc G ∧ Γ.IsNormal G ∧ ¬ IsNullHomotopicOArc G ∧
      (G ∩ Γ.V).ncard ≤ (F ∩ Γ.V).ncard ∧
      ∀ r ∈ Γ.R, IsPreconnected (G ∩ r) := by
  classical
  have hex : ∃ n : ℕ, ∃ G : Set S, IsOArc G ∧ Γ.IsNormal G ∧
      ¬ IsNullHomotopicOArc G ∧ (G ∩ Γ.V).ncard = n :=
    ⟨(F ∩ Γ.V).ncard, F, hF, hn, hnon, rfl⟩
  obtain ⟨G, hG, hGn, hGnon, hcount⟩ := Nat.find_spec hex
  have hmin : ∀ H : Set S, IsOArc H → Γ.IsNormal H → ¬ IsNullHomotopicOArc H →
      (G ∩ Γ.V).ncard ≤ (H ∩ Γ.V).ncard := by
    intro H hH hHn hHnon
    rw [hcount]
    exact Nat.find_min' hex ⟨H, hH, hHn, hHnon, rfl⟩
  refine ⟨G, hG, hGn, hGnon, hmin F hF hn hnon, ?_⟩
  intro r hr
  by_contra hdisconn
  obtain ⟨L, A, B, a, b, hL, hA, hB, hABG, hLA, hLB, hAB, hLr,
      hLAo, hLBo, hLAn, hLBn, hAV, hBV⟩ :=
    exists_theta_of_disconnected_region_intersection hS hr hG hGn hdisconn
  have hLV : Disjoint L Γ.V := disjoint_left.mpr fun x hxL hxV =>
    region_subset hr (hLr hxL) (Γ.V_subset_U hxV)
  have hABV : Disjoint (A ∩ B) Γ.V := hLV.mono_left fun x hx =>
    (hLA.superset (hAB.subset hx)).1
  obtain ⟨hsmallA, hsmallB⟩ := chord_circle_vertex_counts_lt Γ.finite_V hLV hABV hAV hBV
  have hcountA : ((L ∪ A) ∩ Γ.V).ncard < (G ∩ Γ.V).ncard := by
    simpa only [union_comm L A, hABG] using hsmallA
  have hcountB : ((L ∪ B) ∩ Γ.V).ncard < (G ∩ Γ.V).ncard := by
    simpa only [union_comm L B, hABG] using hsmallB
  have hnullA : IsNullHomotopicOArc (L ∪ A) := by
    by_contra hnonnull
    exact (Nat.not_le_of_lt hcountA) (hmin (L ∪ A) hLAo hLAn hnonnull)
  have hnullB : IsNullHomotopicOArc (L ∪ B) := by
    by_contra hnonnull
    exact (Nat.not_le_of_lt hcountB) (hmin (L ∪ B) hLBo hLBn hnonnull)
  have hSurface : IsSurface S := ⟨hS.1, hS.2.1, fun x => (hS.2.2 x).isManifoldPoint⟩
  have hnull := nullHomotopic_third_theta_circle hSurface hA hB hL hAB hLAo hLBo hnullA hnullB
  exact hGnon (hABG ▸ hnull)

end GraphMinor.GM12
