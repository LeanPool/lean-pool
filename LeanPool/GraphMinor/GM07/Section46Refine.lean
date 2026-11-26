/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Matched
public import LeanPool.GraphMinor.GM07.Section46CentralLift
import LeanPool.GraphMinor.GM07.Section46JPlus
import LeanPool.GraphMinor.GM07.Section46WalkOfConnected
import LeanPool.GraphMinor.GM07.ForestFlat
import LeanPool.GraphMinor.GM07.CuffForest
import LeanPool.GraphMinor.GM07.CuffStep
import LeanPool.GraphMinor.GM11.Section4
import LeanPool.GraphMinor.GM11.Walks

/-!
# Adding vertices to a forest

The forest `H₆` of VII (4.6), page 227, is `H₅` with all of `V(G)` added
as vertices. Some of the new vertices lie on edges and others off `U(H₅)`.
The result is a forest with the same paths between boundary vertices, by
`exists_walk_of_preconnected`, and curves in a forest with the same ends
are homotopic.
-/

public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-- A walk contains a simple walk with the same ends. -/
theorem exists_simple_walk_of_walk {Γ : Drawing S} {a b : S} (W : GraphWalk Γ.toGraph a b) :
    ∃ W' : GraphWalk Γ.toGraph a b, W'.IsSimple := by
  induction W with
  | nil h => exact ⟨.nil h, by simp [GraphWalk.IsSimple, GraphWalk.support]⟩
  | @cons u v w e h r ih =>
    obtain ⟨r', hr'⟩ := ih
    by_cases hu : u ∈ r'.support
    · obtain ⟨R₁, R₂, rfl⟩ := r'.exists_append_of_mem hu
      exact ⟨R₂, (isSimple_of_append hr').2⟩
    · exact ⟨.cons h r', List.nodup_cons.mpr ⟨hu, hr'⟩⟩

variable [T1Space S]

omit [T1Space S] in
theorem isPreconnected_closure_of_mem_E {Γ : Drawing S} {e : Set S} (he : e ∈ Γ.E) :
    IsPreconnected (closure e) :=
  he.2.2.1.isConnected.isPreconnected.closure

/-- A forest with more vertices has the same paths between boundary vertices, in VII (4.6),
page 227. -/
theorem exists_refined_forest {S : Type} [TopologicalSpace S] [T1Space S] [ConnectedSpace S]
    (hS : IsSurface S) {H : Drawing S}
    (hH : IsSurfaceForest H) {W : Set S} (hW : W.Finite) (hWbd : W ∩ bd S ⊆ H.V) :
    ∃ H₆ : Drawing S, H₆.U = H.U ∪ W ∧ H₆.V = H.V ∪ W ∧ IsSurfaceForest H₆ ∧
      ForestsHomotopic H H₆ ∧ ∀ e' ∈ H₆.E, ∃ e ∈ H.E, e' ⊆ e := by
  classical
  have : T2Space S := hS.2.1
  have hf₀ : (W ∩ H.U).Finite := hW.subset inter_subset_left
  obtain ⟨D, hDU, hDV⟩ := exists_drawing_with_more_vertices H (H.finite_V.union hf₀)
    subset_union_left (union_subset H.V_subset_U inter_subset_right)
  have hDp : D.IsProper := by
    rintro x ⟨hb, hx⟩
    rw [hDV]
    exact .inl (hH.1 ⟨hb, hDU ▸ hx⟩)
  have hDf : IsSurfaceForest D := ⟨hDp, isForest_of_noOArc fun F hF hs =>
    noOArc_of_forest hH.2 hF (hDU ▸ hs)⟩
  have hdis : Disjoint (W \ H.U) D.U := by
    rw [hDU]
    exact disjoint_sdiff_left
  let H₆ := addIsolated D (W \ H.U) (hW.subset sdiff_subset) hdis
  have hU : H₆.U = H.U ∪ W := by
    change D.U ∪ (W \ H.U) = _
    rw [hDU, union_sdiff_self]
  have hV : H₆.V = H.V ∪ W := by
    change D.V ∪ (W \ H.U) = _
    rw [hDV]
    ext x
    simp only [mem_union, mem_inter_iff, mem_sdiff]
    tauto
  have hF : IsSurfaceForest H₆ := hDf.addIsolated hS _ hdis
  have hedge : ∀ e' ∈ H₆.E, e' ⊆ H.U \ H.V := by
    intro e' he' x hx
    have hx' := he'.2.1 hx
    rw [hU, hV] at hx'
    refine ⟨?_, fun h => hx'.2 (.inl h)⟩
    rcases hx'.1 with h | h
    · exact h
    · exact (hx'.2 (.inr h)).elim
  have hedge' : ∀ e' ∈ H₆.E, closure e' ⊆ H.U := fun e' he' =>
    closure_minimal ((hedge e' he').trans sdiff_subset) H.isClosed_U
  have hsub : H.U ⊆ H₆.U := hU ▸ subset_union_left
  have hup : ∀ {x y : S}, GraphWalk H.toGraph x y → Nonempty (GraphWalk H₆.toGraph x y) := by
    intro x y W
    induction W with
    | nil h => exact ⟨.nil (show _ ∈ H₆.V from hV ▸ .inl h)⟩
    | @cons u v w e h r ih =>
      obtain ⟨R⟩ := ih
      have hc : closure e ∩ H.V = {u, v} := h.2.2.2
      have hu : u ∈ closure e := (hc.symm.subset (by simp)).1
      have hv : v ∈ closure e := (hc.symm.subset (by simp)).1
      obtain ⟨Q⟩ := exists_walk_of_preconnected H₆ (isPreconnected_closure_of_mem_E h.1)
        ((H.closure_subset_U h.1).trans hsub) (hV ▸ .inl h.2.1) hu (hV ▸ .inl h.2.2.1) hv
      exact ⟨Q.append R⟩
  have hdown : ∀ {x y : S}, GraphWalk H₆.toGraph x y → x ∈ H.U →
      ∃ A : Set S, IsPreconnected A ∧ A ⊆ H.U ∧ x ∈ A ∧ y ∈ A := by
    intro x y W
    induction W with
    | nil h =>
      intro hx
      exact ⟨{_}, isPreconnected_singleton, singleton_subset_iff.mpr hx, rfl, rfl⟩
    | @cons u v w e h r ih =>
      intro _
      have hc : closure e ∩ H₆.V = {u, v} := h.2.2.2
      have hu : u ∈ closure e := (hc.symm.subset (by simp)).1
      have hv : v ∈ closure e := (hc.symm.subset (by simp)).1
      obtain ⟨A, hA, hAU, hvA, hwA⟩ := ih (hedge' e h.1 hv)
      exact ⟨closure e ∪ A, (isPreconnected_closure_of_mem_E h.1).union v hv hvA hA,
        union_subset (hedge' e h.1) hAU, .inl hu, .inr hwA⟩
  refine ⟨H₆, hU, hV, hF, ⟨hH.1, hF.1, hH.2, hF.2, ?_, ?_⟩, ?_⟩
  · rw [hV]
    ext x
    constructor
    · rintro ⟨hx, hb⟩
      exact ⟨.inl hx, hb⟩
    · rintro ⟨hx | hx, hb⟩
      · exact ⟨hx, hb⟩
      · exact ⟨hWbd ⟨hx, hb⟩, hb⟩
  · intro s hs t ht _
    have hs₆ : s ∈ H₆.V := hV ▸ .inl hs.1
    have ht₆ : t ∈ H₆.V := hV ▸ .inl ht.1
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rintro ⟨P, -⟩
      obtain ⟨Q⟩ := hup P
      exact exists_simple_walk_of_walk Q
    · rintro ⟨P, -⟩
      obtain ⟨A, hA, hAU, hsA, htA⟩ := hdown P (H.V_subset_U hs.1)
      obtain ⟨Q⟩ := exists_walk_of_preconnected H hA hAU hs.1 hsA ht.1 htA
      exact exists_simple_walk_of_walk Q
    · intro P₁ P₂ φ₁ φ₂ _ _ h₁ h₂
      have e₁ := h₁.endpoints
      have e₂ := h₂.endpoints
      have hflat := isFlat_forest hF.2
      exact IsFlat.curvesHomotopic hflat
        ((h₁.range_subset_U).trans hsub) h₂.range_subset_U (e₁.1.trans e₂.1.symm)
          (e₁.2.trans e₂.2.symm)
  · intro e' he'
    have hx := he'.1
    obtain ⟨x, hx⟩ := hx
    have hxU : x ∈ H.U \ H.V := hedge e' he' hx
    let C := pathComponentIn (H.U \ H.V) x
    have hC : C ∈ H.E := pathComponentIn_mem_arcComponentsIn hxU
    exact ⟨C, hC, he'.2.2.1.subset_pathComponentIn hx (hedge e' he')⟩

end GraphMinor.GM07
