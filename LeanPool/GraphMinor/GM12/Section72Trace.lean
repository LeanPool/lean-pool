/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2PartitionDeformation
public import LeanPool.GraphMinor.GM12.Section2CyclicEmbedding
public import LeanPool.GraphMinor.GM12.Section2BacktrackInside
import LeanPool.GraphMinor.GM12.Section2CurveCounts
import LeanPool.GraphMinor.GM12.Section2CirclePeriod
import LeanPool.GraphMinor.GM12.Section2PeriodicHits

/-!
# The two-spoke trace of a circle meeting one vertex

In XII (7.2), page 260, the boundary circle visits just one region,
starting and ending at the same vertex. Apply the region deformation
from (2.1) to this single visit. Its two-edge trace is either an
embedded circle or a backtracking line. The homotopy stays in the
region together with the boundary vertex.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM07

/-- The single region visit in XII (7.2), page 260, gives a two-edge
radial trace, with its simplicity or backtracking alternative. -/
theorem exists_two_spoke_deformation
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {F r : Set S} {v : S} (hF : IsOArc F) (hvF : v ∈ F)
    (hv : v ∈ Γ.V) (hr : r ∈ Γ.R) (hFr : F \ {v} ⊆ r) :
    ∃ φ ψ : C(Circle, S), ∃ W : GraphWalk K.toGraph v v,
      IsEmbedding φ ∧ range φ = F ∧ W.length = 2 ∧
      range ψ = (walkDrawing K W).U ∧
      ClosedCurvesHomotopicIn (r ∪ {v}) φ ψ ∧
      (IsEmbedding ψ ∨ ∃ L, IsLine L ∧ range ψ = L ∧ L ⊆ r ∪ {v}) := by
  obtain ⟨H⟩ := hF
  let φ : C(Circle, S) := ⟨fun z => (H z).val,
    continuous_subtype_val.comp H.continuous⟩
  have hφ : IsEmbedding φ := IsEmbedding.subtypeVal.comp H.isEmbedding
  have hφF : range φ = F := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact (H z).property
    · intro hx
      exact ⟨H.symm ⟨x, hx⟩, congrArg Subtype.val (H.apply_symm_apply ⟨x, hx⟩)⟩
  obtain ⟨z, hz⟩ := hφF.symm ▸ hvF
  obtain ⟨a, _, ha⟩ := (circle_parameter_bijOn 0).surjOn (mem_univ z)
  have hav : periodicCurve φ a = v := by
    change φ (Circle.exp (2 * Real.pi * a)) = v
    exact (congrArg φ ha).trans hz
  have hφZ : range φ ⊆ r ∪ {v} := by
    intro x hx
    by_cases hxv : x = v
    · exact Or.inr hxv
    · exact Or.inl (hFr ⟨hφF ▸ hx, hxv⟩)
  let t : Fin 2 → ℝ := fun i => a + i.val
  have ht : StrictMono t := by
    intro i j hij
    change a + (i.val : ℝ) < a + (j.val : ℝ)
    exact add_lt_add_right (Nat.cast_lt.mpr hij) a
  have hperiod : t (Fin.last 1) = t 0 + 1 := by simp [t]
  have htΓ : ∀ i, periodicCurve φ (t i) ∈ Γ.V := by
    intro i
    fin_cases i
    · simpa [t, hav] using hv
    · simpa [t, periodicCurve_periodic φ a, hav] using hv
  have hvisit : ∀ (i : Fin 1) s, s ∈ Ioo (t i.castSucc) (t i.succ) →
      periodicCurve φ s ∈ r := by
    intro i s hs
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have hs' : s ∈ Ioo a (a + 1) := by simpa [t] using hs
    apply hFr
    refine ⟨hφF ▸ mem_range_self _ , ?_⟩
    intro hsv
    have heq : Circle.exp (2 * Real.pi * s) = Circle.exp (2 * Real.pi * a) :=
      hφ.injective (hsv.trans hav.symm)
    have hsa := circle_parameter_injOn a ⟨hs'.1.le, hs'.2⟩
      ⟨le_rfl, lt_add_one a⟩ heq
    exact (ne_of_gt hs'.1) hsa
  have ht0 : periodicCurve φ (t 0) = v := by simpa [t] using hav
  have hex := exists_partition_trace_deformation hS hK hE hφZ (by decide : 0 < 1)
      t ht hperiod htΓ (fun _ => r) (fun _ => hr) (fun _ => subset_union_left) hvisit
  rw [ht0] at hex
  obtain ⟨δ, hmatch, W, _, hlen, hψU, hh, _, _, _, halt⟩ := hex
  refine ⟨φ, concatLoop (by decide : 0 < 1) δ hmatch, W,
    hφ, hφF, by simpa using hlen, hψU, hh, ?_⟩
  rcases halt 0 with hinj | ⟨_, L, hL, hδL, hLZ⟩
  · left
    apply ((concatLoop (by decide : 0 < 1) δ hmatch).continuous.isClosedEmbedding _).isEmbedding
    apply concatLoop_injective_of_halfopen_pieces
    intro i j s u hs hu heq
    have hij : i = j := Subsingleton.elim _ _
    have hi : i = 0 := Subsingleton.elim _ _
    subst j
    subst i
    exact ⟨rfl, hinj ⟨unitInterval.nonneg _, hs⟩ ⟨unitInterval.nonneg _, hu⟩ heq⟩
  · right
    refine ⟨L, hL, ?_, ?_⟩
    · rw [range_concatLoop]
      have heq : (⋃ i, range (δ i)) = range (δ 0) := by
        ext x
        simp only [mem_iUnion]
        constructor
        · rintro ⟨i, hi⟩
          exact (Subsingleton.elim i (0 : Fin 1)) ▸ hi
        · intro hx
          exact ⟨0, hx⟩
      exact heq.trans hδL
    · simpa [t, hav] using hLZ

/-- If the selected disc contains an edge, the two-spoke deformation
in XII (7.2), page 260, cannot backtrack. A backtrack would put the
whole disc in the region with just its boundary vertex restored. -/
theorem exists_embedded_two_spoke_deformation
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsPretangle Γ.toHypergraph θ T)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {F r D : Set S} {v : S} (hF : IsOArc F) (hvF : v ∈ F)
    (hv : v ∈ Γ.V) (hr : r ∈ Γ.R) (hFr : F \ {v} ⊆ r)
    (hn : Γ.IsNormal F) (hD : IsClosedDisc D) (hbd : subBd D = F)
    (hm : ((PaintingOrDrawing.drawing Γ).inter D,
      (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T)
    (hED : ∃ e ∈ Γ.E, e ⊆ D) :
    ∃ φ ψ : C(Circle, S), ∃ W : GraphWalk K.toGraph v v,
      IsEmbedding φ ∧ range φ = F ∧ W.length = 2 ∧
      range ψ = (walkDrawing K W).U ∧
      ClosedCurvesHomotopicIn (r ∪ {v}) φ ψ ∧ IsEmbedding ψ := by
  obtain ⟨e, he, heD⟩ := hED
  obtain ⟨φ, ψ, W, hφ, hφF, hlen, hψU, hh, halt⟩ :=
    exists_two_spoke_deformation hS hK ⟨e, he⟩ hF hvF hv hr hFr
  refine ⟨φ, ψ, W, hφ, hφF, hlen, hψU, hh, ?_⟩
  rcases halt with hψ | ⟨L, hL, hψL, hLZ⟩
  · exact hψ
  · have hDZ := selected_disc_subset_region_vertex_of_line_deformation hS hT hφ
      (hφF.symm ▸ hn) hr (hφF.symm ▸ hvF) hD (hbd.trans hφF.symm)
      hm hL hLZ hψL.subset hh
    obtain ⟨x, hx⟩ := he.1
    rcases hDZ (heD hx) with hxr | hxv
    · exact (region_subset hr hxr (he.2.1 hx).1).elim
    · exact ((he.2.1 hx).2 (mem_singleton_iff.mp hxv ▸ hv)).elim

end GraphMinor.GM12
