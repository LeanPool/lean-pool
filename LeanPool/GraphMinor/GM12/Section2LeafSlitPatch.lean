/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2ArcGermChart
public import LeanPool.GraphMinor.GM12.Section2LeafArcData
import LeanPool.GraphMinor.GM11.RadialCorners
import LeanPool.GraphMinor.Surface.ArcErase
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# A slit patch at a drawing leaf

For the entry-edge lemma of XII, page 243, isolate a short initial
part of the leaf edge in a surface chart. The other vertices, other
edge closures, and the far part of this edge form a closed set missing
the leaf. In its complement the drawing agrees with the short arc.
The arc-germ chart and slit-ball contraction then give the required
simply connected patch, with path-connected puncture.
-/

public section

namespace GraphMinor.GM12

open Set Topology Metric Surface GM11

/-- An incident line isolated from all other edges at its initial
vertex has a simply connected slit patch at that vertex. -/
theorem exists_slit_patch_at_leaf_line
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (Γ : Drawing S)
    {e : Set S} (he : e ∈ Γ.E) {u v : S} (hL : IsLineWithEnds (closure e) v u)
    (hleaf : ∀ f ∈ Γ.E, f ≠ e → v ∉ closure f) :
    ∃ N X : Set S, IsOpen N ∧ v ∈ N ∧ v ∈ X ∧
      IsSimplyConnectedSet X ∧ IsPathConnected (X \ {v}) ∧
      X ⊆ Γ.Uᶜ ∪ {v} ∧ N \ Γ.U ⊆ X := by
  obtain ⟨a, ha, harange, ha0, _⟩ := hL.exists_arc
  obtain ⟨U, h, g, c, _, hg0⟩ := (hS.2.2 v).exists_ballChart
    isOpen_univ (mem_univ v) (by norm_num : (0 : ℝ) < 1)
  have hvU : v ∈ U := hg0 ▸ c.gm (mem_ball_self (by norm_num : (0 : ℝ) < 1))
  obtain ⟨τ, hτ, _, hτU⟩ := exists_pos_le ha.1 c.isOpen (ha0.symm ▸ hvU)
    (by norm_num : (0 : unitInterval) < 1)
  let a' := subArc a 0 τ
  have ha' : IsArcMap a' := ha.sub (Ne.symm hτ.ne')
  have ha'0 : a' 0 = v := (subArc_zero a 0 τ).trans ha0
  have ha'range : range a' = a '' Icc 0 τ := range_subArc a (unitInterval.nonneg τ)
  have ha'U : range a' ⊆ U := by
    rw [ha'range]
    rintro _ ⟨t, ht, rfl⟩
    exact hτU t ht.2
  have ha'Γ : range a' ⊆ Γ.U :=
    (range_subArc_subset a 0 τ).trans (harange.le.trans (Γ.closure_subset_U he))
  let T := ((Γ.V \ {v}) ∪ ⋃ f ∈ Γ.E \ {e}, closure f) ∪ a '' Icc τ 1
  have hTc : IsClosed T := by
    refine ((Γ.finite_V.subset sdiff_subset).isClosed.union
      ((Γ.finite_edges.subset sdiff_subset).isClosed_biUnion (fun _ _
        => isClosed_closure))).union ?_
    exact (isCompact_Icc.image ha.1).isClosed
  have hvT : v ∉ T := by
    rintro ((hvV | hvE) | hvA)
    · exact hvV.2 rfl
    · obtain ⟨f, hf, hvf⟩ := mem_iUnion₂.mp hvE
      exact hleaf f hf.1 (fun heq => hf.2 heq) hvf
    · obtain ⟨t, ht, htv⟩ := hvA
      have ht0 : t = 0 := ha.2 (htv.trans ha0.symm)
      exact hτ.not_ge (ht0 ▸ ht.1)
  have hΓgerm : Γ.U ∩ Tᶜ ⊆ range a' := by
    rintro x ⟨hxU, hxT⟩
    by_cases hxV : x ∈ Γ.V
    · by_cases hxv : x = v
      · exact ⟨0, ha'0.trans hxv.symm⟩
      · exact (hxT (Or.inl (Or.inl ⟨hxV, hxv⟩))).elim
    · obtain ⟨f, hf, hxf⟩ := Γ.exists_edge_of_mem hxU hxV
      have hfe : f = e := by
        by_contra hn
        exact hxT (Or.inl (Or.inr (mem_iUnion₂.mpr ⟨f, ⟨hf, hn⟩, subset_closure hxf⟩)))
      have hxe : x ∈ closure e := hfe ▸ subset_closure hxf
      obtain ⟨t, ht⟩ := harange.symm ▸ hxe
      by_cases htτ : t ≤ τ
      · rw [ha'range]
        exact ⟨t, ⟨unitInterval.nonneg t, htτ⟩, ht⟩
      · exact (hxT (Or.inr ⟨t, ⟨(lt_of_not_ge htτ).le, unitInterval.le_one t⟩, ht⟩)).elim
  have hpatch := exists_slit_patch_of_arc_germ (fun x => (hS.2.2 x).isManifoldPoint)
    c ha' ha'U ha'Γ hTc.isOpen_compl (ha'0.symm ▸ hvT) hΓgerm
  rwa [ha'0] at hpatch

end GraphMinor.GM12
