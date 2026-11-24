/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Cited
import LeanPool.GraphMinor.GM11.Section7b
public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM12.Section2ArcHomotopy
import LeanPool.GraphMinor.GM11.Walks

/-!
# Homotopy distinguishes radial spokes

For the omitted uniqueness argument in XII, page 243, two different
spokes with the same ends form a circle. If their paths were homotopic
in the region together with the original vertex, this circle would be
null-homotopic there. XI (7.2) would then give a closed disc there,
contrary to condition (iv) of the pre-radial drawing.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

universe u

/-- The homotopy part of entry-edge uniqueness in XII, page 243. Two
spokes from the same vertex into a region cannot be homotopic there
unless they are the same edge. XI (7.2) is used over its own surface
and circle, before the radial condition excludes the resulting disc. -/
theorem spoke_eq_of_paths_homotopic
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {Γ K : Drawing S} (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K)
    {r e f : Set S} {v w : S} (hr : r ∈ Γ.R) (hv : v ∈ Γ.V)
    (hw : w ∈ r ∩ K.V) (he : e ∈ K.E) (hf : f ∈ K.E)
    (hendsE : closure e ∩ K.V = {v, w}) (hendsF : closure f ∩ K.V = {v, w})
    (p q : Path (⟨v, Or.inr (mem_singleton v)⟩ : (r ∪ {v} : Set S)) ⟨w, Or.inl hw.1⟩)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hpRange : range (fun t => (p t).val) = closure e)
    (hqRange : range (fun t => (q t).val) = closure f)
    (hh : p.Homotopic q) : e = f := by
  have h72 : GM11Theorem72Statement.{u} := by
    intro T _ _ hT hconn Z F hF hFZ hn
    let := hconn
    exact GM11.theorem_7_2_proof hT hF hFZ hn
  by_contra hef
  have hcross : ∀ s t, p s = q t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s t hst
    have hxE : (p s).val ∈ closure e := hpRange ▸ mem_range_self s
    have hxF : (p s).val ∈ closure f := hst ▸ (hqRange ▸ mem_range_self t)
    have hxV : (p s).val ∈ K.V := by
      by_contra hx
      have hxe : (p s).val ∈ e := K.closure_diff_V he ▸ ⟨hxE, hx⟩
      have hxf : (p s).val ∈ f := K.closure_diff_V hf ▸ ⟨hxF, hx⟩
      exact hef (K.edge_eq_of_mem he hf hxe hxf)
    have hxends : (p s).val ∈ ({v, w} : Set S) := hendsE ▸ ⟨hxE, hxV⟩
    rcases hxends with hx | hx
    · have hp0 : p s = p 0 := Subtype.ext (hx.trans (congrArg Subtype.val p.source).symm)
      have hq0 : q t = q 0 := Subtype.ext
        ((congrArg Subtype.val hst).symm.trans (hx.trans (congrArg Subtype.val q.source).symm))
      exact Or.inl ⟨hp hp0, hq hq0⟩
    · have hxw : (p s).val = w := mem_singleton_iff.mp hx
      have hp1 : p s = p 1 := Subtype.ext (hxw.trans (congrArg Subtype.val p.target).symm)
      have hq1 : q t = q 1 := Subtype.ext
        ((congrArg Subtype.val hst).symm.trans (hxw.trans (congrArg Subtype.val q.target).symm))
      exact Or.inr ⟨hp hp1, hq hq1⟩
  have hn := nullHomotopic_union_of_homotopic_arcs p q hp hq hcross hh
  have hmap := nullHomotopic_oArc_image (f := fun x : (r ∪ {v} : Set S) => x.val)
    IsEmbedding.subtypeVal hn
  have himg : (fun x : (r ∪ {v} : Set S) => x.val) '' (range p ∪ range q) = closure e ∪ closure f
    := by
    rw [Set.image_union, ← Set.range_comp, ← Set.range_comp]
    exact congrArg₂ Set.union hpRange hqRange
  have huniv : (fun x : (r ∪ {v} : Set S) => x.val) '' univ = r ∪ {v} := by
    ext x
    simp
  rw [himg, huniv] at hmap
  have hsub : closure e ∪ closure f ⊆ r ∪ {v} := by
    rintro x (hx | hx)
    · rw [← hpRange] at hx
      obtain ⟨t, rfl⟩ := hx
      exact (p t).property
    · rw [← hqRange] at hx
      obtain ⟨t, rfl⟩ := hx
      exact (q t).property
  have hO : IsOArc (closure e ∪ closure f) := ⟨hmap.choose⟩
  obtain ⟨Δ, hΔsub, hΔ, hΔbd⟩ := h72 S hS hConn _ _ hO hsub hmap
  exact hK.2.2.2.2.2 e he f hf hef v hv r hr w hw hendsE hendsF
    ⟨Δ, hΔ, hΔsub, hΔbd⟩

end GraphMinor.GM12
