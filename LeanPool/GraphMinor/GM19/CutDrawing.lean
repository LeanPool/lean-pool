/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutArc
public import LeanPool.GraphMinor.Surface.CutChain
public import LeanPool.GraphMinor.Surface.CutEdges
public import LeanPool.GraphMinor.Surface.InvarianceOfDomain

/-!
# Cutting along several edges of a word

`WordEdges.cut_space` cuts along a set `D` of edges and asks that at most two ends of edges of `D`
meet at a
vertex off the boundary, and only one on the boundary. XIX needs more. It cuts along an `O`-arc that
meets a
cuff in one point, and along circuits joined by a path. Here three points of the cut surface lie
over a
vertex. The word is the same, so `WordEdges.cut_edges` drops the condition. It keeps it only where
it is
needed, which is to tell the two lifts of an edge apart at the ends of that edge.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Function GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] {W : ℕ → List Letter} {f : ℕ × ℂ
  → S} {V : Set S}
  {E : Set (Set S)} {A : Set S → unitInterval → S} {lab : Set S → ℕ}

/-- The endpoint condition for the two lifts of an edge. -/
abbrev EndFine (A : Set S → unitInterval → S) (D : Set (Set S)) (e : Set S) (τ : Bool) : Prop :=
  CutEndCondition A D e τ

/-- Two lifts of an edge, with distinct endpoints when the endpoint condition holds. -/
abbrev IsEdgeLift {Y : Type u} [TopologicalSpace Y] (ψ : Y → S) (a : ℝ → S) (hend : Bool → Prop)
    (r r' : ℝ → Y) : Prop :=
  IsCutEdgeLift ψ a hend r r'

/-- The cut surface over the union of a set `D` of edges of a word. Each edge has two lifts. -/
theorem WordEdges.cut_edges (h : WordEdges W f V E A lab) {D : Set (Set S)} (hD : D ⊆ E)
    (hsd : ∀ e ∈ D, ∃ (i p j q : ℕ) (e₁ e₂ : Bool), EdgeSides W (lab e) i p j q e₁ e₂)
    {Y : Type u} [TopologicalSpace Y] [T2Space Y] {g : ℕ × ℂ → Y} (hg : Presents (cutW W
      (lab '' D)) g) :
    ∃ ψ : Y → S, Continuous ψ ∧ Function.Surjective ψ ∧ InjOn ψ (ψ ⁻¹' (⋃₀ D)ᶜ) ∧ IsSurface Y ∧
      (∀ a ∈ Dsk W, ψ (g a) = f a) ∧ (∀ z : Y, ∃ a ∈ Dsk W, g a = z) ∧
      ∀ e ∈ D, ∃ r r', IsEdgeLift ψ (extI (A e)) (EndFine A D e) r r' :=
  h.lift_cut_edges hD hsd hg

omit [T2Space S] in
/-- A map into a surface, injective on a neighbourhood of an interior point, maps that neighbourhood
to a
neighbourhood of the image, by invariance of domain. The image point may be on the boundary at the
start,
and the lemma then says that it is not. -/
theorem image_mem_nhds_of_injOn {Y : Type*} [TopologicalSpace Y] {ψ : Y → S} {z : Y}
  (hz : IsInteriorPoint z)
    (hm : IsManifoldPoint (ψ z)) (hψ : Continuous ψ) {U : Set Y} (hU : IsOpen U) (hzU : z ∈ U)
      (hinj : InjOn ψ U) :
    ψ '' U ∈ 𝓝 (ψ z) := by
  obtain ⟨C, O, hC, -, hzC, ⟨c⟩⟩ := hm
  obtain ⟨U', hU', hzU', hsub, ⟨e⟩⟩ := hz.exists_subset (hU.inter (hC.preimage hψ)) ⟨hzU, hzC⟩
  have : Nonempty Y := ⟨z⟩
  have : Nonempty S := ⟨ψ z⟩
  have : Nonempty (EuclideanHalfSpace 2) := ⟨(c ⟨ψ z, hzC⟩).1⟩
  obtain ⟨b⟩ := exists_homeomorph_ball (0 : ℂ) one_pos
  obtain ⟨a, a', h1, h2, h3, h4, h5, h6⟩ := exists_functions_of_homeomorph (b.trans e.symm)
  obtain ⟨k, k', h1', h2', h3', h4', h5', h6'⟩ := exists_functions_of_homeomorph c
  let j : S → ℂ := fun x ↦ complexPlane.symm (k x).1
  have hjc : ContinuousOn j C := complexPlane.symm.continuous.comp_continuousOn
    (continuous_subtype_val.comp_continuousOn h1')
  have hji : InjOn j C := fun x hx y hy he ↦
    h5'.injOn hx hy (Subtype.ext (complexPlane.symm.injective he))
  have hGc : ContinuousOn (j ∘ ψ ∘ a) (Metric.ball (0 : ℂ) 1) :=
    hjc.comp (hψ.comp_continuousOn h1) fun w hw ↦ (hsub (h3 hw)).2
  have hGi : InjOn (j ∘ ψ ∘ a) (Metric.ball (0 : ℂ) 1) := fun w hw w' hw' he ↦
    h5.injOn hw hw' (hinj (hsub (h3 hw)).1 (hsub (h3 hw')).1
      (hji (hsub (h3 hw)).2 (hsub (h3 hw')).2 he))
  have hopen := isOpen_image_of_injOn Metric.isOpen_ball hGc hGi
  have hO : IsOpen (C ∩ j ⁻¹' ((j ∘ ψ ∘ a) '' Metric.ball (0 : ℂ) 1)) :=
    hjc.isOpen_inter_preimage hC hopen
  refine Filter.mem_of_superset (hO.mem_nhds ⟨hzC, a' z, h4 hzU', ?_⟩) ?_
  · change j (ψ (a (a' z))) = j (ψ z)
    rw [h6 hzU']
  · rintro y ⟨hyC, w, hw, he⟩
    exact ⟨a w, (hsub (h3 hw)).1, hji (hsub (h3 hw)).2 hyC he⟩

omit [T2Space S] in
/-- A point of `V` on an edge has finitely many points of the polygons over it, which are corners.
-/
theorem WordEdges.subset_range_spe (h : WordEdges W f V E A lab) {a : ℕ × ℂ} (ha : a ∈ Dsk W)
  (hV : f a ∈ V)
    (hE : f a ∈ ⋃₀ E) : a ∈ range (spe W) := by
  obtain ⟨p, e', e, he, u, hu, h1, h2, h3⟩ := h.exists_side ha hE
  have hp : p < (W a.1).length := by
    by_contra hn
    rw [List.getElem?_eq_none (not_lt.mp hn)] at h1
    simp at h1
  have hu01 : u = 0 ∨ u = 1 := by
    by_contra hn
    push Not at hn
    have hI : u ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hu.1 (Ne.symm hn.1), lt_of_le_of_ne hu.2 hn.2⟩
    exact h.extI_notMem he (ofs_Ioo e' hI) (h3 ▸ hV)
  rcases hu01 with rfl | rfl
  · exact ⟨⟨(a.1, p, false), hp⟩, by simpa [spe, eo] using h2.symm⟩
  · exact ⟨⟨(a.1, p, true), hp⟩, by simpa [spe, eo] using h2.symm⟩

omit [T2Space S] in
/-- A point of an edge is a point of the open edge or an end. -/
theorem WordEdges.exists_param (h : WordEdges W f V E A lab) {e : Set S} (he : e ∈ E) {x : S}
  (hx : x ∈ e) :
    ∃ t ∈ Icc (0 : ℝ) 1, extI (A e) t = x ∧ (t ∈ Ioo (0 : ℝ) 1 ∨ ∃ τ, eo τ = t) := by
  have hr : extI (A e) '' Icc 0 1 = e := by rw [image_extI, (h.arc e he).2.1]
  obtain ⟨t, ht, rfl⟩ := hr.symm ▸ hx
  refine ⟨t, ht, rfl, ?_⟩
  by_cases h0 : t = 0
  · exact .inr ⟨false, by simp [eo, h0]⟩
  by_cases h1 : t = 1
  · exact .inr ⟨true, by simp [eo, h1]⟩
  exact .inl ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩

/-- **Cutting along a set of edges.** No condition at the vertices is needed. The fibres are finite,
and the
whole lift of the edges lies in the boundary. Off the ends, by invariance of domain, an interior
point over a
vertex would have a neighbourhood mapped onto a neighbourhood of that vertex, but the edge at the
vertex comes
near it, and only boundary points lie over the open edge. -/
theorem WordEdges.exists_cut (h : WordEdges W f V E A lab) (hS : IsSurface S) (hne :
  (Dsk W).Nonempty)
    {D : Set (Set S)} (hD : D ⊆ E) (hmid : ∀ e ∈ D, edgeMid A e ∉ bd S) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : T2Space Y) (ψ : Y → S), IsSurface Y ∧ Continuous ψ
      ∧
      Function.Surjective ψ ∧ InjOn ψ (ψ ⁻¹' (⋃₀ D)ᶜ) ∧ (∀ x, (ψ ⁻¹' {x}).Finite) ∧ ψ ⁻¹'
        (⋃₀ D) ⊆ bd Y ∧
      ∀ e ∈ D, ∃ r r', IsEdgeLift ψ (extI (A e)) (EndFine A D e) r r' := by
  classical
  have hsd : ∀ e ∈ D, ∃ (i p j q : ℕ) (e₁ e₂ : Bool), EdgeSides W (lab e) i p j q e₁ e₂
    := fun e he ↦ by
    obtain ⟨i, p, j, q, e₁, e₂, h1, h2, h3⟩ := h.exists_sides (hD he) (hmid e he)
    exact ⟨i, p, j, q, e₁, e₂, h1, h2, h3⟩
  obtain ⟨Y, tY, t2, g, hg⟩ := exists_cut_presented.{u} (W := cutW W (lab '' D)) (finW_cut h.fin)
    (isPaired_cut h.paired) (by rw [dsk_cut]; exact hne)
  obtain ⟨ψ, h1, h2, h3, h4, hψ, hrep, hlift⟩ := WordEdges.cut_edges h hD hsd hg
  have : Finite (SE W) := finite_se h.fin
  have hfinV : ∀ v ∈ V ∩ ⋃₀ E, (ψ ⁻¹' {v}).Finite := fun v hv ↦ by
    refine ((finite_range (spe W)).image g).subset ?_
    intro z hz
    obtain ⟨a, ha, rfl⟩ := hrep z
    have hfa : f a = v := by rw [← hψ a ha]; exact hz
    exact ⟨a, WordEdges.subset_range_spe h ha (hfa ▸ hv.1) (hfa ▸ hv.2), rfl⟩
  have hfin : ∀ x, (ψ ⁻¹' {x}).Finite := fun x ↦ by
    by_cases hx : x ∈ ⋃₀ D
    · obtain ⟨e, he, hxe⟩ := hx
      by_cases hxV : x ∈ V
      · exact hfinV x ⟨hxV, e, hD he, hxe⟩
      obtain ⟨t, ht, rfl, hc⟩ := WordEdges.exists_param h (hD he) hxe
      obtain ⟨r, r', -, -, -, -, hf⟩ := hlift e he
      have hI : t ∈ Ioo (0 : ℝ) 1 := hc.resolve_right (by
        rintro ⟨τ, rfl⟩
        exact hxV (h.extI_mem_V (hD he) τ))
      refine (Set.toFinite {r t, r' t}).subset fun z hz ↦ ?_
      exact (hf t ht (.inl hI)).2 z hz
    · have hoff : ∀ {z}, z ∈ ψ ⁻¹' {x} → z ∈ ψ ⁻¹' (⋃₀ D)ᶜ := fun {z} hz ↦ by
        change ψ z ∉ ⋃₀ D
        rw [show ψ z = x from hz]
        exact hx
      exact Set.Subsingleton.finite fun z hz z' hz' ↦ h3 (hoff hz) (hoff hz') (hz.trans hz'.symm)
  refine ⟨Y, tY, t2, ψ, h4, h1, h2, h3, hfin, ?_, hlift⟩
  rintro z ⟨e, he, hze⟩
  by_contra hz
  have hzi : IsInteriorPoint z := not_not.mp hz
  have hend : ∀ {w t e'}, e' ∈ D → t ∈ Ioo (0 : ℝ) 1 → ψ w = extI (A e') t → w ∈ bd Y
    := fun {w t e'} he' ht hw ↦ by
    obtain ⟨r, r', -, -, -, hb, hf⟩ := hlift e' he'
    have hI := Ioo_subset_Icc_self ht
    rcases (hf t hI (.inl ht)).2 w hw with rfl | rfl
    · exact (hb t hI).1
    · exact (hb t hI).2
  obtain ⟨t, ht, hte, hc⟩ := WordEdges.exists_param h (hD he) hze
  obtain ⟨τ, rfl⟩ : ∃ τ, eo τ = t := hc.resolve_left fun hI ↦ hz (hend he hI hte.symm)
  let P : Set Y := ψ ⁻¹' (V ∩ ⋃₀ E)
  have hP : P.Finite := by
    have : P = ⋃ v ∈ V ∩ ⋃₀ E, ψ ⁻¹' {v} := by
      ext w
      simp [P]
    rw [this]
    exact (h.graph.fin.subset inter_subset_left).biUnion fun v _ ↦ hfin v
  let U : Set Y := (bd Y)ᶜ ∩ (P \ {z})ᶜ
  have hUo : IsOpen U := (isClosed_bd Y).isOpen_compl.inter (hP.subset
    sdiff_subset).isClosed.isOpen_compl
  have hzU : z ∈ U := ⟨hz, fun hc ↦ hc.2 rfl⟩
  have key : ∀ w ∈ U, ψ w ∈ ⋃₀ D → w = z := by
    rintro w hw ⟨e', he', hwe⟩
    obtain ⟨t', ht', hte', hc'⟩ := WordEdges.exists_param h (hD he') hwe
    obtain ⟨τ', rfl⟩ : ∃ τ', eo τ' = t' := hc'.resolve_left fun hI ↦ hw.1 (hend he' hI hte'.symm)
    by_contra hne'
    exact hw.2 ⟨⟨hte' ▸ h.extI_mem_V (hD he') τ', e', hD he', hwe⟩, hne'⟩
  have hinj : InjOn ψ U := by
    intro a ha b hb hab
    by_cases hD' : ψ a ∈ ⋃₀ D
    · rw [key a ha hD', key b hb (hab ▸ hD')]
    · exact h3 hD' (show ψ b ∉ ⋃₀ D from hab ▸ hD') hab
  have hN := image_mem_nhds_of_injOn hzi (hS.2.2 (ψ z)) h1 hUo hzU hinj
  have hN' : extI (A e) ⁻¹' (ψ '' U) ∈ 𝓝 (eo τ) :=
    (continuous_extI (h.arc e (hD he)).1.1).continuousAt.preimage_mem_nhds (hte ▸ hN)
  have hcl : eo τ ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (zero_ne_one' ℝ)]
    exact eo_mem τ
  obtain ⟨t', ht'N, ht'I⟩ := mem_closure_iff_nhds.mp hcl _ hN'
  obtain ⟨w, hw, he'⟩ := ht'N
  exact hw.1 (hend he ht'I he')

end GraphMinor.GM19
