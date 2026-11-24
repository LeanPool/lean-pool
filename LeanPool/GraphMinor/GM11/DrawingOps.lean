/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.PaintingCells
public import LeanPool.GraphMinor.GM11.RadialChord

/-!
# Two operations on drawings

`exists_added_vertices` adds a point of each edge to the vertices of a drawing, and keeps the point
set,
so the regions do not change. `exists_transport` moves a drawing along a map that is injective on
its
point set.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- Add one point of each edge of `D` to the vertices. -/
theorem exists_added_vertices (D : Drawing S) {m : Set S → S} (hm : ∀ e ∈ D.E, m e ∈ e) :
    ∃ D₂ : Drawing S, D₂.U = D.U ∧ D₂.V = D.V ∪ m '' D.E := by
  classical
  have key : ∀ T : Finset (Set S), (∀ e ∈ T, e ∈ D.E) →
      ∃ D₂ : Drawing S, D₂.U = D.V ∪ ⋃ e ∈ T, closure e ∧ D₂.V = D.V ∪ m '' T := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨pointsDrawing D.finite_V, by simp [pointsDrawing], by simp [pointsDrawing]⟩
    | insert e T he ih =>
      intro hT
      obtain ⟨C, hU', hV'⟩ := ih fun f hf => hT f (Finset.mem_insert_of_mem hf)
      have hee := hT e (Finset.mem_insert_self _ _)
      have hme := hm e hee
      let A : Set S := insert (m e) (closure e ∩ D.V)
      have hA : A.Finite := (D.finite_V.inter_of_right _).insert _
      have hAe : A ⊆ closure e := insert_subset (subset_closure hme) inter_subset_left
      obtain ⟨L, hLU, hLV⟩ : ∃ L : Drawing S, L.U = closure e ∧ L.V = A := by
        rcases D.edge_cond e hee with ⟨u, v, huv, hcap, hL⟩ | ⟨u, -, hF⟩
        · refine exists_drawing_on_line _ hL huv hA ?_ ?_ hAe le_rfl
          · exact mem_insert_of_mem _ (hcap ▸ mem_insert u {v})
          · exact mem_insert_of_mem _ (hcap ▸ mem_insert_of_mem u rfl)
        · exact exists_drawing_on_oArc hF hA (insert_nonempty _ _) hAe
      have hmeet : C.U ∩ L.U ⊆ C.V ∩ L.V := by
        rw [hU', hV', hLU, hLV]
        rintro x ⟨hx | hx, hxe⟩
        · exact ⟨Or.inl hx, mem_insert_of_mem _ ⟨hxe, hx⟩⟩
        · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
          have hfe : f ≠ e := fun h => he (h ▸ hf)
          have hff := hT f (Finset.mem_insert_of_mem hf)
          by_cases hxV : x ∈ D.V
          · exact ⟨Or.inl hxV, mem_insert_of_mem _ ⟨hxe, hxV⟩⟩
          · have h₁ : x ∈ f := D.closure_diff_V hff ▸ (⟨hxf, hxV⟩ : x ∈ closure f \ D.V)
            have h₂ : x ∈ e := D.closure_diff_V hee ▸ (⟨hxe, hxV⟩ : x ∈ closure e \ D.V)
            exact (hfe (D.edge_eq_of_mem hff hee h₁ h₂)).elim
      refine ⟨C.glue L hmeet, ?_, ?_⟩
      · change C.U ∪ L.U = _
        rw [hU', hLU]
        ext x
        simp only [mem_union, mem_iUnion, Finset.mem_insert, exists_prop]
        constructor
        · rintro ((h | ⟨f, hf, h⟩) | h)
          · exact Or.inl h
          · exact Or.inr ⟨f, Or.inr hf, h⟩
          · exact Or.inr ⟨e, Or.inl rfl, h⟩
        · rintro (h | ⟨f, rfl | hf, h⟩)
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
          · exact Or.inl (Or.inr ⟨f, hf, h⟩)
      · change C.V ∪ L.V = _
        rw [hV', hLV]
        ext x
        simp only [A, mem_union, mem_insert_iff, mem_image, Finset.mem_coe, Finset.mem_insert,
          mem_inter_iff]
        constructor
        · rintro ((h | ⟨f, hf, rfl⟩) | rfl | h)
          · exact Or.inl h
          · exact Or.inr ⟨f, Or.inr hf, rfl⟩
          · exact Or.inr ⟨e, Or.inl rfl, rfl⟩
          · exact Or.inl h.2
        · rintro (h | ⟨f, rfl | hf, rfl⟩)
          · exact Or.inl (Or.inl h)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl (Or.inr ⟨f, hf, rfl⟩)
  have hE : D.E.Finite := D.finite_edges
  obtain ⟨D₂, hU, hV⟩ := key hE.toFinset fun e he => hE.mem_toFinset.mp he
  refine ⟨D₂, ?_, ?_⟩
  · rw [hU]
    conv_rhs => rw [D.U_eq]
    simp
  · rw [hV]
    simp

omit [T2Space S] in
/-- Arc components move along a map with a continuous inverse. -/
theorem arcComponentsIn_image {S' : Type*} [TopologicalSpace S'] {F : Set S} {f : S → S'} {g : S'
  → S}
    (hf : ContinuousOn f F) (hg : ContinuousOn g (f '' F)) (hgf : ∀ x ∈ F, g (f x) = x) :
    arcComponentsIn (f '' F) = image f '' arcComponentsIn F := by
  have hfg : ∀ y ∈ f '' F, f (g y) = y := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hgf x hx]
  have hconn : ∀ {D : Set S}, D ⊆ F → IsPathConnected D → IsPathConnected (f '' D) := fun hD h =>
    h.image' (hf.mono hD)
  have hconn' : ∀ {D : Set S'}, D ⊆ f '' F → IsPathConnected D → IsPathConnected (g '' D)
    := fun hD h =>
    h.image' (hg.mono hD)
  have hgsub : ∀ {D : Set S'}, D ⊆ f '' F → g '' D ⊆ F := by
    rintro D hD _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hD hy
    rwa [hgf x hx]
  have hfgim : ∀ {D : Set S'}, D ⊆ f '' F → f '' (g '' D) = D := fun {D} hD => by
    rw [image_image]
    exact (image_congr fun y hy => hfg y (hD hy)).trans (image_id' D)
  have hgfim : ∀ {D : Set S}, D ⊆ F → g '' (f '' D) = D := fun {D} hD => by
    rw [image_image]
    exact (image_congr fun y hy => hgf y (hD hy)).trans (image_id' D)
  ext C'
  constructor
  · rintro ⟨hne, hsub, hpc, hmax⟩
    refine ⟨g '' C', ⟨hne.image g, hgsub hsub, hconn' hsub hpc, ?_⟩, hfgim hsub⟩
    intro D hD hDc hCD
    have h₁ : C' ⊆ f '' D := by
      have := image_mono (f := f) hCD
      rwa [hfgim hsub] at this
    have h₂ := hmax _ (image_mono hD) (hconn hD hDc) h₁
    rw [← h₂, hgfim hD]
  · rintro ⟨C, ⟨hne, hsub, hpc, hmax⟩, rfl⟩
    refine ⟨hne.image f, image_mono hsub, hconn hsub hpc, ?_⟩
    intro D hD hDc hCD
    have h₁ : C ⊆ g '' D := by
      have := image_mono (f := g) hCD
      rwa [hgfim hsub] at this
    have h₂ := hmax _ (hgsub hD) (hconn' hD hDc) h₁
    rw [← h₂, hfgim hD]

omit [T2Space S] in
/-- Move a drawing along a map that is injective on its point set. -/
theorem exists_transport {S' : Type*} [TopologicalSpace S'] [T2Space S'] [CompactSpace S] [Nonempty
  S]
    (D : Drawing S) {f : S → S'} (hf : Continuous f) (hinj : InjOn f D.U) :
    ∃ D' : Drawing S', D'.U = f '' D.U ∧ D'.V = f '' D.V ∧ D'.E = image f '' D.E ∧
      ∀ e ∈ D.E, closure (f '' e) = f '' closure e := by
  classical
  have hUc : IsCompact D.U := D.isClosed_U.isCompact
  have : CompactSpace D.U := isCompact_iff_compactSpace.mp hUc
  let ι : D.U → S' := fun x => f x.1
  have hιc : Continuous ι := hf.comp continuous_subtype_val
  have hιi : Function.Injective ι := fun x y h => Subtype.ext (hinj x.2 y.2 h)
  have hemb := hιc.isClosedEmbedding hιi
  have hrange : range ι = f '' D.U := by
    ext y
    simp [ι]
  let φ : D.U ≃ₜ range ι := hemb.isEmbedding.toHomeomorph
  let g : S' → S := Function.invFunOn f D.U
  have hgf : ∀ x ∈ D.U, g (f x) = x := fun x hx => by
    have h := Function.invFunOn_mem (f := f) (s := D.U) ⟨x, hx, rfl⟩
    exact hinj h hx (Function.invFunOn_eq ⟨x, hx, rfl⟩)
  have hg : ContinuousOn g (f '' D.U) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (f '' D.U).domRestrict g = fun y => (φ.symm ⟨y.1, hrange.symm ▸ y.2⟩).1 := by
      funext y
      have h₁ : ι (φ.symm ⟨y.1, hrange.symm ▸ y.2⟩) = y.1 :=
        congrArg Subtype.val (φ.apply_symm_apply ⟨y.1, hrange.symm ▸ y.2⟩)
      have h₂ := hgf _ (φ.symm ⟨y.1, hrange.symm ▸ y.2⟩).2
      change g y.1 = _
      rw [← h₂]
      exact congrArg g h₁.symm
    rw [heq]
    refine continuous_subtype_val.comp (φ.symm.continuous.comp ?_)
    exact Continuous.subtype_mk continuous_subtype_val _
  have hsub : D.U \ D.V ⊆ D.U := sdiff_subset
  have hgF : ContinuousOn g (f '' (D.U \ D.V)) := hg.mono (image_mono hsub)
  have harc := arcComponentsIn_image (F := D.U \ D.V) hf.continuousOn hgF fun x hx => hgf x hx.1
  have hdiff : f '' D.U \ f '' D.V = f '' (D.U \ D.V) := (InjOn.image_sdiff_subset hinj
    D.V_subset_U).symm
  have hcl : ∀ e ∈ D.E, closure (f '' e) = f '' closure e := by
    intro e he
    apply subset_antisymm
    · have hc : IsCompact (f '' closure e) := (isClosed_closure.isCompact).image hf
      exact closure_minimal (image_mono subset_closure) hc.isClosed
    · exact image_closure_subset_closure_image hf
  have hcap : ∀ e ∈ D.E, closure (f '' e) ∩ f '' D.V = f '' (closure e ∩ D.V) := by
    intro e he
    rw [hcl e he]
    exact (InjOn.image_inter hinj (D.closure_subset_U he) D.V_subset_U).symm
  refine ⟨⟨f '' D.U, f '' D.V, image_mono D.V_subset_U, hUc.image hf |>.isClosed,
    D.finite_V.image f, ?_, ?_⟩, rfl, rfl, ?_, hcl⟩
  rotate_left 2
  · change arcComponentsIn (f '' D.U \ f '' D.V) = _
    rw [hdiff, harc]
    rfl
  · rw [hdiff, harc]
    exact D.finite_edges.image _
  · rw [hdiff, harc]
    rintro _ ⟨e, he, rfl⟩
    have hinje : InjOn f (closure e) := hinj.mono (D.closure_subset_U he)
    rw [hcap e he]
    rcases D.edge_cond e he with ⟨u, v, huv, hc, hL⟩ | ⟨u, hc, hF⟩
    · left
      have hmem : ∀ z ∈ ({u, v} : Set S), z ∈ closure e := fun z hz => by
        rw [← hc] at hz
        exact hz.1
      refine ⟨f u, f v, fun h => huv (hinje (hmem u (by simp)) (hmem v (by simp)) h), ?_, ?_⟩
      · rw [hc, image_pair]
      · obtain ⟨φ₁, h0, h1⟩ := hL
        have hc₁ : Continuous fun t => f (φ₁ t).1 := hf.comp (continuous_subtype_val.comp
          φ₁.continuous)
        have hi₁ : Function.Injective fun t => f (φ₁ t).1 := fun x y h =>
          φ₁.injective (Subtype.ext (hinje (φ₁ x).2 (φ₁ y).2 h))
        have hl := isLine_range hc₁ hi₁
        have hr : range (fun t => f (φ₁ t).1) = f '' closure e := by
          ext y
          constructor
          · rintro ⟨t, rfl⟩
            exact ⟨_, (φ₁ t).2, rfl⟩
          · rintro ⟨x, hx, rfl⟩
            exact ⟨φ₁.symm ⟨x, hx⟩, by simp⟩
        rw [hr, ← hcl e he] at hl
        simpa only [h0, h1] using hl
    · right
      refine ⟨f u, ?_, ?_⟩
      · rw [hc, image_singleton]
      · obtain ⟨φ₂⟩ := hF
        have hc₂ : Continuous fun t => f (φ₂ t).1 := hf.comp (continuous_subtype_val.comp
          φ₂.continuous)
        have hi₂ : Function.Injective fun t => f (φ₂ t).1 := fun x y h =>
          φ₂.injective (Subtype.ext (hinje (φ₂ x).2 (φ₂ y).2 h))
        have hr : range (fun t => f (φ₂ t).1) = f '' closure e := by
          ext y
          constructor
          · rintro ⟨t, rfl⟩
            exact ⟨_, (φ₂ t).2, rfl⟩
          · rintro ⟨x, hx, rfl⟩
            exact ⟨φ₂.symm ⟨x, hx⟩, by simp⟩
        have hem := (hc₂.isClosedEmbedding hi₂).isEmbedding.toHomeomorph
        exact ⟨hem.trans (Homeomorph.setCongr (hr.trans (hcl e he).symm))⟩

end GraphMinor.GM11
