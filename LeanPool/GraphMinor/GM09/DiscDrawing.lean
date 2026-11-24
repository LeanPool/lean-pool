/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Basic
public import LeanPool.GraphMinor.Surface.Jordan
public import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.GM11.DrawingOps
import LeanPool.GraphMinor.GM11.ArcDrawings

/-! ## Module 2: `GraphDrawing` Transport, Gluing, and Atomic Constructors -/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Topology Metric Graph GraphMinor GraphMinor.Surface GraphMinor.GM06
  GraphMinor.GM11

universe u v w

variable {α : Type u} {β : Type v}

/-- Transport a drawing `D : Drawing S` whose point set `D.U` is compact along a continuous map
`f : S → S'` injective on `D.U`. -/
theorem exists_transport_of_isCompact {S S' : Type*} [TopologicalSpace S] [Nonempty S]
    [TopologicalSpace S'] [T2Space S']
    (D : Drawing S) (hUc : IsCompact D.U) {f : S → S'} (hf : Continuous f) (hinj : InjOn f D.U) :
    ∃ D' : Drawing S', D'.U = f '' D.U ∧ D'.V = f '' D.V ∧ D'.E = image f '' D.E ∧
      ∀ e ∈ D.E, closure (f '' e) = f '' closure e := by
  classical
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
  have hdiff : f '' D.U \ f '' D.V = f '' (D.U \ D.V) :=
    (InjOn.image_sdiff_subset hinj D.V_subset_U).symm
  have hcl : ∀ e ∈ D.E, closure (f '' e) = f '' closure e := by
    intro e he
    apply subset_antisymm
    · have hc : IsCompact (f '' closure e) :=
        (hUc.of_isClosed_subset isClosed_closure (D.closure_subset_U he)).image hf
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
        have hc₁ : Continuous fun t => f (φ₁ t).1 :=
          hf.comp (continuous_subtype_val.comp φ₁.continuous)
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
        have hc₂ : Continuous fun t => f (φ₂ t).1 :=
          hf.comp (continuous_subtype_val.comp φ₂.continuous)
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

/-- If `Γ : GraphDrawing G S` has `(Γ.iso.vertexEquiv v).1 = ν v.1` for all `v : V(G)`, then
`Γ.drawing.V = ν '' V(G)`. -/
theorem drawing_V_eq_image {S : Type*} [TopologicalSpace S] {G : Graph α β}
    (Γ : GraphDrawing G S) {ν : α → S}
    (hν : ∀ v : V(G), (Γ.iso.vertexEquiv v).1 = ν v.1) :
    Γ.drawing.V = ν '' V(G) := by
  ext y
  constructor
  · intro hy
    let v := Γ.iso.vertexEquiv.symm ⟨y, hy⟩
    refine ⟨v.1, v.2, ?_⟩
    rw [← hν v, Γ.iso.vertexEquiv.apply_symm_apply]
  · rintro ⟨x, hx, rfl⟩
    rw [← hν ⟨x, hx⟩]
    exact (Γ.iso.vertexEquiv ⟨x, hx⟩).2

/-- Transport a `GraphDrawing G S` with compact `U` along a continuous map `f : S → S'` injective on
`U`. -/
theorem GraphDrawing.transport {S S' : Type*} [TopologicalSpace S] [Nonempty S]
    [TopologicalSpace S'] [T2Space S'] {G : Graph α β}
    (Γ : GraphDrawing G S) (hUc : IsCompact Γ.drawing.U) {ν : α → S}
    (hν : ∀ v : V(G), (Γ.iso.vertexEquiv v).1 = ν v.1)
    {f : S → S'} (hf : Continuous f) (hinj : InjOn f Γ.drawing.U) :
    ∃ Γ' : GraphDrawing G S',
      Γ'.drawing.U = f '' Γ.drawing.U ∧
      Γ'.drawing.V = f '' Γ.drawing.V ∧
      ∀ v : V(G), (Γ'.iso.vertexEquiv v).1 = f (ν v.1) := by
  obtain ⟨D', hU', hV', hE', hcl⟩ := exists_transport_of_isCompact Γ.drawing hUc hf hinj
  have hinjV : InjOn f Γ.drawing.V := hinj.mono Γ.drawing.V_subset_U
  have hinjE : InjOn (image f) Γ.drawing.E := by
    intro e₁ he₁ e₂ he₂ heq
    ext x
    constructor
    · intro hx₁
      have hfx : f x ∈ f '' e₂ := heq ▸ ⟨x, hx₁, rfl⟩
      obtain ⟨y, hy₂, hfy⟩ := hfx
      have hxy : y = x :=
        hinj (Γ.drawing.closure_subset_U he₂ (subset_closure hy₂))
          (Γ.drawing.closure_subset_U he₁ (subset_closure hx₁)) hfy
      exact hxy ▸ hy₂
    · intro hx₂
      have hfx : f x ∈ f '' e₁ := heq.symm ▸ ⟨x, hx₂, rfl⟩
      obtain ⟨y, hy₁, hfy⟩ := hfx
      have hxy : y = x :=
        hinj (Γ.drawing.closure_subset_U he₁ (subset_closure hy₁))
          (Γ.drawing.closure_subset_U he₂ (subset_closure hx₂)) hfy
      exact hxy ▸ hy₁
  let vFun : Γ.drawing.V → D'.V := fun x => ⟨f x.1, hV' ▸ ⟨x.1, x.2, rfl⟩⟩
  have hvFun_bij : Function.Bijective vFun :=
    ⟨fun x y h => Subtype.ext (hinjV x.2 y.2 (congrArg Subtype.val h)),
     fun z => by
       have hz : z.1 ∈ f '' Γ.drawing.V := hV' ▸ z.2
       obtain ⟨x, hx, hfx⟩ := hz
       exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩⟩
  let eFun : Γ.drawing.E → D'.E := fun e => ⟨f '' e.1, hE' ▸ ⟨e.1, e.2, rfl⟩⟩
  have heFun_bij : Function.Bijective eFun :=
    ⟨fun e₁ e₂ h => Subtype.ext (hinjE e₁.2 e₂.2 (congrArg Subtype.val h)),
     fun a => by
       have ha : a.1 ∈ image f '' Γ.drawing.E := hE' ▸ a.2
       obtain ⟨e, he, hfe⟩ := ha
       exact ⟨⟨e, he⟩, Subtype.ext hfe⟩⟩
  let vEquiv : Γ.drawing.V ≃ D'.V := Equiv.ofBijective vFun hvFun_bij
  let eEquiv : Γ.drawing.E ≃ D'.E := Equiv.ofBijective eFun heFun_bij
  have hvEquiv_val : ∀ x : Γ.drawing.V, (vEquiv x).1 = f x.1 := fun _ => rfl
  have heEquiv_val : ∀ e : Γ.drawing.E, (eEquiv e).1 = f '' e.1 := fun _ => rfl
  let iso' : Iso G D'.toGraph :=
    { vertexEquiv := Γ.iso.vertexEquiv.trans vEquiv
      edgeEquiv := Γ.iso.edgeEquiv.trans eEquiv
      isLink_iff := fun {e x y} => by
        rw [Γ.iso.isLink_iff]
        let e₀ := Γ.iso.edgeEquiv e
        let x₀ := Γ.iso.vertexEquiv x
        let y₀ := Γ.iso.vertexEquiv y
        change Γ.drawing.toGraph.IsLink e₀.1 x₀.1 y₀.1 ↔
          D'.toGraph.IsLink (f '' e₀.1) (f x₀.1) (f y₀.1)
        have he' : f '' e₀.1 ∈ D'.E := hE' ▸ ⟨e₀.1, e₀.2, rfl⟩
        have hx' : f x₀.1 ∈ D'.V := hV' ▸ ⟨x₀.1, x₀.2, rfl⟩
        have hy' : f y₀.1 ∈ D'.V := hV' ▸ ⟨y₀.1, y₀.2, rfl⟩
        have hcap : closure (f '' e₀.1) ∩ D'.V = f '' (closure e₀.1 ∩ Γ.drawing.V) := by
          rw [hcl e₀.1 e₀.2, hV']
          exact (InjOn.image_inter hinj (Γ.drawing.closure_subset_U e₀.2) Γ.drawing.V_subset_U).symm
        constructor
        · rintro ⟨_, _, _, hc⟩
          refine ⟨he', hx', hy', ?_⟩
          rw [hcap, hc, image_pair]
        · rintro ⟨_, _, _, hc'⟩
          refine ⟨e₀.2, x₀.2, y₀.2, ?_⟩
          rw [hcap, ← image_pair] at hc'
          have hsub1 : closure e₀.1 ∩ Γ.drawing.V ⊆ Γ.drawing.U :=
            inter_subset_right.trans Γ.drawing.V_subset_U
          have hsub2 : ({x₀.1, y₀.1} : Set S) ⊆ Γ.drawing.U := by
            rintro z (rfl | rfl)
            · exact Γ.drawing.V_subset_U x₀.2
            · exact Γ.drawing.V_subset_U y₀.2
          exact hinj.image_eq_image_iff hsub1 hsub2 |>.mp hc' }
  refine ⟨⟨D', iso'⟩, hU', hV', fun v => ?_⟩
  change f (Γ.iso.vertexEquiv v).1 = f (ν v.1)
  rw [hν v]

/-- Glue two `GraphDrawing`s on `G₁, G₂ ≤ G` whose drawings meet only inside `ν '' (V(G₁) ∩ V(G₂))`.
-/
theorem GraphDrawing.glue_edges {S : Type*} [TopologicalSpace S] {G G₁ G₂ : Graph α β}
    (hG₁ : G₁ ≤ G) (hG₂ : G₂ ≤ G)
    (hV_union : V(G₁) ∪ V(G₂) = V(G))
    (hE_union : E(G₁) ∪ E(G₂) = E(G))
    (hE_disj : Disjoint E(G₁) E(G₂))
    {ν : α → S} (hν_inj : InjOn ν V(G))
    (Γ₁ : GraphDrawing G₁ S) (Γ₂ : GraphDrawing G₂ S)
    (hν₁ : ∀ v : V(G₁), (Γ₁.iso.vertexEquiv v).1 = ν v.1)
    (hν₂ : ∀ v : V(G₂), (Γ₂.iso.vertexEquiv v).1 = ν v.1)
    (hmeet : Γ₁.drawing.U ∩ Γ₂.drawing.U ⊆ ν '' (V(G₁) ∩ V(G₂))) :
    ∃ Γ : GraphDrawing G S,
      Γ.drawing.U = Γ₁.drawing.U ∪ Γ₂.drawing.U ∧
      (∀ v : V(G), (Γ.iso.vertexEquiv v).1 = ν v.1) ∧
      (∀ e, graphDrawingEdgeSet Γ e =
        graphDrawingEdgeSet Γ₁ e ∪ graphDrawingEdgeSet Γ₂ e) := by
  classical
  have hV₁_eq : Γ₁.drawing.V = ν '' V(G₁) := drawing_V_eq_image Γ₁ hν₁
  have hV₂_eq : Γ₂.drawing.V = ν '' V(G₂) := drawing_V_eq_image Γ₂ hν₂
  have hmeet_V : Γ₁.drawing.U ∩ Γ₂.drawing.U ⊆ Γ₁.drawing.V ∩ Γ₂.drawing.V := by
    refine hmeet.trans ?_
    rw [hV₁_eq, hV₂_eq]
    exact image_inter_subset ν V(G₁) V(G₂)
  let D := Γ₁.drawing.glue Γ₂.drawing hmeet_V
  have hD_V : D.V = ν '' V(G) := by
    change Γ₁.drawing.V ∪ Γ₂.drawing.V = _
    rw [hV₁_eq, hV₂_eq, ← image_union, hV_union]
  have hD_E : D.E = Γ₁.drawing.E ∪ Γ₂.drawing.E := Drawing.glue_E hmeet_V
  have hsub₁ : Γ₁.drawing.IsSubdrawing D :=
    ⟨subset_union_left, hD_E.symm ▸ subset_union_left⟩
  have hsub₂ : Γ₂.drawing.IsSubdrawing D :=
    ⟨subset_union_right, hD_E.symm ▸ subset_union_right⟩
  have hdisj_DE : Disjoint Γ₁.drawing.E Γ₂.drawing.E := by
    rw [disjoint_left]
    intro a ha₁ ha₂
    obtain ⟨z, hz⟩ := ha₁.1
    have hz₁ : z ∈ Γ₁.drawing.U \ Γ₁.drawing.V := ha₁.2.1 hz
    have hz₂ : z ∈ Γ₂.drawing.U \ Γ₂.drawing.V := ha₂.2.1 hz
    exact hz₁.2 (hmeet_V ⟨hz₁.1, hz₂.1⟩).1
  let vFun : V(G) → D.V := fun v => ⟨ν v.1, hD_V ▸ ⟨v.1, v.2, rfl⟩⟩
  have hvFun_bij : Function.Bijective vFun :=
    ⟨fun v₁ v₂ h => Subtype.ext (hν_inj v₁.2 v₂.2 (congrArg Subtype.val h)),
     fun z => by
       have hz : z.1 ∈ ν '' V(G) := hD_V ▸ z.2
       obtain ⟨x, hx, hnx⟩ := hz
       exact ⟨⟨x, hx⟩, Subtype.ext hnx⟩⟩
  let vEquiv : V(G) ≃ D.V := Equiv.ofBijective vFun hvFun_bij
  have hvEquiv_val : ∀ v : V(G), (vEquiv v).1 = ν v.1 := fun _ => rfl
  have he₂_of_not_1 : ∀ e : E(G), e.1 ∉ E(G₁) → e.1 ∈ E(G₂) := fun e he₁ => by
    have : e.1 ∈ E(G₁) ∪ E(G₂) := hE_union.symm ▸ e.2
    exact this.resolve_left he₁
  let eFun : E(G) → D.E := fun e =>
    if he₁ : e.1 ∈ E(G₁) then
      ⟨(Γ₁.iso.edgeEquiv ⟨e.1, he₁⟩).1, hD_E ▸ Or.inl (Γ₁.iso.edgeEquiv ⟨e.1, he₁⟩).2⟩
    else
      ⟨(Γ₂.iso.edgeEquiv ⟨e.1, he₂_of_not_1 e he₁⟩).1,
       hD_E ▸ Or.inr (Γ₂.iso.edgeEquiv ⟨e.1, he₂_of_not_1 e he₁⟩).2⟩
  have heFun_bij : Function.Bijective eFun := by
    refine ⟨fun e₁ e₂ heq => ?_, fun a => ?_⟩
    · have hval := congrArg Subtype.val heq
      dsimp [eFun] at hval
      split_ifs at hval with h1 h2 h2
      · have h := Γ₁.iso.edgeEquiv.injective (Subtype.ext hval)
        have h' : e₁.1 = e₂.1 := congrArg (fun x : E(G₁) => x.1) h
        exact Subtype.ext h'
      · exfalso
        have ha₁ : (Γ₁.iso.edgeEquiv ⟨e₁.1, h1⟩).1 ∈ Γ₁.drawing.E :=
          (Γ₁.iso.edgeEquiv ⟨e₁.1, h1⟩).2
        have ha₂ : (Γ₁.iso.edgeEquiv ⟨e₁.1, h1⟩).1 ∈ Γ₂.drawing.E := by
          rw [hval]
          exact (Γ₂.iso.edgeEquiv ⟨e₂.1, he₂_of_not_1 e₂ h2⟩).2
        exact disjoint_left.mp hdisj_DE ha₁ ha₂
      · exfalso
        have ha₁ : (Γ₁.iso.edgeEquiv ⟨e₂.1, h2⟩).1 ∈ Γ₁.drawing.E :=
          (Γ₁.iso.edgeEquiv ⟨e₂.1, h2⟩).2
        have ha₂ : (Γ₁.iso.edgeEquiv ⟨e₂.1, h2⟩).1 ∈ Γ₂.drawing.E := by
          rw [← hval]
          exact (Γ₂.iso.edgeEquiv ⟨e₁.1, he₂_of_not_1 e₁ h1⟩).2
        exact disjoint_left.mp hdisj_DE ha₁ ha₂
      · have h := Γ₂.iso.edgeEquiv.injective (Subtype.ext hval)
        have h' : e₁.1 = e₂.1 := congrArg (fun x : E(G₂) => x.1) h
        exact Subtype.ext h'
    · have ha_union : a.1 ∈ Γ₁.drawing.E ∪ Γ₂.drawing.E := hD_E ▸ a.2
      rcases ha_union with ha₁ | ha₂
      · let e₁ := Γ₁.iso.edgeEquiv.symm ⟨a.1, ha₁⟩
        have he₁_1 : e₁.1 ∈ E(G₁) := e₁.2
        refine ⟨⟨e₁.1, hG₁.edgeSet_mono he₁_1⟩, ?_⟩
        apply Subtype.ext
        dsimp [eFun]
        split_ifs
        exact congrArg (fun x : Γ₁.drawing.E => x.1)
          (Γ₁.iso.edgeEquiv.apply_symm_apply ⟨a.1, ha₁⟩)
      · let e₂ := Γ₂.iso.edgeEquiv.symm ⟨a.1, ha₂⟩
        have he₂_not_1 : e₂.1 ∉ E(G₁) := disjoint_right.mp hE_disj e₂.2
        refine ⟨⟨e₂.1, hG₂.edgeSet_mono e₂.2⟩, ?_⟩
        apply Subtype.ext
        dsimp [eFun]
        split_ifs
        exact congrArg (fun x : Γ₂.drawing.E => x.1)
          (Γ₂.iso.edgeEquiv.apply_symm_apply ⟨a.1, ha₂⟩)
  let eEquiv : E(G) ≃ D.E := Equiv.ofBijective eFun heFun_bij
  have heEquiv_val : ∀ e : E(G), (eEquiv e).1 = (eFun e).1 := fun _ => rfl
  let iso : Iso G D.toGraph :=
    { vertexEquiv := vEquiv
      edgeEquiv := eEquiv
      isLink_iff := fun {e x y} => by
        change G.IsLink e.1 x.1 y.1 ↔ D.toGraph.IsLink (eEquiv e).1 (vEquiv x).1 (vEquiv y).1
        rw [heEquiv_val, hvEquiv_val, hvEquiv_val]
        dsimp [eFun]
        split_ifs with he₁
        · have ha₁ : (Γ₁.iso.edgeEquiv ⟨e.1, he₁⟩).1 ∈ Γ₁.drawing.E :=
            (Γ₁.iso.edgeEquiv ⟨e.1, he₁⟩).2
          rw [← hsub₁.isLink_iff ha₁]
          constructor
          · intro hlinkG
            have hlink₁ : G₁.IsLink e.1 x.1 y.1 := (hG₁.isLink_iff he₁).mpr hlinkG
            have hx₁ : x.1 ∈ V(G₁) := hlink₁.left_mem
            have hy₁ : y.1 ∈ V(G₁) := hlink₁.right_mem
            have hlinkD' := (Γ₁.iso.isLink_iff (e := ⟨e.1, he₁⟩) (x := ⟨x.1, hx₁⟩)
              (y := ⟨y.1, hy₁⟩)).mp hlink₁
            change Γ₁.drawing.toGraph.IsLink (Γ₁.iso.edgeEquiv ⟨e.1, he₁⟩).1
              (Γ₁.iso.vertexEquiv ⟨x.1, hx₁⟩).1 (Γ₁.iso.vertexEquiv ⟨y.1, hy₁⟩).1 at hlinkD'
            rwa [hν₁ ⟨x.1, hx₁⟩, hν₁ ⟨y.1, hy₁⟩] at hlinkD'
          · intro hlinkD
            have hxV₁ : ν x.1 ∈ Γ₁.drawing.V := hlinkD.2.1
            have hyV₁ : ν y.1 ∈ Γ₁.drawing.V := hlinkD.2.2.1
            rw [hV₁_eq] at hxV₁ hyV₁
            obtain ⟨x', hx'₁, hx'_eq⟩ := hxV₁
            obtain ⟨y', hy'₁, hy'_eq⟩ := hyV₁
            have hx_eq : x' = x.1 := hν_inj (hG₁.vertexSet_mono hx'₁) x.2 hx'_eq
            have hy_eq : y' = y.1 := hν_inj (hG₁.vertexSet_mono hy'₁) y.2 hy'_eq
            have hx₁ : x.1 ∈ V(G₁) := hx_eq ▸ hx'₁
            have hy₁ : y.1 ∈ V(G₁) := hy_eq ▸ hy'₁
            have hlinkD' : Γ₁.drawing.toGraph.IsLink (Γ₁.iso.edgeEquiv ⟨e.1, he₁⟩).1
                (Γ₁.iso.vertexEquiv ⟨x.1, hx₁⟩).1 (Γ₁.iso.vertexEquiv ⟨y.1, hy₁⟩).1 := by
              rwa [hν₁ ⟨x.1, hx₁⟩, hν₁ ⟨y.1, hy₁⟩]
            exact ((Γ₁.iso.isLink_iff (e := ⟨e.1, he₁⟩) (x := ⟨x.1, hx₁⟩)
              (y := ⟨y.1, hy₁⟩)).mpr hlinkD').mono hG₁
        · have he₂ : e.1 ∈ E(G₂) := he₂_of_not_1 e he₁
          have ha₂ : (Γ₂.iso.edgeEquiv ⟨e.1, he₂⟩).1 ∈ Γ₂.drawing.E :=
            (Γ₂.iso.edgeEquiv ⟨e.1, he₂⟩).2
          rw [← hsub₂.isLink_iff ha₂]
          constructor
          · intro hlinkG
            have hlink₂ : G₂.IsLink e.1 x.1 y.1 := (hG₂.isLink_iff he₂).mpr hlinkG
            have hx₂ : x.1 ∈ V(G₂) := hlink₂.left_mem
            have hy₂ : y.1 ∈ V(G₂) := hlink₂.right_mem
            have hlinkD' := (Γ₂.iso.isLink_iff (e := ⟨e.1, he₂⟩) (x := ⟨x.1, hx₂⟩)
              (y := ⟨y.1, hy₂⟩)).mp hlink₂
            change Γ₂.drawing.toGraph.IsLink (Γ₂.iso.edgeEquiv ⟨e.1, he₂⟩).1
              (Γ₂.iso.vertexEquiv ⟨x.1, hx₂⟩).1 (Γ₂.iso.vertexEquiv ⟨y.1, hy₂⟩).1 at hlinkD'
            rwa [hν₂ ⟨x.1, hx₂⟩, hν₂ ⟨y.1, hy₂⟩] at hlinkD'
          · intro hlinkD
            have hxV₂ : ν x.1 ∈ Γ₂.drawing.V := hlinkD.2.1
            have hyV₂ : ν y.1 ∈ Γ₂.drawing.V := hlinkD.2.2.1
            rw [hV₂_eq] at hxV₂ hyV₂
            obtain ⟨x', hx'₂, hx'_eq⟩ := hxV₂
            obtain ⟨y', hy'₂, hy'_eq⟩ := hyV₂
            have hx_eq : x' = x.1 := hν_inj (hG₂.vertexSet_mono hx'₂) x.2 hx'_eq
            have hy_eq : y' = y.1 := hν_inj (hG₂.vertexSet_mono hy'₂) y.2 hy'_eq
            have hx₂ : x.1 ∈ V(G₂) := hx_eq ▸ hx'₂
            have hy₂ : y.1 ∈ V(G₂) := hy_eq ▸ hy'₂
            have hlinkD' : Γ₂.drawing.toGraph.IsLink (Γ₂.iso.edgeEquiv ⟨e.1, he₂⟩).1
                (Γ₂.iso.vertexEquiv ⟨x.1, hx₂⟩).1 (Γ₂.iso.vertexEquiv ⟨y.1, hy₂⟩).1 := by
              rwa [hν₂ ⟨x.1, hx₂⟩, hν₂ ⟨y.1, hy₂⟩]
            exact ((Γ₂.iso.isLink_iff (e := ⟨e.1, he₂⟩) (x := ⟨x.1, hx₂⟩)
              (y := ⟨y.1, hy₂⟩)).mpr hlinkD').mono hG₂ }
  refine ⟨⟨D, iso⟩, rfl, hvEquiv_val, fun e => ?_⟩
  ext x
  simp only [graphDrawingEdgeSet, mem_iUnion, mem_union]
  constructor
  · rintro ⟨he, hx⟩
    have hx' : x ∈ (eFun ⟨e, he⟩).1 := hx
    dsimp [eFun] at hx'
    split_ifs at hx' with he₁
    · exact Or.inl ⟨he₁, hx'⟩
    · exact Or.inr ⟨he₂_of_not_1 ⟨e, he⟩ he₁, hx'⟩
  · rintro (⟨he₁, hx⟩ | ⟨he₂, hx⟩)
    · refine ⟨hG₁.edgeSet_mono he₁, ?_⟩
      change x ∈ (eFun ⟨e, hG₁.edgeSet_mono he₁⟩).1
      dsimp [eFun]
      rw [dite_eq_left_of_eq_true (eq_true he₁)]
      exact hx
    · have hn : e ∉ E(G₁) := disjoint_right.mp hE_disj he₂
      refine ⟨hG₂.edgeSet_mono he₂, ?_⟩
      change x ∈ (eFun ⟨e, hG₂.edgeSet_mono he₂⟩).1
      dsimp [eFun]
      rw [dite_eq_right_of_eq_false (eq_false hn)]
      exact hx

/-- Gluing two drawings along common vertices. -/
theorem GraphDrawing.glue {S : Type*} [TopologicalSpace S] {G G₁ G₂ : Graph α β}
    (hG₁ : G₁ ≤ G) (hG₂ : G₂ ≤ G)
    (hV_union : V(G₁) ∪ V(G₂) = V(G))
    (hE_union : E(G₁) ∪ E(G₂) = E(G))
    (hE_disj : Disjoint E(G₁) E(G₂))
    {ν : α → S} (hν_inj : InjOn ν V(G))
    (Γ₁ : GraphDrawing G₁ S) (Γ₂ : GraphDrawing G₂ S)
    (hν₁ : ∀ v : V(G₁), (Γ₁.iso.vertexEquiv v).1 = ν v.1)
    (hν₂ : ∀ v : V(G₂), (Γ₂.iso.vertexEquiv v).1 = ν v.1)
    (hmeet : Γ₁.drawing.U ∩ Γ₂.drawing.U ⊆ ν '' (V(G₁) ∩ V(G₂))) :
    ∃ Γ : GraphDrawing G S,
      Γ.drawing.U = Γ₁.drawing.U ∪ Γ₂.drawing.U ∧
      ∀ v : V(G), (Γ.iso.vertexEquiv v).1 = ν v.1 := by
  obtain ⟨Γ, h₁, h₂, -⟩ := GraphDrawing.glue_edges hG₁ hG₂ hV_union hE_union hE_disj hν_inj Γ₁ Γ₂
    hν₁ hν₂ hmeet
  exact ⟨Γ, h₁, h₂⟩

/-- Construct a `GraphDrawing` for an edgeless finite graph `G` from an injection `ν` on `V(G)`. -/
theorem GraphDrawing.of_edgeless {S : Type*} [TopologicalSpace S] [T1Space S] {G : Graph α β}
    (hV_fin : V(G).Finite) (hE : E(G) = ∅) {ν : α → S} (hν_inj : InjOn ν V(G)) :
    ∃ Γ : GraphDrawing G S,
      Γ.drawing.U = ν '' V(G) ∧
      ∀ v : V(G), (Γ.iso.vertexEquiv v).1 = ν v.1 := by
  let D := pointsDrawing (hV_fin.image ν)
  have hD_E : D.E = ∅ := by
    refine Subset.antisymm (fun C hC => ?_) (empty_subset _)
    rcases hC with ⟨⟨x, hx⟩, hsub, -⟩
    exact (hsub hx).2 (hsub hx).1
  let vEquiv : V(G) ≃ D.V := Equiv.Set.imageOfInjOn ν V(G) hν_inj
  have h_no_e : ∀ e : E(G), False := fun ⟨x, hx⟩ => by rw [hE] at hx; exact hx
  have h_no_a : ∀ a : D.E, False := fun ⟨x, hx⟩ => by rw [hD_E] at hx; exact hx
  let eEquiv : E(G) ≃ D.E :=
    { toFun := fun e => (h_no_e e).elim
      invFun := fun a => (h_no_a a).elim
      left_inv := fun e => (h_no_e e).elim
      right_inv := fun a => (h_no_a a).elim }
  let iso : Iso G D.toGraph :=
    { vertexEquiv := vEquiv
      edgeEquiv := eEquiv
      isLink_iff := fun {e _ _} => (h_no_e e).elim }
  exact ⟨⟨D, iso⟩, rfl, fun _ => rfl⟩

/-- Construct a `GraphDrawing` for a single non-loop edge `e₀` between `u ≠ v` along a line `K`. -/
theorem GraphDrawing.of_single_edge {S : Type*} [TopologicalSpace S] [T2Space S] {G : Graph α β}
    {u v : α} {e₀ : β} (hV : V(G) = {u, v}) (hE : E(G) = {e₀}) (hlink : G.IsLink e₀ u v)
    {ν : α → S} (hν_ne : ν u ≠ ν v) {K : Set S} (hK : IsLineWithEnds K (ν u) (ν v)) :
    ∃ Γ : GraphDrawing G S,
      Γ.drawing.U = K ∧
      ∀ w : V(G), (Γ.iso.vertexEquiv w).1 = ν w.1 := by
  have huv : u ≠ v := fun h => hν_ne (congrArg ν h)
  have hν_inj : InjOn ν V(G) := by
    rw [hV]
    rintro x (rfl | rfl) y (rfl | rfl) hxy
    · rfl
    · exact (hν_ne hxy).elim
    · exact (hν_ne hxy.symm).elim
    · rfl
  let D := lineDrawing hK hν_ne
  have hD_V : D.V = ν '' V(G) := by
    change {ν u, ν v} = _
    rw [hV, image_pair]
  have hD_E : D.E = {K \ {ν u, ν v}} := lineDrawing_E hK hν_ne
  let vFun : V(G) → D.V := fun w => ⟨ν w.1, hD_V ▸ ⟨w.1, w.2, rfl⟩⟩
  have hvFun_bij : Function.Bijective vFun :=
    ⟨fun w₁ w₂ h => Subtype.ext (hν_inj w₁.2 w₂.2 (congrArg Subtype.val h)),
     fun z => by
       have hz : z.1 ∈ ν '' V(G) := hD_V ▸ z.2
       obtain ⟨x, hx, hnx⟩ := hz
       exact ⟨⟨x, hx⟩, Subtype.ext hnx⟩⟩
  let vEquiv : V(G) ≃ D.V := Equiv.ofBijective vFun hvFun_bij
  have hvEquiv_val : ∀ w : V(G), (vEquiv w).1 = ν w.1 := fun _ => rfl
  let eEquiv : E(G) ≃ D.E :=
    { toFun := fun _ => ⟨K \ {ν u, ν v}, hD_E ▸ mem_singleton _⟩
      invFun := fun _ => ⟨e₀, hE ▸ mem_singleton e₀⟩
      left_inv := fun e => Subtype.ext (mem_singleton_iff.mp (hE ▸ e.2)).symm
      right_inv := fun a => Subtype.ext (mem_singleton_iff.mp (hD_E ▸ a.2)).symm }
  have hcl_inter : closure (K \ {ν u, ν v}) ∩ D.V = {ν u, ν v} := by
    rw [closure_sdiff_pair hK]
    exact inter_eq_right.mpr D.V_subset_U
  let iso : Iso G D.toGraph :=
    { vertexEquiv := vEquiv
      edgeEquiv := eEquiv
      isLink_iff := fun {e x y} => by
        change G.IsLink e.1 x.1 y.1 ↔ D.toGraph.IsLink (K \ {ν u, ν v}) (vEquiv x).1 (vEquiv y).1
        rw [hvEquiv_val, hvEquiv_val]
        have he_eq : e.1 = e₀ := mem_singleton_iff.mp (hE ▸ e.2)
        rw [he_eq]
        constructor
        · intro hxy_link
          refine ⟨hD_E ▸ mem_singleton _, (vEquiv x).2, (vEquiv y).2, ?_⟩
          rw [hcl_inter]
          rcases hxy_link.eq_and_eq_or_eq_and_eq hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · exact pair_comm _ _
        · rintro ⟨_, _, _, hc⟩
          rw [hcl_inter] at hc
          have hx_uv : x.1 = u ∨ x.1 = v := by simpa [hV] using x.2
          have hy_uv : y.1 = u ∨ y.1 = v := by simpa [hV] using y.2
          rcases hx_uv with hxu | hxv <;> rcases hy_uv with hyu | hyv
          · exfalso
            rw [hxu, hyu, pair_eq_singleton] at hc
            have hνv : ν v ∈ ({ν u} : Set S) := hc ▸ by simp
            exact hν_ne (mem_singleton_iff.mp hνv).symm
          · exact hxu ▸ hyv ▸ hlink
          · exact hxv ▸ hyu ▸ hlink.symm
          · exfalso
            rw [hxv, hyv, pair_eq_singleton] at hc
            have hνu : ν u ∈ ({ν v} : Set S) := hc ▸ by simp
            exact hν_ne (mem_singleton_iff.mp hνu) }
  exact ⟨⟨D, iso⟩, rfl, hvEquiv_val⟩

/-- Construct a `GraphDrawing` for a single loop `e₀` at `u` along an `O`-arc `F` containing `ν u`.
-/
theorem GraphDrawing.of_single_loop {S : Type*} [TopologicalSpace S] [T2Space S] {G : Graph α β}
    {u : α} {e₀ : β} (hV : V(G) = {u}) (hE : E(G) = {e₀}) (hlink : G.IsLink e₀ u u)
    {ν : α → S} {F : Set S} (hF : IsOArc F) (hνu : ν u ∈ F) :
    ∃ Γ : GraphDrawing G S,
      Γ.drawing.U = F ∧
      ∀ w : V(G), (Γ.iso.vertexEquiv w).1 = ν w.1 := by
  obtain ⟨D, hDU, hDV⟩ := exists_loop_drawing hF hνu
  obtain ⟨p, hp, h0, h2, hper, himg, hr⟩ := exists_oArc_par hF hνu
  have hpos : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have hsd : F \ {ν u} = p '' Ioo 0 (2 * Real.pi) := by
    ext y
    constructor
    · rintro ⟨hy, hya⟩
      rw [← himg] at hy
      obtain ⟨s, hs, rfl⟩ := hy
      refine ⟨s, ⟨lt_of_le_of_ne hs.1 fun h => hya ?_, hs.2⟩, rfl⟩
      rw [← h, h0]
      exact mem_singleton (ν u)
    · rintro ⟨s, hs, rfl⟩
      refine ⟨hr ⟨s, rfl⟩, fun h => ?_⟩
      obtain ⟨m, hm⟩ := hper s 0 (h.trans h0.symm)
      rw [zero_add] at hm
      have h₁ : (0 : ℝ) < m := by by_contra hc; push Not at hc; nlinarith [hs.1]
      have h₂ : (m : ℝ) < 1 := by by_contra hc; push Not at hc; nlinarith [hs.2]
      have h₃ : (0 : ℤ) < m := by exact_mod_cast h₁
      have h₄ : m < (1 : ℤ) := by exact_mod_cast h₂
      omega
  have hpc : IsPathConnected (F \ {ν u}) := by
    rw [hsd]
    exact ((convex_Ioo _ _).isPathConnected (nonempty_Ioo.mpr hpos)).image hp
  have hD_E : D.E = {F \ {ν u}} := by
    change arcComponentsIn (D.U \ D.V) = _
    rw [hDU, hDV]
    refine Subset.antisymm (fun C ⟨_, hsub, _, hmax⟩ => ?_) ?_
    · rw [mem_singleton_iff]
      exact (hmax _ Subset.rfl hpc hsub).symm
    · rw [singleton_subset_iff]
      exact ⟨hpc.nonempty, Subset.rfl, hpc, fun C hC _ hsub => Subset.antisymm hC hsub⟩
  let vEquiv : V(G) ≃ D.V :=
    { toFun := fun _ => ⟨ν u, hDV ▸ mem_singleton (ν u)⟩
      invFun := fun _ => ⟨u, hV ▸ mem_singleton u⟩
      left_inv := fun w => Subtype.ext (mem_singleton_iff.mp (hV ▸ w.2)).symm
      right_inv := fun z => Subtype.ext (mem_singleton_iff.mp (hDV ▸ z.2)).symm }
  have hvEquiv_val : ∀ w : V(G), (vEquiv w).1 = ν w.1 := fun w => by
    have hw : w.1 = u := mem_singleton_iff.mp (hV ▸ w.2)
    simp [vEquiv, hw]
  let eEquiv : E(G) ≃ D.E :=
    { toFun := fun _ => ⟨F \ {ν u}, hD_E ▸ mem_singleton _⟩
      invFun := fun _ => ⟨e₀, hE ▸ mem_singleton e₀⟩
      left_inv := fun e => Subtype.ext (mem_singleton_iff.mp (hE ▸ e.2)).symm
      right_inv := fun a => Subtype.ext (mem_singleton_iff.mp (hD_E ▸ a.2)).symm }
  have hcl_inter : closure (F \ {ν u}) ∩ D.V = {ν u} := by
    have he_mem : F \ {ν u} ∈ D.E := hD_E ▸ mem_singleton _
    rcases D.edge_cond (F \ {ν u}) he_mem with ⟨a, b, hab, hc, _⟩ | ⟨a, hc, _⟩
    · exfalso
      have ha_in : a ∈ closure (F \ {ν u}) ∩ D.V := hc ▸ by simp
      have hb_in : b ∈ closure (F \ {ν u}) ∩ D.V := hc ▸ by simp
      have ha : a = ν u := mem_singleton_iff.mp (hDV ▸ ha_in.2)
      have hb : b = ν u := mem_singleton_iff.mp (hDV ▸ hb_in.2)
      exact hab (ha.trans hb.symm)
    · have ha_in : a ∈ closure (F \ {ν u}) ∩ D.V := hc ▸ by simp
      have ha : a = ν u := mem_singleton_iff.mp (hDV ▸ ha_in.2)
      exact ha ▸ hc
  let iso : Iso G D.toGraph :=
    { vertexEquiv := vEquiv
      edgeEquiv := eEquiv
      isLink_iff := fun {e x y} => by
        change G.IsLink e.1 x.1 y.1 ↔ D.toGraph.IsLink (F \ {ν u}) (vEquiv x).1 (vEquiv y).1
        have he_eq : e.1 = e₀ := mem_singleton_iff.mp (hE ▸ e.2)
        have hx_eq : x.1 = u := mem_singleton_iff.mp (hV ▸ x.2)
        have hy_eq : y.1 = u := mem_singleton_iff.mp (hV ▸ y.2)
        rw [hvEquiv_val, hvEquiv_val, he_eq, hx_eq, hy_eq]
        constructor
        · intro _
          refine ⟨hD_E ▸ mem_singleton _, hDV ▸ mem_singleton _, hDV ▸ mem_singleton _, ?_⟩
          rw [pair_eq_singleton]
          exact hcl_inter
        · intro _
          exact hlink }
  exact ⟨⟨D, iso⟩, hDU, hvEquiv_val⟩

/-! ### Module 3: Loop Circles in the Closed Unit Disc and Base Case Drawing -/

/-- A small circle in `ClosedUnitDisc` tangent to `UnitCircle` at `p ∈ sphere 0 1` of radius `ρ`. -/
def loopCircle (p : ℂ) (ρ : ℝ) : Set ℂ :=
  range (fun w : Circle => (1 - (ρ : ℂ)) * p + (ρ : ℂ) * (w : ℂ))

theorem isOArc_loopCircle (p : ℂ) {ρ : ℝ} (hρ : 0 < ρ) : IsOArc (loopCircle p ρ) := by
  let g : Circle → ℂ := fun w => (1 - (ρ : ℂ)) * p + (ρ : ℂ) * (w : ℂ)
  have hg_cont : Continuous g := by fun_prop
  have hg_inj : Function.Injective g := by
    intro w₁ w₂ heq
    have hmul : (ρ : ℂ) * (w₁ : ℂ) = (ρ : ℂ) * (w₂ : ℂ) := add_left_cancel heq
    have hρ_ne : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ.ne'
    exact Subtype.ext (mul_left_cancel₀ hρ_ne hmul)
  have hemb := hg_cont.isClosedEmbedding hg_inj
  exact ⟨hemb.isEmbedding.toHomeomorph⟩

theorem mem_loopCircle_self {p : ℂ} (hp : p ∈ Metric.sphere (0 : ℂ) 1) (ρ : ℝ) :
    p ∈ loopCircle p ρ := by
  refine ⟨⟨p, hp⟩, ?_⟩
  change (1 - (ρ : ℂ)) * p + (ρ : ℂ) * p = p
  ring

private theorem normSq_loopCircle_pt (p w : ℂ) (ρ : ℝ) :
    Complex.normSq ((1 - (ρ : ℂ)) * p + (ρ : ℂ) * w) =
      (1 - ρ) * Complex.normSq p + ρ * Complex.normSq w -
        ρ * (1 - ρ) * Complex.normSq (w - p) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im]
  ring

private theorem loopCircle_implicit_eq (p w : ℂ) (ρ : ℝ) :
    let z := (1 - (ρ : ℂ)) * p + (ρ : ℂ) * w
    Complex.normSq (z - p) + 2 * ρ * ((z.re - p.re) * p.re + (z.im - p.im) * p.im) =
      ρ ^ 2 * (Complex.normSq w - Complex.normSq p) := by
  intro z
  change Complex.normSq (((1 - (ρ : ℂ)) * p + (ρ : ℂ) * w) - p) +
    2 * ρ * ((((1 - (ρ : ℂ)) * p + (ρ : ℂ) * w).re - p.re) * p.re +
      (((1 - (ρ : ℂ)) * p + (ρ : ℂ) * w).im - p.im) * p.im) =
    ρ ^ 2 * (Complex.normSq w - Complex.normSq p)
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im]
  ring

theorem loopCircle_subset_closedBall {p : ℂ} (hp : p ∈ Metric.sphere (0 : ℂ) 1)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    loopCircle p ρ ⊆ Metric.closedBall (0 : ℂ) 1 := by
  rintro z ⟨w, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hp_norm : ‖p‖ = 1 := by simpa using hp
  have hw_norm : ‖(w : ℂ)‖ = 1 := by simp
  calc
    ‖(1 - (ρ : ℂ)) * p + (ρ : ℂ) * (w : ℂ)‖
      ≤ ‖(1 - (ρ : ℂ)) * p‖ + ‖(ρ : ℂ) * (w : ℂ)‖ := norm_add_le _ _
    _ = ‖(1 - (ρ : ℂ))‖ * ‖p‖ + ‖(ρ : ℂ)‖ * ‖(w : ℂ)‖ := by rw [norm_mul, norm_mul]
    _ = |1 - ρ| * 1 + |ρ| * 1 := by
      rw [hp_norm, hw_norm, ← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    _ = (1 - ρ) + ρ := by
      rw [abs_of_pos (by linarith), abs_of_pos hρ0, mul_one, mul_one]
    _ = 1 := by ring

theorem loopCircle_inter_sphere {p : ℂ} (hp : p ∈ Metric.sphere (0 : ℂ) 1)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    loopCircle p ρ ∩ Metric.sphere (0 : ℂ) 1 = {p} := by
  refine Subset.antisymm (fun z ⟨⟨w, hw⟩, hz_sph⟩ => ?_) (singleton_subset_iff.mpr
    ⟨mem_loopCircle_self hp ρ, hp⟩)
  rw [mem_singleton_iff]
  change (1 - (ρ : ℂ)) * p + (ρ : ℂ) * (w : ℂ) = z at hw
  have hp_sq : Complex.normSq p = 1 := by
    have hp1 : ‖p‖ = 1 := by simpa using hp
    rw [Complex.normSq_eq_norm_sq, hp1, one_pow]
  have hw_sq : Complex.normSq (w : ℂ) = 1 := by
    have hw1 : ‖(w : ℂ)‖ = 1 := by simp
    rw [Complex.normSq_eq_norm_sq, hw1, one_pow]
  have hz_sq : Complex.normSq z = 1 := by
    have hz1 : ‖z‖ = 1 := by simpa using hz_sph
    rw [Complex.normSq_eq_norm_sq, hz1, one_pow]
  have hId := normSq_loopCircle_pt p (w : ℂ) ρ
  rw [hw, hp_sq, hw_sq, hz_sq] at hId
  have hsub_zero : Complex.normSq ((w : ℂ) - p) = 0 := by
    have hpos : 0 < ρ * (1 - ρ) := mul_pos hρ0 (by linarith)
    nlinarith
  have hwp : (w : ℂ) = p := sub_eq_zero.mp (Complex.normSq_eq_zero.mp hsub_zero)
  rw [← hw, hwp]
  ring

theorem loopCircle_inter_loopCircle_same {p : ℂ} (hp : p ∈ Metric.sphere (0 : ℂ) 1)
    {ρ₁ ρ₂ : ℝ} (hne : ρ₁ ≠ ρ₂) :
    loopCircle p ρ₁ ∩ loopCircle p ρ₂ = {p} := by
  refine Subset.antisymm (fun z ⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩⟩ => ?_) (singleton_subset_iff.mpr
    ⟨mem_loopCircle_self hp ρ₁, mem_loopCircle_self hp ρ₂⟩)
  rw [mem_singleton_iff]
  change (1 - (ρ₁ : ℂ)) * p + (ρ₁ : ℂ) * (w₁ : ℂ) = z at hw₁
  change (1 - (ρ₂ : ℂ)) * p + (ρ₂ : ℂ) * (w₂ : ℂ) = z at hw₂
  have hp_sq : Complex.normSq p = 1 := by
    have hp1 : ‖p‖ = 1 := by simpa using hp
    rw [Complex.normSq_eq_norm_sq, hp1, one_pow]
  have hw₁_sq : Complex.normSq (w₁ : ℂ) = 1 := by
    have hw1 : ‖(w₁ : ℂ)‖ = 1 := by simp
    rw [Complex.normSq_eq_norm_sq, hw1, one_pow]
  have hw₂_sq : Complex.normSq (w₂ : ℂ) = 1 := by
    have hw2 : ‖(w₂ : ℂ)‖ = 1 := by simp
    rw [Complex.normSq_eq_norm_sq, hw2, one_pow]
  have h1 := loopCircle_implicit_eq p (w₁ : ℂ) ρ₁
  dsimp only at h1
  rw [hw₁, hw₁_sq, hp_sq, sub_self, mul_zero] at h1
  have h2 := loopCircle_implicit_eq p (w₂ : ℂ) ρ₂
  dsimp only at h2
  rw [hw₂, hw₂_sq, hp_sq, sub_self, mul_zero] at h2
  have hdot : (z.re - p.re) * p.re + (z.im - p.im) * p.im = 0 := by
    have hdiff : 2 * (ρ₁ - ρ₂) * ((z.re - p.re) * p.re + (z.im - p.im) * p.im) = 0 := by
      linarith
    rcases mul_eq_zero.mp hdiff with hρ | hd
    · exfalso; apply hne; linarith
    · exact hd
  have hnorm_zero : Complex.normSq (z - p) = 0 := by
    rw [hdot, mul_zero, add_zero] at h1
    exact h1
  exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp hnorm_zero)

theorem norm_sub_le_two_mul_of_mem_loopCircle {p z : ℂ} (hp : p ∈ Metric.sphere (0 : ℂ) 1)
    {ρ : ℝ} (hρ : 0 < ρ) (hz : z ∈ loopCircle p ρ) :
    ‖z - p‖ ≤ 2 * ρ := by
  rcases hz with ⟨w, rfl⟩
  have hsub : (1 - (ρ : ℂ)) * p + (ρ : ℂ) * (w : ℂ) - p = (ρ : ℂ) * ((w : ℂ) - p) := by ring
  rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
  have hp_norm : ‖p‖ = 1 := by simpa using hp
  have hw_norm : ‖(w : ℂ)‖ = 1 := by simp
  have hle : ‖(w : ℂ) - p‖ ≤ 2 := by
    calc ‖(w : ℂ) - p‖ ≤ ‖(w : ℂ)‖ + ‖p‖ := norm_sub_le _ _
      _ = 2 := by rw [hw_norm, hp_norm]; norm_num
  nlinarith

theorem loopCircle_disjoint_of_dist {p q : ℂ}
    (hp : p ∈ Metric.sphere (0 : ℂ) 1) (hq : q ∈ Metric.sphere (0 : ℂ) 1)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) (hdist : 2 * ρ₁ + 2 * ρ₂ < ‖p - q‖) :
    loopCircle p ρ₁ ∩ loopCircle q ρ₂ = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun z ⟨hz₁, hz₂⟩ => ?_
  have h1 := norm_sub_le_two_mul_of_mem_loopCircle hp hρ₁ hz₁
  have h2 := norm_sub_le_two_mul_of_mem_loopCircle hq hρ₂ hz₂
  have htri : ‖p - q‖ ≤ ‖z - p‖ + ‖z - q‖ := by
    calc ‖p - q‖ = ‖(p - z) + (z - q)‖ := by congr 1; ring
      _ ≤ ‖p - z‖ + ‖z - q‖ := norm_add_le _ _
      _ = ‖z - p‖ + ‖z - q‖ := by rw [norm_sub_rev]
  linarith

/-- For any finite set of vertices mapped injectively into `ℂ`, there exists `0 < δ < 1 / 4`
such that distinct vertices are at distance strictly greater than `4 * δ`. -/
theorem exists_pos_delta_lt_dist {V : Set α} (hV : V.Finite) {ν : α → ℂ} (hν : InjOn ν V) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧ ∀ u ∈ V, ∀ v ∈ V, u ≠ v → 4 * δ < ‖ν u - ν v‖ := by
  have hP_fin : {p : α × α | p.1 ∈ V ∧ p.2 ∈ V ∧ p.1 ≠ p.2}.Finite :=
    (hV.prod hV).subset (fun _ hp => ⟨hp.1, hp.2.1⟩)
  suffices ∀ P : Set (α × α), P.Finite → (∀ p ∈ P, p.1 ∈ V ∧ p.2 ∈ V ∧ p.1 ≠ p.2) →
      ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧ ∀ p ∈ P, 4 * δ < ‖ν p.1 - ν p.2‖ by
    obtain ⟨δ, hδ0, hδ1, hδ⟩ := this _ hP_fin (fun _ hp => hp)
    exact ⟨δ, hδ0, hδ1, fun u hu v hv huv => hδ (u, v) ⟨hu, hv, huv⟩⟩
  intro P hP
  refine Set.Finite.induction_on P hP ?_ ?_
  · intro _
    exact ⟨1 / 8, by norm_num, by norm_num, fun _ hp => False.elim hp⟩
  · intro a s _ _ ih hsub
    obtain ⟨δ₀, hδ₀_pos, hδ₀_lt, hδ₀⟩ := ih (fun p hp => hsub p (mem_insert_of_mem a hp))
    have ha_mem := hsub a (mem_insert a s)
    have hne : ν a.1 ≠ ν a.2 := fun heq => ha_mem.2.2 (hν ha_mem.1 ha_mem.2.1 heq)
    have hnorm_pos : 0 < ‖ν a.1 - ν a.2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    let δ := min δ₀ (‖ν a.1 - ν a.2‖ / 8)
    refine ⟨δ, lt_min hδ₀_pos (by linarith), lt_of_le_of_lt (min_le_left _ _) hδ₀_lt, ?_⟩
    intro p hp
    rcases mem_insert_iff.mp hp with rfl | hps
    · have : δ ≤ ‖ν p.1 - ν p.2‖ / 8 := min_le_right _ _
      linarith
    · have : δ ≤ δ₀ := min_le_left _ _
      linarith [hδ₀ p hps]

theorem GraphDrawing.of_eq {S : Type*} [TopologicalSpace S] {G₁ G₂ : Graph α β}
    (h : G₁ = G₂) (Γ : GraphDrawing G₁ S) {ν : α → S}
    (hν : ∀ v : V(G₁), (Γ.iso.vertexEquiv v).1 = ν v.1) :
    ∃ Γ' : GraphDrawing G₂ S,
      Γ'.drawing = Γ.drawing ∧
      ∀ v : V(G₂), (Γ'.iso.vertexEquiv v).1 = ν v.1 := by
  subst h
  exact ⟨Γ, rfl, hν⟩

/-- Base case drawing construction: if `G` is a finite graph whose edges are all loops and `ν`
injectively maps `V(G)` into `sphere (0 : ℂ) 1`, then `G` admits a drawing in `closedBall (0 : ℂ) 1`
intersecting `sphere (0 : ℂ) 1` exactly at `ν '' V(G)`. -/
theorem exists_drawing_of_loops_only {G : Graph α β}
    (hV_fin : V(G).Finite) (hE_fin : E(G).Finite)
    (hloops : ∀ e x y, G.IsLink e x y → x = y)
    {ν : α → ℂ} (hν_inj : InjOn ν V(G)) (hν_sph : ∀ v ∈ V(G), ν v ∈ Metric.sphere (0 : ℂ) 1) :
    ∃ Γ : GraphDrawing G ℂ,
      Γ.drawing.U ⊆ Metric.closedBall (0 : ℂ) 1 ∧
      Γ.drawing.U ∩ Metric.sphere (0 : ℂ) 1 = ν '' V(G) ∧
      ∀ v : V(G), (Γ.iso.vertexEquiv v).1 = ν v.1 := by
  obtain ⟨δ, hδ_pos, hδ_lt, hδ_dist⟩ := exists_pos_delta_lt_dist hV_fin hν_inj
  let ρ : ℕ → ℝ := fun k => δ / ((k : ℝ) + 2)
  have hρ_pos : ∀ k : ℕ, 0 < ρ k := fun k => div_pos hδ_pos (by positivity)
  have hρ_lt_delta : ∀ k : ℕ, ρ k < δ := fun k => by
    dsimp [ρ]
    exact div_lt_self hδ_pos (by linarith : (1 : ℝ) < (k : ℝ) + 2)
  have hρ_lt_one : ∀ k : ℕ, ρ k < 1 := fun k => by linarith [hρ_lt_delta k]
  have hρ_inj : ∀ k₁ k₂ : ℕ, k₁ ≠ k₂ → ρ k₁ ≠ ρ k₂ := fun k₁ k₂ hne heq => by
    dsimp [ρ] at heq
    have h1 : (0 : ℝ) < (k₁ : ℝ) + 2 := by positivity
    have h2 : (0 : ℝ) < (k₂ : ℝ) + 2 := by positivity
    have hmul : δ * ((k₂ : ℝ) + 2) = δ * ((k₁ : ℝ) + 2) := (div_eq_div_iff h1.ne' h2.ne').mp heq
    have hcast : (k₂ : ℝ) = (k₁ : ℝ) := by nlinarith
    exact hne (Nat.cast_injective hcast.symm)
  suffices ∀ (n : ℕ) (F : Set β), F ⊆ E(G) → F.ncard = n →
      ∃ Γ : GraphDrawing (G.restrict F) ℂ,
        ν '' V(G) ⊆ Γ.drawing.U ∧
        Γ.drawing.U ⊆ ν '' V(G) ∪ {z : ℂ | ∃ k < n, ∃ u ∈ V(G), z ∈ loopCircle (ν u) (ρ k)} ∧
        ∀ v : V(G.restrict F), (Γ.iso.vertexEquiv v).1 = ν v.1 by
    obtain ⟨Γ₀, hU_sub₁, hU_sub₂, hν₀⟩ := this E(G).ncard E(G) Subset.rfl rfl
    have hG_eq : G.restrict E(G) = G := by
      refine le_antisymm restrict_le ⟨by simp, fun {e x y} hl => ?_⟩
      refine (restrict_le.isLink_iff ?_).mpr hl
      rw [edgeSet_restrict, inter_self]
      exact hl.edge_mem
    obtain ⟨Γ, hD_eq, hν⟩ := GraphDrawing.of_eq hG_eq Γ₀ hν₀
    refine ⟨Γ, ?_, ?_, hν⟩
    · rw [hD_eq]
      refine Subset.trans hU_sub₂ ?_
      refine union_subset ?_ ?_
      · rintro z ⟨v, hv, rfl⟩
        exact Metric.sphere_subset_closedBall (hν_sph v hv)
      · rintro z ⟨k, _, u, hu, hzk⟩
        exact loopCircle_subset_closedBall (hν_sph u hu) (hρ_pos k) (hρ_lt_one k) hzk
    · rw [hD_eq]
      refine Subset.antisymm ?_ ?_
      · rintro z ⟨hzU, hzS⟩
        rcases hU_sub₂ hzU with hzV | ⟨k, _, u, hu, hzk⟩
        · exact hzV
        · have hzu : z = ν u := mem_singleton_iff.mp
            ((loopCircle_inter_sphere (hν_sph u hu) (hρ_pos k) (hρ_lt_one k)) ▸ ⟨hzk, hzS⟩)
          exact ⟨u, hu, hzu.symm⟩
      · rintro z ⟨v, hv, rfl⟩
        exact ⟨hU_sub₁ ⟨v, hv, rfl⟩, hν_sph v hv⟩
  intro n
  induction n with
  | zero =>
    intro F hF hn
    have hF_fin : F.Finite := hE_fin.subset hF
    have hF_empty : F = ∅ := (ncard_eq_zero hF_fin).mp hn
    have hE_empty : E(G.restrict F) = ∅ := by simp [edgeSet_restrict, hF_empty]
    have hV_eq : V(G.restrict F) = V(G) := vertexSet_restrict G F
    obtain ⟨Γ, hU, hν⟩ := GraphDrawing.of_edgeless
      (hV_eq ▸ hV_fin) hE_empty (hV_eq ▸ hν_inj)
    refine ⟨Γ, ?_, ?_, hν⟩
    · rw [hU, hV_eq]
    · rw [hU, hV_eq]
      exact subset_union_left
  | succ n ih =>
    intro F hF hn
    have hF_fin : F.Finite := hE_fin.subset hF
    have hF_ne : F.Nonempty := (ncard_pos hF_fin).mp (by omega)
    obtain ⟨e₀, he₀F⟩ := hF_ne
    let F' := F \ {e₀}
    have hF'_sub : F' ⊆ E(G) := Subset.trans sdiff_subset hF
    have hF'_card : F'.ncard = n := by
      change (F \ {e₀}).ncard = n
      rw [ncard_sdiff_singleton_of_mem he₀F, hn]
      omega
    obtain ⟨Γ₁, hU₁_sub₁, hU₁_sub₂, hν₁⟩ := ih F' hF'_sub hF'_card
    have he₀E : e₀ ∈ E(G) := hF he₀F
    obtain ⟨u, v, hlink⟩ := exists_isLink_of_mem_edgeSet he₀E
    have huv : u = v := hloops e₀ u v hlink
    subst huv
    have huV : u ∈ V(G) := hlink.left_mem
    let H₂ : Graph α β := (G.induce {u}).restrict {e₀}
    have hV₂ : V(H₂) = {u} := by simp [H₂]
    have hE₂ : E(H₂) = {e₀} := by
      ext e
      simp only [H₂, edgeSet_restrict, mem_inter_iff, mem_singleton_iff, edgeSet_induce,
        mem_ofPred_eq]
      refine ⟨fun h => h.2, fun h => ?_⟩
      subst h
      exact ⟨⟨u, u, hlink, rfl, rfl⟩, rfl⟩
    have hH₂_le_F : H₂ ≤ G.restrict F :=
      ⟨by simp [H₂, huV], fun {_ _ _} hl => ⟨hl.1 ▸ he₀F, hl.2.1⟩⟩
    have hlink₂ : H₂.IsLink e₀ u u := ⟨rfl, hlink, rfl, rfl⟩
    let K := loopCircle (ν u) (ρ n)
    have hK_oArc : IsOArc K := isOArc_loopCircle (ν u) (hρ_pos n)
    have hu_in_K : ν u ∈ K := mem_loopCircle_self (hν_sph u huV) (ρ n)
    obtain ⟨Γ₂, hU₂, hν₂⟩ := GraphDrawing.of_single_loop hV₂ hE₂ hlink₂ hK_oArc hu_in_K
    have hG₁_le : G.restrict F' ≤ G.restrict F :=
      ⟨by simp, fun {_ _ _} hl => ⟨sdiff_subset hl.1, hl.2⟩⟩
    have hV_union : V(G.restrict F') ∪ V(H₂) = V(G.restrict F) := by
      rw [hV₂, vertexSet_restrict, vertexSet_restrict, union_eq_self_of_subset_right]
      exact singleton_subset_iff.mpr huV
    have hE_union : E(G.restrict F') ∪ E(H₂) = E(G.restrict F) := by
      rw [hE₂, edgeSet_restrict, edgeSet_restrict]
      ext e
      simp only [mem_union, mem_inter_iff, mem_sdiff, mem_singleton_iff, F']
      constructor
      · rintro (⟨heG, heF, _⟩ | rfl)
        · exact ⟨heG, heF⟩
        · exact ⟨he₀E, he₀F⟩
      · rintro ⟨heG, heF⟩
        by_cases he : e = e₀
        · exact Or.inr he
        · exact Or.inl ⟨heG, heF, he⟩
    have hE_disj : Disjoint E(G.restrict F') E(H₂) := by
      rw [hE₂, edgeSet_restrict, disjoint_singleton_right]
      simp [F']
    have hU_inter : Γ₁.drawing.U ∩ Γ₂.drawing.U ⊆ ν '' (V(G.restrict F') ∩ V(H₂)) := by
      have hV_inter : V(G.restrict F') ∩ V(H₂) = {u} := by
        rw [hV₂, vertexSet_restrict, inter_eq_right]
        exact singleton_subset_iff.mpr huV
      rw [hV_inter, image_singleton, hU₂]
      rintro z ⟨hz₁, hz₂⟩
      rcases hU₁_sub₂ hz₁ with ⟨v, hv, rfl⟩ | ⟨k, hk_lt, v, hv, hzk⟩
      · have h_sph : ν v ∈ K ∩ Metric.sphere (0 : ℂ) 1 := ⟨hz₂, hν_sph v hv⟩
        rwa [loopCircle_inter_sphere (hν_sph u huV) (hρ_pos n) (hρ_lt_one n)] at h_sph
      · by_cases hvu : v = u
        · subst hvu
          have h_inter : z ∈ loopCircle (ν v) (ρ k) ∩ K := ⟨hzk, hz₂⟩
          rwa [loopCircle_inter_loopCircle_same (hν_sph v hv) (hρ_inj k n (Nat.ne_of_lt hk_lt))]
            at h_inter
        · exfalso
          have hdist : 2 * ρ k + 2 * ρ n < ‖ν v - ν u‖ := by
            have h1 := hρ_lt_delta k
            have h2 := hρ_lt_delta n
            have h3 := hδ_dist v hv u huV hvu
            linarith
          have h_empty := loopCircle_disjoint_of_dist (hν_sph v hv) (hν_sph u huV)
            (hρ_pos k) (hρ_pos n) hdist
          have h_mem : z ∈ loopCircle (ν v) (ρ k) ∩ K := ⟨hzk, hz₂⟩
          rw [h_empty] at h_mem
          exact h_mem
    obtain ⟨Γ, hU_eq, hν_eq⟩ := GraphDrawing.glue hG₁_le hH₂_le_F hV_union hE_union hE_disj
      (by rwa [vertexSet_restrict]) Γ₁ Γ₂ hν₁ hν₂ hU_inter
    refine ⟨Γ, ?_, ?_, hν_eq⟩
    · rw [hU_eq]
      exact Subset.trans hU₁_sub₁ subset_union_left
    · rw [hU_eq, hU₂]
      refine union_subset ?_ ?_
      · refine Subset.trans hU₁_sub₂ (union_subset subset_union_left ?_)
        rintro z ⟨k, hk, v, hv, hzk⟩
        exact Or.inr ⟨k, Nat.lt_succ_of_lt hk, v, hv, hzk⟩
      · intro z hzK
        exact Or.inr ⟨n, Nat.lt_succ_self n, u, huV, hzK⟩

/-! ### Module 4: Half-Disc Maps, Lens Arcs, and Angular Boundary Alignment -/

noncomputable section

/-- The `k`-th subdivision point `-1 + 2 * k / (m - 1)` on `[-1, 1]`. -/
def pathX (m k : ℕ) : ℝ :=
  -1 + 2 * (k : ℝ) / ((m : ℝ) - 1)

theorem pathX_zero (m : ℕ) : pathX m 0 = -1 := by
  simp [pathX]

theorem pathX_pred {m : ℕ} (hm : 2 ≤ m) : pathX m (m - 1) = 1 := by
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := Nat.ofNat_le_cast.mpr hm
    linarith
  dsimp [pathX]
  rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one, mul_div_cancel_right₀ _ hm1.ne']
  ring

theorem pathX_strictMono {m : ℕ} (hm : 2 ≤ m) {j k : ℕ} (hjk : j < k) :
    pathX m j < pathX m k := by
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := Nat.ofNat_le_cast.mpr hm
    linarith
  have hlt : (j : ℝ) < (k : ℝ) := Nat.cast_lt.mpr hjk
  dsimp [pathX]
  have : 2 * (j : ℝ) / ((m : ℝ) - 1) < 2 * (k : ℝ) / ((m : ℝ) - 1) :=
    div_lt_div_of_pos_right (by linarith) hm1
  linarith

theorem pathX_mem_Icc {m : ℕ} (hm : 2 ≤ m) {k : ℕ} (hk : k < m) :
    pathX m k ∈ Icc (-1 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · rw [← pathX_zero m]
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact le_rfl
    · exact (pathX_strictMono hm hpos).le
  · rw [← pathX_pred hm]
    rcases lt_or_eq_of_le (Nat.le_sub_one_of_lt hk) with hlt | rfl
    · exact (pathX_strictMono hm hlt).le
    · exact le_rfl

/-- Polynomial vanishing on `[-1, 1]` precisely at `{pathX m 0, ..., pathX m (m - 1)}`
and bounded in `[0, 1]` on `[-1, 1]`. -/
def pathPoly (m : ℕ) (x : ℝ) : ℝ :=
  ∏ k ∈ Finset.range m, ((x - pathX m k) / 2) ^ 2

theorem continuous_pathPoly (m : ℕ) : Continuous (pathPoly m) := by
  unfold pathPoly
  fun_prop

theorem pathPoly_nonneg (m : ℕ) (x : ℝ) : 0 ≤ pathPoly m x :=
  Finset.prod_nonneg fun _ _ => sq_nonneg _

theorem pathPoly_le_one {m : ℕ} (hm : 2 ≤ m) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    pathPoly m x ≤ 1 := by
  have h_fac : ∀ k ∈ Finset.range m, ((x - pathX m k) / 2) ^ 2 ≤ 1 := fun k hk => by
    have hk_lt : k < m := Finset.mem_range.mp hk
    have hxk := pathX_mem_Icc hm hk_lt
    have h1 : -1 ≤ (x - pathX m k) / 2 := by linarith [hx.1, hxk.2]
    have h2 : (x - pathX m k) / 2 ≤ 1 := by linarith [hx.2, hxk.1]
    nlinarith
  suffices ∀ s : Finset ℕ, (∀ k ∈ s, ((x - pathX m k) / 2) ^ 2 ≤ 1) →
      ∏ k ∈ s, ((x - pathX m k) / 2) ^ 2 ≤ 1 from this (Finset.range m) h_fac
  intro s
  refine Finset.induction_on s (by simp) fun a s ha ih hs => ?_
  rw [Finset.prod_insert ha]
  have ha1 : ((x - pathX m a) / 2) ^ 2 ≤ 1 := hs a (Finset.mem_insert_self a s)
  have ha0 : 0 ≤ ((x - pathX m a) / 2) ^ 2 := sq_nonneg _
  have hs1 : ∏ k ∈ s, ((x - pathX m k) / 2) ^ 2 ≤ 1 :=
    ih (fun k hk => hs k (Finset.mem_insert_of_mem hk))
  have hs0 : 0 ≤ ∏ k ∈ s, ((x - pathX m k) / 2) ^ 2 :=
    Finset.prod_nonneg fun _ _ => sq_nonneg _
  nlinarith

theorem pathPoly_eq_zero_iff (m : ℕ) (x : ℝ) :
    pathPoly m x = 0 ↔ ∃ k < m, x = pathX m k := by
  simp only [pathPoly, Finset.prod_eq_zero_iff, Finset.mem_range, sq_eq_zero_iff,
    div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false, sub_eq_zero]

theorem pathPoly_mul_sqrt_eq_zero_iff {m : ℕ} (hm : 2 ≤ m) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    pathPoly m x * Real.sqrt (1 - x ^ 2) = 0 ↔ ∃ k < m, x = pathX m k := by
  rw [mul_eq_zero, pathPoly_eq_zero_iff]
  refine ⟨fun h => ?_, fun h => Or.inl h⟩
  rcases h with h | hsqrt
  · exact h
  · have hnonneg : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    have h1 : 1 - x ^ 2 = 0 := (Real.sqrt_eq_zero hnonneg).mp hsqrt
    have hx_eq : x = -1 ∨ x = 1 := by
      have : (x + 1) * (x - 1) = 0 := by linarith
      rcases mul_eq_zero.mp this with h2 | h2
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases hx_eq with rfl | rfl
    · exact ⟨0, by omega, (pathX_zero m).symm⟩
    · exact ⟨m - 1, by omega, (pathX_pred hm).symm⟩

/-- Upper pinched half-disc map `F⁺`. -/
def upperDiscMap (m : ℕ) (z : ℂ) : ℂ :=
  (z.re : ℂ) +
    (((z.im + Real.sqrt (1 - z.re ^ 2)) / 2 +
      pathPoly m z.re * (Real.sqrt (1 - z.re ^ 2) - z.im) / 4 : ℝ) : ℂ) * Complex.I

/-- Lower pinched half-disc map `F⁻`. -/
def lowerDiscMap (m : ℕ) (z : ℂ) : ℂ :=
  (z.re : ℂ) +
    (((z.im - Real.sqrt (1 - z.re ^ 2)) / 2 -
      pathPoly m z.re * (Real.sqrt (1 - z.re ^ 2) + z.im) / 4 : ℝ) : ℂ) * Complex.I

@[simp]
theorem upperDiscMap_re (m : ℕ) (z : ℂ) : (upperDiscMap m z).re = z.re := by
  simp [upperDiscMap]

@[simp]
theorem upperDiscMap_im (m : ℕ) (z : ℂ) :
    (upperDiscMap m z).im =
      (z.im + Real.sqrt (1 - z.re ^ 2)) / 2 +
        pathPoly m z.re * (Real.sqrt (1 - z.re ^ 2) - z.im) / 4 := by
  simp [upperDiscMap]

@[simp]
theorem lowerDiscMap_re (m : ℕ) (z : ℂ) : (lowerDiscMap m z).re = z.re := by
  simp [lowerDiscMap]

@[simp]
theorem lowerDiscMap_im (m : ℕ) (z : ℂ) :
    (lowerDiscMap m z).im =
      (z.im - Real.sqrt (1 - z.re ^ 2)) / 2 -
        pathPoly m z.re * (Real.sqrt (1 - z.re ^ 2) + z.im) / 4 := by
  simp [lowerDiscMap]

theorem continuous_upperDiscMap (m : ℕ) : Continuous (upperDiscMap m) := by
  have h1 : Continuous (pathPoly m) := continuous_pathPoly m
  unfold upperDiscMap
  fun_prop

theorem continuous_lowerDiscMap (m : ℕ) : Continuous (lowerDiscMap m) := by
  have h1 : Continuous (pathPoly m) := continuous_pathPoly m
  unfold lowerDiscMap
  fun_prop

theorem mem_closedBall_unit_iff {z : ℂ} :
    z ∈ Metric.closedBall (0 : ℂ) 1 ↔
      z.re ∈ Icc (-1 : ℝ) 1 ∧
        -Real.sqrt (1 - z.re ^ 2) ≤ z.im ∧ z.im ≤ Real.sqrt (1 - z.re ^ 2) := by
  rw [Metric.mem_closedBall, dist_zero_right, ← sq_le_one_iff₀ (norm_nonneg z),
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  constructor
  · intro h
    have hre : z.re ^ 2 ≤ 1 := by nlinarith [sq_nonneg z.im]
    have him : z.im ^ 2 ≤ 1 - z.re ^ 2 := by linarith
    have hx : z.re ∈ Icc (-1 : ℝ) 1 := ⟨by nlinarith, by nlinarith⟩
    have hsqrt : |z.im| ≤ Real.sqrt (1 - z.re ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt him
    exact ⟨hx, (abs_le.mp hsqrt).1, (abs_le.mp hsqrt).2⟩
  · rintro ⟨hx, h1, h2⟩
    have hnonneg : 0 ≤ 1 - z.re ^ 2 := by nlinarith [hx.1, hx.2]
    have habs : |z.im| ≤ Real.sqrt (1 - z.re ^ 2) := abs_le.mpr ⟨h1, h2⟩
    have hsq : z.im ^ 2 ≤ 1 - z.re ^ 2 := by
      calc z.im ^ 2 = |z.im| ^ 2 := (sq_abs z.im).symm
        _ ≤ (Real.sqrt (1 - z.re ^ 2)) ^ 2 := sq_le_sq.mpr (by rwa [abs_abs, abs_of_nonneg
          (Real.sqrt_nonneg _)])
        _ = 1 - z.re ^ 2 := Real.sq_sqrt hnonneg
    linarith

theorem mem_sphere_unit_iff {z : ℂ} :
    z ∈ Metric.sphere (0 : ℂ) 1 ↔
      z.re ∈ Icc (-1 : ℝ) 1 ∧
        (z.im = Real.sqrt (1 - z.re ^ 2) ∨ z.im = -Real.sqrt (1 - z.re ^ 2)) := by
  rw [Metric.mem_sphere, dist_zero_right]
  have hnorm_iff : ‖z‖ = 1 ↔ Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    exact ⟨fun h => by rw [h, one_pow], fun h => by nlinarith [norm_nonneg z]⟩
  rw [hnorm_iff, Complex.normSq_apply]
  constructor
  · intro h
    have hre : z.re ^ 2 ≤ 1 := by nlinarith [sq_nonneg z.im]
    have hx : z.re ∈ Icc (-1 : ℝ) 1 := ⟨by nlinarith, by nlinarith⟩
    have hnonneg : 0 ≤ 1 - z.re ^ 2 := by nlinarith
    have him : z.im ^ 2 = (Real.sqrt (1 - z.re ^ 2)) ^ 2 := by
      rw [Real.sq_sqrt hnonneg]
      linarith
    exact ⟨hx, sq_eq_sq_iff_eq_or_eq_neg.mp him⟩
  · rintro ⟨hx, him | him⟩
    · have hnonneg : 0 ≤ 1 - z.re ^ 2 := by nlinarith [hx.1, hx.2]
      have hsq : z.im ^ 2 = 1 - z.re ^ 2 := by rw [him, Real.sq_sqrt hnonneg]
      linarith
    · have hnonneg : 0 ≤ 1 - z.re ^ 2 := by nlinarith [hx.1, hx.2]
      have hsq : z.im ^ 2 = 1 - z.re ^ 2 := by rw [him, neg_sq, Real.sq_sqrt hnonneg]
      linarith

theorem injOn_upperDiscMap {m : ℕ} (hm : 2 ≤ m) :
    InjOn (upperDiscMap m) (Metric.closedBall (0 : ℂ) 1) := by
  intro z₁ hz₁ z₂ _ heq
  have hre : z₁.re = z₂.re := by simpa using congrArg Complex.re heq
  have him := congrArg Complex.im heq
  simp only [upperDiscMap_im, hre] at him
  have hx₂ : z₂.re ∈ Icc (-1 : ℝ) 1 := hre ▸ (mem_closedBall_unit_iff.mp hz₁).1
  have hb1 : pathPoly m z₂.re ≤ 1 := pathPoly_le_one hm hx₂
  have him_eq : z₁.im = z₂.im := by nlinarith
  exact Complex.ext hre him_eq

theorem injOn_lowerDiscMap {m : ℕ} (hm : 2 ≤ m) :
    InjOn (lowerDiscMap m) (Metric.closedBall (0 : ℂ) 1) := by
  intro z₁ hz₁ z₂ _ heq
  have hre : z₁.re = z₂.re := by simpa using congrArg Complex.re heq
  have him := congrArg Complex.im heq
  simp only [lowerDiscMap_im, hre] at him
  have hx₂ : z₂.re ∈ Icc (-1 : ℝ) 1 := hre ▸ (mem_closedBall_unit_iff.mp hz₁).1
  have hb1 : pathPoly m z₂.re ≤ 1 := pathPoly_le_one hm hx₂
  have him_eq : z₁.im = z₂.im := by nlinarith
  exact Complex.ext hre him_eq

theorem upperDiscMap_im_ge {m : ℕ} (hm : 2 ≤ m) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    pathPoly m z.re * Real.sqrt (1 - z.re ^ 2) / 2 ≤ (upperDiscMap m z).im := by
  obtain ⟨hx, h1, _⟩ := mem_closedBall_unit_iff.mp hz
  have hb1 : pathPoly m z.re ≤ 1 := pathPoly_le_one hm hx
  rw [upperDiscMap_im]
  nlinarith

theorem upperDiscMap_im_le {m : ℕ} (hm : 2 ≤ m) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    (upperDiscMap m z).im ≤ Real.sqrt (1 - z.re ^ 2) := by
  obtain ⟨hx, _, h2⟩ := mem_closedBall_unit_iff.mp hz
  have hb1 : pathPoly m z.re ≤ 1 := pathPoly_le_one hm hx
  rw [upperDiscMap_im]
  nlinarith

theorem upperDiscMap_im_nonneg {m : ℕ} (hm : 2 ≤ m) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    0 ≤ (upperDiscMap m z).im := by
  have hge := upperDiscMap_im_ge hm hz
  have hb0 : 0 ≤ pathPoly m z.re := pathPoly_nonneg m z.re
  have hs0 : 0 ≤ Real.sqrt (1 - z.re ^ 2) := Real.sqrt_nonneg _
  nlinarith

theorem upperDiscMap_mem_closedBall {m : ℕ} (hm : 2 ≤ m) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    upperDiscMap m z ∈ Metric.closedBall (0 : ℂ) 1 := by
  rw [mem_closedBall_unit_iff, upperDiscMap_re]
  refine ⟨(mem_closedBall_unit_iff.mp hz).1, ?_, upperDiscMap_im_le hm hz⟩
  have h0 := upperDiscMap_im_nonneg hm hz
  have hs0 : 0 ≤ Real.sqrt (1 - z.re ^ 2) := Real.sqrt_nonneg _
  linarith

theorem upperDiscMap_eq_self_of_mem_sphere {m : ℕ} {z : ℂ}
    (hz : z ∈ Metric.sphere (0 : ℂ) 1) (him : 0 ≤ z.im) :
    upperDiscMap m z = z := by
  obtain ⟨_, h_eq | h_eq⟩ := mem_sphere_unit_iff.mp hz
  · apply Complex.ext (upperDiscMap_re m z)
    rw [upperDiscMap_im, h_eq]
    ring
  · have hs0 : 0 ≤ Real.sqrt (1 - z.re ^ 2) := Real.sqrt_nonneg _
    have h_zero : z.im = 0 := by linarith
    have hs_zero : Real.sqrt (1 - z.re ^ 2) = 0 := by linarith
    apply Complex.ext (upperDiscMap_re m z)
    rw [upperDiscMap_im, h_zero, hs_zero]
    ring

theorem upperDiscMap_mem_sphere_iff {m : ℕ} (hm : 2 ≤ m) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    upperDiscMap m z ∈ Metric.sphere (0 : ℂ) 1 ↔
      z ∈ Metric.sphere (0 : ℂ) 1 ∧ 0 ≤ z.im := by
  constructor
  · intro h_sph
    obtain ⟨hx, h1, h2⟩ := mem_closedBall_unit_iff.mp hz
    have hb1 : pathPoly m z.re ≤ 1 := pathPoly_le_one hm hx
    have h_im_nonneg : 0 ≤ (upperDiscMap m z).im := upperDiscMap_im_nonneg hm hz
    obtain ⟨_, h_up | h_low⟩ := mem_sphere_unit_iff.mp h_sph
    · rw [upperDiscMap_re, upperDiscMap_im] at h_up
      have him_eq : z.im = Real.sqrt (1 - z.re ^ 2) := by nlinarith
      exact ⟨mem_sphere_unit_iff.mpr ⟨hx, Or.inl him_eq⟩,
        him_eq.symm ▸ Real.sqrt_nonneg _⟩
    · rw [upperDiscMap_re] at h_low
      have hs0 : 0 ≤ Real.sqrt (1 - z.re ^ 2) := Real.sqrt_nonneg _
      have hs_zero : Real.sqrt (1 - z.re ^ 2) = 0 := by linarith
      have him_eq : z.im = Real.sqrt (1 - z.re ^ 2) := by linarith
      exact ⟨mem_sphere_unit_iff.mpr ⟨hx, Or.inl him_eq⟩, by linarith⟩
  · rintro ⟨h_sph, him⟩
    rwa [upperDiscMap_eq_self_of_mem_sphere h_sph him]

theorem upperDiscMap_pathX (m : ℕ) {k : ℕ} (hk : k < m) :
    upperDiscMap m ((pathX m k : ℂ) - (Real.sqrt (1 - (pathX m k) ^ 2) : ℂ) * Complex.I) =
      (pathX m k : ℂ) := by
  have hb : pathPoly m (pathX m k) = 0 :=
    (pathPoly_eq_zero_iff m (pathX m k)).mpr ⟨k, hk, rfl⟩
  apply Complex.ext
  · simp [upperDiscMap]
  · simp [upperDiscMap, hb]

theorem lowerDiscMap_im_le {m : ℕ} (hm : 2 ≤ m) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    (lowerDiscMap m z).im ≤ -(pathPoly m z.re * Real.sqrt (1 - z.re ^ 2) / 2) := by
  obtain ⟨hx, _, h2⟩ := mem_closedBall_unit_iff.mp hz
  have hb1 : pathPoly m z.re ≤ 1 := pathPoly_le_one hm hx
  rw [lowerDiscMap_im]
  nlinarith

theorem lowerDiscMap_im_ge {m : ℕ} (hm : 2 ≤ m) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    -Real.sqrt (1 - z.re ^ 2) ≤ (lowerDiscMap m z).im := by
  obtain ⟨hx, h1, _⟩ := mem_closedBall_unit_iff.mp hz
  have hb1 : pathPoly m z.re ≤ 1 := pathPoly_le_one hm hx
  rw [lowerDiscMap_im]
  nlinarith

theorem lowerDiscMap_im_nonpos {m : ℕ} (hm : 2 ≤ m) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    (lowerDiscMap m z).im ≤ 0 := by
  have hle := lowerDiscMap_im_le hm hz
  have hb0 : 0 ≤ pathPoly m z.re := pathPoly_nonneg m z.re
  have hs0 : 0 ≤ Real.sqrt (1 - z.re ^ 2) := Real.sqrt_nonneg _
  nlinarith

theorem lowerDiscMap_mem_closedBall {m : ℕ} (hm : 2 ≤ m) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    lowerDiscMap m z ∈ Metric.closedBall (0 : ℂ) 1 := by
  rw [mem_closedBall_unit_iff, lowerDiscMap_re]
  refine ⟨(mem_closedBall_unit_iff.mp hz).1, lowerDiscMap_im_ge hm hz, ?_⟩
  have h0 := lowerDiscMap_im_nonpos hm hz
  have hs0 : 0 ≤ Real.sqrt (1 - z.re ^ 2) := Real.sqrt_nonneg _
  linarith

theorem lowerDiscMap_eq_self_of_mem_sphere {m : ℕ} {z : ℂ}
    (hz : z ∈ Metric.sphere (0 : ℂ) 1) (him : z.im ≤ 0) :
    lowerDiscMap m z = z := by
  obtain ⟨_, h_eq | h_eq⟩ := mem_sphere_unit_iff.mp hz
  · have hs0 : 0 ≤ Real.sqrt (1 - z.re ^ 2) := Real.sqrt_nonneg _
    have h_zero : z.im = 0 := by linarith
    have hs_zero : Real.sqrt (1 - z.re ^ 2) = 0 := by linarith
    apply Complex.ext (lowerDiscMap_re m z)
    rw [lowerDiscMap_im, h_zero, hs_zero]
    ring
  · apply Complex.ext (lowerDiscMap_re m z)
    rw [lowerDiscMap_im, h_eq]
    ring

theorem lowerDiscMap_mem_sphere_iff {m : ℕ} (hm : 2 ≤ m) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    lowerDiscMap m z ∈ Metric.sphere (0 : ℂ) 1 ↔
      z ∈ Metric.sphere (0 : ℂ) 1 ∧ z.im ≤ 0 := by
  constructor
  · intro h_sph
    obtain ⟨hx, h1, h2⟩ := mem_closedBall_unit_iff.mp hz
    have hb1 : pathPoly m z.re ≤ 1 := pathPoly_le_one hm hx
    have h_im_nonpos : (lowerDiscMap m z).im ≤ 0 := lowerDiscMap_im_nonpos hm hz
    obtain ⟨_, h_up | h_low⟩ := mem_sphere_unit_iff.mp h_sph
    · rw [lowerDiscMap_re] at h_up
      have hs0 : 0 ≤ Real.sqrt (1 - z.re ^ 2) := Real.sqrt_nonneg _
      have hs_zero : Real.sqrt (1 - z.re ^ 2) = 0 := by linarith
      have him_eq : z.im = -Real.sqrt (1 - z.re ^ 2) := by linarith
      exact ⟨mem_sphere_unit_iff.mpr ⟨hx, Or.inr him_eq⟩, by linarith⟩
    · rw [lowerDiscMap_re, lowerDiscMap_im] at h_low
      have him_eq : z.im = -Real.sqrt (1 - z.re ^ 2) := by nlinarith
      exact ⟨mem_sphere_unit_iff.mpr ⟨hx, Or.inr him_eq⟩,
        by linarith [Real.sqrt_nonneg (1 - z.re ^ 2)]⟩
  · rintro ⟨h_sph, him⟩
    rwa [lowerDiscMap_eq_self_of_mem_sphere h_sph him]

theorem lowerDiscMap_pathX (m : ℕ) {k : ℕ} (hk : k < m) :
    lowerDiscMap m ((pathX m k : ℂ) + (Real.sqrt (1 - (pathX m k) ^ 2) : ℂ) * Complex.I) =
      (pathX m k : ℂ) := by
  have hb : pathPoly m (pathX m k) = 0 :=
    (pathPoly_eq_zero_iff m (pathX m k)).mpr ⟨k, hk, rfl⟩
  apply Complex.ext
  · simp [lowerDiscMap]
  · simp [lowerDiscMap, hb]

theorem upperDiscMap_inter_lowerDiscMap {m : ℕ} (hm : 2 ≤ m) :
    (upperDiscMap m '' Metric.closedBall (0 : ℂ) 1) ∩
      (lowerDiscMap m '' Metric.closedBall (0 : ℂ) 1) ⊆
      {w : ℂ | ∃ k < m, w = (pathX m k : ℂ)} := by
  rintro w ⟨⟨z₁, hz₁, rfl⟩, ⟨z₂, hz₂, h₂⟩⟩
  have hge := upperDiscMap_im_ge hm hz₁
  have hle := lowerDiscMap_im_le hm hz₂
  have hre : z₂.re = z₁.re := by
    have := congrArg Complex.re h₂
    simpa using this
  have him : (lowerDiscMap m z₂).im = (upperDiscMap m z₁).im := congrArg Complex.im h₂
  rw [hre, him] at hle
  have hmul_nonneg : 0 ≤ pathPoly m z₁.re * Real.sqrt (1 - z₁.re ^ 2) :=
    mul_nonneg (pathPoly_nonneg m z₁.re) (Real.sqrt_nonneg _)
  have hmul_zero : pathPoly m z₁.re * Real.sqrt (1 - z₁.re ^ 2) = 0 := by linarith
  have him_zero : (upperDiscMap m z₁).im = 0 := by linarith
  have hx₁ : z₁.re ∈ Icc (-1 : ℝ) 1 := (mem_closedBall_unit_iff.mp hz₁).1
  obtain ⟨k, hk, hxk⟩ := (pathPoly_mul_sqrt_eq_zero_iff hm hx₁).mp hmul_zero
  refine ⟨k, hk, Complex.ext ?_ ?_⟩
  · simp [hxk]
  · simpa using him_zero

/-- Curve for a lens arc connecting `(pathX m k, 0)` and `(pathX m (k + 1), 0)`
with vertical scale `c`. -/
def lensCurve (m k : ℕ) (c : ℝ) (t : ℝ) : ℂ :=
  let x := (1 - t) * pathX m k + t * pathX m (k + 1)
  (x : ℂ) + ((c * pathPoly m x * Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) * Complex.I

/-- Lens arc connecting `(pathX m k, 0)` and `(pathX m (k + 1), 0)`. -/
def lensArc (m k : ℕ) (c : ℝ) : Set ℂ :=
  lensCurve m k c '' Icc 0 1

@[simp]
theorem lensCurve_re (m k : ℕ) (c t : ℝ) :
    (lensCurve m k c t).re = (1 - t) * pathX m k + t * pathX m (k + 1) := by
  simp [lensCurve]

@[simp]
theorem lensCurve_im (m k : ℕ) (c t : ℝ) :
    (lensCurve m k c t).im =
      let x := (1 - t) * pathX m k + t * pathX m (k + 1)
      c * pathPoly m x * Real.sqrt (1 - x ^ 2) := by
  simp [lensCurve]

theorem lensCurve_zero (m : ℕ) {k : ℕ} (hk : k < m) (c : ℝ) :
    lensCurve m k c 0 = (pathX m k : ℂ) := by
  have hb : pathPoly m (pathX m k) = 0 :=
    (pathPoly_eq_zero_iff m (pathX m k)).mpr ⟨k, hk, rfl⟩
  apply Complex.ext <;> simp [lensCurve, hb]

theorem lensCurve_one (m : ℕ) {k : ℕ} (hk : k + 1 < m) (c : ℝ) :
    lensCurve m k c 1 = (pathX m (k + 1) : ℂ) := by
  have hb : pathPoly m (pathX m (k + 1)) = 0 :=
    (pathPoly_eq_zero_iff m (pathX m (k + 1))).mpr ⟨k + 1, hk, rfl⟩
  apply Complex.ext <;> simp [lensCurve, hb]

theorem isLineWithEnds_lensArc {m k : ℕ} (hm : 2 ≤ m) (hk : k + 1 < m) (c : ℝ) :
    IsLineWithEnds (lensArc m k c) (pathX m k : ℂ) (pathX m (k + 1) : ℂ) := by
  have hcont : Continuous (lensCurve m k c) := by
    have := continuous_pathPoly m
    unfold lensCurve
    fun_prop
  have hinj : InjOn (lensCurve m k c) (Icc 0 1) := by
    intro t₁ _ t₂ _ heq
    have hre := congrArg Complex.re heq
    simp only [lensCurve_re] at hre
    have hlt : pathX m k < pathX m (k + 1) := pathX_strictMono hm (Nat.lt_succ_self k)
    nlinarith
  have hL := GraphMinor.GM11.isLine_of_injOn hcont zero_lt_one hinj
  rwa [lensCurve_zero m (Nat.lt_of_succ_lt hk) c, lensCurve_one m hk c] at hL

theorem mem_lensArc_props {m k : ℕ} (hm : 2 ≤ m) (hk : k + 1 < m) {c : ℝ} {w : ℂ}
    (hw : w ∈ lensArc m k c) :
    w.re ∈ Icc (pathX m k) (pathX m (k + 1)) ∧
      w.re ∈ Icc (-1 : ℝ) 1 ∧
      w.im = c * pathPoly m w.re * Real.sqrt (1 - w.re ^ 2) := by
  rcases hw with ⟨t, ⟨ht0, ht1⟩, rfl⟩
  have hlt : pathX m k < pathX m (k + 1) := pathX_strictMono hm (Nat.lt_succ_self k)
  have hxk := pathX_mem_Icc hm (Nat.lt_of_succ_lt hk)
  have hxk1 := pathX_mem_Icc hm hk
  have hre_k : pathX m k ≤ (lensCurve m k c t).re := by
    rw [lensCurve_re]; nlinarith
  have hre_k1 : (lensCurve m k c t).re ≤ pathX m (k + 1) := by
    rw [lensCurve_re]; nlinarith
  refine ⟨⟨hre_k, hre_k1⟩, ⟨by linarith [hxk.1], by linarith [hxk1.2]⟩, ?_⟩
  simp

theorem eq_end_of_mem_lensArc_of_mul_eq_zero {m k : ℕ} (hm : 2 ≤ m) (hk : k + 1 < m)
    {c : ℝ} {w : ℂ} (hw : w ∈ lensArc m k c)
    (hz : pathPoly m w.re * Real.sqrt (1 - w.re ^ 2) = 0) :
    w = (pathX m k : ℂ) ∨ w = (pathX m (k + 1) : ℂ) := by
  obtain ⟨hre_Icc, hre_unit, him_eq⟩ := mem_lensArc_props hm hk hw
  have him_zero : w.im = 0 := by linear_combination him_eq + c * hz
  obtain ⟨j, hj, hxj⟩ := (pathPoly_mul_sqrt_eq_zero_iff hm hre_unit).mp hz
  have hjk : j = k ∨ j = k + 1 := by
    by_contra hne
    push Not at hne
    rcases lt_or_gt_of_ne hne.1 with hlt | hgt
    · have : pathX m j < pathX m k := pathX_strictMono hm hlt
      linarith [hre_Icc.1]
    · have hgt' : k + 1 < j := Nat.lt_of_le_of_ne hgt hne.2.symm
      have : pathX m (k + 1) < pathX m j := pathX_strictMono hm hgt'
      linarith [hre_Icc.2]
  rcases hjk with rfl | rfl
  · left; exact Complex.ext (by simp [hxj]) (by simp [him_zero])
  · right; exact Complex.ext (by simp [hxj]) (by simp [him_zero])

theorem lensArc_subset_closedBall {m k : ℕ} (hm : 2 ≤ m) (hk : k + 1 < m)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1 / 2) :
    lensArc m k c ⊆ Metric.closedBall (0 : ℂ) 1 := by
  intro w hw
  obtain ⟨_, hre_unit, him_eq⟩ := mem_lensArc_props hm hk hw
  rw [mem_closedBall_unit_iff]
  have hb0 : 0 ≤ pathPoly m w.re := pathPoly_nonneg m w.re
  have hb1 : pathPoly m w.re ≤ 1 := pathPoly_le_one hm hre_unit
  have hs0 : 0 ≤ Real.sqrt (1 - w.re ^ 2) := Real.sqrt_nonneg _
  have him0 : 0 ≤ w.im := by rw [him_eq]; positivity
  have him_le : w.im ≤ Real.sqrt (1 - w.re ^ 2) := by
    have : c * pathPoly m w.re ≤ 1 := by nlinarith
    rw [him_eq]
    nlinarith
  exact ⟨hre_unit, by linarith, him_le⟩

theorem lensArc_inter_sphere {m k : ℕ} (hm : 2 ≤ m) (hk : k + 1 < m)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1 / 2) :
    lensArc m k c ∩ Metric.sphere (0 : ℂ) 1 ⊆
      {(pathX m 0 : ℂ), (pathX m (m - 1) : ℂ)} := by
  rintro w ⟨hw, h_sph⟩
  obtain ⟨_, hre_unit, him_eq⟩ := mem_lensArc_props hm hk hw
  have hb0 : 0 ≤ pathPoly m w.re := pathPoly_nonneg m w.re
  have hb1 : pathPoly m w.re ≤ 1 := pathPoly_le_one hm hre_unit
  have hs0 : 0 ≤ Real.sqrt (1 - w.re ^ 2) := Real.sqrt_nonneg _
  have h_prod : c * pathPoly m w.re ≤ 1 / 2 := by nlinarith
  have him_le : w.im ≤ (1 / 2) * Real.sqrt (1 - w.re ^ 2) := by
    rw [him_eq]; nlinarith
  have him0 : 0 ≤ w.im := by rw [him_eq]; positivity
  obtain ⟨_, h_up | h_low⟩ := mem_sphere_unit_iff.mp h_sph
  · have hs_zero : Real.sqrt (1 - w.re ^ 2) = 0 := by linarith
    have him_zero : w.im = 0 := by linarith
    have hnonneg : 0 ≤ 1 - w.re ^ 2 := by nlinarith [hre_unit.1, hre_unit.2]
    have h1 : 1 - w.re ^ 2 = 0 := (Real.sqrt_eq_zero hnonneg).mp hs_zero
    have hx_eq : w.re = -1 ∨ w.re = 1 := by
      have : (w.re + 1) * (w.re - 1) = 0 := by linarith
      rcases mul_eq_zero.mp this with h2 | h2
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases hx_eq with hre | hre
    · left; exact Complex.ext (by simp [hre, pathX_zero]) (by simp [him_zero])
    · right; exact Complex.ext (by simp [hre, pathX_pred hm]) (by simp [him_zero])
  · have hs_zero : Real.sqrt (1 - w.re ^ 2) = 0 := by linarith
    have him_zero : w.im = 0 := by linarith
    have hnonneg : 0 ≤ 1 - w.re ^ 2 := by nlinarith [hre_unit.1, hre_unit.2]
    have h1 : 1 - w.re ^ 2 = 0 := (Real.sqrt_eq_zero hnonneg).mp hs_zero
    have hx_eq : w.re = -1 ∨ w.re = 1 := by
      have : (w.re + 1) * (w.re - 1) = 0 := by linarith
      rcases mul_eq_zero.mp this with h2 | h2
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases hx_eq with hre | hre
    · left; exact Complex.ext (by simp [hre, pathX_zero]) (by simp [him_zero])
    · right; exact Complex.ext (by simp [hre, pathX_pred hm]) (by simp [him_zero])

theorem lensArc_inter_upperDiscMap {m k : ℕ} (hm : 2 ≤ m) (hk : k + 1 < m)
    {c : ℝ} (hc1 : c < 1 / 2) :
    (upperDiscMap m '' Metric.closedBall (0 : ℂ) 1) ∩ lensArc m k c ⊆
      {(pathX m k : ℂ), (pathX m (k + 1) : ℂ)} := by
  rintro w ⟨⟨z, hz, hzw⟩, hw⟩
  obtain ⟨_, _, him_eq⟩ := mem_lensArc_props hm hk hw
  have hre : z.re = w.re := by simpa using congrArg Complex.re hzw
  have him : (upperDiscMap m z).im = w.im := congrArg Complex.im hzw
  have hge := upperDiscMap_im_ge hm hz
  rw [hre, him, him_eq] at hge
  have hmul0 : 0 ≤ pathPoly m w.re * Real.sqrt (1 - w.re ^ 2) :=
    mul_nonneg (pathPoly_nonneg m w.re) (Real.sqrt_nonneg _)
  have hmul_zero : pathPoly m w.re * Real.sqrt (1 - w.re ^ 2) = 0 := by nlinarith
  exact eq_end_of_mem_lensArc_of_mul_eq_zero hm hk hw hmul_zero

theorem lensArc_inter_lowerDiscMap {m k : ℕ} (hm : 2 ≤ m) (hk : k + 1 < m)
    {c : ℝ} (hc0 : 0 < c) :
    (lowerDiscMap m '' Metric.closedBall (0 : ℂ) 1) ∩ lensArc m k c ⊆
      {(pathX m k : ℂ), (pathX m (k + 1) : ℂ)} := by
  rintro w ⟨⟨z, hz, hzw⟩, hw⟩
  obtain ⟨_, _, him_eq⟩ := mem_lensArc_props hm hk hw
  have hre : z.re = w.re := by simpa using congrArg Complex.re hzw
  have him : (lowerDiscMap m z).im = w.im := congrArg Complex.im hzw
  have hle := lowerDiscMap_im_le hm hz
  rw [hre, him, him_eq] at hle
  have hmul0 : 0 ≤ pathPoly m w.re * Real.sqrt (1 - w.re ^ 2) :=
    mul_nonneg (pathPoly_nonneg m w.re) (Real.sqrt_nonneg _)
  have hmul_zero : pathPoly m w.re * Real.sqrt (1 - w.re ^ 2) = 0 := by nlinarith
  exact eq_end_of_mem_lensArc_of_mul_eq_zero hm hk hw hmul_zero

theorem lensArc_inter_lensArc {m k₁ k₂ : ℕ} (hm : 2 ≤ m)
    (hk₁ : k₁ + 1 < m) (hk₂ : k₂ + 1 < m) {c₁ c₂ : ℝ} (hne : c₁ ≠ c₂) :
    lensArc m k₁ c₁ ∩ lensArc m k₂ c₂ ⊆
      {(pathX m k₂ : ℂ), (pathX m (k₂ + 1) : ℂ)} := by
  rintro w ⟨hw₁, hw₂⟩
  obtain ⟨_, _, him₁⟩ := mem_lensArc_props hm hk₁ hw₁
  obtain ⟨_, _, him₂⟩ := mem_lensArc_props hm hk₂ hw₂
  have hdiff : (c₁ - c₂) * (pathPoly m w.re * Real.sqrt (1 - w.re ^ 2)) = 0 := by
    linear_combination him₂ - him₁
  have hmul_zero : pathPoly m w.re * Real.sqrt (1 - w.re ^ 2) = 0 :=
    (mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hne)
  exact eq_end_of_mem_lensArc_of_mul_eq_zero hm hk₂ hw₂ hmul_zero

/-- Glue a finite set `E_P` of non-loop edges along lens arcs onto a base drawing `Γ_base`. -/
theorem exists_drawing_gluing_lensArcs {G : Graph α β} {E_base E_P : Set β} {m : ℕ}
    (hm : 2 ≤ m) (hE_fin : E(G).Finite)
    (hE_union : E_base ∪ E_P = E(G)) (hE_disj : Disjoint E_base E_P)
    {ν : α → ℂ} (hν_inj : InjOn ν V(G))
    (hEP_links : ∀ e ∈ E_P, ∃ u v : α, G.IsLink e u v ∧
      ∃ k : ℕ, k + 1 < m ∧ ν u = (pathX m k : ℂ) ∧ ν v = (pathX m (k + 1) : ℂ))
    (Γ_base : GraphDrawing (G.restrict E_base) ℂ)
    (hU_base_sub : Γ_base.drawing.U ⊆
      (upperDiscMap m '' Metric.closedBall (0 : ℂ) 1) ∪
      (lowerDiscMap m '' Metric.closedBall (0 : ℂ) 1))
    (hν_base : ∀ v : V(G.restrict E_base), (Γ_base.iso.vertexEquiv v).1 = ν v.1) :
    ∃ Γ : GraphDrawing G ℂ,
      Γ_base.drawing.U ⊆ Γ.drawing.U ∧
      Γ.drawing.U ⊆ Γ_base.drawing.U ∪
        {w : ℂ | ∃ n : ℕ, ∃ k : ℕ, k + 1 < m ∧
          w ∈ lensArc m k (1 / (4 * ((n : ℝ) + 2)))} ∧
      ∀ v : V(G), (Γ.iso.vertexEquiv v).1 = ν v.1 := by
  let c : ℕ → ℝ := fun n => 1 / (4 * ((n : ℝ) + 2))
  have hc_pos : ∀ n : ℕ, 0 < c n := fun n => by dsimp [c]; positivity
  have hc_lt : ∀ n : ℕ, c n < 1 / 2 := fun n => by
    dsimp [c]
    have : (2 : ℝ) < 4 * ((n : ℝ) + 2) := by linarith
    exact one_div_lt_one_div_of_lt (by norm_num) this
  have hc_inj : ∀ n₁ n₂ : ℕ, n₁ ≠ n₂ → c n₁ ≠ c n₂ := fun n₁ n₂ hne heq => by
    dsimp [c] at heq
    have h1 : (0 : ℝ) < 4 * ((n₁ : ℝ) + 2) := by positivity
    have h2 : (0 : ℝ) < 4 * ((n₂ : ℝ) + 2) := by positivity
    have hmul : 1 * (4 * ((n₂ : ℝ) + 2)) = 1 * (4 * ((n₁ : ℝ) + 2)) :=
      (div_eq_div_iff h1.ne' h2.ne').mp heq
    have hcast : (n₂ : ℝ) = (n₁ : ℝ) := by linarith
    exact hne (Nat.cast_injective hcast.symm)
  suffices ∀ (n : ℕ) (F : Set β), F ⊆ E_P → F.ncard = n →
      ∃ Γ : GraphDrawing (G.restrict (E_base ∪ F)) ℂ,
        Γ_base.drawing.U ⊆ Γ.drawing.U ∧
        Γ.drawing.U ⊆ Γ_base.drawing.U ∪
          {w : ℂ | ∃ j < n, ∃ k : ℕ, k + 1 < m ∧ w ∈ lensArc m k (c j)} ∧
        ∀ v : V(G.restrict (E_base ∪ F)), (Γ.iso.vertexEquiv v).1 = ν v.1 by
    obtain ⟨Γ₀, hU₁, hU₂, hν₀⟩ := this E_P.ncard E_P Subset.rfl rfl
    have hG_eq : G.restrict (E_base ∪ E_P) = G := by
      rw [hE_union]
      refine le_antisymm restrict_le ⟨by simp, fun {_ _ _} hl => ⟨hl.edge_mem, hl⟩⟩
    obtain ⟨Γ, hD_eq, hν⟩ := GraphDrawing.of_eq hG_eq Γ₀ hν₀
    refine ⟨Γ, hD_eq.symm ▸ hU₁, ?_, hν⟩
    rw [hD_eq]
    refine Subset.trans hU₂ (union_subset subset_union_left ?_)
    rintro w ⟨j, _, k, hk, hw⟩
    exact Or.inr ⟨j, k, hk, hw⟩
  intro n
  induction n with
  | zero =>
    intro F hF hn
    have hF_fin : F.Finite := hE_fin.subset (Subset.trans hF (hE_union ▸ subset_union_right))
    have hF_empty : F = ∅ := (ncard_eq_zero hF_fin).mp hn
    have hG_eq : G.restrict E_base = G.restrict (E_base ∪ F) := by simp [hF_empty]
    obtain ⟨Γ, hD_eq, hν⟩ := GraphDrawing.of_eq hG_eq Γ_base hν_base
    refine ⟨Γ, hD_eq.symm ▸ Subset.rfl, ?_, hν⟩
    rw [hD_eq]
    exact subset_union_left
  | succ n ih =>
    intro F hF hn
    have hF_fin : F.Finite := hE_fin.subset (Subset.trans hF (hE_union ▸ subset_union_right))
    have hF_ne : F.Nonempty := (ncard_pos hF_fin).mp (by omega)
    obtain ⟨e₀, he₀F⟩ := hF_ne
    let F' := F \ {e₀}
    have hF'_sub : F' ⊆ E_P := Subset.trans sdiff_subset hF
    have hF'_card : F'.ncard = n := by
      change (F \ {e₀}).ncard = n
      rw [ncard_sdiff_singleton_of_mem he₀F, hn]
      omega
    obtain ⟨Γ₁, hU₁_sub₁, hU₁_sub₂, hν₁⟩ := ih F' hF'_sub hF'_card
    have he₀_EP : e₀ ∈ E_P := hF he₀F
    have he₀E : e₀ ∈ E(G) := hE_union ▸ Or.inr he₀_EP
    obtain ⟨u, v, hlink, k, hk_lt, hu_eq, hv_eq⟩ := hEP_links e₀ he₀_EP
    have huV : u ∈ V(G) := hlink.left_mem
    have hvV : v ∈ V(G) := hlink.right_mem
    have hν_ne : ν u ≠ ν v := by
      have hlt : pathX m k < pathX m (k + 1) := pathX_strictMono hm (Nat.lt_succ_self k)
      intro heq
      rw [hu_eq, hv_eq] at heq
      have := congrArg Complex.re heq
      simp only [Complex.ofReal_re] at this
      linarith
    let K := lensArc m k (c n)
    have hK_line : IsLineWithEnds K (ν u) (ν v) := by
      rw [hu_eq, hv_eq]
      exact isLineWithEnds_lensArc hm hk_lt (c n)
    let H₂ : Graph α β := (G.induce {u, v}).restrict {e₀}
    have hV₂ : V(H₂) = {u, v} := rfl
    have hE₂ : E(H₂) = {e₀} := by
      ext e
      simp only [H₂, edgeSet_restrict, mem_inter_iff, mem_singleton_iff, edgeSet_induce,
        mem_ofPred_eq]
      refine ⟨fun h => h.2, fun h => ?_⟩
      subst h
      exact ⟨⟨u, v, hlink, Or.inl rfl, Or.inr rfl⟩, rfl⟩
    have hlink₂ : H₂.IsLink e₀ u v := ⟨rfl, hlink, Or.inl rfl, Or.inr rfl⟩
    obtain ⟨Γ₂, hU₂, hν₂⟩ := GraphDrawing.of_single_edge hV₂ hE₂ hlink₂ hν_ne hK_line
    have hG₁_le : G.restrict (E_base ∪ F') ≤ G.restrict (E_base ∪ F) :=
      ⟨by simp, fun {_ _ _} hl => ⟨hl.1.elim Or.inl (fun h => Or.inr (sdiff_subset h)), hl.2⟩⟩
    have hH₂_le : H₂ ≤ G.restrict (E_base ∪ F) :=
      ⟨by rw [hV₂, vertexSet_restrict]; rintro w (rfl | rfl) <;> assumption,
       fun {_ _ _} hl => ⟨Or.inr (hl.1 ▸ he₀F), hl.2.1⟩⟩
    have hV_union : V(G.restrict (E_base ∪ F')) ∪ V(H₂) = V(G.restrict (E_base ∪ F)) := by
      rw [hV₂, vertexSet_restrict, vertexSet_restrict, union_eq_self_of_subset_right]
      rintro w (rfl | rfl) <;> assumption
    have hE_union' : E(G.restrict (E_base ∪ F')) ∪ E(H₂) = E(G.restrict (E_base ∪ F)) := by
      rw [hE₂, edgeSet_restrict, edgeSet_restrict]
      ext e
      simp only [mem_union, mem_inter_iff, mem_sdiff, mem_singleton_iff, F']
      constructor
      · rintro (⟨heG, heB | ⟨heF, _⟩⟩ | rfl)
        · exact ⟨heG, Or.inl heB⟩
        · exact ⟨heG, Or.inr heF⟩
        · exact ⟨he₀E, Or.inr he₀F⟩
      · rintro ⟨heG, heB | heF⟩
        · exact Or.inl ⟨heG, Or.inl heB⟩
        · by_cases he : e = e₀
          · exact Or.inr he
          · exact Or.inl ⟨heG, Or.inr ⟨heF, he⟩⟩
    have hE_disj' : Disjoint E(G.restrict (E_base ∪ F')) E(H₂) := by
      rw [hE₂, edgeSet_restrict, disjoint_singleton_right]
      rintro ⟨_, heB | ⟨_, he_ne⟩⟩
      · exact disjoint_left.mp hE_disj heB he₀_EP
      · exact he_ne rfl
    have h_pair_eq : ({(pathX m k : ℂ), (pathX m (k + 1) : ℂ)} : Set ℂ) = {ν u, ν v} := by
      rw [hu_eq, hv_eq]
    have hU_inter : Γ₁.drawing.U ∩ Γ₂.drawing.U ⊆
        ν '' (V(G.restrict (E_base ∪ F')) ∩ V(H₂)) := by
      have hV_inter : V(G.restrict (E_base ∪ F')) ∩ V(H₂) = {u, v} := by
        rw [hV₂, vertexSet_restrict, inter_eq_right]
        rintro w (rfl | rfl) <;> assumption
      rw [hV_inter, image_pair, hU₂, ← h_pair_eq]
      rintro w ⟨hw₁, hw₂⟩
      rcases hU₁_sub₂ hw₁ with hw_base | ⟨j, hj_lt, k', hk'_lt, hw_j⟩
      · rcases hU_base_sub hw_base with hw_up | hw_low
        · exact lensArc_inter_upperDiscMap hm hk_lt (hc_lt n) ⟨hw_up, hw₂⟩
        · exact lensArc_inter_lowerDiscMap hm hk_lt (hc_pos n) ⟨hw_low, hw₂⟩
      · exact lensArc_inter_lensArc hm hk'_lt hk_lt (hc_inj j n (Nat.ne_of_lt hj_lt)) ⟨hw_j, hw₂⟩
    obtain ⟨Γ, hU_eq, hν_eq⟩ := GraphDrawing.glue hG₁_le hH₂_le hV_union hE_union' hE_disj'
      (by rwa [vertexSet_restrict]) Γ₁ Γ₂ hν₁ hν₂ hU_inter
    refine ⟨Γ, Subset.trans hU₁_sub₁ (hU_eq ▸ subset_union_left), ?_, hν_eq⟩
    rw [hU_eq, hU₂]
    refine union_subset ?_ ?_
    · refine Subset.trans hU₁_sub₂ (union_subset subset_union_left ?_)
      rintro w ⟨j, hj, k', hk', hw⟩
      exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, k', hk', hw⟩
    · intro w hwK
      exact Or.inr ⟨n, Nat.lt_succ_self n, k, hk_lt, hwK⟩

/-- Angular coordinate used by `discAngleMap` on `ℂ`. -/
def discAngleTheta (θ_s θ_t : ℝ) (z : ℂ) : ℝ :=
  if 0 ≤ z.im then
    θ_s + (θ_t - θ_s) * (Real.arccos (z.re / ‖z‖) / Real.pi)
  else
    θ_t + (θ_s + 2 * Real.pi - θ_t) * ((Real.pi - Real.arccos (z.re / ‖z‖)) / Real.pi)

/-- Radial-angular homeomorphism of `ℂ` preserving norms and aligning the upper and lower
semicircles of `sphere (0 : ℂ) 1` with `[θ_s, θ_t]` and `[θ_t, θ_s + 2π]`. -/
def discAngleMap (θ_s θ_t : ℝ) (z : ℂ) : ℂ :=
  (‖z‖ : ℂ) * (Circle.exp (discAngleTheta θ_s θ_t z) : ℂ)

@[simp]
theorem norm_discAngleMap (θ_s θ_t : ℝ) (z : ℂ) :
    ‖discAngleMap θ_s θ_t z‖ = ‖z‖ := by
  simp [discAngleMap]

@[simp]
theorem discAngleMap_zero (θ_s θ_t : ℝ) :
    discAngleMap θ_s θ_t 0 = 0 := by
  simp [discAngleMap]

theorem discAngleMap_mem_closedBall_iff (θ_s θ_t : ℝ) (z : ℂ) :
    discAngleMap θ_s θ_t z ∈ Metric.closedBall (0 : ℂ) 1 ↔
      z ∈ Metric.closedBall (0 : ℂ) 1 := by
  simp [Metric.mem_closedBall, dist_zero_right]

theorem discAngleMap_mem_sphere_iff (θ_s θ_t : ℝ) (z : ℂ) :
    discAngleMap θ_s θ_t z ∈ Metric.sphere (0 : ℂ) 1 ↔
      z ∈ Metric.sphere (0 : ℂ) 1 := by
  simp

private theorem continuous_norm_mul_circle_exp {ψ : ℂ → ℝ}
    (hψ : ∀ z : ℂ, z ≠ 0 → ContinuousAt ψ z) :
    Continuous (fun z : ℂ => (‖z‖ : ℂ) * (Circle.exp (ψ z) : ℂ)) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε, hε, fun {w} hw => ?_⟩
    simpa [dist_zero_right] using hw
  · have h1 : ContinuousAt (fun w : ℂ => (‖w‖ : ℂ)) z := by fun_prop
    have h_exp : Continuous (fun t : ℝ => (Circle.exp t : ℂ)) := by fun_prop
    have h2 : ContinuousAt (fun w : ℂ => (Circle.exp (ψ w) : ℂ)) z :=
      h_exp.continuousAt.comp (hψ z hz)
    exact h1.mul h2

theorem continuous_discAngleMap (θ_s θ_t : ℝ) :
    Continuous (discAngleMap θ_s θ_t) := by
  let φ₁ : ℂ → ℂ := fun z =>
    (‖z‖ : ℂ) * (Circle.exp (θ_s + (θ_t - θ_s) * (Real.arccos (z.re / ‖z‖) / Real.pi)) : ℂ)
  let φ₂ : ℂ → ℂ := fun z =>
    (‖z‖ : ℂ) * (Circle.exp (θ_t + (θ_s + 2 * Real.pi - θ_t) *
      ((Real.pi - Real.arccos (z.re / ‖z‖)) / Real.pi)) : ℂ)
  have hφ₁ : Continuous φ₁ := continuous_norm_mul_circle_exp fun z hz => by
    have : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    fun_prop (disch := assumption)
  have hφ₂ : Continuous φ₂ := continuous_norm_mul_circle_exp fun z hz => by
    have : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    fun_prop (disch := assumption)
  have heq : discAngleMap θ_s θ_t = fun z : ℂ => if 0 ≤ z.im then φ₁ z else φ₂ z := by
    ext z
    dsimp [discAngleMap, discAngleTheta, φ₁, φ₂]
    split_ifs <;> rfl
  rw [heq]
  refine Continuous.if_le hφ₁ hφ₂ continuous_const Complex.continuous_im fun z hz => ?_
  by_cases hz0 : z = 0
  · simp [φ₁, φ₂, hz0]
  · have hz_eq : z = (z.re : ℂ) := Complex.ext rfl hz.symm
    have hre_ne : z.re ≠ 0 := fun h => hz0 (Complex.ext h hz.symm)
    have hnorm : ‖z‖ = |z.re| := by
      conv_lhs => rw [hz_eq]
      exact Complex.norm_real z.re
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    rcases lt_or_gt_of_ne hre_ne with hneg | hpos
    · have hdiv : z.re / ‖z‖ = -1 := by
        rw [hnorm, abs_of_neg hneg, div_neg_self hre_ne]
      have harc : Real.arccos (z.re / ‖z‖) = Real.pi := by
        rw [hdiv, Real.arccos_neg_one]
      change (‖z‖ : ℂ) * (Circle.exp (θ_s + (θ_t - θ_s) * (Real.arccos
        (z.re / ‖z‖) / Real.pi)) : ℂ) =
        (‖z‖ : ℂ) * (Circle.exp (θ_t + (θ_s + 2 * Real.pi - θ_t) *
          ((Real.pi - Real.arccos (z.re / ‖z‖)) / Real.pi)) : ℂ)
      rw [harc, div_self hpi, mul_one, sub_self, zero_div, mul_zero, add_zero,
        add_sub_cancel]
    · have hdiv : z.re / ‖z‖ = 1 := by
        rw [hnorm, abs_of_pos hpos, div_self hre_ne]
      have harc : Real.arccos (z.re / ‖z‖) = 0 := by
        rw [hdiv, Real.arccos_one]
      have h_add : θ_t + (θ_s + 2 * Real.pi - θ_t) = θ_s + 2 * Real.pi := by ring
      have h_exp : Circle.exp (θ_t + (θ_s + 2 * Real.pi - θ_t)) = Circle.exp θ_s := by
        rw [h_add, Circle.exp_add, Circle.exp_two_pi, mul_one]
      change (‖z‖ : ℂ) * (Circle.exp (θ_s + (θ_t - θ_s) * (Real.arccos
        (z.re / ‖z‖) / Real.pi)) : ℂ) =
        (‖z‖ : ℂ) * (Circle.exp (θ_t + (θ_s + 2 * Real.pi - θ_t) *
          ((Real.pi - Real.arccos (z.re / ‖z‖)) / Real.pi)) : ℂ)
      rw [harc, zero_div, mul_zero, add_zero, sub_zero, div_self hpi, mul_one, h_exp]

theorem circle_exp_inj_of_abs_sub_lt {a b : ℝ}
    (h_lt : |a - b| < 2 * Real.pi) (heq : Circle.exp a = Circle.exp b) :
    a = b := by
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp heq
  have hpi : 0 < 2 * Real.pi := Real.two_pi_pos
  obtain ⟨h1, h2⟩ := abs_lt.mp h_lt
  have hm1 : (-1 : ℝ) < (m : ℝ) := by nlinarith
  have hm2 : (m : ℝ) < 1 := by nlinarith
  have hm1' : (-1 : ℤ) < m := by exact_mod_cast hm1
  have hm2' : m < (1 : ℤ) := by exact_mod_cast hm2
  have hm0 : m = 0 := by omega
  simpa [hm0] using hm

theorem re_div_norm_mem_Icc (z : ℂ) : z.re / ‖z‖ ∈ Icc (-1 : ℝ) 1 := by
  by_cases hz : z = 0
  · simp [hz]
  · have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have habs : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    obtain ⟨h1, h2⟩ := abs_le.mp habs
    exact ⟨(le_div_iff₀ hpos).mpr (by linarith), (div_le_iff₀ hpos).mpr (by linarith)⟩

theorem re_div_norm_mem_Ioo_of_im_ne_zero {z : ℂ} (him : z.im ≠ 0) :
    z.re / ‖z‖ ∈ Ioo (-1 : ℝ) 1 := by
  have hz : z ≠ 0 := fun h => him (by simp [h])
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have him_sq : 0 < z.im ^ 2 := sq_pos_of_ne_zero him
  have hnorm_sq : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hre_sq : z.re ^ 2 < ‖z‖ ^ 2 := by linarith
  have habs : |z.re| < ‖z‖ := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq hpos.le]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) hre_sq
  obtain ⟨h1, h2⟩ := abs_lt.mp habs
  exact ⟨(lt_div_iff₀ hpos).mpr (by linarith), (div_lt_iff₀ hpos).mpr (by linarith)⟩

theorem discAngleTheta_bounds_of_im_nonneg {θ_s θ_t : ℝ} (h_lt : θ_s < θ_t)
    {z : ℂ} (him : 0 ≤ z.im) :
    θ_s ≤ discAngleTheta θ_s θ_t z ∧ discAngleTheta θ_s θ_t z ≤ θ_t := by
  simp only [discAngleTheta, him, ↓reduceIte]
  have hpi : 0 < Real.pi := Real.pi_pos
  have harc0 : 0 ≤ Real.arccos (z.re / ‖z‖) := Real.arccos_nonneg _
  have harc1 : Real.arccos (z.re / ‖z‖) ≤ Real.pi := Real.arccos_le_pi _
  have hdiv0 : 0 ≤ Real.arccos (z.re / ‖z‖) / Real.pi := div_nonneg harc0 hpi.le
  have hdiv1 : Real.arccos (z.re / ‖z‖) / Real.pi ≤ 1 := (div_le_one hpi).mpr harc1
  refine ⟨by nlinarith, by nlinarith⟩

theorem discAngleTheta_bounds_of_im_neg {θ_s θ_t : ℝ}
    (h_span : θ_t < θ_s + 2 * Real.pi) {z : ℂ} (him : z.im < 0) :
    θ_t < discAngleTheta θ_s θ_t z ∧ discAngleTheta θ_s θ_t z < θ_s + 2 * Real.pi := by
  have hnot : ¬ 0 ≤ z.im := not_le.mpr him
  simp only [discAngleTheta, hnot, ↓reduceIte]
  have hpi : 0 < Real.pi := Real.pi_pos
  obtain ⟨h1, h2⟩ := re_div_norm_mem_Ioo_of_im_ne_zero him.ne
  have harc0 : 0 < Real.arccos (z.re / ‖z‖) := Real.arccos_pos.mpr h2
  have harc1 : Real.arccos (z.re / ‖z‖) < Real.pi := Real.arccos_lt_pi.mpr h1
  have hdiv0 : 0 < (Real.pi - Real.arccos (z.re / ‖z‖)) / Real.pi :=
    div_pos (by linarith) hpi
  have hdiv1 : (Real.pi - Real.arccos (z.re / ‖z‖)) / Real.pi < 1 :=
    (div_lt_one hpi).mpr (by linarith)
  refine ⟨by nlinarith, by nlinarith⟩

theorem injective_discAngleMap {θ_s θ_t : ℝ}
    (h_lt : θ_s < θ_t) (h_span : θ_t < θ_s + 2 * Real.pi) :
    Function.Injective (discAngleMap θ_s θ_t) := by
  intro z₁ z₂ heq
  have hnorm : ‖z₁‖ = ‖z₂‖ := by
    simpa only [norm_discAngleMap] using congrArg norm heq
  by_cases hz₁ : z₁ = 0
  · subst hz₁
    have hz₂ : ‖z₂‖ = 0 := by simpa using hnorm.symm
    exact (norm_eq_zero.mp hz₂).symm
  · have hpos₁ : 0 < ‖z₁‖ := norm_pos_iff.mpr hz₁
    have hne_c : (‖z₁‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos₁.ne'
    have hexp_c : (Circle.exp (discAngleTheta θ_s θ_t z₁) : ℂ) =
        (Circle.exp (discAngleTheta θ_s θ_t z₂) : ℂ) := by
      apply mul_left_cancel₀ hne_c
      calc (‖z₁‖ : ℂ) * (Circle.exp (discAngleTheta θ_s θ_t z₁) : ℂ)
        _ = discAngleMap θ_s θ_t z₁ := rfl
        _ = discAngleMap θ_s θ_t z₂ := heq
        _ = (‖z₁‖ : ℂ) * (Circle.exp (discAngleTheta θ_s θ_t z₂) : ℂ) := by
          simp [discAngleMap, hnorm]
    have hexp : Circle.exp (discAngleTheta θ_s θ_t z₁) =
        Circle.exp (discAngleTheta θ_s θ_t z₂) := Subtype.ext hexp_c
    have h_range : ∀ z : ℂ,
        θ_s ≤ discAngleTheta θ_s θ_t z ∧ discAngleTheta θ_s θ_t z < θ_s + 2 * Real.pi := by
      intro z
      by_cases him : 0 ≤ z.im
      · obtain ⟨b1, b2⟩ := discAngleTheta_bounds_of_im_nonneg h_lt him
        exact ⟨b1, by linarith⟩
      · obtain ⟨b1, b2⟩ := discAngleTheta_bounds_of_im_neg h_span (lt_of_not_ge him)
        exact ⟨by linarith, b2⟩
    have hθ_eq : discAngleTheta θ_s θ_t z₁ = discAngleTheta θ_s θ_t z₂ := by
      apply circle_exp_inj_of_abs_sub_lt _ hexp
      obtain ⟨l1, u1⟩ := h_range z₁
      obtain ⟨l2, u2⟩ := h_range z₂
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    have hpi : 0 < Real.pi := Real.pi_pos
    have harc_eq : Real.arccos (z₁.re / ‖z₁‖) = Real.arccos (z₂.re / ‖z₂‖) := by
      by_cases h1 : 0 ≤ z₁.im <;> by_cases h2 : 0 ≤ z₂.im
      · simp only [discAngleTheta, h1, h2, ↓reduceIte] at hθ_eq
        have hdiv : Real.arccos (z₁.re / ‖z₁‖) / Real.pi =
            Real.arccos (z₂.re / ‖z₂‖) / Real.pi := by nlinarith
        exact (div_left_inj₀ hpi.ne').mp hdiv
      · exfalso
        have b1 := (discAngleTheta_bounds_of_im_nonneg h_lt h1).2
        have b2 := (discAngleTheta_bounds_of_im_neg h_span (lt_of_not_ge h2)).1
        linarith
      · exfalso
        have b1 := (discAngleTheta_bounds_of_im_neg h_span (lt_of_not_ge h1)).1
        have b2 := (discAngleTheta_bounds_of_im_nonneg h_lt h2).2
        linarith
      · simp only [discAngleTheta, h1, h2, ↓reduceIte] at hθ_eq
        have hdiv : (Real.pi - Real.arccos (z₁.re / ‖z₁‖)) / Real.pi =
            (Real.pi - Real.arccos (z₂.re / ‖z₂‖)) / Real.pi := by nlinarith
        have hsub := (div_left_inj₀ hpi.ne').mp hdiv
        linarith
    have hdiv_eq : z₁.re / ‖z₁‖ = z₂.re / ‖z₂‖ := by
      have hc1 := Real.cos_arccos (re_div_norm_mem_Icc z₁).1 (re_div_norm_mem_Icc z₁).2
      have hc2 := Real.cos_arccos (re_div_norm_mem_Icc z₂).1 (re_div_norm_mem_Icc z₂).2
      rw [← hc1, ← hc2, harc_eq]
    have hre_eq : z₁.re = z₂.re := by
      rw [← hnorm] at hdiv_eq
      exact (div_left_inj₀ hpos₁.ne').mp hdiv_eq
    have him_sq : z₁.im ^ 2 = z₂.im ^ 2 := by
      have hsq1 : z₁.re ^ 2 + z₁.im ^ 2 = ‖z₁‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
      have hsq2 : z₂.re ^ 2 + z₂.im ^ 2 = ‖z₂‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
      rw [hre_eq, hnorm] at hsq1
      linarith
    have him_eq : z₁.im = z₂.im := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp him_sq with h | h
      · exact h
      · by_cases h1 : 0 ≤ z₁.im <;> by_cases h2 : 0 ≤ z₂.im
        · linarith
        · exfalso
          have b1 := (discAngleTheta_bounds_of_im_nonneg h_lt h1).2
          have b2 := (discAngleTheta_bounds_of_im_neg h_span (lt_of_not_ge h2)).1
          linarith
        · exfalso
          have b1 := (discAngleTheta_bounds_of_im_neg h_span (lt_of_not_ge h1)).1
          have b2 := (discAngleTheta_bounds_of_im_nonneg h_lt h2).2
          linarith
        · linarith
    exact Complex.ext hre_eq him_eq

private theorem circle_exp_re (t : ℝ) : ((Circle.exp t : ℂ)).re = Real.cos t := by
  simp [Circle.coe_exp]

private theorem circle_exp_im (t : ℝ) : ((Circle.exp t : ℂ)).im = Real.sin t := by
  simp [Circle.coe_exp]

theorem circle_exp_arccos {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (Circle.exp (Real.arccos x) : ℂ) =
      (x : ℂ) + (Real.sqrt (1 - x ^ 2) : ℂ) * Complex.I := by
  apply Complex.ext
  · rw [circle_exp_re, Real.cos_arccos hx.1 hx.2]
    simp
  · rw [circle_exp_im, Real.sin_arccos]
    simp

theorem circle_exp_two_pi_sub_arccos {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (Circle.exp (2 * Real.pi - Real.arccos x) : ℂ) =
      (x : ℂ) - (Real.sqrt (1 - x ^ 2) : ℂ) * Complex.I := by
  have h_sub : Circle.exp (2 * Real.pi - Real.arccos x) = Circle.exp (-Real.arccos x) := by
    rw [sub_eq_add_neg, Circle.exp_add, Circle.exp_two_pi, one_mul]
  rw [h_sub]
  apply Complex.ext
  · rw [circle_exp_re, Real.cos_neg, Real.cos_arccos hx.1 hx.2]
    simp
  · rw [circle_exp_im, Real.sin_neg, Real.sin_arccos]
    simp

theorem discAngleMap_one (θ_s θ_t : ℝ) :
    discAngleMap θ_s θ_t 1 = (Circle.exp θ_s : ℂ) := by
  simp [discAngleMap, discAngleTheta]

theorem discAngleMap_neg_one (θ_s θ_t : ℝ) :
    discAngleMap θ_s θ_t (-1) = (Circle.exp θ_t : ℂ) := by
  simp [discAngleMap, discAngleTheta]

theorem discAngleMap_upper_exp {θ_s θ_t θ : ℝ}
    (h1 : θ_s < θ) (h2 : θ < θ_t) :
    discAngleMap θ_s θ_t
      (Circle.exp (2 * Real.pi + Real.pi * (θ - θ_s) / (θ_t - θ_s)) : ℂ) =
      (Circle.exp θ : ℂ) := by
  let u := Real.pi * (θ - θ_s) / (θ_t - θ_s)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hdiff : 0 < θ_t - θ_s := by linarith
  have hu0 : 0 < u := div_pos (mul_pos hpi (by linarith)) hdiff
  have hu_pi : u < Real.pi := by
    dsimp [u]
    rw [div_lt_iff₀ hdiff]
    nlinarith
  have hexp_eq : Circle.exp (2 * Real.pi + u) = Circle.exp u := by
    rw [Circle.exp_add, Circle.exp_two_pi, one_mul]
  rw [hexp_eq]
  let z : ℂ := (Circle.exp u : ℂ)
  have hz_norm : ‖z‖ = 1 := Circle.norm_coe (Circle.exp u)
  have hz_re : z.re = Real.cos u := circle_exp_re u
  have hz_im : z.im = Real.sin u := circle_exp_im u
  have him_pos : 0 ≤ z.im := by
    rw [hz_im]
    exact (Real.sin_pos_of_pos_of_lt_pi hu0 hu_pi).le
  have harc : Real.arccos (z.re / ‖z‖) = u := by
    rw [hz_norm, div_one, hz_re]
    exact Real.arccos_cos hu0.le hu_pi.le
  change (‖z‖ : ℂ) * (Circle.exp (discAngleTheta θ_s θ_t z) : ℂ) = (Circle.exp θ : ℂ)
  rw [hz_norm, Complex.ofReal_one, one_mul]
  congr 1
  simp only [discAngleTheta, him_pos, ↓reduceIte, harc]
  congr 1
  dsimp [u]
  field_simp [hpi.ne', hdiff.ne']
  ring

theorem discAngleMap_lower_exp {θ_s θ_t θ : ℝ}
    (h1 : θ_t < θ) (h2 : θ < θ_s + 2 * Real.pi) :
    discAngleMap θ_s θ_t
      (Circle.exp (Real.pi + Real.pi * (θ - θ_t) / (θ_s + 2 * Real.pi - θ_t)) : ℂ) =
      (Circle.exp θ : ℂ) := by
  let u := Real.pi * (θ - θ_t) / (θ_s + 2 * Real.pi - θ_t)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hdiff : 0 < θ_s + 2 * Real.pi - θ_t := by linarith
  have hu0 : 0 < u := div_pos (mul_pos hpi (by linarith)) hdiff
  have hu_pi : u < Real.pi := by
    dsimp [u]
    rw [div_lt_iff₀ hdiff]
    nlinarith
  let z : ℂ := (Circle.exp (Real.pi + u) : ℂ)
  have hz_norm : ‖z‖ = 1 := Circle.norm_coe (Circle.exp (Real.pi + u))
  have hz_re : z.re = Real.cos (Real.pi - u) := by
    rw [circle_exp_re, add_comm Real.pi u, Real.cos_add_pi, Real.cos_pi_sub]
  have hz_im : z.im = -Real.sin u := by
    rw [circle_exp_im, add_comm Real.pi u, Real.sin_add_pi]
  have him_neg : z.im < 0 := by
    rw [hz_im]
    linarith [Real.sin_pos_of_pos_of_lt_pi hu0 hu_pi]
  have hnot : ¬ 0 ≤ z.im := not_le.mpr him_neg
  have harc : Real.arccos (z.re / ‖z‖) = Real.pi - u := by
    rw [hz_norm, div_one, hz_re]
    exact Real.arccos_cos (by linarith) (by linarith)
  change (‖z‖ : ℂ) * (Circle.exp (discAngleTheta θ_s θ_t z) : ℂ) = (Circle.exp θ : ℂ)
  rw [hz_norm, Complex.ofReal_one, one_mul]
  congr 1
  simp only [discAngleTheta, hnot, ↓reduceIte, harc]
  congr 1
  dsimp [u]
  field_simp [hpi.ne', hdiff.ne']
  ring


/-! ## Unit Circle Drawings and `ClosedUnitDisc` Boundary Homeomorphism -/

theorem subBd_closedUnitDisc_eq_unitCircle :
    subBd ClosedUnitDisc = UnitCircle := by
  have hclosed : IsClosed ClosedUnitDisc := Metric.isClosed_closedBall
  have hcompl : Set.univ \ ClosedUnitDisc = ClosedUnitDiscᶜ := (compl_eq_univ_sdiff _).symm
  rw [subBd, hclosed.closure_eq, hcompl, closure_compl, ← sdiff_eq]
  unfold ClosedUnitDisc UnitCircle
  rw [interior_closedBall (0 : EuclideanPlane) one_ne_zero]
  exact Metric.closedBall_sdiff_ball

/-- The complex unit circle as the boundary of the unit disc in the Euclidean plane. -/
noncomputable def circleHomeomorphSubBdClosedUnitDisc :
    Circle ≃ₜ subBd ClosedUnitDisc where
  toFun z := ⟨complexPlane (z : ℂ), by
    rw [subBd_closedUnitDisc_eq_unitCircle, UnitCircle, mem_sphere_zero_iff_norm,
      LinearIsometryEquiv.norm_map, Circle.norm_coe]⟩
  invFun y := ⟨complexPlane.symm y.1, by
    have hy : y.1 ∈ UnitCircle := subBd_closedUnitDisc_eq_unitCircle ▸ y.2
    rw [UnitCircle, mem_sphere_zero_iff_norm] at hy
    change complexPlane.symm y.1 ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map, hy]⟩
  left_inv z := Subtype.ext (complexPlane.symm_apply_apply (z : ℂ))
  right_inv y := Subtype.ext (complexPlane.apply_symm_apply y.1)
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact complexPlane.continuous.comp continuous_subtype_val
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact complexPlane.symm.continuous.comp continuous_subtype_val

theorem isClockwiseDiscHomeo_closedUnitDisc :
    IsClockwiseDiscHomeo ClosedUnitDisc circleHomeomorphSubBdClosedUnitDisc := by
  intro x hx
  have hx_ball : complexPlane.symm x ∈ Metric.ball (0 : ℂ) 1 := by
    have h1 : x ∈ Metric.ball (0 : EuclideanPlane) 1 := by
      rwa [ClosedUnitDisc, interior_closedBall (0 : EuclideanPlane) one_ne_zero] at hx
    rw [Metric.mem_ball, dist_zero_right] at h1 ⊢
    rwa [LinearIsometryEquiv.norm_map]
  have hφ : (fun w : Circle => complexPlane.symm (circleHomeomorphSubBdClosedUnitDisc w).1) =
      fun w : Circle => (w : ℂ) := by
    funext w
    exact complexPlane.symm_apply_apply (w : ℂ)
  rw [hφ]
  have hball := Surface.wind_eq_of_ball (Homeomorph.refl ℂ) (φ := fun w : Circle => (w : ℂ))
    continuous_subtype_val (fun _ => rfl) hx_ball (Metric.mem_ball_self zero_lt_one)
  change 0 < Surface.wind (fun w : Circle => (w : ℂ))
    ((Homeomorph.refl ℂ) (complexPlane.symm x))
  rw [hball]
  change 0 < GM19.turn (fun t => (Circle.exp t : ℂ) - 0) 0 (2 * Real.pi)
  simp only [sub_zero]
  rw [Surface.isAngle_exp.turn_eq (fun _ => Circle.coe_ne_zero _) 0 (2 * Real.pi)]
  linarith [Real.pi_pos]

theorem circle_exp_add_two_pi (t : ℝ) :
    Circle.exp (t + 2 * Real.pi) = Circle.exp t := by
  rw [Circle.exp_add, Circle.exp_two_pi, mul_one]

theorem circle_exp_injOn_Ico :
    Set.InjOn Circle.exp (Set.Ico 0 (2 * Real.pi)) := by
  intro x hx y hy hxy
  have hcos : Real.cos x = Real.cos y := by
    have := congrArg Complex.re (congrArg Subtype.val hxy)
    simpa [Circle.coe_exp] using this
  have hsin : Real.sin x = Real.sin y := by
    have := congrArg Complex.im (congrArg Subtype.val hxy)
    simpa [Circle.coe_exp] using this
  have hsin_neg : ∀ z : ℝ, Real.pi < z → z < 2 * Real.pi → Real.sin z < 0 := by
    intro z hz1 hz2
    have hpos : 0 < Real.sin (z - Real.pi) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at hpos
    linarith
  rcases le_or_gt x Real.pi with hx_pi | hx_pi
  · rcases le_or_gt y Real.pi with hy_pi | hy_pi
    · exact Real.injOn_cos ⟨hx.1, hx_pi⟩ ⟨hy.1, hy_pi⟩ hcos
    · exfalso
      have h1 : 0 ≤ Real.sin x := Real.sin_nonneg_of_mem_Icc ⟨hx.1, hx_pi⟩
      have h2 : Real.sin y < 0 := hsin_neg y hy_pi hy.2
      linarith
  · rcases le_or_gt y Real.pi with hy_pi | hy_pi
    · exfalso
      have h1 : Real.sin x < 0 := hsin_neg x hx_pi hx.2
      have h2 : 0 ≤ Real.sin y := Real.sin_nonneg_of_mem_Icc ⟨hy.1, hy_pi⟩
      linarith
    · have hcos' : Real.cos (2 * Real.pi - x) = Real.cos (2 * Real.pi - y) := by
        rw [Real.cos_two_pi_sub, Real.cos_two_pi_sub, hcos]
      have hsub := Real.injOn_cos ⟨by linarith [hx.2], by linarith [hx_pi]⟩
        ⟨by linarith [hy.2], by linarith [hy_pi]⟩ hcos'
      linarith

/-! ## Subgraph Restrictions, Plane Closed Discs, and Radial Shrinking -/

private theorem graphDrawingVertexSet_eq_singleton' {S : Type w} [TopologicalSpace S]
    {G : Graph α β} (Γ : GraphDrawing G S) {v : α} (hv : v ∈ V(G)) :
    graphDrawingVertexSet Γ v = {(Γ.iso.vertexEquiv ⟨v, hv⟩).1} := by
  ext x
  simp [graphDrawingVertexSet, hv, eq_comm]

private theorem graphDrawingVertexSet_of_notMem {S : Type w} [TopologicalSpace S]
    {G : Graph α β} (Γ : GraphDrawing G S) {v : α} (hv : v ∉ V(G)) :
    graphDrawingVertexSet Γ v = ∅ := by
  ext x
  simp [graphDrawingVertexSet, hv]

private theorem graphDrawingEdgeSet_eq' {S : Type w} [TopologicalSpace S]
    {G : Graph α β} (Γ : GraphDrawing G S) {e : β} (he : e ∈ E(G)) :
    graphDrawingEdgeSet Γ e = (Γ.iso.edgeEquiv ⟨e, he⟩).1 := by
  ext x
  simp [graphDrawingEdgeSet, he]

private theorem graphDrawingEdgeSet_of_notMem {S : Type w} [TopologicalSpace S]
    {G : Graph α β} (Γ : GraphDrawing G S) {e : β} (he : e ∉ E(G)) :
    graphDrawingEdgeSet Γ e = ∅ := by
  ext x
  simp [graphDrawingEdgeSet, he]

theorem graphDrawingSubgraphU_subset_drawing_U {S : Type w} [TopologicalSpace S]
    {G : Graph α β} (Γ : GraphDrawing G S) (H : Graph α β) :
    graphDrawingSubgraphU Γ H ⊆ Γ.drawing.U := by
  rintro x (hxV | hxE)
  · obtain ⟨v, _, hv, rfl⟩ := mem_iUnion₂.mp hxV
    exact Γ.drawing.V_subset_U (Γ.iso.vertexEquiv ⟨v, hv⟩).2
  · obtain ⟨e, _, hxe⟩ := mem_iUnion₂.mp hxE
    by_cases he : e ∈ E(G)
    · rw [graphDrawingEdgeSet_eq' Γ he] at hxe
      exact Γ.drawing.closure_subset_U (Γ.iso.edgeEquiv ⟨e, he⟩).2 hxe
    · rw [graphDrawingEdgeSet_of_notMem Γ he, closure_empty] at hxe
      exact hxe.elim

/-- Restrict a `GraphDrawing G S` to any subgraph `H ≤ G`. -/
theorem GraphDrawing.ofSubgraph {S : Type w} [TopologicalSpace S] [T1Space S]
    {G H : Graph α β} (Γ : GraphDrawing G S) (hH : H ≤ G) :
    ∃ Γ' : GraphDrawing H S,
      Γ'.drawing.U = graphDrawingSubgraphU Γ H ∧
      Γ'.drawing.U ⊆ Γ.drawing.U ∧
      Γ'.drawing.IsSubdrawing Γ.drawing ∧
      (∀ v : V(H), (Γ'.iso.vertexEquiv v).1 =
        (Γ.iso.vertexEquiv ⟨v.1, hH.vertexSet_mono v.2⟩).1) ∧
      (∀ v ∈ V(H), graphDrawingVertexSet Γ' v = graphDrawingVertexSet Γ v) ∧
      (∀ e ∈ E(H), graphDrawingEdgeSet Γ' e = graphDrawingEdgeSet Γ e) ∧
      (∀ P ≤ H, graphDrawingSubgraphU Γ' P = graphDrawingSubgraphU Γ P) := by
  classical
  let V' : Set S := ⋃ v ∈ V(H), graphDrawingVertexSet Γ v
  let E' : Set (Set S) := (fun e : E(H) => (Γ.iso.edgeEquiv ⟨e.1, hH.edgeSet_mono e.2⟩).1) '' univ
  let D' : Drawing S := Γ.drawing.span V' E'
  have hV'_sub : V' ⊆ Γ.drawing.V := by
    rintro x hx
    obtain ⟨v, hvH, hvG, rfl⟩ := mem_iUnion₂.mp hx
    exact (Γ.iso.vertexEquiv ⟨v, hvG⟩).2
  have hE'_sub : E' ⊆ Γ.drawing.E := by
    rintro a ⟨e, _, rfl⟩
    exact (Γ.iso.edgeEquiv ⟨e.1, hH.edgeSet_mono e.2⟩).2
  have hE'_inter : E' ∩ Γ.drawing.E = E' := inter_eq_left.mpr hE'_sub
  have hspanV : Γ.drawing.spanV V' E' = V' := by
    apply subset_antisymm
    · rintro x (hxV | hxE)
      · exact hxV.1
      · obtain ⟨a, ha, hxa, hxGV⟩ := mem_iUnion₂.mp hxE
        rw [hE'_inter] at ha
        obtain ⟨e, _, rfl⟩ := ha
        have heG : e.1 ∈ E(G) := hH.edgeSet_mono e.2
        obtain ⟨u, w, hlH⟩ := H.exists_isLink_of_mem_edgeSet e.2
        have hlG : G.IsLink e.1 u w := hlH.mono hH
        have huG : u ∈ V(G) := hlG.left_mem
        have hwG : w ∈ V(G) := hlG.right_mem
        have hlink := (Γ.iso.isLink_iff ⟨e.1, heG⟩ ⟨u, huG⟩ ⟨w, hwG⟩).mp hlG
        have hx_ends : x ∈ ({(Γ.iso.vertexEquiv ⟨u, huG⟩).1,
            (Γ.iso.vertexEquiv ⟨w, hwG⟩).1} : Set S) := by
          rw [← hlink.2.2.2]
          exact ⟨hxa, hxGV⟩
        rcases hx_ends with rfl | hxw
        · exact mem_iUnion₂.mpr ⟨u, hlH.left_mem, huG, rfl⟩
        · rw [mem_singleton_iff] at hxw
          subst hxw
          exact mem_iUnion₂.mpr ⟨w, hlH.right_mem, hwG, rfl⟩
    · intro x hx
      exact Or.inl ⟨hx, hV'_sub hx⟩
  have hD'_V : D'.V = V' := hspanV
  have hD'_E : D'.E = E' := (Γ.drawing.span_E V' E').trans hE'_inter
  have hD'_U : D'.U = graphDrawingSubgraphU Γ H := by
    change Γ.drawing.spanV V' E' ∪ ⋃ a ∈ E' ∩ Γ.drawing.E, closure a = _
    rw [hspanV, hE'_inter]
    congr 1
    ext x
    simp only [mem_iUnion, E', image_univ, mem_range, exists_prop]
    constructor
    · rintro ⟨a, ⟨e, rfl⟩, hxa⟩
      refine ⟨e.1, e.2, ?_⟩
      rw [graphDrawingEdgeSet_eq' Γ (hH.edgeSet_mono e.2)]
      exact hxa
    · rintro ⟨e, heH, hxe⟩
      rw [graphDrawingEdgeSet_eq' Γ (hH.edgeSet_mono heH)] at hxe
      exact ⟨_, ⟨⟨e, heH⟩, rfl⟩, hxe⟩
  have hsub : D'.IsSubdrawing Γ.drawing :=
    ⟨hD'_V ▸ hV'_sub, hD'_E ▸ hE'_sub⟩
  let vFun : V(H) → D'.V := fun v =>
    ⟨(Γ.iso.vertexEquiv ⟨v.1, hH.vertexSet_mono v.2⟩).1,
      hD'_V ▸ mem_iUnion₂.mpr ⟨v.1, v.2, hH.vertexSet_mono v.2, rfl⟩⟩
  have hvFun_bij : Function.Bijective vFun := by
    refine ⟨fun u v h => ?_, fun y => ?_⟩
    · have hval : (vFun u).1 = (vFun v).1 := congrArg Subtype.val h
      have heq : Γ.iso.vertexEquiv ⟨u.1, hH.vertexSet_mono u.2⟩ =
          Γ.iso.vertexEquiv ⟨v.1, hH.vertexSet_mono v.2⟩ :=
        Subtype.ext hval
      have huv := Γ.iso.vertexEquiv.injective heq
      exact Subtype.ext (Subtype.mk.inj huv)
    · have hy : y.1 ∈ V' := hD'_V ▸ y.2
      obtain ⟨v, hvH, hvG, hvy⟩ := mem_iUnion₂.mp hy
      exact ⟨⟨v, hvH⟩, Subtype.ext hvy⟩
  let eFun : E(H) → D'.E := fun e =>
    ⟨(Γ.iso.edgeEquiv ⟨e.1, hH.edgeSet_mono e.2⟩).1,
      hD'_E ▸ ⟨e, mem_univ e, rfl⟩⟩
  have heFun_bij : Function.Bijective eFun := by
    refine ⟨fun e₁ e₂ h => ?_, fun a => ?_⟩
    · have hval : (eFun e₁).1 = (eFun e₂).1 := congrArg Subtype.val h
      have heq : Γ.iso.edgeEquiv ⟨e₁.1, hH.edgeSet_mono e₁.2⟩ =
          Γ.iso.edgeEquiv ⟨e₂.1, hH.edgeSet_mono e₂.2⟩ :=
        Subtype.ext hval
      have he₁₂ := Γ.iso.edgeEquiv.injective heq
      exact Subtype.ext (Subtype.mk.inj he₁₂)
    · have ha : a.1 ∈ E' := hD'_E ▸ a.2
      obtain ⟨e, _, hea⟩ := ha
      exact ⟨e, Subtype.ext hea⟩
  let iso' : Iso H D'.toGraph :=
    { vertexEquiv := Equiv.ofBijective vFun hvFun_bij
      edgeEquiv := Equiv.ofBijective eFun heFun_bij
      isLink_iff := fun {e u v} => by
        change H.IsLink e.1 u.1 v.1 ↔
          D'.toGraph.IsLink (eFun e).1 (vFun u).1 (vFun v).1
        rw [hsub.isLink_iff (eFun e).2]
        rw [← Γ.iso.isLink_iff ⟨e.1, hH.edgeSet_mono e.2⟩
          ⟨u.1, hH.vertexSet_mono u.2⟩ ⟨v.1, hH.vertexSet_mono v.2⟩]
        exact hH.isLink_iff e.2 }
  let Γ' : GraphDrawing H S := ⟨D', iso'⟩
  have hvert : ∀ v ∈ V(H), graphDrawingVertexSet Γ' v = graphDrawingVertexSet Γ v := by
    intro v hvH
    have hvG : v ∈ V(G) := hH.vertexSet_mono hvH
    rw [graphDrawingVertexSet_eq_singleton' Γ' hvH, graphDrawingVertexSet_eq_singleton' Γ hvG]
    rfl
  have hedge : ∀ e ∈ E(H), graphDrawingEdgeSet Γ' e = graphDrawingEdgeSet Γ e := by
    intro e heH
    have heG : e ∈ E(G) := hH.edgeSet_mono heH
    rw [graphDrawingEdgeSet_eq' Γ' heH, graphDrawingEdgeSet_eq' Γ heG]
    rfl
  refine ⟨Γ', hD'_U, hD'_U ▸ graphDrawingSubgraphU_subset_drawing_U Γ H, hsub,
    fun _ => rfl, hvert, hedge, fun P hPH => ?_⟩
  simp only [graphDrawingSubgraphU]
  congr 1
  · ext x
    simp only [mem_iUnion, exists_prop]
    exact ⟨fun ⟨v, hvP, hx⟩ => ⟨v, hvP, hvert v (hPH.vertexSet_mono hvP) ▸ hx⟩,
      fun ⟨v, hvP, hx⟩ => ⟨v, hvP, (hvert v (hPH.vertexSet_mono hvP)).symm ▸ hx⟩⟩
  · ext x
    simp only [mem_iUnion, exists_prop]
    exact ⟨fun ⟨e, heP, hx⟩ => ⟨e, heP, by rw [← hedge e (hPH.edgeSet_mono heP)]; exact hx⟩,
      fun ⟨e, heP, hx⟩ => ⟨e, heP, by rw [hedge e (hPH.edgeSet_mono heP)]; exact hx⟩⟩

/-- Subgraph restriction of a rural neighborhood: if `N` is rural, `N'.G ≤ N.G`,
`N'.Ω.bar = N.Ω.bar ∩ V(N'.G)`, `N'.Ω₀.bar = N.Ω₀.bar ∩ V(N'.G)`, and clockwise triples in `N'.Ω`
and `N'.Ω₀` are clockwise in `N.Ω` and `N.Ω₀`, then `N'` is rural. -/
theorem Neighborhood.IsRural.ofSubgraph {N N' : Neighborhood α β}
    (hrural : N.IsRural) (hG : N'.G ≤ N.G)
    (hbar : N'.Ω.bar = N.Ω.bar ∩ V(N'.G))
    (hcw : ∀ v₁ v₂ v₃ : α, N'.Ω.IsClockwise3 v₁ v₂ v₃ → N.Ω.IsClockwise3 v₁ v₂ v₃)
    (hbar₀ : N'.Ω₀.bar = N.Ω₀.bar ∩ V(N'.G))
    (hcw₀ : ∀ v₁ v₂ v₃ : α, N'.Ω₀.IsClockwise3 v₁ v₂ v₃ → N.Ω₀.IsClockwise3 v₁ v₂ v₃) :
    N'.IsRural := by
  obtain ⟨Γ, Δ, Δ₀, hΔ, hΔ₀_sub, hU_sub, hbd, hbd₀, ⟨φ, hφ_cw, hagrees⟩, hinner⟩ := hrural
  obtain ⟨Γ', hU'_eq, hU'_sub, _, _, hvert, _, _⟩ := GraphDrawing.ofSubgraph Γ hG
  refine ⟨Γ', Δ, Δ₀, hΔ, hΔ₀_sub, hU'_sub.trans hU_sub, ?_, ?_, ⟨φ, hφ_cw, ?_⟩, ?_⟩
  · intro v hv
    rw [hvert v hv, hbd v (hG.vertexSet_mono hv), hbar, mem_inter_iff, and_iff_left hv]
  · intro v hv
    rw [hvert v hv, hbd₀ v (hG.vertexSet_mono hv), hbar₀, mem_inter_iff, and_iff_left hv]
  · refine ⟨fun v hv => ?_, fun v₁ v₂ v₃ h => ?_⟩
    · rw [hvert v (N'.bar_subset hv)]
      exact hagrees.1 v (hbar ▸ hv).1
    · have hv₁ : v₁ ∈ V(N'.G) := N'.bar_subset (h.2.1 v₁ (by simp))
      have hv₂ : v₂ ∈ V(N'.G) := N'.bar_subset (h.2.1 v₂ (by simp))
      have hv₃ : v₃ ∈ V(N'.G) := N'.bar_subset (h.2.1 v₃ (by simp))
      rw [hvert v₁ hv₁, hvert v₂ hv₂, hvert v₃ hv₃]
      exact hagrees.2 v₁ v₂ v₃ (hcw v₁ v₂ v₃ h)
  · rcases hinner with ⟨hΔ₀_emp, hΩ₀_emp⟩ | ⟨hΔ₀_disc, φ₀, hφ₀_cw, hagrees₀⟩
    · left
      refine ⟨hΔ₀_emp, ?_⟩
      rw [hbar₀, hΩ₀_emp, empty_inter]
    · right
      refine ⟨hΔ₀_disc, φ₀, hφ₀_cw, fun v hv => ?_, fun v₁ v₂ v₃ h => ?_⟩
      · rw [hvert v (N'.bar₀_subset hv)]
        exact hagrees₀.1 v (hbar₀ ▸ hv).1
      · have hv₁ : v₁ ∈ V(N'.G) := N'.bar₀_subset (h.2.1 v₁ (by simp))
        have hv₂ : v₂ ∈ V(N'.G) := N'.bar₀_subset (h.2.1 v₂ (by simp))
        have hv₃ : v₃ ∈ V(N'.G) := N'.bar₀_subset (h.2.1 v₃ (by simp))
        rw [hvert v₁ hv₁, hvert v₂ hv₂, hvert v₃ hv₃]
        exact hagrees₀.2 v₁ v₂ v₃ (hcw₀ v₁ v₂ v₃ h)

/-- Transport a drawing `D : Drawing S` whose point set `D.U` is compact along a map `f : S → S'`
continuous and injective on `D.U`. -/
theorem exists_transportOn_of_isCompact {S S' : Type*} [TopologicalSpace S] [Nonempty S]
    [TopologicalSpace S'] [T2Space S']
    (D : Drawing S) (hUc : IsCompact D.U) {f : S → S'} (hf : ContinuousOn f D.U)
    (hinj : InjOn f D.U) :
    ∃ D' : Drawing S', D'.U = f '' D.U ∧ D'.V = f '' D.V ∧ D'.E = image f '' D.E ∧
      ∀ e ∈ D.E, closure (f '' e) = f '' closure e := by
  classical
  have : CompactSpace D.U := isCompact_iff_compactSpace.mp hUc
  let ι : D.U → S' := fun x => f x.1
  have hιc : Continuous ι := hf.comp_continuous continuous_subtype_val Subtype.prop
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
  have harc := arcComponentsIn_image (F := D.U \ D.V) (hf.mono hsub) hgF fun x hx => hgf x hx.1
  have hdiff : f '' D.U \ f '' D.V = f '' (D.U \ D.V) :=
    (InjOn.image_sdiff_subset hinj D.V_subset_U).symm
  have hcl : ∀ e ∈ D.E, closure (f '' e) = f '' closure e := by
    intro e he
    have he_sub : closure e ⊆ D.U := D.closure_subset_U he
    apply subset_antisymm
    · have hc : IsCompact (f '' closure e) :=
        (hUc.of_isClosed_subset isClosed_closure he_sub).image_of_continuousOn (hf.mono he_sub)
      exact closure_minimal (image_mono subset_closure) hc.isClosed
    · rintro _ ⟨x, hx, rfl⟩
      rw [_root_.mem_closure_iff]
      intro V hV hfxV
      obtain ⟨W, hW_open, hxW, hWV⟩ :=
        mem_nhdsWithin.mp (hf.mono he_sub x hx (hV.mem_nhds hfxV))
      obtain ⟨y, hyW, hye⟩ := _root_.mem_closure_iff.mp hx W hW_open hxW
      exact ⟨f y, hWV ⟨hyW, subset_closure hye⟩, mem_image_of_mem f hye⟩
  have hcap : ∀ e ∈ D.E, closure (f '' e) ∩ f '' D.V = f '' (closure e ∩ D.V) := by
    intro e he
    rw [hcl e he]
    exact (InjOn.image_inter hinj (D.closure_subset_U he) D.V_subset_U).symm
  refine ⟨⟨f '' D.U, f '' D.V, image_mono D.V_subset_U,
    (hUc.image_of_continuousOn hf).isClosed,
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
        have hc₁ : Continuous fun t => f (φ₁ t).1 :=
          hf.comp_continuous (continuous_subtype_val.comp φ₁.continuous)
            fun t => D.closure_subset_U he (φ₁ t).2
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
        have hc₂ : Continuous fun t => f (φ₂ t).1 :=
          hf.comp_continuous (continuous_subtype_val.comp φ₂.continuous)
            fun t => D.closure_subset_U he (φ₂ t).2
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

/-- Transport a `GraphDrawing G S` with compact `U` along a map `f : S → S'` continuous and
injective on `U`. -/
theorem GraphDrawing.transportOn {S S' : Type*} [TopologicalSpace S] [T2Space S] [Nonempty S]
    [TopologicalSpace S'] [T2Space S'] {G : Graph α β}
    (Γ : GraphDrawing G S) (hUc : IsCompact Γ.drawing.U)
    {f : S → S'} (hf : ContinuousOn f Γ.drawing.U) (hinj : InjOn f Γ.drawing.U) :
    ∃ Γ' : GraphDrawing G S',
      Γ'.drawing.U = f '' Γ.drawing.U ∧
      Γ'.drawing.V = f '' Γ.drawing.V ∧
      (∀ v : V(G), (Γ'.iso.vertexEquiv v).1 = f (Γ.iso.vertexEquiv v).1) ∧
      (∀ v, graphDrawingVertexSet Γ' v = f '' graphDrawingVertexSet Γ v) ∧
      (∀ e, graphDrawingEdgeSet Γ' e = f '' graphDrawingEdgeSet Γ e) ∧
      (∀ H, graphDrawingSubgraphU Γ' H = f '' graphDrawingSubgraphU Γ H) := by
  obtain ⟨D', hU', hV', hE', hcl⟩ := exists_transportOn_of_isCompact Γ.drawing hUc hf hinj
  have hinjV : InjOn f Γ.drawing.V := hinj.mono Γ.drawing.V_subset_U
  have hinjE : InjOn (image f) Γ.drawing.E := by
    intro e₁ he₁ e₂ he₂ heq
    ext x
    constructor
    · intro hx₁
      have hfx : f x ∈ f '' e₂ := heq ▸ ⟨x, hx₁, rfl⟩
      obtain ⟨y, hy₂, hfy⟩ := hfx
      have hxy : y = x :=
        hinj (Γ.drawing.closure_subset_U he₂ (subset_closure hy₂))
          (Γ.drawing.closure_subset_U he₁ (subset_closure hx₁)) hfy
      exact hxy ▸ hy₂
    · intro hx₂
      have hfx : f x ∈ f '' e₁ := heq.symm ▸ ⟨x, hx₂, rfl⟩
      obtain ⟨y, hy₁, hfy⟩ := hfx
      have hxy : y = x :=
        hinj (Γ.drawing.closure_subset_U he₁ (subset_closure hy₁))
          (Γ.drawing.closure_subset_U he₂ (subset_closure hx₂)) hfy
      exact hxy ▸ hy₁
  let vFun : Γ.drawing.V → D'.V := fun x => ⟨f x.1, hV' ▸ ⟨x.1, x.2, rfl⟩⟩
  have hvFun_bij : Function.Bijective vFun :=
    ⟨fun x y h => Subtype.ext (hinjV x.2 y.2 (congrArg Subtype.val h)),
     fun z => by
       have hz : z.1 ∈ f '' Γ.drawing.V := hV' ▸ z.2
       obtain ⟨x, hx, hfx⟩ := hz
       exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩⟩
  let eFun : Γ.drawing.E → D'.E := fun e => ⟨f '' e.1, hE' ▸ ⟨e.1, e.2, rfl⟩⟩
  have heFun_bij : Function.Bijective eFun :=
    ⟨fun e₁ e₂ h => Subtype.ext (hinjE e₁.2 e₂.2 (congrArg Subtype.val h)),
     fun a => by
       have ha : a.1 ∈ image f '' Γ.drawing.E := hE' ▸ a.2
       obtain ⟨e, he, hfe⟩ := ha
       exact ⟨⟨e, he⟩, Subtype.ext hfe⟩⟩
  let vEquiv : Γ.drawing.V ≃ D'.V := Equiv.ofBijective vFun hvFun_bij
  let eEquiv : Γ.drawing.E ≃ D'.E := Equiv.ofBijective eFun heFun_bij
  let iso' : Iso G D'.toGraph :=
    { vertexEquiv := Γ.iso.vertexEquiv.trans vEquiv
      edgeEquiv := Γ.iso.edgeEquiv.trans eEquiv
      isLink_iff := fun {e x y} => by
        rw [Γ.iso.isLink_iff]
        let e₀ := Γ.iso.edgeEquiv e
        let x₀ := Γ.iso.vertexEquiv x
        let y₀ := Γ.iso.vertexEquiv y
        change Γ.drawing.toGraph.IsLink e₀.1 x₀.1 y₀.1 ↔
          D'.toGraph.IsLink (f '' e₀.1) (f x₀.1) (f y₀.1)
        have he' : f '' e₀.1 ∈ D'.E := hE' ▸ ⟨e₀.1, e₀.2, rfl⟩
        have hx' : f x₀.1 ∈ D'.V := hV' ▸ ⟨x₀.1, x₀.2, rfl⟩
        have hy' : f y₀.1 ∈ D'.V := hV' ▸ ⟨y₀.1, y₀.2, rfl⟩
        have hcap : closure (f '' e₀.1) ∩ D'.V = f '' (closure e₀.1 ∩ Γ.drawing.V) := by
          rw [hcl e₀.1 e₀.2, hV']
          exact (InjOn.image_inter hinj (Γ.drawing.closure_subset_U e₀.2) Γ.drawing.V_subset_U).symm
        constructor
        · rintro ⟨_, _, _, hc⟩
          refine ⟨he', hx', hy', ?_⟩
          rw [hcap, hc, image_pair]
        · rintro ⟨_, _, _, hc'⟩
          refine ⟨e₀.2, x₀.2, y₀.2, ?_⟩
          rw [hcap, ← image_pair] at hc'
          have hsub1 : closure e₀.1 ∩ Γ.drawing.V ⊆ Γ.drawing.U :=
            inter_subset_right.trans Γ.drawing.V_subset_U
          have hsub2 : ({x₀.1, y₀.1} : Set S) ⊆ Γ.drawing.U := by
            rintro z (rfl | rfl)
            · exact Γ.drawing.V_subset_U x₀.2
            · exact Γ.drawing.V_subset_U y₀.2
          exact hinj.image_eq_image_iff hsub1 hsub2 |>.mp hc' }
  let Γ' : GraphDrawing G S' := ⟨D', iso'⟩
  have hvert : ∀ v, graphDrawingVertexSet Γ' v = f '' graphDrawingVertexSet Γ v := by
    intro v
    by_cases hv : v ∈ V(G)
    · rw [graphDrawingVertexSet_eq_singleton' Γ' hv, graphDrawingVertexSet_eq_singleton' Γ hv,
        image_singleton]
      rfl
    · rw [graphDrawingVertexSet_of_notMem Γ' hv, graphDrawingVertexSet_of_notMem Γ hv, image_empty]
  have hedge : ∀ e, graphDrawingEdgeSet Γ' e = f '' graphDrawingEdgeSet Γ e := by
    intro e
    by_cases he : e ∈ E(G)
    · rw [graphDrawingEdgeSet_eq' Γ' he, graphDrawingEdgeSet_eq' Γ he]
      rfl
    · rw [graphDrawingEdgeSet_of_notMem Γ' he, graphDrawingEdgeSet_of_notMem Γ he, image_empty]
  have hedge_cl : ∀ e, closure (graphDrawingEdgeSet Γ' e) = f '' closure (graphDrawingEdgeSet Γ e)
    := by
    intro e
    by_cases he : e ∈ E(G)
    · rw [graphDrawingEdgeSet_eq' Γ' he, graphDrawingEdgeSet_eq' Γ he]
      exact hcl (Γ.iso.edgeEquiv ⟨e, he⟩).1 (Γ.iso.edgeEquiv ⟨e, he⟩).2
    · simp [graphDrawingEdgeSet_of_notMem Γ' he, graphDrawingEdgeSet_of_notMem Γ he]
  refine ⟨Γ', hU', hV', fun _ => rfl, hvert, hedge, fun H => ?_⟩
  simp only [graphDrawingSubgraphU, image_union, image_iUnion, hvert, hedge_cl]

theorem isInteriorPoint_plane (x : EuclideanPlane) : IsInteriorPoint x := by
  let B : Set ℂ := ball (complexPlane.symm x) 1
  let U : Set EuclideanPlane := complexPlane.symm ⁻¹' B
  have hU : IsOpen U := isOpen_ball.preimage complexPlane.symm.continuous
  have hxU : x ∈ U := mem_ball_self zero_lt_one
  let f₁ : U ≃ₜ B := {
    toFun := fun y => ⟨complexPlane.symm y.1, y.2⟩
    invFun := fun z => ⟨complexPlane z.1, by
      change complexPlane.symm (complexPlane z.1) ∈ B
      rw [LinearIsometryEquiv.symm_apply_apply]
      exact z.2⟩
    left_inv := fun y => Subtype.ext (LinearIsometryEquiv.apply_symm_apply complexPlane y.1)
    right_inv := fun z => Subtype.ext (LinearIsometryEquiv.symm_apply_apply complexPlane z.1)
    continuous_toFun := Continuous.subtype_mk
      (complexPlane.symm.continuous.comp continuous_subtype_val) (fun y => y.2)
    continuous_invFun := Continuous.subtype_mk
      (complexPlane.continuous.comp continuous_subtype_val) (fun z => by
        change complexPlane.symm (complexPlane z.1) ∈ B
        rw [LinearIsometryEquiv.symm_apply_apply]
        exact z.2)
  }
  obtain ⟨f₂⟩ := exists_homeomorph_ball (complexPlane.symm x) zero_lt_one
  exact ⟨U, hU, hxU, ⟨f₁.trans f₂⟩⟩

theorem isManifoldPoint_plane (x : EuclideanPlane) : IsManifoldPoint x :=
  (isInteriorPoint_plane x).isManifoldPoint

theorem frontier_eq_discBd_plane {D : Set EuclideanPlane} (hD : IsClosedDisc D) :
    frontier D = discBd D := by
  have hman : ∀ x : EuclideanPlane, IsManifoldPoint x := isManifoldPoint_plane
  have hcl : IsClosed D := hD.isCompact.isClosed
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  obtain ⟨u1, -⟩ := c.union_ball
  have hO := c.isOpen_image_ball hman
  have hsub : g '' ball 0 1 ⊆ D := fun x hx => u1 ▸ Or.inl hx
  apply subset_antisymm
  · intro x hx
    have hxD : x ∈ D := hcl.frontier_subset hx
    rw [← u1] at hxD
    rcases hxD with h' | h'
    · exact absurd (interior_maximal hsub hO h') hx.2
    · exact h'
  · intro x hx
    have hxD : x ∈ D := Surface.discBd_subset _ hx
    refine ⟨subset_closure hxD, fun hint => ?_⟩
    obtain ⟨U, hU, hxU, ⟨f⟩⟩ := isInteriorPoint_plane x
    classical
    let G : ℂ → EuclideanPlane := fun w =>
      if hw : complexPlane w ∈ OpenUnitDisc then (f.symm ⟨_, hw⟩).1 else x
    let M : Set ℂ := complexPlane ⁻¹' OpenUnitDisc
    have hMo : IsOpen M := by
      have : IsOpen OpenUnitDisc := by
        have := Metric.isOpen_ball (x := (0 : EuclideanPlane)) (ε := 1)
        convert this using 1
        ext y
        simp [OpenUnitDisc]
      exact this.preimage complexPlane.continuous
    have hG : ∀ w (hw : w ∈ M), G w = (f.symm ⟨_, hw⟩).1 := fun w hw => by
      have hw' : complexPlane w ∈ OpenUnitDisc := hw
      simp only [G, hw', dite_true]
    have hGc : ContinuousOn G M := by
      rw [continuousOn_iff_continuous_domRestrict]
      have : M.domRestrict G = fun w : M => (f.symm ⟨complexPlane w.1, w.2⟩).1 :=
        funext fun w => hG w.1 w.2
      rw [this]
      refine continuous_subtype_val.comp (f.symm.continuous.comp ?_)
      exact Continuous.subtype_mk (complexPlane.continuous.comp continuous_subtype_val)
        (fun w => w.2)
    have hGi : InjOn G M := by
      intro a ha b hb hab
      rw [hG a ha, hG b hb] at hab
      have h₁ := f.symm.injective (Subtype.ext hab)
      exact complexPlane.injective (congrArg Subtype.val h₁)
    let B : Set ℂ := M ∩ G ⁻¹' interior D
    have hBo : IsOpen B := hGc.isOpen_inter_preimage hMo isOpen_interior
    have hBD : MapsTo G B D := fun w hw => interior_subset hw.2
    have hHc : ContinuousOn (h ∘ G) B := c.hc.comp (hGc.mono inter_subset_left) hBD
    have hHi : InjOn (h ∘ G) B := by
      intro a ha b hb hab
      apply hGi ha.1 hb.1
      have := congrArg g hab
      simpa [c.gh (hBD ha), c.gh (hBD hb)] using this
    have hOpen := isOpen_image_of_injOn hBo hHc hHi
    set w₀ : ℂ := complexPlane.symm (f ⟨x, hxU⟩).1 with hw₀
    have hw₀M : w₀ ∈ M := by
      change complexPlane w₀ ∈ OpenUnitDisc
      rw [hw₀, LinearIsometryEquiv.apply_symm_apply]
      exact (f ⟨x, hxU⟩).2
    have hGw : G w₀ = x := by
      rw [hG w₀ hw₀M]
      have : (⟨complexPlane w₀, hw₀M⟩ : OpenUnitDisc) = f ⟨x, hxU⟩ := by
        apply Subtype.ext
        change complexPlane w₀ = _
        rw [hw₀, LinearIsometryEquiv.apply_symm_apply]
      rw [this, f.symm_apply_apply]
    have hw₀B : w₀ ∈ B := ⟨hw₀M, show G w₀ ∈ interior D from hGw ▸ hint⟩
    have hball : h x ∈ interior (closedBall (0 : ℂ) 1) := by
      refine mem_interior.mpr ⟨_, ?_, hOpen, ⟨w₀, hw₀B, by simp [hGw]⟩⟩
      rintro _ ⟨w, hw, rfl⟩
      exact c.hm (hBD hw)
    rw [interior_closedBall _ one_ne_zero] at hball
    have hsph : h x ∈ sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem h hx
    rw [mem_ball, mem_sphere.mp hsph] at hball
    exact lt_irrefl _ hball

theorem subBd_eq_discBd_plane {D : Set EuclideanPlane} (hD : IsClosedDisc D) :
    subBd D = discBd D := by
  rw [GraphMinor.GM11.subBd_eq_frontier, frontier_eq_discBd_plane hD]

theorem interior_eq_discInt_plane {D : Set EuclideanPlane} (hD : IsClosedDisc D) :
    interior D = discInt D := by
  ext x
  simp only [discInt, mem_sdiff, ← frontier_eq_discBd_plane hD, frontier,
    hD.isCompact.isClosed.closure_eq]
  exact ⟨fun hx => ⟨interior_subset hx, fun h => h.2 hx⟩,
    fun ⟨hxD, hnf⟩ => by_contra fun hni => hnf ⟨hxD, hni⟩⟩

/-- Radial shrink factor on `ℂ` fixing a subset `F₀` of the unit circle and shrinking the rest
toward the origin. -/
noncomputable def radialShrinkFactor (F₀ : Set ℂ) (z : ℂ) : ℝ := by
  classical
  exact if F₀.Nonempty then (1 / 8 : ℝ) * Metric.infDist z F₀ else (1 / 2 : ℝ)

/-- Radial shrink map `z ↦ (1 - τ(z)) z` on `ℂ`. -/
noncomputable def radialShrinkMap (F₀ : Set ℂ) (z : ℂ) : ℂ :=
  ((1 - radialShrinkFactor F₀ z : ℝ) : ℂ) * z

theorem continuous_radialShrinkFactor (F₀ : Set ℂ) :
    Continuous (radialShrinkFactor F₀) := by
  classical
  unfold radialShrinkFactor
  split_ifs
  · exact continuous_const.mul (Metric.continuous_infDist_pt F₀)
  · exact continuous_const

theorem continuous_radialShrinkMap (F₀ : Set ℂ) :
    Continuous (radialShrinkMap F₀) := by
  unfold radialShrinkMap
  exact (Complex.continuous_ofReal.comp (continuous_const.sub (continuous_radialShrinkFactor
    F₀))).mul
    continuous_id

theorem radialShrinkFactor_nonneg (F₀ : Set ℂ) (z : ℂ) :
    0 ≤ radialShrinkFactor F₀ z := by
  by_cases hne : F₀.Nonempty <;> simp only [radialShrinkFactor, hne, ite_true, ite_false]
  · exact mul_nonneg (by norm_num) Metric.infDist_nonneg
  · norm_num

theorem radialShrinkFactor_le_half {F₀ : Set ℂ} (hF₀ : F₀ ⊆ Metric.sphere (0 : ℂ) 1)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    radialShrinkFactor F₀ z ≤ 1 / 2 := by
  by_cases hne : F₀.Nonempty <;> simp only [radialShrinkFactor, hne, ite_true, ite_false]
  · rcases hne with ⟨w, hw⟩
    have hle : Metric.infDist z F₀ ≤ dist z w := Metric.infDist_le_dist_of_mem hw
    have hzw : dist z w ≤ 2 := by
      have hz0 : dist z 0 ≤ 1 := Metric.mem_closedBall.mp hz
      have hw0 : dist w 0 = 1 := Metric.mem_sphere.mp (hF₀ hw)
      calc dist z w ≤ dist z 0 + dist 0 w := dist_triangle z 0 w
        _ = dist z 0 + dist w 0 := by rw [dist_comm 0 w]
        _ ≤ 1 + 1 := by linarith
        _ = 2 := by norm_num
    linarith
  · norm_num

theorem abs_radialShrinkFactor_sub_le (F₀ : Set ℂ) (z w : ℂ) :
    |radialShrinkFactor F₀ z - radialShrinkFactor F₀ w| ≤ (1 / 8 : ℝ) * dist z w := by
  by_cases hne : F₀.Nonempty <;> simp only [radialShrinkFactor, hne, ite_true, ite_false]
  · have hsub : (1 / 8 : ℝ) * Metric.infDist z F₀ - (1 / 8 : ℝ) * Metric.infDist w F₀ =
        (1 / 8 : ℝ) * (Metric.infDist z F₀ - Metric.infDist w F₀) := by ring
    have hdist : |Metric.infDist z F₀ - Metric.infDist w F₀| ≤ dist z w := by
      rw [abs_sub_le_iff]
      refine ⟨?_, ?_⟩
      · linarith [Metric.infDist_le_infDist_add_dist (x := z) (y := w) (s := F₀)]
      · have h2 := Metric.infDist_le_infDist_add_dist (x := w) (y := z) (s := F₀)
        rw [dist_comm] at h2
        linarith
    rw [hsub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8)]
    exact mul_le_mul_of_nonneg_left hdist (by norm_num)
  · simp only [sub_self, abs_zero]
    exact mul_nonneg (by norm_num) dist_nonneg

theorem injOn_radialShrinkMap {F₀ : Set ℂ} (hF₀ : F₀ ⊆ Metric.sphere (0 : ℂ) 1) :
    InjOn (radialShrinkMap F₀) (Metric.closedBall (0 : ℂ) 1) := by
  intro z hz w hw heq
  have hτz : radialShrinkFactor F₀ z ≤ 1 / 2 := radialShrinkFactor_le_half hF₀ hz
  have hτz0 : 0 ≤ radialShrinkFactor F₀ z := radialShrinkFactor_nonneg F₀ z
  have hlip : |radialShrinkFactor F₀ z - radialShrinkFactor F₀ w| ≤ (1 / 8 : ℝ) * ‖z - w‖ := by
    simpa [dist_eq_norm] using abs_radialShrinkFactor_sub_le F₀ z w
  have hw1 : ‖w‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hw
  have hid : z - w = ((radialShrinkFactor F₀ z : ℝ) : ℂ) * (z - w) +
      ((radialShrinkFactor F₀ z - radialShrinkFactor F₀ w : ℝ) : ℂ) * w := by
    have heq' : ((1 - radialShrinkFactor F₀ z : ℝ) : ℂ) * z =
        ((1 - radialShrinkFactor F₀ w : ℝ) : ℂ) * w := heq
    push_cast at heq' ⊢
    linear_combination heq'
  have hnorm1 : ‖((radialShrinkFactor F₀ z : ℝ) : ℂ) * (z - w)‖ =
      |radialShrinkFactor F₀ z| * ‖z - w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hnorm2 : ‖((radialShrinkFactor F₀ z - radialShrinkFactor F₀ w : ℝ) : ℂ) * w‖ =
      |radialShrinkFactor F₀ z - radialShrinkFactor F₀ w| * ‖w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hnorm : ‖z - w‖ ≤ (5 / 8 : ℝ) * ‖z - w‖ := by
    calc ‖z - w‖
      _ = ‖((radialShrinkFactor F₀ z : ℝ) : ℂ) * (z - w) +
            ((radialShrinkFactor F₀ z - radialShrinkFactor F₀ w : ℝ) : ℂ) * w‖ := by
          rw [← hid]
      _ ≤ ‖((radialShrinkFactor F₀ z : ℝ) : ℂ) * (z - w)‖ +
            ‖((radialShrinkFactor F₀ z - radialShrinkFactor F₀ w : ℝ) : ℂ) * w‖ :=
          norm_add_le _ _
      _ = |radialShrinkFactor F₀ z| * ‖z - w‖ +
            |radialShrinkFactor F₀ z - radialShrinkFactor F₀ w| * ‖w‖ := by
          rw [hnorm1, hnorm2]
      _ ≤ (1 / 2 : ℝ) * ‖z - w‖ + ((1 / 8 : ℝ) * ‖z - w‖) * 1 := by
          rw [abs_of_nonneg hτz0]
          gcongr
      _ = (5 / 8 : ℝ) * ‖z - w‖ := by ring
  have hzero : ‖z - w‖ = 0 := by
    have hnonneg : 0 ≤ ‖z - w‖ := norm_nonneg _
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

theorem radialShrinkMap_eq_self {F₀ : Set ℂ} {z : ℂ} (hz : z ∈ F₀) :
    radialShrinkMap F₀ z = z := by
  have hne : F₀.Nonempty := ⟨z, hz⟩
  have hdist : Metric.infDist z F₀ = 0 := Metric.infDist_zero_of_mem hz
  simp [radialShrinkMap, radialShrinkFactor, hne, hdist]

theorem radialShrinkMap_mem_ball {F₀ : Set ℂ} (hF₀ : F₀ ⊆ Metric.sphere (0 : ℂ) 1)
    (hF₀_closed : IsClosed F₀) {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) (hzF : z ∉ F₀) :
    radialShrinkMap F₀ z ∈ Metric.ball (0 : ℂ) 1 := by
  have hτ_pos : 0 < radialShrinkFactor F₀ z := by
    by_cases hne : F₀.Nonempty <;> simp only [radialShrinkFactor, hne, ite_true, ite_false]
    · have hpos : 0 < Metric.infDist z F₀ :=
        (hF₀_closed.notMem_iff_infDist_pos hne).mp hzF
      linarith
    · norm_num
  have hτ_le : radialShrinkFactor F₀ z ≤ 1 / 2 := radialShrinkFactor_le_half hF₀ hz
  have hz1 : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
  rw [Metric.mem_ball, dist_zero_right, radialShrinkMap, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by linarith)]
  nlinarith

theorem radialShrinkMap_mem_closedBall {F₀ : Set ℂ} (hF₀ : F₀ ⊆ Metric.sphere (0 : ℂ) 1)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    radialShrinkMap F₀ z ∈ Metric.closedBall (0 : ℂ) 1 := by
  have hτ_nonneg : 0 ≤ radialShrinkFactor F₀ z := radialShrinkFactor_nonneg F₀ z
  have hτ_le : radialShrinkFactor F₀ z ≤ 1 / 2 := radialShrinkFactor_le_half hF₀ hz
  have hz1 : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
  rw [Metric.mem_closedBall, dist_zero_right, radialShrinkMap, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by linarith)]
  nlinarith

/-- Interpolates from the identity to the radial shrink map, with time clamped to `[0, 1]`. -/
noncomputable def radialShrinkHomotopy (F₀ : Set ℂ) (u : ℝ) (z : ℂ) : ℂ :=
  ((1 - max 0 (min u 1) * radialShrinkFactor F₀ z : ℝ) : ℂ) * z

theorem continuous_radialShrinkHomotopy (F₀ : Set ℂ) :
    Continuous (fun p : ℝ × ℂ => radialShrinkHomotopy F₀ p.1 p.2) := by
  unfold radialShrinkHomotopy
  have hcl : Continuous (fun p : ℝ × ℂ => max 0 (min p.1 1)) :=
    continuous_const.max (continuous_fst.min continuous_const)
  have hτ : Continuous (fun p : ℝ × ℂ => radialShrinkFactor F₀ p.2) :=
    (continuous_radialShrinkFactor F₀).comp continuous_snd
  exact (Complex.continuous_ofReal.comp (continuous_const.sub (hcl.mul hτ))).mul continuous_snd

theorem radialShrinkHomotopy_zero (F₀ : Set ℂ) (z : ℂ) :
    radialShrinkHomotopy F₀ 0 z = z := by
  simp [radialShrinkHomotopy]

theorem radialShrinkHomotopy_one (F₀ : Set ℂ) (z : ℂ) :
    radialShrinkHomotopy F₀ 1 z = radialShrinkMap F₀ z := by
  simp [radialShrinkHomotopy, radialShrinkMap]

theorem radialShrinkHomotopy_mem_closedBall {F₀ : Set ℂ} (hF₀ : F₀ ⊆ Metric.sphere (0 : ℂ) 1)
    (u : ℝ) {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    radialShrinkHomotopy F₀ u z ∈ Metric.closedBall (0 : ℂ) 1 := by
  let c : ℝ := max 0 (min u 1)
  have hc0 : 0 ≤ c := le_max_left 0 _
  have hc1 : c ≤ 1 := max_le zero_le_one (min_le_right u 1)
  have hτ_nonneg : 0 ≤ radialShrinkFactor F₀ z := radialShrinkFactor_nonneg F₀ z
  have hτ_le : radialShrinkFactor F₀ z ≤ 1 / 2 := radialShrinkFactor_le_half hF₀ hz
  have hz1 : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
  have hprod0 : 0 ≤ c * radialShrinkFactor F₀ z := mul_nonneg hc0 hτ_nonneg
  have hprod_le : c * radialShrinkFactor F₀ z ≤ 1 / 2 := by nlinarith
  rw [Metric.mem_closedBall, dist_zero_right]
  change ‖((1 - c * radialShrinkFactor F₀ z : ℝ) : ℂ) * z‖ ≤ 1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  nlinarith

theorem injOn_radialShrinkHomotopy {F₀ : Set ℂ} (hF₀ : F₀ ⊆ Metric.sphere (0 : ℂ) 1) (u : ℝ) :
    InjOn (radialShrinkHomotopy F₀ u) (Metric.closedBall (0 : ℂ) 1) := by
  intro z hz w hw heq
  let c : ℝ := max 0 (min u 1)
  have hc0 : 0 ≤ c := le_max_left 0 _
  have hc1 : c ≤ 1 := max_le zero_le_one (min_le_right u 1)
  have hτz : c * radialShrinkFactor F₀ z ≤ 1 / 2 := by
    nlinarith [radialShrinkFactor_le_half hF₀ hz, radialShrinkFactor_nonneg F₀ z]
  have hτz0 : 0 ≤ c * radialShrinkFactor F₀ z := mul_nonneg hc0 (radialShrinkFactor_nonneg F₀ z)
  have hlip : |c * radialShrinkFactor F₀ z - c * radialShrinkFactor F₀ w| ≤
      (1 / 8 : ℝ) * ‖z - w‖ := by
    have h1 : |radialShrinkFactor F₀ z - radialShrinkFactor F₀ w| ≤ (1 / 8 : ℝ) * ‖z - w‖ := by
      simpa [dist_eq_norm] using abs_radialShrinkFactor_sub_le F₀ z w
    rw [← mul_sub, abs_mul, abs_of_nonneg hc0]
    nlinarith [abs_nonneg (radialShrinkFactor F₀ z - radialShrinkFactor F₀ w)]
  have hw1 : ‖w‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hw
  have hid : z - w = ((c * radialShrinkFactor F₀ z : ℝ) : ℂ) * (z - w) +
      ((c * radialShrinkFactor F₀ z - c * radialShrinkFactor F₀ w : ℝ) : ℂ) * w := by
    have heq' : ((1 - c * radialShrinkFactor F₀ z : ℝ) : ℂ) * z =
        ((1 - c * radialShrinkFactor F₀ w : ℝ) : ℂ) * w := heq
    push_cast at heq' ⊢
    linear_combination heq'
  have hnorm1 : ‖((c * radialShrinkFactor F₀ z : ℝ) : ℂ) * (z - w)‖ =
      |c * radialShrinkFactor F₀ z| * ‖z - w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hnorm2 : ‖((c * radialShrinkFactor F₀ z - c * radialShrinkFactor F₀ w : ℝ) : ℂ) * w‖ =
      |c * radialShrinkFactor F₀ z - c * radialShrinkFactor F₀ w| * ‖w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hnorm : ‖z - w‖ ≤ (5 / 8 : ℝ) * ‖z - w‖ := by
    calc ‖z - w‖
      _ = ‖((c * radialShrinkFactor F₀ z : ℝ) : ℂ) * (z - w) +
            ((c * radialShrinkFactor F₀ z - c * radialShrinkFactor F₀ w : ℝ) : ℂ) * w‖ := by
          rw [← hid]
      _ ≤ ‖((c * radialShrinkFactor F₀ z : ℝ) : ℂ) * (z - w)‖ +
            ‖((c * radialShrinkFactor F₀ z - c * radialShrinkFactor F₀ w : ℝ) : ℂ) * w‖ :=
          norm_add_le _ _
      _ = |c * radialShrinkFactor F₀ z| * ‖z - w‖ +
            |c * radialShrinkFactor F₀ z - c * radialShrinkFactor F₀ w| * ‖w‖ := by
          rw [hnorm1, hnorm2]
      _ ≤ (1 / 2 : ℝ) * ‖z - w‖ + ((1 / 8 : ℝ) * ‖z - w‖) * 1 := by
          rw [abs_of_nonneg hτz0]
          gcongr
      _ = (5 / 8 : ℝ) * ‖z - w‖ := by ring
  have hzero : ‖z - w‖ = 0 := by
    have hnonneg : 0 ≤ ‖z - w‖ := norm_nonneg _
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

/-- Given a closed disc `D` in a `T2Space` `S` and a closed subset `F ⊆ discBd D`, there is a
continuous injective self-map `Ψ : S → S` on `D` with a continuous left inverse `Ψ'` on `Ψ '' D`
that fixes `F` pointwise and sends `D \ F` into `D \ discBd D`, together with a homotopy `Ψ_hom`
through injective maps on `D` from `id` to `Ψ`. -/
theorem exists_disc_shrink_map_with_homotopy {S : Type w} [TopologicalSpace S] [T2Space S]
  [Nonempty S]
    {D F : Set S} (hD : IsClosedDisc D) (hF_closed : IsClosed F) (hF_sub : F ⊆ discBd D) :
    ∃ (Ψ Ψ' : S → S) (Ψ_hom : ℝ → S → S),
      ContinuousOn Ψ D ∧
      ContinuousOn Ψ' (Ψ '' D) ∧
      LeftInvOn Ψ' Ψ D ∧
      InjOn Ψ D ∧
      Ψ '' D ⊆ D ∧
      (∀ x ∈ F, Ψ x = x) ∧
      (∀ x ∈ D \ F, Ψ x ∈ D \ discBd D) ∧
      ContinuousOn (fun p : ℝ × S => Ψ_hom p.1 p.2) (univ ×ˢ D) ∧
      (∀ x ∈ D, Ψ_hom 0 x = x) ∧
      (∀ x ∈ D, Ψ_hom 1 x = Ψ x) ∧
      (∀ u : ℝ, InjOn (Ψ_hom u) D) := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  have hFD : F ⊆ D := hF_sub.trans (Surface.discBd_subset D)
  let F₀ : Set ℂ := h '' F
  have hF₀_sphere : F₀ ⊆ Metric.sphere (0 : ℂ) 1 := by
    rw [← c.bd]
    exact image_mono hF_sub
  have hF_compact : IsCompact F := hD.isCompact.of_isClosed_subset hF_closed hFD
  have hF₀_closed : IsClosed F₀ :=
    (hF_compact.image_of_continuousOn (c.hc.mono hFD)).isClosed
  let Ψ : S → S := fun x => g (radialShrinkMap F₀ (h x))
  let Ψ_hom : ℝ → S → S := fun u x => g (radialShrinkHomotopy F₀ u (h x))
  have hΦ_maps : MapsTo (radialShrinkMap F₀) (Metric.closedBall (0 : ℂ) 1)
      (Metric.closedBall (0 : ℂ) 1) :=
    fun z hz => radialShrinkMap_mem_closedBall hF₀_sphere hz
  have hΨ_cont : ContinuousOn Ψ D := by
    refine c.gc.comp ((continuous_radialShrinkMap F₀).continuousOn.comp c.hc c.hm) ?_
    exact hΦ_maps.comp c.hm
  have hΨ_inj : InjOn Ψ D := by
    intro x hx y hy heq
    have h₁ : radialShrinkMap F₀ (h x) = radialShrinkMap F₀ (h y) :=
      c.injOn (hΦ_maps (c.hm hx)) (hΦ_maps (c.hm hy)) heq
    have h₂ : h x = h y := injOn_radialShrinkMap hF₀_sphere (c.hm hx) (c.hm hy) h₁
    exact c.gh.injOn hx hy h₂
  obtain ⟨Ψ', hΨ'_cont, hΨ'_left⟩ := exists_inv_of_compactOn hD.isCompact hΨ_cont hΨ_inj
  refine ⟨Ψ, Ψ', Ψ_hom, hΨ_cont, hΨ'_cont, hΨ'_left, hΨ_inj, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [← c.g_closedBall]
    exact mem_image_of_mem g (hΦ_maps (c.hm hx))
  · intro x hx
    have hx₀ : h x ∈ F₀ := mem_image_of_mem h hx
    change g (radialShrinkMap F₀ (h x)) = x
    rw [radialShrinkMap_eq_self hx₀, c.gh (hFD hx)]
  · rintro x ⟨hxD, hxF⟩
    have hxhF₀ : h x ∉ F₀ := by
      rintro ⟨y, hyF, hyx⟩
      exact hxF (c.gh.injOn hxD (hFD hyF) hyx.symm ▸ hyF)
    have hball : radialShrinkMap F₀ (h x) ∈ Metric.ball (0 : ℂ) 1 :=
      radialShrinkMap_mem_ball hF₀_sphere hF₀_closed (c.hm hxD) hxhF₀
    have hmem : g (radialShrinkMap F₀ (h x)) ∈ g '' Metric.ball (0 : ℂ) 1 :=
      mem_image_of_mem g hball
    obtain ⟨u1, u2⟩ := c.union_ball
    exact ⟨u1 ▸ Or.inl hmem, disjoint_left.mp u2 hmem⟩
  · have hmap : MapsTo Prod.snd ((univ : Set ℝ) ×ˢ D) D := fun _ hp => hp.2
    have h1 : ContinuousOn (fun p : ℝ × S => radialShrinkHomotopy F₀ p.1 (h p.2)) (univ ×ˢ D) :=
      (continuous_radialShrinkHomotopy F₀).comp_continuousOn
        (continuousOn_fst.prodMk (c.hc.comp continuousOn_snd hmap))
    refine c.gc.comp h1 ?_
    intro p hp
    exact radialShrinkHomotopy_mem_closedBall hF₀_sphere p.1 (c.hm hp.2)
  · intro x hx
    change g (radialShrinkHomotopy F₀ 0 (h x)) = x
    rw [radialShrinkHomotopy_zero, c.gh hx]
  · intro x _
    change g (radialShrinkHomotopy F₀ 1 (h x)) = g (radialShrinkMap F₀ (h x))
    rw [radialShrinkHomotopy_one]
  · intro u x hx y hy heq
    have h₁ : radialShrinkHomotopy F₀ u (h x) = radialShrinkHomotopy F₀ u (h y) :=
      c.injOn (radialShrinkHomotopy_mem_closedBall hF₀_sphere u (c.hm hx))
        (radialShrinkHomotopy_mem_closedBall hF₀_sphere u (c.hm hy)) heq
    have h₂ : h x = h y := injOn_radialShrinkHomotopy hF₀_sphere u (c.hm hx) (c.hm hy) h₁
    exact c.gh.injOn hx hy h₂

/-- Given a closed disc `D` in a `T2Space` `S` and a closed subset `F ⊆ discBd D`, there is a
continuous injective self-map `Ψ : S → S` on `D` with a continuous left inverse `Ψ'` on `Ψ '' D`
that fixes `F` pointwise and sends `D \ F` into `D \ discBd D`. -/
theorem exists_disc_shrink_map {S : Type w} [TopologicalSpace S] [T2Space S] [Nonempty S]
    {D F : Set S} (hD : IsClosedDisc D) (hF_closed : IsClosed F) (hF_sub : F ⊆ discBd D) :
    ∃ Ψ Ψ' : S → S,
      ContinuousOn Ψ D ∧
      ContinuousOn Ψ' (Ψ '' D) ∧
      LeftInvOn Ψ' Ψ D ∧
      InjOn Ψ D ∧
      Ψ '' D ⊆ D ∧
      (∀ x ∈ F, Ψ x = x) ∧
      (∀ x ∈ D \ F, Ψ x ∈ D \ discBd D) := by
  obtain ⟨Ψ, Ψ', _, h1, h2, h3, h4, h5, h6, h7, _, _, _, _⟩ :=
    exists_disc_shrink_map_with_homotopy hD hF_closed hF_sub
  exact ⟨Ψ, Ψ', h1, h2, h3, h4, h5, h6, h7⟩

theorem isClockwiseDiscHomeo_of_homotopy {D D₀ : Set EuclideanPlane}
    (hD₀ : IsClosedDisc D₀) (hD₀_sub : D₀ ⊆ D)
    {Ψ : EuclideanPlane → EuclideanPlane}
    (hint_eq : interior (Ψ '' D₀) = Ψ '' interior D₀)
    {C₀ C₀' : Set EuclideanPlane} (hC₀ : C₀ = subBd D₀)
    (φ₀ : Circle ≃ₜ C₀) (φ₀' : Circle ≃ₜ C₀')
    (hφ₀' : ∀ w : Circle, (φ₀' w).1 = Ψ (φ₀ w).1)
    {Ψ_hom : ℝ → EuclideanPlane → EuclideanPlane}
    (hΨ_hom_cont : ContinuousOn (fun p : ℝ × EuclideanPlane => Ψ_hom p.1 p.2) (univ ×ˢ D))
    (hΨ_hom_zero : ∀ x ∈ D, Ψ_hom 0 x = x)
    (hΨ_hom_one : ∀ x ∈ D, Ψ_hom 1 x = Ψ x)
    (hΨ_hom_inj : ∀ u : ℝ, InjOn (Ψ_hom u) D)
    (hφ₀_cw : IsClockwiseDiscHomeo D₀ φ₀) :
    IsClockwiseDiscHomeo (Ψ '' D₀) φ₀' := by
  intro y hy
  rw [hint_eq] at hy
  obtain ⟨x₀, hx₀, rfl⟩ := hy
  have hx₀_D : x₀ ∈ D := hD₀_sub (interior_subset hx₀)
  have hφ₀_D : ∀ w : Circle, (φ₀ w).1 ∈ D := fun w => by
    have hw : (φ₀ w).1 ∈ discBd D₀ := by
      rw [← subBd_eq_discBd_plane hD₀, ← hC₀]
      exact (φ₀ w).2
    exact hD₀_sub (Surface.discBd_subset D₀ hw)
  have hφ₀_ne : ∀ w : Circle, (φ₀ w).1 ≠ x₀ := fun w heq => by
    have hw : (φ₀ w).1 ∈ frontier D₀ := by
      rw [← GM11.subBd_eq_frontier, ← hC₀]
      exact (φ₀ w).2
    rw [heq] at hw
    exact hw.2 hx₀
  let H : ℝ → ℝ → ℂ := fun u t =>
    complexPlane.symm (Ψ_hom u (φ₀ (Circle.exp t)).1) - complexPlane.symm (Ψ_hom u x₀)
  have hH : Continuous fun q : ℝ × ℝ => H q.1 q.2 := by
    have hc1 : Continuous fun q : ℝ × ℝ => Ψ_hom q.1 (φ₀ (Circle.exp q.2)).1 :=
      hΨ_hom_cont.comp_continuous
        (continuous_fst.prodMk
          (continuous_subtype_val.comp (φ₀.continuous.comp (Circle.exp.continuous.comp
            continuous_snd))))
        (fun q => ⟨trivial, hφ₀_D _⟩)
    have hc2 : Continuous fun q : ℝ × ℝ => Ψ_hom q.1 x₀ :=
      hΨ_hom_cont.comp_continuous (continuous_fst.prodMk continuous_const)
        (fun _ => ⟨trivial, hx₀_D⟩)
    exact (complexPlane.symm.continuous.comp hc1).sub (complexPlane.symm.continuous.comp hc2)
  have hne : ∀ u t, H u t ≠ 0 := fun u t h => by
    have h1 := complexPlane.symm.injective (sub_eq_zero.mp h)
    have h2 := hΨ_hom_inj u (hφ₀_D _) hx₀_D h1
    exact hφ₀_ne (Circle.exp t) h2
  have hper : ∀ u, Function.Periodic (H u) (2 * Real.pi) := fun u t => by
    simp only [H, circle_exp_add_two_pi]
  have hv : ∀ t, ∃ t' ∈ Icc 0 (2 * Real.pi), ∀ u, H u t = H u t' := fun t => by
    obtain ⟨t', ht', n, rfl⟩ := Surface.exists_mem_period t
    exact ⟨_, ht', fun u => ((hper u).sub_zsmul_eq n).symm⟩
  have hhom := GM19.turn_eq_of_homotopy hH hne isCompact_Icc hv (s := 0) (t := 2 * Real.pi)
    (fun u => by
      have := hper u 0
      rw [zero_add] at this
      exact this.symm) 0 1
  have hH0 : H 0 = fun t => complexPlane.symm (φ₀ (Circle.exp t)).1 - complexPlane.symm x₀ := by
    funext t
    simp only [H, hΨ_hom_zero _ (hφ₀_D _), hΨ_hom_zero x₀ hx₀_D]
  have hH1 : H 1 = fun t => complexPlane.symm (φ₀' (Circle.exp t)).1 - complexPlane.symm (Ψ x₀)
    := by
    funext t
    simp only [H, hΨ_hom_one _ (hφ₀_D _), hΨ_hom_one x₀ hx₀_D, hφ₀']
  have hpos : 0 < Surface.wind (fun w => complexPlane.symm (φ₀ w).1) (complexPlane.symm x₀) :=
    hφ₀_cw x₀ hx₀
  change 0 < GM19.turn (fun t => complexPlane.symm (φ₀' (Circle.exp t)).1 - complexPlane.symm
    (Ψ x₀))
    0 (2 * Real.pi)
  rw [← hH1, ← hhom, hH0]
  exact hpos

/-- Transporting `AgreesWithOArcHomeo` along a map `Ψ` with a continuous left inverse on `C`
that fixes `α_pt v` for every `v ∈ Ω.bar`. -/
theorem agreesWithOArcHomeo_of_image {S : Type w} [TopologicalSpace S]
    {α_pt : α → S} {Ω : CyclicPerm α} {C C' : Set S} (φ : Circle ≃ₜ C)
    {Ψ Ψ' : S → S} (hΨ_cont : ContinuousOn Ψ C) (hΨ'_cont : ContinuousOn Ψ' (Ψ '' C))
    (hΨ_left : LeftInvOn Ψ' Ψ C) (hC' : C' = Ψ '' C)
    (hfix : ∀ v ∈ Ω.bar, Ψ (α_pt v) = α_pt v)
    (hagrees : AgreesWithOArcHomeo α_pt Ω C φ) :
    ∃ φ' : Circle ≃ₜ C', AgreesWithOArcHomeo α_pt Ω C' φ' := by
  obtain ⟨e, he⟩ := exists_homeomorph_image hΨ_cont hΨ'_cont hΨ_left
  let φ' : Circle ≃ₜ C' := (φ.trans e).trans (Homeomorph.setCongr hC'.symm)
  have hφ'_val : ∀ z : Circle, (φ' z).1 = Ψ (φ z).1 := fun z => he (φ z)
  refine ⟨φ', ?_, ?_⟩
  · intro v hv
    rw [hC', ← hfix v hv]
    exact mem_image_of_mem Ψ (hagrees.1 v hv)
  · intro v₁ v₂ v₃ hcw
    have hv₁ : v₁ ∈ Ω.bar := hcw.2.1 v₁ (by simp)
    have hv₂ : v₂ ∈ Ω.bar := hcw.2.1 v₂ (by simp)
    have hv₃ : v₃ ∈ Ω.bar := hcw.2.1 v₃ (by simp)
    obtain ⟨t₁, t₂, t₃, hlt₁₂, hlt₂₃, hlt₃₁, he₁, he₂, he₃⟩ := hagrees.2 v₁ v₂ v₃ hcw
    refine ⟨t₁, t₂, t₃, hlt₁₂, hlt₂₃, hlt₃₁, ?_, ?_, ?_⟩
    · rw [hφ'_val, he₁, hfix v₁ hv₁]
    · rw [hφ'_val, he₂, hfix v₂ hv₂]
    · rw [hφ'_val, he₃, hfix v₃ hv₃]

/-- Transporting `DrawingAgreesWithOArcHomeo` along a map `Ψ` with a continuous left inverse on `C`.
-/
theorem drawingAgreesWithOArcHomeo_of_image {S : Type w} [TopologicalSpace S]
    {G : Graph α β} (Γ Γ' : GraphDrawing G S) {Ω : CyclicPerm α} {C C' : Set S} (φ : Circle ≃ₜ C)
    {Ψ Ψ' : S → S} (hΨ_cont : ContinuousOn Ψ C) (hΨ'_cont : ContinuousOn Ψ' (Ψ '' C))
    (hΨ_left : LeftInvOn Ψ' Ψ C) (hC' : C' = Ψ '' C)
    (hvert : ∀ v ∈ Ω.bar, graphDrawingVertexSet Γ' v = Ψ '' graphDrawingVertexSet Γ v)
    (hagrees : DrawingAgreesWithOArcHomeo Γ Ω C φ) :
    ∃ φ' : Circle ≃ₜ C',
      (∀ z : Circle, (φ' z).1 = Ψ (φ z).1) ∧ DrawingAgreesWithOArcHomeo Γ' Ω C' φ' := by
  obtain ⟨e, he⟩ := exists_homeomorph_image hΨ_cont hΨ'_cont hΨ_left
  let φ' : Circle ≃ₜ C' := (φ.trans e).trans (Homeomorph.setCongr hC'.symm)
  have hφ'_val : ∀ z : Circle, (φ' z).1 = Ψ (φ z).1 := fun z => he (φ z)
  refine ⟨φ', hφ'_val, ?_, ?_⟩
  · intro v hv
    rw [hvert v hv, hC']
    exact image_mono (hagrees.1 v hv)
  · intro v₁ v₂ v₃ hcw
    have hv₁ : v₁ ∈ Ω.bar := hcw.2.1 v₁ (by simp)
    have hv₂ : v₂ ∈ Ω.bar := hcw.2.1 v₂ (by simp)
    have hv₃ : v₃ ∈ Ω.bar := hcw.2.1 v₃ (by simp)
    obtain ⟨t₁, t₂, t₃, hlt₁₂, hlt₂₃, hlt₃₁, he₁, he₂, he₃⟩ := hagrees.2 v₁ v₂ v₃ hcw
    refine ⟨t₁, t₂, t₃, hlt₁₂, hlt₂₃, hlt₃₁, ?_, ?_, ?_⟩
    · rw [hφ'_val, hvert v₁ hv₁]
      exact mem_image_of_mem Ψ he₁
    · rw [hφ'_val, hvert v₂ hv₂]
      exact mem_image_of_mem Ψ he₂
    · rw [hφ'_val, hvert v₃ hv₃]
      exact mem_image_of_mem Ψ he₃

/-- Given a rural presentation `(Γ, Δ, Δ₀)` of `(G, Ω, Ω₀)` and any cyclic permutation `Ω'`
with `Ω'.bar ⊆ Ω.bar` whose clockwise triples are clockwise in `Ω`, radial shrinking produces a
clean rural presentation `(Γ', Δ, Δ₀')` of `(G, Ω', Ω₀)` where `Γ'.drawing.U` and `Δ₀'` meet
`subBd Δ` only inside `⋃ v ∈ Ω'.bar, graphDrawingVertexSet Γ' v`, via a continuous injective map
`Ψ : EuclideanPlane → EuclideanPlane` on `Δ` with continuous left inverse `Ψ'` on `Ψ '' Δ`. -/
theorem exists_clean_presentation_of_restrict_outer
    {G : Graph α β} {Ω Ω' Ω₀ : CyclicPerm α}
    (hbar'G : Ω'.bar ⊆ V(G)) (hbar : Ω'.bar ⊆ Ω.bar)
    (hcw : ∀ v₁ v₂ v₃ : α, Ω'.IsClockwise3 v₁ v₂ v₃ → Ω.IsClockwise3 v₁ v₂ v₃)
    (Γ : GraphDrawing G EuclideanPlane) (Δ Δ₀ : Set EuclideanPlane)
    (hΔ : IsClosedDisc Δ) (hΔ₀_sub : Δ₀ ⊆ Δ) (hU_sub : Γ.drawing.U ⊆ Δ \ interior Δ₀)
    (hbd : ∀ v ∈ V(G), (graphDrawingVertexSet Γ v ⊆ subBd Δ ↔ v ∈ Ω.bar))
    (hbd₀ : ∀ v ∈ V(G), (graphDrawingVertexSet Γ v ⊆ subBd Δ₀ ↔ v ∈ Ω₀.bar))
    (φ : Circle ≃ₜ subBd Δ) (hagrees : DrawingAgreesWithOArcHomeo Γ Ω (subBd Δ) φ)
    (hinner : (Δ₀ = ∅ ∧ Ω₀.bar = ∅) ∨
      (IsClosedDisc Δ₀ ∧
        ∃ φ₀ : Circle ≃ₜ subBd Δ₀,
          IsClockwiseDiscHomeo Δ₀ φ₀ ∧ DrawingAgreesWithOArcHomeo Γ Ω₀ (subBd Δ₀) φ₀)) :
    ∃ (Ψ Ψ' : EuclideanPlane → EuclideanPlane)
      (Γ' : GraphDrawing G EuclideanPlane) (Δ₀' : Set EuclideanPlane),
      ContinuousOn Ψ Δ ∧
      ContinuousOn Ψ' (Ψ '' Δ) ∧
      LeftInvOn Ψ' Ψ Δ ∧
      InjOn Ψ Δ ∧
      Ψ '' Δ ⊆ Δ ∧
      Δ₀' = Ψ '' Δ₀ ∧
      Δ₀' ⊆ Δ ∧
      Γ'.drawing.U = Ψ '' Γ.drawing.U ∧
      Γ'.drawing.U ⊆ Δ \ interior Δ₀' ∧
      (∀ v, graphDrawingVertexSet Γ' v = Ψ '' graphDrawingVertexSet Γ v) ∧
      (∀ v ∈ Ω'.bar, graphDrawingVertexSet Γ' v = graphDrawingVertexSet Γ v) ∧
      (∀ H, graphDrawingSubgraphU Γ' H = Ψ '' graphDrawingSubgraphU Γ H) ∧
      Γ'.drawing.U ∩ subBd Δ = (⋃ v ∈ Ω'.bar, graphDrawingVertexSet Γ' v) ∧
      Δ₀' ∩ subBd Δ ⊆ (⋃ v ∈ Ω'.bar, graphDrawingVertexSet Γ' v) ∧
      (∀ v ∈ V(G), (graphDrawingVertexSet Γ' v ⊆ subBd Δ ↔ v ∈ Ω'.bar)) ∧
      (∀ v ∈ V(G), (graphDrawingVertexSet Γ' v ⊆ subBd Δ₀' ↔ v ∈ Ω₀.bar)) ∧
      DrawingAgreesWithOArcHomeo Γ' Ω' (subBd Δ) φ ∧
      ((Δ₀' = ∅ ∧ Ω₀.bar = ∅) ∨
        (IsClosedDisc Δ₀' ∧
          ∃ φ₀' : Circle ≃ₜ subBd Δ₀',
            IsClockwiseDiscHomeo Δ₀' φ₀' ∧ DrawingAgreesWithOArcHomeo Γ' Ω₀ (subBd Δ₀') φ₀')) := by
  let F : Set EuclideanPlane := ⋃ v ∈ Ω'.bar, graphDrawingVertexSet Γ v
  have hF_closed : IsClosed F := by
    refine Ω'.finite_bar.isClosed_biUnion fun v hv => ?_
    rw [graphDrawingVertexSet_eq_singleton' Γ (hbar'G hv)]
    exact isClosed_singleton
  have hsubBd_Δ : subBd Δ = discBd Δ := subBd_eq_discBd_plane hΔ
  have hF_sub : F ⊆ discBd Δ := by
    rw [← hsubBd_Δ]
    rintro x hx
    obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
    exact (hbd v (hbar'G hv)).mpr (hbar hv) hxv
  obtain ⟨Ψ, Ψ', Ψ_hom, hΨ_cont, hΨ'_cont, hΨ_left, hΨ_inj, hΨ_sub, hΨ_fix, hΨ_int,
    hΨ_hom_cont, hΨ_hom_zero, hΨ_hom_one, hΨ_hom_inj⟩ :=
    exists_disc_shrink_map_with_homotopy hΔ hF_closed hF_sub
  have hU_Δ : Γ.drawing.U ⊆ Δ := hU_sub.trans sdiff_subset
  have hUc : IsCompact Γ.drawing.U :=
    hΔ.isCompact.of_isClosed_subset Γ.drawing.isClosed_U hU_Δ
  obtain ⟨Γ', hU'_eq, hV'_eq, hveq', hvert', hedge', hsubU'⟩ :=
    GraphDrawing.transportOn Γ hUc (hΨ_cont.mono hU_Δ) (hΨ_inj.mono hU_Δ)
  have hvert_fix : ∀ v ∈ Ω'.bar, graphDrawingVertexSet Γ' v = graphDrawingVertexSet Γ v := by
    intro v hv
    rw [hvert' v]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyF : y ∈ F := mem_iUnion₂.mpr ⟨v, hv, hy⟩
      rw [hΨ_fix y hyF]
      exact hy
    · intro hx
      have hxF : x ∈ F := mem_iUnion₂.mpr ⟨v, hv, hx⟩
      exact ⟨x, hx, hΨ_fix x hxF⟩
  have hF_eq : (⋃ v ∈ Ω'.bar, graphDrawingVertexSet Γ' v) = F := by
    ext x
    simp only [mem_iUnion, exists_prop, F]
    exact ⟨fun ⟨v, hv, hx⟩ => ⟨v, hv, hvert_fix v hv ▸ hx⟩,
      fun ⟨v, hv, hx⟩ => ⟨v, hv, (hvert_fix v hv).symm ▸ hx⟩⟩
  let Δ₀' : Set EuclideanPlane := Ψ '' Δ₀
  have hΔ₀'_sub : Δ₀' ⊆ Δ := (image_mono hΔ₀_sub).trans hΨ_sub
  have hΔ₀_bd_int :
      interior Δ₀' = Ψ '' interior Δ₀ ∧ subBd Δ₀' = Ψ '' subBd Δ₀ ∧
      ((Δ₀' = ∅ ∧ Ω₀.bar = ∅) ∨
        (IsClosedDisc Δ₀' ∧
          ∃ φ₀' : Circle ≃ₜ subBd Δ₀',
            IsClockwiseDiscHomeo Δ₀' φ₀' ∧ DrawingAgreesWithOArcHomeo Γ' Ω₀ (subBd Δ₀') φ₀')) := by
    rcases hinner with ⟨rfl, hΩ₀_emp⟩ | ⟨hΔ₀_disc, φ₀, hφ₀_cw, hagrees₀⟩
    · refine ⟨by simp [Δ₀'], by simp [Δ₀', subBd], Or.inl ⟨by simp [Δ₀'], hΩ₀_emp⟩⟩
    · have hΔ₀_cont : ContinuousOn Ψ Δ₀ := hΨ_cont.mono hΔ₀_sub
      have hΔ₀'_cont : ContinuousOn Ψ' (Ψ '' Δ₀) := hΨ'_cont.mono (image_mono hΔ₀_sub)
      have hΔ₀_left : LeftInvOn Ψ' Ψ Δ₀ := hΨ_left.mono hΔ₀_sub
      obtain ⟨hΔ₀'_disc, hΔ₀'_bd⟩ := hΔ₀_disc.image hΔ₀_cont hΔ₀'_cont hΔ₀_left
      have hbd₀_eq : subBd Δ₀' = Ψ '' subBd Δ₀ := by
        rw [subBd_eq_discBd_plane hΔ₀'_disc, subBd_eq_discBd_plane hΔ₀_disc, hΔ₀'_bd]
      have hint₀_eq : interior Δ₀' = Ψ '' interior Δ₀ := by
        rw [interior_eq_discInt_plane hΔ₀'_disc, interior_eq_discInt_plane hΔ₀_disc]
        change Δ₀' \ discBd Δ₀' = Ψ '' (Δ₀ \ discBd Δ₀)
        rw [hΔ₀'_bd]
        exact (InjOn.image_sdiff_subset (hΨ_inj.mono hΔ₀_sub) (Surface.discBd_subset Δ₀)).symm
      have hbd₀_sub : subBd Δ₀ ⊆ Δ :=
        (subBd_eq_discBd_plane hΔ₀_disc ▸ Surface.discBd_subset Δ₀).trans hΔ₀_sub
      obtain ⟨φ₀', hφ₀'_val, hagrees₀'⟩ :=
        drawingAgreesWithOArcHomeo_of_image Γ Γ' φ₀ (hΨ_cont.mono hbd₀_sub)
          (hΨ'_cont.mono (image_mono hbd₀_sub)) (hΨ_left.mono hbd₀_sub) hbd₀_eq
          (fun v _ => hvert' v) hagrees₀
      have hφ₀'_cw : IsClockwiseDiscHomeo Δ₀' φ₀' :=
        isClockwiseDiscHomeo_of_homotopy hΔ₀_disc hΔ₀_sub hint₀_eq rfl φ₀ φ₀' hφ₀'_val
          hΨ_hom_cont hΨ_hom_zero hΨ_hom_one hΨ_hom_inj hφ₀_cw
      exact ⟨hint₀_eq, hbd₀_eq, Or.inr ⟨hΔ₀'_disc, φ₀', hφ₀'_cw, hagrees₀'⟩⟩
  obtain ⟨hint₀_eq, hbd₀_eq, hinner'⟩ := hΔ₀_bd_int
  have hU'_sub : Γ'.drawing.U ⊆ Δ \ interior Δ₀' := by
    rw [hU'_eq, hint₀_eq]
    rintro _ ⟨x, hxU, rfl⟩
    have hx := hU_sub hxU
    refine ⟨hΨ_sub (mem_image_of_mem Ψ hx.1), ?_⟩
    rintro ⟨y, hy_int, hyx⟩
    have hyΔ : y ∈ Δ := hΔ₀_sub (interior_subset hy_int)
    have hy_eq : y = x := hΨ_inj hyΔ hx.1 hyx
    exact hx.2 (hy_eq ▸ hy_int)
  have hΨ_mem_subBd_iff : ∀ x ∈ Δ, Ψ x ∈ subBd Δ ↔ x ∈ F := by
    intro x hxΔ
    constructor
    · intro hΨx
      by_contra hxF
      have h := hΨ_int x ⟨hxΔ, hxF⟩
      rw [← hsubBd_Δ] at h
      exact h.2 hΨx
    · intro hxF
      rw [hΨ_fix x hxF, hsubBd_Δ]
      exact hF_sub hxF
  have hU'_inter_bd : Γ'.drawing.U ∩ subBd Δ = ⋃ v ∈ Ω'.bar, graphDrawingVertexSet Γ' v := by
    rw [hF_eq, hU'_eq]
    apply subset_antisymm
    · rintro _ ⟨⟨x, hxU, rfl⟩, hΨx⟩
      have hxF : x ∈ F := (hΨ_mem_subBd_iff x (hU_Δ hxU)).mp hΨx
      rw [hΨ_fix x hxF]
      exact hxF
    · intro x hxF
      obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hxF
      have hxU : x ∈ Γ.drawing.U :=
        graphDrawingSubgraphU_subset_drawing_U Γ G (Or.inl (mem_iUnion₂.mpr ⟨v, hbar'G hv, hxv⟩))
      refine ⟨?_, hsubBd_Δ ▸ hF_sub hxF⟩
      rw [← hΨ_fix x hxF]
      exact mem_image_of_mem Ψ hxU
  have hΔ₀'_inter_bd : Δ₀' ∩ subBd Δ ⊆ ⋃ v ∈ Ω'.bar, graphDrawingVertexSet Γ' v := by
    rw [hF_eq]
    rintro _ ⟨⟨x, hxΔ₀, rfl⟩, hΨx⟩
    have hxF : x ∈ F := (hΨ_mem_subBd_iff x (hΔ₀_sub hxΔ₀)).mp hΨx
    rw [hΨ_fix x hxF]
    exact hxF
  have hbd' : ∀ v ∈ V(G), (graphDrawingVertexSet Γ' v ⊆ subBd Δ ↔ v ∈ Ω'.bar) := by
    intro v hv
    constructor
    · intro hsub
      let x := (Γ.iso.vertexEquiv ⟨v, hv⟩).1
      have hxv : x ∈ graphDrawingVertexSet Γ v := ⟨hv, rfl⟩
      have hxΔ : x ∈ Δ := hU_Δ (Γ.drawing.V_subset_U (Γ.iso.vertexEquiv ⟨v, hv⟩).2)
      have hΨx : Ψ x ∈ subBd Δ := hsub (hvert' v ▸ mem_image_of_mem Ψ hxv)
      have hxF : x ∈ F := (hΨ_mem_subBd_iff x hxΔ).mp hΨx
      obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hxF
      rcases hxu with ⟨huG, hux⟩
      have heq : Γ.iso.vertexEquiv ⟨u, huG⟩ = Γ.iso.vertexEquiv ⟨v, hv⟩ := Subtype.ext hux
      have huv : u = v := Subtype.mk.inj (Γ.iso.vertexEquiv.injective heq)
      exact huv ▸ hu
    · intro hv'
      rw [hvert_fix v hv', hsubBd_Δ]
      exact (subset_biUnion_of_mem (u := fun u => graphDrawingVertexSet Γ u) hv').trans hF_sub
  have hbd₀' : ∀ v ∈ V(G), (graphDrawingVertexSet Γ' v ⊆ subBd Δ₀' ↔ v ∈ Ω₀.bar) := by
    intro v hv
    rw [← hbd₀ v hv, hvert' v, hbd₀_eq]
    constructor
    · intro hsub x hxv
      have hxΔ : x ∈ Δ := hU_Δ (Γ.drawing.V_subset_U (by
        rcases hxv with ⟨_, rfl⟩; exact (Γ.iso.vertexEquiv ⟨v, hv⟩).2))
      obtain ⟨y, hy_bd₀, hyx⟩ := hsub (mem_image_of_mem Ψ hxv)
      have hyΔ : y ∈ Δ := by
        rcases hinner with ⟨rfl, _⟩ | ⟨hΔ₀_disc, _⟩
        · simp [subBd] at hy_bd₀
        · exact hΔ₀_sub (Surface.discBd_subset Δ₀ (subBd_eq_discBd_plane hΔ₀_disc ▸ hy_bd₀))
      exact hΨ_inj hyΔ hxΔ hyx ▸ hy_bd₀
    · exact image_mono
  have hagrees' : DrawingAgreesWithOArcHomeo Γ' Ω' (subBd Δ) φ := by
    refine ⟨fun v hv => ?_, fun v₁ v₂ v₃ h => ?_⟩
    · rw [hvert_fix v hv]
      exact hagrees.1 v (hbar hv)
    · have hv₁ : v₁ ∈ Ω'.bar := h.2.1 v₁ (by simp)
      have hv₂ : v₂ ∈ Ω'.bar := h.2.1 v₂ (by simp)
      have hv₃ : v₃ ∈ Ω'.bar := h.2.1 v₃ (by simp)
      rw [hvert_fix v₁ hv₁, hvert_fix v₂ hv₂, hvert_fix v₃ hv₃]
      exact hagrees.2 v₁ v₂ v₃ (hcw v₁ v₂ v₃ h)
  exact ⟨Ψ, Ψ', Γ', Δ₀', hΨ_cont, hΨ'_cont, hΨ_left, hΨ_inj, hΨ_sub, rfl, hΔ₀'_sub,
    hU'_eq, hU'_sub, hvert', hvert_fix, hsubU', hU'_inter_bd, hΔ₀'_inter_bd,
    hbd', hbd₀', hagrees', hinner'⟩

/-- Restricting the outer cyclic permutation `N.Ω` of a rural neighborhood `N` to any `N'.Ω` with
`N'.Ω.bar ⊆ N.Ω.bar` whose clockwise triples are clockwise in `N.Ω` preserves rurality. -/
theorem Neighborhood.IsRural.restrict_outer {N N' : Neighborhood α β}
    (hrural : N.IsRural) (hG : N'.G = N.G) (hΩ₀ : N'.Ω₀ = N.Ω₀)
    (hbar : N'.Ω.bar ⊆ N.Ω.bar)
    (hcw : ∀ v₁ v₂ v₃ : α, N'.Ω.IsClockwise3 v₁ v₂ v₃ → N.Ω.IsClockwise3 v₁ v₂ v₃) :
    N'.IsRural := by
  obtain ⟨Γ, Δ, Δ₀, hΔ, hΔ₀_sub, hU_sub, hbd, hbd₀, ⟨φ, hφ_cw, hagrees⟩, hinner⟩ := hrural
  have hbar'G : N'.Ω.bar ⊆ V(N.G) := hG ▸ N'.bar_subset
  obtain ⟨_, _, Γ', Δ₀', _, _, _, _, _, _, hΔ₀'_sub, _, hU'_sub, _, _, _, _, _, hbd', hbd₀',
    hagrees', hinner'⟩ :=
    exists_clean_presentation_of_restrict_outer hbar'G hbar hcw Γ Δ Δ₀
      hΔ hΔ₀_sub hU_sub hbd hbd₀ φ hagrees hinner
  cases N; cases N'
  dsimp at hG hΩ₀ ⊢
  subst hG; subst hΩ₀
  exact ⟨Γ', Δ, Δ₀', hΔ, hΔ₀'_sub, hU'_sub, hbd', hbd₀', ⟨φ, hφ_cw, hagrees'⟩, hinner'⟩

/-- If `Γ` is a drawing of `G` and `α_pt v = (Γ.iso.vertexEquiv ⟨v, hv⟩).1` for all `v ∈ V(G)`,
then `DrawingAgreesWithOArcHomeo Γ Ω C φ` implies `AgreesWithOArcHomeo α_pt Ω C φ`. -/
theorem agreesWithOArcHomeo_of_drawingAgreesWithOArcHomeo
    {S : Type w} [TopologicalSpace S] {G : Graph α β}
    (Γ : GraphDrawing G S) {Ω : CyclicPerm α} (hbar : Ω.bar ⊆ V(G))
    {C : Set S} {φ : Circle ≃ₜ C} {α_pt : α → S}
    (hα : ∀ v (hv : v ∈ V(G)), α_pt v = (Γ.iso.vertexEquiv ⟨v, hv⟩).1)
    (h : DrawingAgreesWithOArcHomeo Γ Ω C φ) :
    AgreesWithOArcHomeo α_pt Ω C φ := by
  refine ⟨fun v hv => ?_, fun v₁ v₂ v₃ hcw => ?_⟩
  · have hvG : v ∈ V(G) := hbar hv
    have hsub := h.1 v hv
    rw [graphDrawingVertexSet_eq_singleton' Γ hvG, singleton_subset_iff, ← hα v hvG] at hsub
    exact hsub
  · obtain ⟨t₁, t₂, t₃, ht₁₂, ht₂₃, ht₃₁, h₁, h₂, h₃⟩ := h.2 v₁ v₂ v₃ hcw
    have hv₁ : v₁ ∈ V(G) := hbar (hcw.2.1 v₁ (by simp))
    have hv₂ : v₂ ∈ V(G) := hbar (hcw.2.1 v₂ (by simp))
    have hv₃ : v₃ ∈ V(G) := hbar (hcw.2.1 v₃ (by simp))
    rw [graphDrawingVertexSet_eq_singleton' Γ hv₁, mem_singleton_iff, ← hα v₁ hv₁] at h₁
    rw [graphDrawingVertexSet_eq_singleton' Γ hv₂, mem_singleton_iff, ← hα v₂ hv₂] at h₂
    rw [graphDrawingVertexSet_eq_singleton' Γ hv₃, mem_singleton_iff, ← hα v₃ hv₃] at h₃
    exact ⟨t₁, t₂, t₃, ht₁₂, ht₂₃, ht₃₁, h₁, h₂, h₃⟩

/-- A 3-cycle on three pairwise distinct elements `u₁, u₂, u₃`. -/
private noncomputable def cyclicPermOfThree (u₁ u₂ u₃ : α)
    (h₁₂ : u₁ ≠ u₂) (h₂₃ : u₂ ≠ u₃) (h₁₃ : u₁ ≠ u₃) : CyclicPerm α := by
  classical
  let f : α → α := fun x => if x = u₁ then u₂ else if x = u₂ then u₃ else u₁
  have hf₁ : f u₁ = u₂ := by simp [f]
  have hf₂ : f u₂ = u₃ := by simp [f, h₁₂.symm]
  have hf₃ : f u₃ = u₁ := by simp [f, h₁₃.symm, h₂₃.symm]
  have hfin : ({u₁, u₂, u₃} : Set α).Finite :=
    ((finite_singleton u₃).insert u₂).insert u₁
  refine
    { bar := {u₁, u₂, u₃}
      toFun := f
      finite_bar := hfin
      bijOn := ⟨?_, ?_, ?_⟩
      single_orbit := ?_ }
  · rintro x (rfl | rfl | rfl) <;> simp [hf₁, hf₂, hf₃]
  · rintro x (rfl | rfl | rfl) y (rfl | rfl | rfl) hxy <;>
      simp only [hf₁, hf₂, hf₃] at hxy
    · rfl
    · exact (h₂₃ hxy).elim
    · exact (h₁₂ hxy.symm).elim
    · exact (h₂₃ hxy.symm).elim
    · rfl
    · exact (h₁₃ hxy.symm).elim
    · exact (h₁₂ hxy).elim
    · exact (h₁₃ hxy).elim
    · rfl
  · rintro x (rfl | rfl | rfl)
    · exact ⟨u₃, by simp, hf₃⟩
    · exact ⟨u₁, by simp, hf₁⟩
    · exact ⟨u₂, by simp, hf₂⟩
  · rintro x (rfl | rfl | rfl) y (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, hf₁⟩
    · exact ⟨2, by simp [Function.iterate_succ_apply', hf₁, hf₂]⟩
    · exact ⟨2, by simp [Function.iterate_succ_apply', hf₂, hf₃]⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, hf₂⟩
    · exact ⟨1, hf₃⟩
    · exact ⟨2, by simp [Function.iterate_succ_apply', hf₃, hf₁]⟩
    · exact ⟨0, rfl⟩

private theorem isClockwise3_cyclicPermOfThree_iff {u₁ u₂ u₃ : α}
    (h₁₂ : u₁ ≠ u₂) (h₂₃ : u₂ ≠ u₃) (h₁₃ : u₁ ≠ u₃) {v₁ v₂ v₃ : α} :
    (cyclicPermOfThree u₁ u₂ u₃ h₁₂ h₂₃ h₁₃).IsClockwise3 v₁ v₂ v₃ →
      (v₁ = u₁ ∧ v₂ = u₂ ∧ v₃ = u₃) ∨
      (v₁ = u₂ ∧ v₂ = u₃ ∧ v₃ = u₁) ∨
      (v₁ = u₃ ∧ v₂ = u₁ ∧ v₃ = u₂) := by
  classical
  let Ω := cyclicPermOfThree u₁ u₂ u₃ h₁₂ h₂₃ h₁₃
  have hf₁ : Ω.toFun u₁ = u₂ := by simp [Ω, cyclicPermOfThree]
  have hf₂ : Ω.toFun u₂ = u₃ := by simp [Ω, cyclicPermOfThree, h₁₂.symm]
  have hf₃ : Ω.toFun u₃ = u₁ := by simp [Ω, cyclicPermOfThree, h₁₃.symm, h₂₃.symm]
  intro ⟨hnodup, hmem, hhit⟩
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnodup
  obtain ⟨⟨hv₁₂, hv₁₃⟩, hv₂₃, _⟩ := hnodup
  have h1 : v₁ ∈ ({u₁, u₂, u₃} : Set α) := hmem v₁ (by simp)
  have h2 : v₂ ∈ ({u₁, u₂, u₃} : Set α) := hmem v₂ (by simp)
  have h3 : v₃ ∈ ({u₁, u₂, u₃} : Set α) := hmem v₃ (by simp)
  have hfin : ({u₁, u₂, u₃} : Set α).Finite :=
    ((finite_singleton u₃).insert u₂).insert u₁
  have hbar_sub : ({u₁, u₂, u₃} : Set α) ⊆ {v | v ∈ [v₁, v₂, v₃]} := by
    have hsub : ({v₁, v₂, v₃} : Set α) ⊆ {u₁, u₂, u₃} := by
      rintro x (rfl | rfl | rfl) <;> assumption
    have hcard₁ : ({v₁, v₂, v₃} : Set α).ncard = 3 := by
      rw [ncard_insert_of_notMem (by simp [hv₁₂, hv₁₃]),
        ncard_insert_of_notMem (by simp [hv₂₃]), ncard_singleton]
    have hcard₂ : ({u₁, u₂, u₃} : Set α).ncard ≤ 3 :=
      (ncard_insert_le _ _).trans (Nat.add_le_add_right ((ncard_insert_le _ _).trans (by simp)) 1)
    have heq := eq_of_subset_of_ncard_le hsub (hcard₂.trans hcard₁.symm.le) hfin
    intro x hx
    rw [← heq] at hx
    simpa using hx
  have hlen : 0 < [v₁, v₂, v₃].length := by simp
  have h01 := hhit 0 hlen
  obtain ⟨k, hk1, hkeq, _, hkmin⟩ := h01
  have hk_eq_1 : k = 1 := by
    by_contra hne
    have hlt : 1 < k := lt_of_le_of_ne hk1 (Ne.symm hne)
    refine hkmin 1 le_rfl hlt (hbar_sub ?_)
    exact Ω.bijOn.1 h1
  subst hk_eq_1
  change Ω.toFun v₁ = v₂ at hkeq
  rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
    rcases h3 with rfl | rfl | rfl <;>
    try (exfalso; first | exact hv₁₂ rfl | exact hv₁₃ rfl | exact hv₂₃ rfl)
  · exact Or.inl ⟨rfl, rfl, rfl⟩
  · rw [hf₁] at hkeq; exact (h₂₃ hkeq).elim
  · rw [hf₂] at hkeq; exact (h₁₃ hkeq.symm).elim
  · exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)
  · rw [hf₃] at hkeq; exact (h₁₂ hkeq).elim

/-- For any subset `K ⊆ α` of cardinality `≤ 3` whose image under `α_pt` is injective and lies in
an `O`-arc `C` with homeomorphism `φ : Circle ≃ₜ C`, there exists a cyclic permutation `Ω_K` with
`Ω_K.bar = K` agreeing with `φ`. -/
theorem exists_cyclicPerm_agreesWithOArcHomeo_of_ncard_le_three
    {S : Type w} [TopologicalSpace S] {C : Set S} (φ : Circle ≃ₜ C)
    (α_pt : α → S) {K : Set α} (hfin : K.Finite) (hle : K.ncard ≤ 3)
    (hinj : InjOn α_pt K) (hK_C : ∀ v ∈ K, α_pt v ∈ C) :
    ∃ Ω_K : CyclicPerm α, Ω_K.bar = K ∧ AgreesWithOArcHomeo α_pt Ω_K C φ := by
  classical
  have hcases : K.ncard = 0 ∨ K.ncard = 1 ∨ K.ncard = 2 ∨ K.ncard = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · have hK : K = ∅ := (ncard_eq_zero hfin).mp h0
    subst hK
    refine ⟨⟨∅, id, finite_empty, bijOn_empty id, fun _ h => h.elim⟩, rfl,
      ⟨fun _ h => h.elim, fun v₁ _ _ hcw => (hcw.2.1 v₁ (by simp)).elim⟩⟩
  · obtain ⟨a, rfl⟩ := ncard_eq_one.mp h1
    refine ⟨⟨{a}, id, finite_singleton a, bijOn_singleton.mpr rfl, fun x hx y hy =>
      ⟨0, by rw [mem_singleton_iff.mp hx, mem_singleton_iff.mp hy]; rfl⟩⟩, rfl,
      ⟨fun v hv => hK_C v hv, fun v₁ v₂ v₃ ⟨hnodup, hmem, _⟩ => ?_⟩⟩
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnodup
    have hv₁ : v₁ = a := hmem v₁ (by simp)
    have hv₂ : v₂ = a := hmem v₂ (by simp)
    exact (hnodup.1.1 (hv₁.trans hv₂.symm)).elim
  · obtain ⟨a, b, hab, rfl⟩ := ncard_eq_two.mp h2
    let f : α → α := fun x => if x = a then b else a
    have hfa : f a = b := by simp [f]
    have hfb : f b = a := by simp [f, hab.symm]
    have hfin₂ : ({a, b} : Set α).Finite := (finite_singleton b).insert a
    have hbij : BijOn f {a, b} {a, b} := by
      refine ⟨?_, ?_, ?_⟩
      · rintro x (rfl | rfl) <;> simp [hfa, hfb]
      · rintro x (rfl | rfl) y (rfl | rfl) hxy <;>
          simp only [hfa, hfb] at hxy
        · rfl
        · exact (hab hxy.symm).elim
        · exact (hab hxy).elim
        · rfl
      · rintro x (rfl | rfl)
        · exact ⟨b, by simp, hfb⟩
        · exact ⟨a, by simp, hfa⟩
    have hcyc : ∀ x ∈ ({a, b} : Set α), ∀ y ∈ ({a, b} : Set α), ∃ k : ℕ, (f^[k]) x = y := by
      rintro x (rfl | rfl) y (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, hfa⟩
      · exact ⟨1, hfb⟩
      · exact ⟨0, rfl⟩
    let Ω₂ : CyclicPerm α := ⟨{a, b}, f, hfin₂, hbij, hcyc⟩
    refine ⟨Ω₂, rfl, ⟨fun v hv => hK_C v hv, fun v₁ v₂ v₃ ⟨hnodup, hmem, _⟩ => ?_⟩⟩
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnodup
    have hv₁ : v₁ ∈ ({a, b} : Set α) := hmem v₁ (by simp)
    have hv₂ : v₂ ∈ ({a, b} : Set α) := hmem v₂ (by simp)
    have hv₃ : v₃ ∈ ({a, b} : Set α) := hmem v₃ (by simp)
    rcases hv₁ with rfl | rfl <;> rcases hv₂ with rfl | rfl <;> rcases hv₃ with rfl | rfl <;>
      tauto
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ncard_eq_three.mp h3
    let θ : α → ℝ := fun v =>
      if hv : v ∈ ({a, b, c} : Set α) then
        Complex.arg ((φ.symm ⟨α_pt v, hK_C v hv⟩ : Circle) : ℂ)
      else 0
    have hθ_exp : ∀ v (hv : v ∈ ({a, b, c} : Set α)),
        (φ (Circle.exp (θ v))).1 = α_pt v := by
      intro v hv
      simp only [θ, hv, dite_true, Circle.exp_arg, Homeomorph.apply_symm_apply]
    have hθ_gt : ∀ v (hv : v ∈ ({a, b, c} : Set α)), -Real.pi < θ v := by
      intro v hv
      simp only [θ, hv, dite_true]
      exact Complex.neg_pi_lt_arg _
    have hθ_le : ∀ v (hv : v ∈ ({a, b, c} : Set α)), θ v ≤ Real.pi := by
      intro v hv
      simp only [θ, hv, dite_true]
      exact Complex.arg_le_pi _
    have hθ_inj : ∀ u ∈ ({a, b, c} : Set α), ∀ v ∈ ({a, b, c} : Set α),
        θ u = θ v → u = v := by
      intro u hu v hv huv
      have hexp : (φ (Circle.exp (θ u))).1 = (φ (Circle.exp (θ v))).1 := by rw [huv]
      rw [hθ_exp u hu, hθ_exp v hv] at hexp
      exact hinj hu hv hexp
    have hwlog : ∀ u₁ u₂ u₃ : α,
        ({u₁, u₂, u₃} : Set α) = {a, b, c} →
        u₁ ≠ u₂ → u₂ ≠ u₃ → u₁ ≠ u₃ →
        θ u₁ < θ u₂ → θ u₂ < θ u₃ →
        ∃ Ω_K : CyclicPerm α, Ω_K.bar = {a, b, c} ∧ AgreesWithOArcHomeo α_pt Ω_K C φ := by
      intro u₁ u₂ u₃ hset h₁₂ h₂₃ h₁₃ hlt₁₂ hlt₂₃
      have hu₁ : u₁ ∈ ({a, b, c} : Set α) := hset ▸ by simp
      have hu₂ : u₂ ∈ ({a, b, c} : Set α) := hset ▸ by simp
      have hu₃ : u₃ ∈ ({a, b, c} : Set α) := hset ▸ by simp
      refine ⟨cyclicPermOfThree u₁ u₂ u₃ h₁₂ h₂₃ h₁₃, hset,
        ⟨fun v hv => hK_C v (hset ▸ hv), fun v₁ v₂ v₃ hcw => ?_⟩⟩
      have hgt₁ := hθ_gt u₁ hu₁
      have hle₃ := hθ_le u₃ hu₃
      have hexp₂π : ∀ t : ℝ, Circle.exp (t + 2 * Real.pi) = Circle.exp t :=
        fun t => Circle.exp_add_two_pi t
      rcases isClockwise3_cyclicPermOfThree_iff h₁₂ h₂₃ h₁₃ hcw with
        ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> rw [h1, h2, h3]
      · exact ⟨θ u₁, θ u₂, θ u₃, hlt₁₂, hlt₂₃, by linarith,
          hθ_exp u₁ hu₁, hθ_exp u₂ hu₂, hθ_exp u₃ hu₃⟩
      · refine ⟨θ u₂, θ u₃, θ u₁ + 2 * Real.pi, hlt₂₃, by linarith, by linarith,
          hθ_exp u₂ hu₂, hθ_exp u₃ hu₃, ?_⟩
        rw [hexp₂π, hθ_exp u₁ hu₁]
      · refine ⟨θ u₃, θ u₁ + 2 * Real.pi, θ u₂ + 2 * Real.pi, by linarith, by linarith, by linarith,
          hθ_exp u₃ hu₃, ?_, ?_⟩
        · rw [hexp₂π, hθ_exp u₁ hu₁]
        · rw [hexp₂π, hθ_exp u₂ hu₂]
    have ha : a ∈ ({a, b, c} : Set α) := by simp
    have hb : b ∈ ({a, b, c} : Set α) := by simp
    have hc : c ∈ ({a, b, c} : Set α) := by simp
    have hθ_ab : θ a ≠ θ b := fun h => hab (hθ_inj a ha b hb h)
    have hθ_ac : θ a ≠ θ c := fun h => hac (hθ_inj a ha c hc h)
    have hθ_bc : θ b ≠ θ c := fun h => hbc (hθ_inj b hb c hc h)
    rcases lt_or_gt_of_ne hθ_ab with hab' | hba'
    · rcases lt_or_gt_of_ne hθ_bc with hbc' | hcb'
      · exact hwlog a b c rfl hab hbc hac hab' hbc'
      · rcases lt_or_gt_of_ne hθ_ac with hac' | hca'
        · exact hwlog a c b (by ext; simp; tauto) hac hbc.symm hab hac' hcb'
        · exact hwlog c a b (by ext; simp; tauto) hac.symm hab hbc.symm hca' hab'
    · rcases lt_or_gt_of_ne hθ_ac with hac' | hca'
      · exact hwlog b a c (by ext; simp; tauto) hab.symm hac hbc hba' hac'
      · rcases lt_or_gt_of_ne hθ_bc with hbc' | hcb'
        · exact hwlog b c a (by ext; simp; tauto) hbc hac.symm hab.symm hbc' hca'
        · exact hwlog c b a (by ext; simp; tauto) hbc.symm hab.symm hac.symm hcb' hba'

end

end GraphMinor.GM09
