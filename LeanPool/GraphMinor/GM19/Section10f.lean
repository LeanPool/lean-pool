/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section10e
public import LeanPool.GraphMinor.GM19.Section15a

import LeanPool.GraphMinor.GM19.FeatureCount

import LeanPool.GraphMinor.GM19.FragmentForm

/-!
# Graph Minors XIX, (10.3)
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}


omit [T2Space S] [T2Space Shat] in
theorem IsCutFormOf.image_subset {K : Drawing S} {F : Set Shat} (hf : IsCutFormOf cap K F) :
  cap.emb '' K.U ⊆ F := by
  obtain ⟨rfl, -, -⟩ | ⟨s, t, Θ, -, -, -, -, -, -, h, -⟩ := hf
  · exact Subset.rfl
  · exact h

omit [T2Space Shat] in
/-- A cut along a feature of the two forms. -/
theorem exists_cut_of_form (hS : IsSurface S) [ConnectedSpace S] {Φ : Frame S} {Γ : Painting S}
  (hfit : Γ.Fits Φ) {K : Drawing S}
    {F : Set Shat} (hf : IsCutFormOf cap K F) (hinter : Γ.U ∩ K.U ⊆ Γ.V ∩ K.V)
    (hlines : ∀ e ∈ arcComponentsIn (K.U \ K.V), ∃ u v, u ≠ v ∧ closure e ∩ K.V = {u, v}
      ∧ IsLineWithEnds (closure e) u v)
    (hKne : K.V ⊆ ⋃ e ∈ arcComponentsIn (K.U \ K.V), closure e) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : T2Space Y) (ψ : Y → S), IsSurface Y ∧ IsCutMap ψ K.U
      ∧ HasSheets ψ K := by
  obtain ⟨-, hO, -⟩ | ⟨s, t, Θ, hΘ, hst, hs, ht, -, hl, -, -⟩ := hf
  · obtain ⟨Y, tY, t2, ψ, h₁, h₂, h₃, -⟩ := exists_pullData_of_shape (𝓞 := {K.U}) (𝓛
      := ∅) hS hfit hinter hlines hKne
      (finite_singleton _) finite_empty (fun C hC ↦ hC ▸ hO) (fun L hL ↦ absurd hL
        (notMem_empty L)) (by simp)
    exact ⟨Y, tY, t2, ψ, h₁, h₂, h₃⟩
  · obtain ⟨Y, tY, t2, ψ, h₁, h₂, h₃, -⟩ := exists_pullData_of_shape (𝓞 := ∅) (𝓛
      := {K.U}) hS hfit hinter hlines hKne
      finite_empty (finite_singleton _) (fun C hC ↦ absurd hC (notMem_empty C))
      (fun L hL ↦ ⟨s, t, hst, hL ▸ hl, Or.inl (cuff_subset_bd ⟨Θ, hΘ⟩ hs), Or.inl
        (cuff_subset_bd ⟨Θ, hΘ⟩ ht)⟩) (by simp)
    exact ⟨Y, tY, t2, ψ, h₁, h₂, h₃⟩

omit [T2Space Shat] in
/-- The places of one fragment are well-behaved, by `S₁`, if the capped fragment is simpler. -/
theorem wellBehaved_S1 (hS : IsSurface S) {K : Drawing S} (hF : IsFeature χ.Φ K)
    (hlines : ∀ e ∈ arcComponentsIn (K.U \ K.V), ∃ u v, u ≠ v ∧ closure e ∩ K.V = {u, v}
      ∧ IsLineWithEnds (closure e) u v)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] {ψ : Y → S} (hY : IsSurface Y)
      (hψ : IsCutMap ψ K.U) (hsheet : HasSheets ψ K)
    (y : Y) (l : List S) (m : ℕ) (a₀ : β) (hS1 : ConditionS1.{0, w} Shat)
    (hsimple : ∀ (Shat₁ : Type) [TopologicalSpace Shat₁], IsCappedSurface
      (connectedComponent y) Shat₁ → IsSimplerThan Shat₁ Shat) :
    IsWellBehavedPlaces {X | IsCutPlace χ K (fun x : connectedComponent y ↦ ψ x.1) l m X ∧ True}
      := by
  have : Nonempty (connectedComponent y) := ⟨⟨y, mem_connectedComponent⟩⟩
  apply wellBehaved_of_fragment (fun x : connectedComponent y ↦ ψ x.1) hF l m a₀
    (fun a b hab hoff ↦ Subtype.ext (hψ.2.2.1 hoff (fun h ↦ hoff (hab ▸ h)) hab))
    (fun X hX ↦ frameData_of_cut hS X.P.fits hX.inter hlines hY hψ hsheet y)
  intro seq _ h flip hflip
  set D := fun i ↦ frameData_of_cut hS (seq i).P.fits (h i).inter hlines hY hψ hsheet y with hDdef
  have hfrag := (D 0).pull.frag
  obtain ⟨Shat₁, t₁, ⟨cap₁⟩⟩ := exists_cappedSurface _ _ hfrag.isSurface hfrag.connected rfl
  have hnb := hS1 _ Shat₁ β (fragScheme χ a₀ (D 0) hF flip) ⟨cap₁⟩ (hsimple Shat₁ cap₁)
  unfold ColourScheme.IsBad at hnb
  push Not at hnb
  have := hnb fun m ↦ fragPainting (a₀ := a₀) (D 0) hF flip (seq m).P (D m) (h m).anchored
  unfold IsBadSequence at this
  push Not at this
  obtain ⟨i, j, hij, σv, σe, hσ⟩ := this
  exact ⟨i, j, hij, σv, σe, hσ⟩

/-- **The place of a flaw.** Let `F` be a flaw, `Σ₂` its disc side, and let `α` carry the fixed
feature `Kc` to the part `K` of `F` in `Σ`,
and the fragment `ψ` onto the part of `Σ₂` in `Σ`. Then the arm `Γ ∩ Σ₁` isolates `𝒯`, and the
location comes from a place of the fragment. -/
theorem exists_place [ConnectedSpace Shat] (hS : IsSurface S) {D : TangleDatum cap χ}
    (h3 : D.P.Γ.IsInternallyThreeConnected) (hd : χ.IsDisjoint) {F : Drawing Shat}
      (hFl : D.IsRepFlaw F) {Δ : Set Shat}
    (hΔ : IsClosedDisc Δ) (hbd : discBd Δ = F.U) (hnd : ¬ IsClosedDisc (closure Δᶜ))
    (hm : (partIn cap D.P.Γ (closure Δᶜ), partIn cap D.P.Γ Δ) ∈ D.𝒯) {K Kc : Drawing S}
    (hpart : IsCircuitPart cap χ.Φ D.P.Γ F K) (htwo : ∃ a ∈ K.U ∩ D.P.Γ.V, ∃ b ∈ K.U ∩ D.P.Γ.V, a ≠
      b) {α : S ≃ₜ S}
    (hα : IsFramePreservingHomeo χ.Φ α) (hαU : α '' Kc.U = K.U) (hαV : α '' Kc.V
      = K.V) {Z : Type} {ψ : Z → S}
    (hrange : range ψ = α ⁻¹' (cap.emb ⁻¹' Δ)) {l : List S} (hl : ∀ v, v ∈ l ↔ v ∈ Kc.V
      ∧ α v ∈ D.P.Γ.V) {n : ℕ}
    (hrep : D.rep < n) (hord : n ≤ D.ord) :
    ∃ L : RootedLocation D.P.Γ, L.Isolates D.tb n D.ord D.𝒯 ∧
      ∃ X : Place χ, IsCutPlace χ Kc ψ l 1 X ∧ IsPlaceHomeoImage X ⟨hd, D.P, L⟩ α := by
  classical
  have hT := cap.isClosedSurface
  set Γ := D.P.Γ with hΓ
  set A₁ := cap.emb ⁻¹' closure Δᶜ with hA₁
  set A₂ := cap.emb ⁻¹' Δ with hA₂
  have hsep : Γ.toHypergraph.IsSeparation (Γ.restrict A₁) (Γ.restrict A₂)
    := D.isTangle.isSeparation hm
  have hsides : IsSidesOf F (closure Δᶜ) Δ := by
    have h₀ : Sided F (discInt Δ) Δᶜ := ⟨Δ, hΔ, hbd, Or.inl ⟨rfl, rfl⟩⟩
    have := (Sided.symm h₀).isSidesOf hT
    rwa [closure_discInt hΔ] at this
  obtain ⟨-, -, S₁', S₂', hs', hlink⟩ := TangleDatum.IsRepFlaw.linked hS h3 hFl hsides hnd hm
  have hlink' : GM18.IsLambdaLinkedTo D.tb.lambdaOrder D.𝒯 (Γ.restrict A₁) (Γ.restrict A₂) := by
    rcases isSidesOf_cases hT hΔ hbd hs' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂] at hlink
      refine absurd ?_ (D.isTangle.axiom2 hm hm hlink.1)
      change Γ.restrict A₁ ∪ Γ.restrict A₁ ∪ Γ.restrict A₂ = Γ.toHypergraph
      rw [GM10.union_self, hsep.union_eq]
    · rw [h₁, h₂] at hlink
      exact hlink
  let π : List S := (Γ.restrict A₁ ∩ Γ.restrict A₂).vertexSet_finite.toFinset.toList
  have hπ : {v | v ∈ π} = (Γ.restrict A₁ ∩ Γ.restrict A₂).vertexSet := by
    ext v
    simp [π]
  let A : Arm Γ := restrictArm Γ A₁ A₂ hsep π (Finset.nodup_toList _) hπ
  let L : RootedLocation Γ := oneLocation A
  have hLord : L.ord = A.order := by
    change sSup (Arm.order '' ({A} : Set (Arm Γ))) = _
    simp
  have hord' : A.order ≤ D.rep := by
    have : F.E.ncard = 2 * Hypergraph.separationOrder (Γ.restrict A₂) (Γ.restrict A₁) :=
      disc_order hS h3 D.rad hFl.is_circuit hΔ hbd
    have h₂ := hFl.card_le
    change Hypergraph.separationOrder (Γ.restrict A₁) (Γ.restrict A₂) ≤ _
    rw [separationOrder_comm]
    omega
  have hLl : L.IsLambdaLinked D.tb D.𝒯 := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨B, rfl, rfl⟩
      exact hm
    · rintro B rfl
      exact hlink'
  refine ⟨L, theorem_8_8_proof D.tb hS h3 D.isTangle hLl (by rw [hLord]; omega) hord, ?_⟩
  let Q : ColouredPainting χ := D.P.image α.symm hα.symm
  have hQ : IsColouredImage α.symm D.P Q := ColouredPainting.isImage_image _ _ _
  have I : IsColouredImage α Q D.P := hQ.symm
  have hsym : ∀ X : Set S, α '' (α.symm '' X) = X := fun X ↦ by
    rw [image_image]
    simp
  let B₁ := α.symm '' A₁
  let B₂ := α.symm '' A₂
  have hsep' : Q.Γ.toHypergraph.IsSeparation (Q.Γ.restrict B₁) (Q.Γ.restrict B₂)
    := sep_image hQ hsep
  have hB₂ : range ψ = B₂ := by
    rw [hrange]
    ext x
    exact ⟨fun h ↦ ⟨α x, h, by simp⟩, fun ⟨y, hy, hyx⟩ ↦ by
      subst hyx
      simpa using hy⟩
  have hπ' : {v | v ∈ π.map α.symm} = (Q.Γ.restrict B₁ ∩ Q.Γ.restrict B₂).vertexSet := by
    change _ = (Q.Γ.restrict B₁).vertexSet ∩ (Q.Γ.restrict B₂).vertexSet
    rw [restrict_image_V hQ, restrict_image_V hQ, ← image_inter α.symm.injective]
    ext v
    change v ∈ π.map α.symm ↔ _
    rw [List.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact mem_image_of_mem _ (hπ.subset hu)
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hπ.superset hu, rfl⟩
  let A' : Arm Q.Γ := restrictArm Q.Γ B₁ B₂ hsep' (π.map α.symm)
    ((Finset.nodup_toList _).map α.symm.injective) hπ'
  have hinter : Q.Γ.U ∩ Kc.U ⊆ Q.Γ.V ∩ Kc.V := by
    rintro x ⟨hx₁, hx₂⟩
    rw [hQ.U] at hx₁
    obtain ⟨y, hy, rfl⟩ := hx₁
    have hy' : y ∈ K.U := by
      rw [← hαU]
      exact ⟨_, hx₂, α.apply_symm_apply y⟩
    obtain ⟨h₁, h₂⟩ := hpart.inter ⟨hy, hy'⟩
    refine ⟨?_, ?_⟩
    · rw [hQ.V]
      exact mem_image_of_mem _ h₁
    · rw [← hαV] at h₂
      obtain ⟨z, hz, rfl⟩ := h₂
      rwa [α.symm_apply_apply]
  have hclosed : IsClosed B₂ := by
    change IsClosed (α.symm '' _)
    rw [α.symm.image_eq_preimage_symm]
    exact (hΔ.isClosed.preimage cap.isEmbedding.continuous).preimage α.symm.symm.continuous
  have hUF : ∀ {v}, v ∈ Kc.U → v ∈ range ψ := fun {v} hv ↦ by
    rw [hrange]
    refine (hbd ▸ Surface.discBd_subset Δ : F.U ⊆ Δ) (hpart.form.image_subset
      (mem_image_of_mem _ ?_))
    rw [← hαU]
    exact mem_image_of_mem _ hv
  have htwo' : ∃ a ∈ Kc.U ∩ Q.Γ.V, ∃ b ∈ Kc.U ∩ Q.Γ.V, a ≠ b := by
    obtain ⟨a, ha, b, hb, hab⟩ := htwo
    have key : ∀ {a}, a ∈ K.U ∩ D.P.Γ.V → α.symm a ∈ Kc.U ∩ Q.Γ.V := fun {a} ha ↦ by
      refine ⟨?_, ?_⟩
      · have := ha.1
        rw [← hαU] at this
        obtain ⟨z, hz, rfl⟩ := this
        rwa [α.symm_apply_apply]
      · rw [hQ.V]
        exact mem_image_of_mem _ ha.2
    exact ⟨_, key ha, _, key hb, fun h ↦ hab (α.symm.injective h)⟩
  refine ⟨⟨hd, Q, oneLocation A'⟩, ⟨hinter, fun v ↦ ?_, fun v hv ↦ ?_, ?_, ?_, ?_, ?_, ?_⟩,
    hα, I.U.symm, I.V.symm, fun e he ↦ ⟨I.γ e he, I.φ e he⟩, fun _ ↦ A, ?_, ?_⟩
  · rw [hl, hQ.V]
    refine ⟨fun h ↦ ⟨h.1, _, h.2, α.symm_apply_apply v⟩, ?_⟩
    rintro ⟨h₁, u, hu, rfl⟩
    exact ⟨h₁, by simpa using hu⟩
  · exact hUF (Kc.V_subset_U ((hl v).1 hv).1)
  · exact isAnchored_of_form (hpart.form.ofHomeo α hαU) hinter htwo'
  · change (oneLocation A').M.vertexSet = _
    rw [oneLocation_M_V, hB₂]
    ext v
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, h⟩⟩
  · change (oneLocation A').M.edgeSet = _
    rw [oneLocation_M_E, hB₂]
    ext e
    constructor
    · exact fun h ↦ ⟨h.1, h.2.2.1⟩
    · refine fun h ↦ ⟨h.1, h.1, h.2, ?_⟩
      exact fun x hx ↦ closure_minimal h.2 hclosed hx.1.1
  · rintro B rfl v hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hv
    have hu' : u ∈ (Γ.restrict A₁ ∩ Γ.restrict A₂).vertexSet := hπ.subset hu
    have h₁ : cap.emb u ∈ F.U := (disc_facts hS h3 D.rad hFl.is_circuit hΔ hbd).2.1 u ⟨hu'.2, hu'.1⟩
    have h₂ : u ∈ K.U := hpart.form.mem_U h₁
    have h₃ := (hpart.inter ⟨Γ.V_subset hu'.1.1, h₂⟩).2
    rw [← hαV] at h₃
    obtain ⟨z, hz, rfl⟩ := h₃
    refine (hl _).2 ⟨by simpa using hz, by simpa using hu'.1.1⟩
  · change ({A'} : Set (Arm Q.Γ)).ncard ≤ 1
    simp
  · refine ⟨fun B hB ↦ rfl, fun B hB C hC _ ↦ hB.trans hC.symm, ?_⟩
    rintro B rfl
    exact ⟨A', rfl, rfl⟩
  · rintro B rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have := restrict_image_V I B₁
      rwa [hsym] at this
    · have := restrict_image_E I B₁
      rwa [hsym] at this
    · have := restrict_image_V I B₂
      rwa [hsym] at this
    · have := restrict_image_E I B₂
      rwa [hsym] at this
    · change π = (π.map α.symm).map α
      simp

omit [T2Space S] in
theorem IsCutPlace.congr {Z Z' : Type} {K : Drawing S} {ψ : Z → S} {ψ' : Z'
  → S} {l l' : List S} {m : ℕ} {X : Place χ}
    (h : IsCutPlace χ K ψ l m X) (hr : range ψ = range ψ') (hl : ∀ v, v ∈ l ↔ v ∈ l') : IsCutPlace
      χ K ψ' l' m X where
  inter := h.inter
  roots v := by rw [← hl]; exact h.roots v
  roots_range v hv := hr ▸ h.roots_range v ((hl v).2 hv)
  anchored := h.anchored
  M_V := hr ▸ h.M_V
  M_E := hr ▸ h.M_E
  arms_π A hA v hv := (hl v).1 (h.arms_π A hA v hv)
  arms_card := h.arms_card

theorem finite_components {Y : Type} [TopologicalSpace Y] (hY : IsSurface Y) : Finite
  (ConnectedComponents Y) := by
  have : LocallyConnectedSpace Y := hY.locallyConnected
  have : CompactSpace Y := hY.1
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x : Y ↦ connectedComponent x)
    (fun x ↦ isOpen_connectedComponent) (fun x _ ↦ mem_iUnion.mpr ⟨x, mem_connectedComponent⟩)
  refine Finite.of_surjective (fun t : T ↦ (ConnectedComponents.mk t.1 : ConnectedComponents Y))
    fun c ↦ ?_
  obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.mp (hT (mem_univ z))
  exact ⟨⟨t, ht⟩, ConnectedComponents.coe_eq_coe'.2 hzt |>.symm⟩

omit [T2Space S] in
/-- For a fixed cut, one well-behaved set holds the places of all good fragments and all sets of
roots. -/
theorem exists_class_cut_on {K : Drawing S} {Y : Type} [TopologicalSpace Y]
  (hY : IsSurface Y) {ψ : Y → S} (m : ℕ) (Good : Set Y → Prop)
    (Q : Set Y → Place χ → Prop) (hw : ∀ (y : Y) (l : List S), Good (connectedComponent y) →
      IsWellBehavedPlaces {X | IsCutPlace χ K (fun x : connectedComponent y ↦ ψ x.1) l m X ∧ Q
        (connectedComponent y) X}) :
    ∃ B : Set (Place χ), IsWellBehavedPlaces B ∧ ∀ (y : Y) (l : List S) (X : Place χ), Good
      (connectedComponent y) →
      (∀ v ∈ l, v ∈ K.V) → IsCutPlace χ K (fun x : connectedComponent y ↦ ψ x.1) l m X → Q
        (connectedComponent y) X → X ∈ B := by
  classical
  have := finite_components hY
  let y₀ : ConnectedComponents Y → Y := fun c ↦ (ConnectedComponents.surjective_coe c).choose
  have hy₀ : ∀ c, (ConnectedComponents.mk (y₀ c) : ConnectedComponents Y) = c :=
    fun c ↦ (ConnectedComponents.surjective_coe c).choose_spec
  let ι := ConnectedComponents Y × ↥K.finite_V.toFinset.powerset
  let C : ι → Set (Place χ) := fun p ↦
    {X | Good (connectedComponent (y₀ p.1)) ∧ IsCutPlace χ K (fun x : connectedComponent
      (y₀ p.1) ↦ ψ x.1) p.2.1.toList m X ∧ Q (connectedComponent (y₀ p.1)) X}
  refine ⟨⋃ p, C p, IsWellBehavedPlaces.iUnion fun p ↦ ?_, fun y l X hs hl hX hQ ↦ ?_⟩
  · by_cases h : Good (connectedComponent (y₀ p.1))
    · exact IsWellBehavedPlaces.mono (Pl' := C p) (hw (y₀ p.1) p.2.1.toList h) fun _ hX ↦ hX.2
    · exact fun Ω hΩ seq hseq ↦ absurd (hseq 0).1 h
  · have heq : connectedComponent (y₀ (ConnectedComponents.mk y)) = connectedComponent y :=
      ConnectedComponents.coe_eq_coe.1 (hy₀ _)
    let W : Finset S := l.toFinset
    have hW : W ∈ K.finite_V.toFinset.powerset := by
      refine Finset.mem_powerset.2 fun v hv ↦ ?_
      exact K.finite_V.mem_toFinset.2 (hl v (List.mem_toFinset.1 hv))
    refine mem_iUnion.2 ⟨(ConnectedComponents.mk y, ⟨W, hW⟩), ?_, ?_, heq.symm ▸ hQ⟩
    · exact heq.symm ▸ hs
    · refine hX.congr ?_ fun v ↦ by simp [W]
      have h₁ : range (fun x : connectedComponent y ↦ ψ x.1) = ψ '' connectedComponent y := by
        ext z
        simp
      have h₂ : range (fun x : connectedComponent (y₀ (ConnectedComponents.mk y)) ↦ ψ x.1) =
          ψ '' connectedComponent (y₀ (ConnectedComponents.mk y)) := by
        ext z
        simp
      rw [h₁, h₂, heq]

omit [T2Space S] in
theorem exists_class_cut {K : Drawing S} {Y : Type} [TopologicalSpace Y] (hY : IsSurface Y) {ψ : Y
  → S} (m : ℕ) (Good : Set Y → Prop)
    (Q : Place χ → Prop) (hw : ∀ (y : Y) (l : List S), Good (connectedComponent y) →
      IsWellBehavedPlaces {X | IsCutPlace χ K (fun x : connectedComponent y ↦ ψ x.1) l m X ∧ Q X}) :
    ∃ B : Set (Place χ), IsWellBehavedPlaces B ∧ ∀ (y : Y) (l : List S) (X : Place χ), Good
      (connectedComponent y) →
      (∀ v ∈ l, v ∈ K.V) → IsCutPlace χ K (fun x : connectedComponent y ↦ ψ x.1) l m X → Q X
        → X ∈ B :=
  exists_class_cut_on hY m Good (fun _ ↦ Q) hw

/-- `Kc` is the part in `Σ` of a circuit. -/
def IsPartFeature (cap : IsCappedSurface S Shat) (χ : ColourScheme S β) (Kc : Drawing S) : Prop :=
  ∃ (D : TangleDatum cap χ) (F : Drawing Shat), IsCircuitPart cap χ.Φ D.P.Γ F Kc

/-- `D` has a flaw whose part in `Σ` is an image of `Kc`. -/
def TangleDatum.IsFlawAt (D : TangleDatum cap χ) (Kc : Drawing S) : Prop :=
  ∃ (F : Drawing Shat) (Δ : Set Shat) (K : Drawing S) (α : S ≃ₜ S), D.IsRepFlaw F ∧ IsClosedDisc Δ
    ∧ discBd Δ = F.U ∧
    ¬ IsClosedDisc (closure Δᶜ) ∧ (partIn cap D.P.Γ (closure Δᶜ), partIn cap D.P.Γ Δ) ∈ D.𝒯 ∧
    IsCircuitPart cap χ.Φ D.P.Γ F K ∧ (∃ a ∈ K.U ∩ D.P.Γ.V, ∃ b ∈ K.U ∩ D.P.Γ.V, a ≠ b) ∧
    IsFramePreservingHomeo χ.Φ α ∧ α '' Kc.U = K.U ∧ α '' Kc.V = K.V

/-- One well-behaved set for all flaws with a given feature. -/
theorem exists_class_feature (hS : IsSurface S) (hd : χ.IsDisjoint) (n : ℕ) (a₀ : β)
    (hS1 : ConditionS1.{0, w} Shat) {Kc : Drawing S} (hg : IsPartFeature cap χ Kc) :
    ∃ B : Set (Place χ), IsWellBehavedPlaces B ∧ ∀ D : TangleDatum cap χ, D.rep < n → n ≤ D.ord
      → D.IsFlawAt Kc →
      ∃ L : RootedLocation D.P.Γ, L.Isolates D.tb n D.ord D.𝒯 ∧ (⟨hd, D.P, L⟩ : Place χ) ∈ B := by
  classical
  have : ConnectedSpace S := χ.connected
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨D₀, F₀, hp⟩ := hg
  have hKne : Kc.V ⊆ ⋃ e ∈ arcComponentsIn (Kc.U \ Kc.V), closure e := fun v hv ↦ by
    obtain ⟨e, he, hve⟩ := hp.feature.no_isolated_vertices v hv
    exact mem_biUnion he hve.1
  obtain ⟨Y, tY, t2Y, ψ, hY, hψ, hsheet⟩ := exists_cut_of_form hS D₀.P.fits hp.form hp.inter
    hp.lines hKne
  obtain ⟨B, hB, hmem⟩ := exists_class_cut (χ := χ) (K := Kc) hY (ψ := ψ) 1
    (fun c ↦ ∀ (Shat₁ : Type) [TopologicalSpace Shat₁], IsCappedSurface c Shat₁
      → IsSimplerThan Shat₁ Shat) (fun _ ↦ True)
    (fun y l h ↦ wellBehaved_S1 hS hp.feature hp.lines hY hψ hsheet y l 1 a₀ hS1 h)
  refine ⟨_, theorem_9_4_proof hB, ?_⟩
  rintro D hrep hord ⟨F, Δ, K, α, hFl, hΔ, hbd, hnd, hm, hpart, htwo, hα, hαU, hαV⟩
  obtain ⟨y, hy, hsph⟩ := GraphMinor.GM19.discSide S Shat (cap.ofHomeo α) Kc F.U Δ hS
    (hpart.form.ofHomeo α hαU) hΔ hbd Y tY t2Y ψ hY hψ
  have hfin : (Kc.V ∩ α ⁻¹' D.P.Γ.V).Finite := Kc.finite_V.subset inter_subset_left
  have hrange : range (fun x : connectedComponent y ↦ ψ x.1) = α ⁻¹' (cap.emb ⁻¹' Δ) := by
    have : range (fun x : connectedComponent y ↦ ψ x.1) = ψ '' connectedComponent y := by
      ext z
      simp
    rw [this, hy]
    rfl
  obtain ⟨L, hL, X, hX, hXim⟩ := exists_place hS D.P.fits.internally_three_connected hd hFl hΔ hbd
    hnd hm hpart htwo hα hαU hαV
    hrange (l := hfin.toFinset.toList) (fun v ↦ by simp) hrep hord
  refine ⟨L, hL, X, hmem y _ X (fun Shat₁ _ cap₁ ↦ ?_) (fun v hv ↦ ?_) hX trivial, α, hXim⟩
  · exact simpler_of_sphere cap hFl.not_sphere (hsph Shat₁ cap₁)
  · exact (hfin.mem_toFinset.1 (Finset.mem_toList.1 hv)).1

/-- **Graph Minors XIX, (10.3)** (page 355), from (5.2) and the topological step of (10.2). -/
theorem theorem_10_3_proof : Theorem103Statement.{w} := by
  intro S Shat _ _ _ _ β _ cap χ hd 𝒮 _ hS1 n _
  classical
  have hS := χ.isSurface
  have : ConnectedSpace S := χ.connected
  have : ConnectedSpace Shat := cap.connected
  have hT := cap.isClosedSurface
  let a₀ : β := Classical.arbitrary β
  obtain ⟨𝓕, hf, h𝓕⟩ := GraphMinor.GM19.theorem_5_2_proof S hS χ.connected χ.Φ (4 * n)
  have hpick : ∀ K₀, ∃ K', ∀ K, IsPartFeature cap χ K → FeatureEquiv χ.Φ K₀ K →
      IsPartFeature cap χ K' ∧ FeatureEquiv χ.Φ K₀ K' := fun K₀ ↦ by
    by_cases h : ∃ K, IsPartFeature cap χ K ∧ FeatureEquiv χ.Φ K₀ K
    · obtain ⟨K, h₁, h₂⟩ := h
      exact ⟨K, fun _ _ _ ↦ ⟨h₁, h₂⟩⟩
    · exact ⟨K₀, fun K h₁ h₂ ↦ absurd ⟨K, h₁, h₂⟩ h⟩
  choose p hp using hpick
  have hB : ∀ Kc, ∃ B : Set (Place χ), IsWellBehavedPlaces B ∧ (IsPartFeature cap χ Kc
    → ∀ D : TangleDatum cap χ, D.rep < n →
      n ≤ D.ord → D.IsFlawAt Kc → ∃ L : RootedLocation D.P.Γ, L.Isolates D.tb n D.ord D.𝒯 ∧
        (⟨hd, D.P, L⟩ : Place χ) ∈ B) := fun Kc ↦ by
    by_cases hg : IsPartFeature cap χ Kc
    · obtain ⟨B, h₁, h₂⟩ := exists_class_feature hS hd n a₀ hS1 hg
      exact ⟨B, h₁, fun _ ↦ h₂⟩
    · exact ⟨∅, fun Ω hΩ seq hseq ↦ absurd (hseq 0) (notMem_empty _), fun h ↦ absurd h hg⟩
  choose B hBw hBm using hB
  have : Finite 𝓕 := hf
  refine ⟨⋃ K₀ : 𝓕, B (p K₀.1), IsWellBehavedPlaces.iUnion fun _ ↦ hBw _, ?_⟩
  intro D _ hrep hord hlt hdist
  have h₁ : (D.rep : ℕ∞) < Painting.rep D.rad := lt_of_lt_of_le (by exact_mod_cast hlt) hrep
  have h₂ : D.rep < D.ord := by omega
  have h3 := D.P.fits.internally_three_connected
  obtain ⟨F, hFl⟩ := TangleDatum.exists_repFlaw hS h3 h₁ h₂
  obtain ⟨S₁, S₂, hs, hnd, hm⟩ := hFl.has_non_disc
  obtain ⟨Δ, hΔ, hbd⟩ := exists_disc_of_lt_rep hFl.is_circuit hFl.lt_two_rep
  have hsides : S₁ = closure Δᶜ ∧ S₂ = Δ := by
    rcases isSidesOf_cases hT hΔ hbd hs with ⟨rfl, -⟩ | h
    · exact absurd hΔ hnd
    · exact h
  obtain ⟨rfl, rfl⟩ := hsides
  have hE := hFl.card_le
  have hdd : ((F.E.ncard + 4 : ℕ) : ℕ∞) < Painting.dist D.rad * 4 := by
    calc ((F.E.ncard + 4 : ℕ) : ℕ∞) < ((2 * (n + 2) : ℕ) : ℕ∞) := by
          have : F.E.ncard + 4 < 2 * (n + 2) := by omega
          exact_mod_cast this
      _ = 2 * ((n + 2 : ℕ) : ℕ∞) := by push_cast; ring
      _ ≤ 2 * (2 * Painting.dist D.rad) := by gcongr
      _ = Painting.dist D.rad * 4 := by ring
  obtain ⟨K, hK, htwo⟩ := TangleDatum.exists_flaw_part hS h3 hFl hs hnd hm hdd
  have hV : F.V.ncard = F.E.ncard := by
    obtain ⟨-, hFc⟩ := hFl.is_circuit
    exact IsCircuit.ncard_V hFc
  obtain ⟨K₀, hK₀, f, hfp, hfU, hfV⟩ := h𝓕 K hK.feature (by
    have := hK.V_le
    have := hK.E_le
    omega)
  have hg : IsPartFeature cap χ K := ⟨D, F, hK⟩
  obtain ⟨hg', g, hgp, hgU, hgV⟩ := hp K₀ K hg ⟨f, hfp, hfU, hfV⟩
  have hU : (g.symm.trans f) '' (p K₀).U = K.U := by
    have : (g.symm.trans f) '' (p K₀).U = f '' (g.symm '' (p K₀).U) := by
      rw [image_image]
      rfl
    rw [this, ← hgU, symm_image_image', hfU]
  have hV' : (g.symm.trans f) '' (p K₀).V = K.V := by
    have : (g.symm.trans f) '' (p K₀).V = f '' (g.symm '' (p K₀).V) := by
      rw [image_image]
      rfl
    rw [this, ← hgV, symm_image_image', hfV]
  obtain ⟨L, hL, hmem⟩ := hBm (p K₀) hg' D hlt hord
    ⟨F, S₂, K, g.symm.trans f, hFl, hΔ, hbd, hnd, hm, hK, htwo, hgp.symm.trans hfp, hU, hV'⟩
  exact ⟨L, hL, mem_iUnion.2 ⟨⟨K₀, hK₀⟩, hmem⟩⟩

end GraphMinor.GM19
