/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section10g

/-!
# Locations and their images

The image of a rooted location under a homeomorphism, and the place of a location whose set `M` is
the part of a fragment.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10

universe w

variable {S : Type} [TopologicalSpace S] [T2Space S] {β : Type w} {χ : ColourScheme S β}


/-- The image of a hypergraph with edges in `S`. -/
def mapSub (f : S ≃ₜ S) (H : Hypergraph S (Set S)) : Hypergraph S (Set S) where
  vertexSet := f '' H.vertexSet
  edgeSet := (fun e ↦ f '' e) '' H.edgeSet
  Inc e v := H.Inc (f.symm '' e) (f.symm v)
  vertex_mem_of_inc _ v h := ⟨_, H.vertex_mem_of_inc h, f.apply_symm_apply v⟩
  edge_mem_of_inc e _ h := ⟨_, H.edge_mem_of_inc h, by simp [image_image]⟩
  vertexSet_finite := H.vertexSet_finite.image _
  edgeSet_finite := H.edgeSet_finite.image _

omit [T2Space S] in
theorem mapSub_symm (f : S ≃ₜ S) (H : Hypergraph S (Set S)) : mapSub f.symm (mapSub f H) = H := by
  refine Hypergraph.ext ?_ ?_ ?_
  · simp [mapSub, image_image]
  · simp [mapSub, image_image]
  · funext e v
    simp [mapSub, image_image]

omit [T2Space S] in
theorem mapSub_symm' (f : S ≃ₜ S) (H : Hypergraph S (Set S)) : mapSub f (mapSub f.symm H) = H := by
  simpa using mapSub_symm f.symm H

omit [T2Space S] in
theorem mapSub_mono (f : S ≃ₜ S) {H H' : Hypergraph S (Set S)} (h : H ≤ H') : mapSub f H
  ≤ mapSub f H' where
  vertexSet_subset := image_mono h.vertexSet_subset
  edgeSet_subset := image_mono h.edgeSet_subset
  ends_eq e he := by
    obtain ⟨c, hc, rfl⟩ := he
    ext v
    have := Set.ext_iff.1 (h.ends_eq c hc) (f.symm v)
    simp only [Hypergraph.ends, mapSub, symm_image_image'] at this ⊢
    exact this

variable {f : S ≃ₜ S} {P P' : ColouredPainting χ}

omit [T2Space S] in
theorem mapSub_toHypergraph (I : IsColouredImage f P P') : mapSub f P.Γ.toHypergraph
  = P'.Γ.toHypergraph := by
  refine Hypergraph.ext I.V.symm I.E_eq.symm ?_
  funext e v
  apply propext
  change (f.symm '' e ∈ P.Γ.E ∧ f.symm v ∈ P.Γ.V ∧ f.symm v ∈ tilde (f.symm '' e)) ↔ e ∈ P'.Γ.E
    ∧ v ∈ P'.Γ.V ∧ v ∈ tilde e
  have hE : ∀ c, c ∈ P'.Γ.E ↔ f.symm '' c ∈ P.Γ.E := fun c ↦ by
    rw [I.E_eq]
    constructor
    · rintro ⟨d, hd, rfl⟩
      rwa [symm_image_image']
    · exact fun h ↦ ⟨_, h, by simp [image_image]⟩
  have hV : ∀ w, w ∈ P'.Γ.V ↔ f.symm w ∈ P.Γ.V := fun w ↦ by
    rw [I.V]
    constructor
    · rintro ⟨d, hd, rfl⟩
      simpa using hd
    · exact fun h ↦ ⟨_, h, f.apply_symm_apply w⟩
  rw [hE, hV, tilde_image_homeo f.symm]
  have : f.symm v ∈ f.symm '' tilde e ↔ v ∈ tilde e :=
    ⟨fun ⟨y, hy, hyv⟩ ↦ f.symm.injective hyv ▸ hy, mem_image_of_mem _⟩
  rw [this]

/-- The image of an arm. -/
def Arm.map (I : IsColouredImage f P P') (A : Arm P.Γ) : Arm P'.Γ where
  minus := mapSub f A.minus
  compl := mapSub f A.compl
  isSeparation := by
    have h₁ : mapSub f A.minus ≤ P'.Γ.toHypergraph := mapSub_toHypergraph I ▸ mapSub_mono f
      A.isSeparation.left_le
    have h₂ : mapSub f A.compl ≤ P'.Γ.toHypergraph := mapSub_toHypergraph I ▸ mapSub_mono f
      A.isSeparation.right_le
    rw [isSeparation_iff_of_le h₁ h₂]
    have hs := A.isSeparation
    refine ⟨?_, ?_, ?_⟩
    · change f '' _ ∪ f '' _ = _
      rw [← image_union, hs.vertexSet_union]
      exact I.V.symm
    · change (fun e ↦ f '' e) '' _ ∪ (fun e ↦ f '' e) '' _ = _
      rw [← image_union, hs.edgeSet_union]
      exact I.E_eq.symm
    · change (fun e ↦ f '' e) '' _ ∩ (fun e ↦ f '' e) '' _ = _
      have h₃ : A.minus.edgeSet ∩ A.compl.edgeSet = ∅ := hs.edgeSet_inter_eq
      rw [← image_inter f.injective.image_injective, h₃, image_empty]
  π := A.π.map f
  π_nodup := A.π_nodup.map f.injective
  π_set := by
    change _ = f '' _ ∩ f '' _
    rw [← image_inter f.injective]
    have := A.π_set
    ext v
    change v ∈ A.π.map f ↔ v ∈ f '' (A.minus ∩ A.compl).vertexSet
    rw [List.mem_map, ← this]
    rfl

omit [T2Space S] in
theorem Arm.ext' {Γ : Painting S} {A B : Arm Γ} (h₁ : A.minus = B.minus) (h₂ : A.compl = B.compl)
  (h₃ : A.π = B.π) : A = B := by
  cases A
  cases B
  cases h₁
  cases h₂
  cases h₃
  rfl

omit [T2Space S] in
theorem Arm.map_symm (I : IsColouredImage f P P') (A : Arm P.Γ) : Arm.map I.symm (Arm.map I A) = A
  := by
  refine Arm.ext' (mapSub_symm f _) (mapSub_symm f _) ?_
  change (A.π.map f).map f.symm = A.π
  simp

omit [T2Space S] in
theorem Arm.map_symm' (I : IsColouredImage f P P') (A : Arm P'.Γ) : Arm.map I (Arm.map I.symm A)
  = A := by
  refine Arm.ext' (mapSub_symm' f _) (mapSub_symm' f _) ?_
  change (A.π.map f.symm).map f = A.π
  simp

/-- The image of a rooted location. -/
def RootedLocation.map (I : IsColouredImage f P P') (L : RootedLocation P.Γ) : RootedLocation P'.Γ
  where
  arms := Arm.map I '' L.arms
  finite_arms := L.finite_arms.image _
  disjoint_arms := by
    rintro _ ⟨A₁, h₁, rfl⟩ _ ⟨A₂, h₂, rfl⟩ hne
    exact mapSub_mono f (L.disjoint_arms A₁ h₁ A₂ h₂ fun h ↦ hne (h ▸ rfl))

variable {K : Drawing S} {Z : Type} [TopologicalSpace Z] {ψ : Z → S}

omit [TopologicalSpace Z] in
omit [T2Space S] in
/-- Let `ℒ` be a location of `P'` with `M(Γ', ℒ)` the part of `Γ'` in `R`, and let the fragment `ψ`
lie over `f⁻¹(R)`. Then the
location `f⁻¹(ℒ)` of `P` gives a place of the fragment. -/
theorem exists_cut_place (hd : χ.IsDisjoint) (hf : IsFramePreservingHomeo χ.Φ f)
  (I : IsColouredImage f P P') (L : RootedLocation P'.Γ)
    {R : Set S} (hV : L.M.vertexSet = P'.Γ.V ∩ R) (hE : L.M.edgeSet = {e ∈ P'.Γ.E | e ⊆ R})
      (hrange : range ψ = f ⁻¹' R)
    (hinter : P.Γ.U ∩ K.U ⊆ P.Γ.V ∩ K.V) (han : IsAnchored P.Γ K) {l : List S}
      (hl : ∀ v, v ∈ l ↔ v ∈ K.V ∩ P.Γ.V)
    (hr : ∀ v, v ∈ K.U → v ∈ range ψ) (hπ : ∀ A ∈ L.arms, ∀ v ∈ A.π, f.symm v ∈ K.U) {m : ℕ}
      (hm : L.arms.ncard ≤ m) :
    ∃ X : Place χ, X.P = P ∧ IsCutPlace χ K ψ l m X ∧ IsPlaceHomeoImage X ⟨hd, P', L⟩ f := by
  classical
  let J := I.symm
  let X : Place χ := ⟨hd, P, L.map J⟩
  have hg : BijOn (Arm.map I) X.L.arms L.arms := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨A, hA, rfl⟩
      rw [Arm.map_symm']
      exact hA
    · rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hAB
      rw [Arm.map_symm', Arm.map_symm'] at hAB
      rw [hAB]
    · exact fun A hA ↦ ⟨Arm.map J A, mem_image_of_mem _ hA, Arm.map_symm' I A⟩
  have hc₁ : ∀ A ∈ X.L.arms, (Arm.map I A).compl.vertexSet = f '' A.compl.vertexSet := fun _ _ ↦ rfl
  have hc₂ : ∀ A ∈ X.L.arms, (Arm.map I A).compl.edgeSet = (fun e ↦ f '' e) '' A.compl.edgeSet
    := fun _ _ ↦ rfl
  have hMV : L.M.vertexSet = f '' X.L.M.vertexSet :=
    IsPlaceHomeoImage.M_V (X := X) (Y := ⟨hd, P', L⟩) I.V hg hc₁
  have hME : L.M.edgeSet = (fun e ↦ f '' e) '' X.L.M.edgeSet :=
    IsPlaceHomeoImage.M_E (X := X) (Y := ⟨hd, P', L⟩) I.E_eq hg hc₂
  refine ⟨X, rfl, ⟨hinter, fun v ↦ hl v, fun v hv ↦ hr v (K.V_subset_U ((hl v).1 hv).1), han, ?_,
    ?_, ?_, ?_⟩,
    hf, I.U.symm, I.V.symm, fun e he ↦ ⟨I.γ e he, I.φ e he⟩, Arm.map I, hg, fun A _ ↦ ⟨rfl, rfl,
      rfl, rfl, rfl⟩⟩
  · ext v
    rw [hrange]
    constructor
    · intro hv
      have : f v ∈ L.M.vertexSet := hMV ▸ mem_image_of_mem _ hv
      rw [hV, I.V] at this
      obtain ⟨⟨u, hu, huv⟩, hR⟩ := this
      exact ⟨f.injective huv ▸ hu, hR⟩
    · rintro ⟨hv, hR⟩
      have : f v ∈ L.M.vertexSet := by
        rw [hV, I.V]
        exact ⟨mem_image_of_mem _ hv, hR⟩
      rw [hMV] at this
      obtain ⟨u, hu, huv⟩ := this
      exact f.injective huv ▸ hu
  · ext e
    rw [hrange]
    constructor
    · intro he
      have : f '' e ∈ L.M.edgeSet := hME ▸ mem_image_of_mem _ he
      rw [hE] at this
      obtain ⟨h₁, h₂⟩ := this
      rw [I.E_eq] at h₁
      obtain ⟨c, hc, hce⟩ := h₁
      obtain rfl := f.injective.image_injective hce
      exact ⟨hc, fun x hx ↦ h₂ (mem_image_of_mem _ hx)⟩
    · rintro ⟨he, hR⟩
      have : f '' e ∈ L.M.edgeSet := by
        rw [hE]
        refine ⟨I.E_eq ▸ mem_image_of_mem _ he, ?_⟩
        rintro _ ⟨x, hx, rfl⟩
        exact hR hx
      rw [hME] at this
      obtain ⟨c, hc, hce⟩ := this
      obtain rfl := f.injective.image_injective hce
      exact hc
  · rintro _ ⟨A, hA, rfl⟩ v hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hv
    have h₁ := hπ A hA u hu
    have h₂ : u ∈ (A.minus ∩ A.compl).vertexSet := A.π_set ▸ hu
    have h₃ : u ∈ P'.Γ.V := A.isSeparation.left_le.vertexSet_subset h₂.1
    rw [I.V] at h₃
    obtain ⟨z, hz, rfl⟩ := h₃
    have hzK : f.symm (f z) ∈ K.U := h₁
    rw [f.symm_apply_apply] at hzK ⊢
    exact (hl z).2 ⟨(hinter ⟨P.Γ.V_subset hz, hzK⟩).2, hz⟩
  · refine le_trans (ncard_image_le L.finite_arms) hm

end GraphMinor.GM19
