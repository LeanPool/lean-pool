/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section44
public import LeanPool.GraphMinor.GM07.PushForest
public import LeanPool.GraphMinor.GM07.Section46Matching
import LeanPool.GraphMinor.GM07.Section3
import LeanPool.GraphMinor.GM07.Section41
import LeanPool.GraphMinor.GM07.Section46MatchedId
import LeanPool.GraphMinor.GM07.Section46Refine
import LeanPool.GraphMinor.GM07.CuffForest
import LeanPool.GraphMinor.GM07.CuffStep
import LeanPool.GraphMinor.GM07.ForestFlat
import LeanPool.GraphMinor.GM19.Section6Delete

/-!
# Claim (1) of VII (4.6)

Page 227: (4.4) gives `H₁` off `U(L)`, with the set `M₂` isolated in its
pullback. We delete `M₂`, and (3.6) gives `H₃` with few crossings of the
matching. A slide puts the crossings at vertices. We add `M₂` back to get
`H₄`, apply (4.5) to get `H₅ = θ(H₄)`, and add `V(G)` to get `H₆`.
-/

public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11

variable {S S' : Type} [TopologicalSpace S] [TopologicalSpace S']

/-- The forest `H₂` from which the isolated vertices `M₂` are deleted. -/
private theorem exists_delete_isolated [T2Space S'] {H' : Drawing
  S'}
    (hH' : IsSurfaceForest H') {M : Set S'} (hM : ∀ z ∈ M, IsIsolatedVertex H' z) :
    ∃ H₂ : Drawing S', H₂.U = H'.U \ M ∧ H₂.V = H'.V \ M ∧ H₂.E = H'.E ∧ IsSurfaceForest H₂ := by
  have hoff : ∀ e ∈ H'.E, Disjoint (tilde e) M := by
    intro e he
    rw [disjoint_left]
    intro z hz hzM
    exact (hM z hzM).2 e he (((GraphMinor.GM07.vertexIncident_iff_mem_tilde H'
      (hM z hzM).1 he)).mpr hz)
  have hoff' : ∀ e ∈ H'.E, Disjoint (closure e) M := by
    intro e he
    rw [disjoint_left]
    intro z hz hzM
    exact (hM z hzM).2 e he ⟨(hM z hzM).1, .inl he, hz⟩
  let H₂ := GM19.delete H' M
  have hE : H₂.E = H'.E := by
    rw [GM19.delete_E]
    ext e
    exact ⟨fun h => h.1, fun h => ⟨h, hoff e h⟩⟩
  have hV : H₂.V = H'.V \ M := GM19.delete_V H' M
  have hU : H₂.U = H'.U \ M := by
    apply Subset.antisymm
    · rw [GM19.delete_U]
      rintro x (hx | hx)
      · exact ⟨H'.V_subset_U hx.1, hx.2⟩
      · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
        exact ⟨H'.closure_subset_U he.1 hxe, fun h => disjoint_left.mp (hoff' e he.1) hxe h⟩
    · rintro x ⟨hxU, hxM⟩
      rcases (mem_U_iff_edge H').mp hxU with h | ⟨e, he, hxe⟩
      · exact H₂.V_subset_U (hV ▸ ⟨h, hxM⟩)
      · have : e ∈ H₂.E := hE ▸ he
        exact (this.2.1 hxe).1
  refine ⟨H₂, hU, hV, hE, ?_, IsGraphForest.of_subdrawing hH'.2 (GM19.delete_subdrawing H' M)⟩
  rintro x ⟨hb, hx⟩
  rw [hU] at hx
  rw [hV]
  exact ⟨hH'.1 ⟨hb, hx.1⟩, hx.2⟩

private theorem mapDrawing_E {X : Type} [TopologicalSpace X] (α : X ≃ₜ X) (H : Drawing X) :
    (mapDrawingHomeo α H).E = image α '' H.E := by
  change arcComponentsIn (α '' H.U \ α '' H.V) = _
  rw [← image_sdiff α.injective]
  exact arcComponentsIn_image_homeo α _

private theorem homotopic_refl {X : Type} [TopologicalSpace X] (hX : IsSurface X) {H : Drawing X}
    (hH : IsSurfaceForest H) : ForestsHomotopic H H := by
  have : T2Space X := hX.2.1
  have : CompactSpace X := hX.1
  refine ForestsHomotopic.refl hH fun s _ t _ _ P₁ P₂ φ₁ φ₂ _ _ h₁ h₂ => ?_
  have e₁ := h₁.endpoints
  have e₂ := h₂.endpoints
  exact IsFlat.curvesHomotopic (isFlat_forest hH.2) h₁.range_subset_U h₂.range_subset_U
    (e₁.1.trans e₂.1.symm) (e₁.2.trans e₂.2.symm)

private theorem homoplastic_of_homotopic {X : Type} [TopologicalSpace X] {H₁ H₂ : Drawing X}
    (h : ForestsHomotopic H₁ H₂) : ForestsHomoplastic H₁ H₂ := by
  refine ⟨Homeomorph.refl X, fun _ _ => rfl, ?_⟩
  have : mapDrawingHomeo (Homeomorph.refl X) H₁ = H₁ := drawing_eq (image_id _) (image_id _)
  rw [this]
  exact h

private theorem map_matches_after_isolated_deletion
    {S' : Type}
    [TopologicalSpace S']
    (Hp : Drawing S') :
    ∀ (P : Set S'),
    ∀ (M₁ : Set S'),
    let M₂ : Set S' := P \ M₁
    (P ⊆ bd S') →
    (∀ z ∈ M₂, IsIsolatedVertex Hp z) →
    ∀ (H₂ : Drawing S'),
    (H₂.U = Hp.U \ M₂) →
    (H₂.V = Hp.V \ M₂) →
    (H₂.E = Hp.E) →
    ∀ (α : S' ≃ₜ S'),
    (∀ x ∈ bd S', α x = x) →
    (⇑α '' M₂ = M₂) →
    (∀ e ∈ Hp.E, Disjoint (closure e) M₂) →
    IsMatched (mapDrawingHomeo α Hp) (mapDrawingHomeo α H₂) id M₂ := by
  intro P M₁ M₂ hPbd hM₂iso H₂ h2U h2V h2E α hα hαM hoffp
  refine isMatched_id ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact ⟨x, (hM₂iso x hx).1, hα x (hPbd hx.1)⟩
  · intro e he
    rw [mapDrawing_E] at he
    obtain ⟨e₀, he₀, rfl⟩ := he
    rw [← α.image_closure, disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ hz
    have hyM : y ∈ M₂ := by
      have := hα (α y) (hPbd hz.1)
      have heq : α y = y := α.injective this
      rwa [heq] at hz
    exact disjoint_left.mp (hoffp e₀ he₀) hy hyM
  · change α '' Hp.U \ M₂ = α '' H₂.U
    nth_rewrite 1 [← hαM]
    rw [← image_sdiff α.injective, h2U]
  · change α '' Hp.V \ M₂ = α '' H₂.V
    nth_rewrite 1 [← hαM]
    rw [← image_sdiff α.injective, h2V]
  · rw [mapDrawing_E, mapDrawing_E, h2E]

private theorem pushforward_forest_is_saturated
    {S : Type}
    {S' : Type}
    [TopologicalSpace S]
    [TopologicalSpace S']
    {L : Drawing S}
    {G : Drawing S}
    {θ : S' → S}
    (hθ : IsCutAlongGraph L S' θ)
    (P : Set S') (hP : P = θ ⁻¹' (G.V ∩ bd S))
    (H₄ : Drawing S')
    (hp₄ : H₄.IsProper)
    (h4bd : H₄.V ∩ bd S' = P)
    (H₅ : Drawing S)
    (himg : IsImageDrawing θ H₄ H₅) :
    θ ⁻¹' H₅.U = H₄.U := by
  apply Subset.antisymm
  · intro y hy
    have hy' : θ y ∈ θ '' H₄.U := himg.1 ▸ hy
    obtain ⟨x, hx, hxy⟩ := hy'
    by_cases hxb : x ∈ bd S'
    · have hxP : x ∈ P := h4bd ▸ ⟨hp₄ ⟨hxb, hx⟩, hxb⟩
      have hyP : y ∈ P := by
        rw [hP] at hxP ⊢
        change θ y ∈ G.V ∩ bd S
        rw [← hxy]
        exact hxP
      exact H₄.V_subset_U (h4bd.symm.subset hyP).1
    · rw [← hθ.interior_inj x hxb y hxy]
      exact hx
  · intro y hy
    change θ y ∈ H₅.U
    rw [himg.1]
    exact mem_image_of_mem θ hy

private theorem refined_forest_meets_cut_only_at_graph_vertices
    {S : Type}
    {S' : Type}
    [TopologicalSpace S]
    [TopologicalSpace S']
    {L : Drawing S}
    {K : Drawing S}
    {G : Drawing S}
    {K' : Drawing S'}
    {θ : S' → S}
    (hK'p : IsPullbackDrawing θ K K')
    (M₂ : Set S')
    (H₃₀ : Drawing S')
    (β : S' ≃ₜ S')
    (hβG : ∀ x ∈ K'.U ∩ H₃₀.U, β x ∈ θ ⁻¹' G.V)
    (H₃ : Drawing S')
    (hKH : H₃.U ∩ K'.U ⊆ ⇑β '' (K'.U ∩ H₃₀.U))
    (H₄ : Drawing S') (h4U : H₄.U = H₃.U ∪ M₂) (hM₂ : M₂ ⊆ θ ⁻¹' G.V)
    (H₅ : Drawing S)
    (himg : IsImageDrawing θ H₄ H₅)
    (H₆ : Drawing S)
    (h6U : H₆.U = H₅.U ∪ G.V)
    (hG₄ : ∀ y ∈ H₄.U, θ y ∈ bd S ∪ L.U → θ y ∈ G.V ∩ bd S) :
    H₆.U ∩ (bd S ∪ L.U ∪ K.U) ⊆ G.V := by
  rintro x ⟨hx, hxJ⟩
  rw [h6U] at hx
  rcases hx with hx | hx
  · rw [himg.1] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rcases hxJ with hxJ | hxK
    · exact (hG₄ y hy hxJ).1
    · have hyK : y ∈ K'.U := hK'p.1 ▸ hxK
      rw [h4U] at hy
      rcases hy with hy | hy
      · obtain ⟨z, ⟨hz₁, hz₂⟩, hz⟩ := hKH ⟨hy, hyK⟩
        have := hβG z ⟨hz₁, hz₂⟩
        rw [hz] at this
        exact this
      · exact hM₂ hy
  · exact hx

/-- Claim (1) of VII (4.6), page 227, with the set `T = U(H₃)`, which contains the closure of each
edge of `θ⁻¹(H₆)`. -/
theorem exists_claim_one [T1Space S] [ConnectedSpace S] (hS : IsSurface S)
    {L K G H : Drawing S} {K' : Drawing S'} {θ : S' → S} (hθ : IsCutAlongGraph L S' θ)
    (hNo : NoArcs L) (hH : IsSurfaceForest H) (hbd : G.V ∩ bd S = H.V ∩ bd S) {k n w : ℕ}
    (hcard : (G.V ∩ bd S).ncard ≤ 2 * k) (l' : S → S')
    (hl : ∀ z ∈ G.V ∩ bd S, θ (l' z) = z) (hK'p : IsPullbackDrawing θ K K')
    (hK'm : IsMatching K') (hK'c : K'.V.ncard ≤ 2 * n) (hw : IsW36Bound S' (2 * k) n w)
    (hslide : ∀ X : Set S', X.Finite → X ⊆ K'.U → X.ncard ≤ w →
      ∃ β : S' ≃ₜ S', (∀ x ∈ bd S', β x = x) ∧ K'.U ⊆ β '' K'.U ∧ ∀ x ∈ X, β x ∈ θ ⁻¹' G.V) :
    ∃ (H₆ : Drawing S) (H₆' : Drawing S') (T : Set S'), IsSurfaceForest H₆ ∧
      ForestsHomoplastic H H₆ ∧ IsPullbackDrawing θ H₆ H₆' ∧ IsSurfaceForest H₆' ∧
      (∀ e' ∈ H₆'.E, ∃ e ∈ H₆.E, e' = θ ⁻¹' e ∧ θ '' closure e' = closure e ∧ InjOn θ (closure e'))
        ∧
      H₆.U ∩ (bd S ∪ L.U ∪ K.U) ⊆ G.V ∧ G.V ⊆ H₆.V ∧ IsClosed T ∧ (∀ e' ∈ H₆'.E, closure e' ⊆ T) ∧
      (T ∩ K'.U).Finite ∧ (T ∩ K'.U).ncard ≤ w ∧ ∀ z ∈ T ∩ bd S', z ∈ l' '' (G.V ∩ bd S) := by
  classical
  have : T2Space S := hS.2.1
  have hS' := hθ.isSurface
  have : T2Space S' := hS'.2.1
  have : CompactSpace S' := hS'.1
  have hs := hθ.quotientMap.surjective
  have : Nonempty S' := by
    obtain ⟨x⟩ : Nonempty S := inferInstance
    exact ⟨(hs x).choose⟩
  obtain ⟨H₁, H', hH₁, hhom₁, hH₁L, hpull, hiso⟩ := theorem_4_4_proof hS L θ hθ
    (fun F hF => ⟨hNo.1 F hF, hNo.2 F hF⟩) H l' hH (fun z hz => hl z (hbd ▸ hz))
  have hnorm₁ : H₁.IsNormal L.U := fun x hx => hH₁.1 ⟨hH₁L ⟨hx.2, hx.1⟩, hx.2⟩
  obtain ⟨Hp, hpp, hHpf, hpush⟩ := theorem_4_5_proof hS L H₁ θ hθ hH₁ hnorm₁
  have hHeq : Hp = H' := drawing_eq (hpp.1.trans hpull.1.symm) (hpp.2.trans hpull.2.symm)
  subst hHeq
  have hbdsub : ∀ x, θ x ∈ bd S → x ∈ bd S' := fun x hx => by
    rw [← hθ.preimage_bd_union_U]
    exact .inl hx
  have hbdL : ∀ x, x ∈ bd S' → θ x ∈ bd S ∨ θ x ∈ L.U := fun x hx => by
    rw [← hθ.preimage_bd_union_U] at hx
    exact hx
  let P : Set S' := θ ⁻¹' (G.V ∩ bd S)
  let M₁ : Set S' := l' '' (G.V ∩ bd S)
  let M₂ : Set S' := P \ M₁
  have hG₁ : H₁.V ∩ bd S = G.V ∩ bd S := hhom₁.2.2.2.2.1.trans hbd.symm
  have hPV : Hp.V ∩ bd S' = P := by
    ext x
    constructor
    · rintro ⟨hxV, hxb⟩
      rw [hpull.2] at hxV
      have hxb' : θ x ∈ bd S := by
        rcases hbdL x hxb with h | h
        · exact h
        · exact hH₁L ⟨H₁.V_subset_U hxV, h⟩
      change θ x ∈ G.V ∩ bd S
      rw [← hG₁]
      exact ⟨hxV, hxb'⟩
    · intro hx
      have hx' : θ x ∈ H₁.V ∩ bd S := hG₁ ▸ hx
      exact ⟨by rw [hpull.2]; exact hx'.1, hbdsub x hx'.2⟩
  have hM₁P : M₁ ⊆ P := by
    rintro _ ⟨z, hz, rfl⟩
    change θ (l' z) ∈ G.V ∩ bd S
    rw [hl z hz]
    exact hz
  have hPbd : P ⊆ bd S' := fun x hx => hbdsub x hx.2
  have hPf : P.Finite := Set.Finite.preimage' (G.finite_V.subset inter_subset_left)
    fun b _ => hθ.finite_fiber b
  have hMf : M₂.Finite := hPf.subset sdiff_subset
  have hM₂iso : ∀ z ∈ M₂, IsIsolatedVertex Hp z := by
    rintro z ⟨hzP, hzM⟩
    have hmem : θ z ∈ H.V ∩ bd S := hbd ▸ hzP
    exact hiso (θ z) hmem z ⟨rfl, fun h => hzM ⟨θ z, hzP, (show z = l' (θ z) from h).symm⟩⟩
  obtain ⟨H₂, h2U, h2V, h2E, hF₂⟩ := exists_delete_isolated hHpf hM₂iso
  have h2bd : H₂.V ∩ bd S' = M₁ := by
    rw [h2V]
    ext x
    constructor
    · rintro ⟨⟨hxV, hxM⟩, hxb⟩
      have hxP : x ∈ P := hPV ▸ ⟨hxV, hxb⟩
      by_contra hn
      exact hxM ⟨hxP, hn⟩
    · intro hx
      have hxP := hM₁P hx
      have h' : x ∈ Hp.V ∩ bd S' := hPV ▸ hxP
      exact ⟨⟨h'.1, fun h => h.2 hx⟩, h'.2⟩
  have hM₁f : (G.V ∩ bd S).Finite := G.finite_V.subset inter_subset_left
  have hM₁c : M₁.ncard ≤ 2 * k := (ncard_image_le hM₁f).trans hcard
  obtain ⟨H₃₀, hF₃₀, hH₃₀, hfin, hle⟩ := hw K' H₂ hK'm hK'c hF₂ (by rw [h2bd]; exact hM₁c)
  obtain ⟨β, hβbd, hβK, hβG⟩ := hslide _ hfin inter_subset_left hle
  let H₃ := mapDrawingHomeo β H₃₀
  have hmap := ForestsHomotopic.map_homeo β (homotopic_refl hS' hF₃₀)
  have hF₃ : IsSurfaceForest H₃ := ⟨hmap.1, hmap.2.2.1⟩
  have hhom₂₃ : ForestsHomoplastic H₂ H₃ := hH₃₀.trans ⟨β, hβbd, hmap⟩
  have hKH : H₃.U ∩ K'.U ⊆ β '' (K'.U ∩ H₃₀.U) := by
    rintro y ⟨⟨z, hz, rfl⟩, hyK⟩
    obtain ⟨z', hz', hzz⟩ := hβK hyK
    have heq : z' = z := β.injective hzz
    exact ⟨z, ⟨heq ▸ hz', hz⟩, rfl⟩
  have h3bd : H₃.V ∩ bd S' = M₁ := (bd_inter_V_eq_of_homoplastic hhom₂₃).symm.trans h2bd
  have hdis : Disjoint M₂ H₃.U := by
    rw [disjoint_left]
    intro x hx hxU
    have hxb := hPbd hx.1
    have : x ∈ M₁ := h3bd ▸ ⟨hF₃.1 ⟨hxb, hxU⟩, hxb⟩
    exact hx.2 this
  let H₄ := addIsolated H₃ M₂ hMf hdis
  have hsdiffU : (H₃.U ∪ M₂) \ M₂ = H₃.U := by
    rw [union_sdiff_right, sdiff_eq_left.mpr hdis.symm]
  have hsdiffV : (H₃.V ∪ M₂) \ M₂ = H₃.V := by
    rw [union_sdiff_right, sdiff_eq_left.mpr (hdis.symm.mono_left H₃.V_subset_U)]
  have h4E : H₄.E = H₃.E := by
    change arcComponentsIn _ = arcComponentsIn _
    congr 1
    ext x
    simp only [H₄, addIsolated, mem_sdiff, mem_union, not_or]
    constructor
    · rintro ⟨h1 | h1, h2, h3⟩
      · exact ⟨h1, h2⟩
      · exact absurd h1 h3
    · rintro ⟨h1, h2⟩
      exact ⟨.inl h1, h2, fun h3 => disjoint_left.mp hdis h3 h1⟩
  have m₂ : IsMatched H₄ H₃ id M₂ := isMatched_id (fun x hx => Or.inr hx)
    (fun e he => (hdis.symm.mono_left (H₃.closure_subset_U (h4E ▸ he)))) hsdiffU hsdiffV h4E.symm
  have hp₄ : H₄.IsProper := by
    rintro x ⟨hb, hx | hx⟩
    · exact .inl (hF₃.1 ⟨hb, hx⟩)
    · exact .inr hx
  have hF₄ : IsSurfaceForest H₄ := ⟨hp₄, m₂.isGraphForest_iff.mpr hF₃.2⟩
  have h4bd : H₄.V ∩ bd S' = P := by
    ext x
    constructor
    · rintro ⟨hx | hx, hb⟩
      · have : x ∈ M₁ := h3bd ▸ ⟨hx, hb⟩
        exact hM₁P this
      · exact hx.1
    · intro hx
      refine ⟨?_, hPbd hx⟩
      by_cases hm : x ∈ M₁
      · exact .inl (h3bd.symm.subset hm).1
      · exact .inr ⟨hx, hm⟩
  obtain ⟨α, hα, hhomα⟩ := hhom₂₃
  have hαM : α '' M₂ = M₂ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hα y (hPbd hy.1)]
      exact hy
    · intro hx
      exact ⟨x, hx, hα x (hPbd hx.1)⟩
  have hoffp : ∀ e ∈ Hp.E, Disjoint (closure e) M₂ := by
    intro e he
    rw [disjoint_left]
    intro z hz hzM
    exact (hM₂iso z hzM).2 e he ⟨(hM₂iso z hzM).1, .inl he, hz⟩
  have m₁ : IsMatched (mapDrawingHomeo α Hp) (mapDrawingHomeo α H₂) id M₂ := by
    exact map_matches_after_isolated_deletion (S' := S') Hp P M₁ hPbd hM₂iso H₂ h2U h2V h2E α
      hα hαM hoffp
  have hmap' := ForestsHomotopic.map_homeo α (homotopic_refl hS' hHpf)
  have hbdα : (mapDrawingHomeo α Hp).V ∩ bd S' = H₄.V ∩ bd S' := by
    rw [h4bd]
    ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hb⟩
      have hy' : y ∈ bd S' := by
        rw [← image_bd_homeomorph α] at hb
        obtain ⟨y', hy', hyy⟩ := hb
        rwa [← α.injective hyy]
      rw [hα y hy']
      exact hPV ▸ ⟨hy, hy'⟩
    · intro hx
      have h' : x ∈ Hp.V ∩ bd S' := hPV ▸ hx
      exact ⟨⟨x, h'.1, hα x h'.2⟩, h'.2⟩
  have hhom₄ : ForestsHomoplastic Hp H₄ :=
    ⟨α, hα, ForestsHomotopic.of_matched_id m₁ m₂ hhomα hmap'.1 hp₄ hbdα⟩
  obtain ⟨H₅, himg, hF₅, hhom₅⟩ := hpush H₄ hF₄ hhom₄.symm
  have hH₅H : ForestsHomoplastic H H₅ :=
    (hhom₅.trans (homoplastic_of_homotopic hhom₁)).symm
  have h5bd : H₅.V ∩ bd S = G.V ∩ bd S := (bd_inter_V_eq_of_homoplastic hH₅H).symm.trans hbd.symm
  obtain ⟨H₆, h6U, h6V, hF₆, hhom₆, -⟩ := exists_refined_forest hS hF₅ G.finite_V
    (fun x hx => (h5bd.symm.subset hx).1)
  have hsat : θ ⁻¹' H₅.U = H₄.U := by
    exact pushforward_forest_is_saturated (S := S) (S' := S') (L := L) (G := G) (θ := θ) hθ P rfl H₄
      hp₄ h4bd H₅ himg
  have hG₄ : ∀ y ∈ H₄.U, θ y ∈ bd S ∪ L.U → θ y ∈ G.V ∩ bd S := by
    intro y hy hb
    have hyb : y ∈ bd S' := by
      rw [← hθ.preimage_bd_union_U]
      exact hb
    exact (h4bd.subset ⟨hp₄ ⟨hyb, hy⟩, hyb⟩ : y ∈ P)
  have hmain : H₆.U ∩ (bd S ∪ L.U ∪ K.U) ⊆ G.V := by
    exact refined_forest_meets_cut_only_at_graph_vertices (S := S) (S' := S') (L := L) (K := K) (G
      := G) (K' := K') (θ := θ) hK'p M₂ H₃₀ β hβG H₃ hKH H₄ rfl
      (fun _ hx => hx.1.1) H₅ himg H₆ h6U hG₄
  have hGV : G.V ⊆ H₆.V := h6V ▸ subset_union_right
  have hnorm₆ : H₆.IsNormal L.U := fun x hx => hGV (hmain ⟨hx.2, .inl (.inr hx.1)⟩)
  obtain ⟨H₆', hp₆, hprop₆, hE₆⟩ := exists_pullback hS hθ hF₆ hnorm₆
  refine ⟨H₆, H₆', H₃.U, hF₆, hH₅H.trans (homoplastic_of_homotopic hhom₆), hp₆,
    ⟨hprop₆, isGraphForest_pullback hs hF₆.2 hp₆.2 hE₆⟩,
    hE₆, hmain, hGV, H₃.isClosed_U, ?_, ?_, ?_, ?_⟩
  · intro e' he'
    apply closure_minimal _ H₃.isClosed_U
    intro y hy
    have hy' := he'.2.1 hy
    rw [hp₆.1, hp₆.2] at hy'
    have hyU : θ y ∈ H₅.U ∨ θ y ∈ G.V := by
      have := hy'.1
      rw [mem_preimage, h6U] at this
      exact this
    have hnG : θ y ∉ G.V := fun h => hy'.2 (hGV h)
    rcases (hsat ▸ hyU.resolve_right hnG : y ∈ H₄.U) with h | h
    · exact h
    · exact (hnG h.1.1).elim
  · exact (hfin.image β).subset hKH
  · calc (H₃.U ∩ K'.U).ncard ≤ (β '' (K'.U ∩ H₃₀.U)).ncard := ncard_le_ncard hKH (hfin.image β)
      _ ≤ _ := ncard_image_le hfin
      _ ≤ w := hle
  · rintro z ⟨hz, hzb⟩
    exact h3bd.subset ⟨hF₃.1 ⟨hzb, hz⟩, hzb⟩

end GraphMinor.GM07
