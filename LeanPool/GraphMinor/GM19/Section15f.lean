/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section15e
public import LeanPool.GraphMinor.GM19.Section15c
public import LeanPool.GraphMinor.GM19.Section8e

/-!
# Graph Minors XIX: the small side of a separation in `𝒯`

This file proves the part of (6.3) of Graph Minors XI that the proof of (15.2) needs, for a tangle
in a painting in `Σ̂`. The
painting is not a drawing or a painting in the sense of XI, so we repeat the proof, with the drawing
`G₃` of Section 8 in place of
the radial drawing. If `(A, B) ∈ 𝒯` has small order, then the edges of `A` lie in the insides of
short circuits of `Γ*` whose
vertices in `Γ` lie in `V(A ∩ B)`. The result used later is `TangleDatum.exists_inside_cover`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 Hypergraph

universe w

/-- For a separation `(A, B)` of small order, the pair `(A ∩ B, G)` lies in a pretangle `𝒯`, since
`(G, A ∩ B)` would break the
second tangle axiom. -/
theorem mem_pretangle_inter {α β : Type*} {G : Hypergraph α β} {θ : ℕ} {T : Set
  (Hypergraph α β × Hypergraph α β)} (hT : IsPretangle G θ T) {A B : Hypergraph α β}
    (hsep : G.IsSeparation A B)
    (hord : separationOrder A B < θ) : (A ∩ B, G) ∈ T := by
  have hinf : (A ∩ B) ≤ G := by
    refine le_trans ?_ hsep.left_le
    refine ⟨inter_subset_left, inter_subset_left, fun e he => ?_⟩
    have h₀ : (A ∩ B).edgeSet = ∅ := hsep.edgeSet_inter_eq
    rw [h₀] at he
    exact absurd he (notMem_empty e)
  have hE₀ : (A ∩ B).edgeSet = ∅ := hsep.edgeSet_inter_eq
  have hsep₀ : G.IsSeparation (A ∩ B) G := by
    refine ⟨hinf, le_rfl, ?_, ?_⟩
    · exact le_antisymm (by
        refine ⟨union_subset hinf.vertexSet_subset subset_rfl,
          union_subset hinf.edgeSet_subset subset_rfl, fun e he => ?_⟩
        rcases he with he | he
        · rw [hE₀] at he
          exact absurd he (notMem_empty e)
        · ext v
          constructor
          · exact fun h => Or.inr h
          · rintro (h | h)
            · exact absurd ((A ∩ B).edge_mem_of_inc h) (by rw [hE₀]; exact notMem_empty e)
            · exact h)
        (Hypergraph.IsSubhypergraph.mk subset_union_right subset_union_right fun e he => by
          ext v
          constructor
          · rintro (h | h)
            · exact absurd ((A ∩ B).edge_mem_of_inc h) (by rw [hE₀]; exact notMem_empty e)
            · exact h
          · exact fun h => Or.inr h)
    · have : ((A ∩ B) ∩ G).edgeSet ⊆ ∅ := fun e he => hE₀ ▸ he.1
      exact subset_empty_iff.mp this
  have hord₀ : separationOrder (A ∩ B) G < θ := by
    refine lt_of_le_of_lt (ncard_le_ncard inter_subset_left (A ∩ B).vertexSet_finite) hord
  rcases hT.axiom1 hsep₀ hord₀ with h | h
  · exact h
  · have heq : G ∪ G ∪ G = G := by
      rw [GM10.union_self, GM10.union_self]
    exact absurd heq (hT.axiom2 h h h)

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}

namespace TangleDatum

private theorem boundary_vertex_in_both_sides
    {S : Type}
    {Shat : Type}
    [TopologicalSpace S]
    [TopologicalSpace Shat]
    {cap : IsCappedSurface S Shat}
    {β : Type w}
    {χ : ColourScheme S β}
    (D : TangleDatum cap χ)
    {A : Hypergraph S (Set S)}
    {B : Hypergraph S (Set S)} :
    let Γ : Painting S := D.P.Γ
    ∀ (rad : RadialDrawing cap D.P.Γ),
    ∀ (G₃ : Drawing Shat),
    (Drawing.IsSubdrawing rad.G G₃) →
    (Γ.toHypergraph.IsSeparation A B) →
    let t : Set S → Prop := fun x ↦ x ∈ A.edgeSet
    ∀ (N₀ : Drawing Shat),
    (∀ {e : Set Shat}, e ∈ Drawing.E N₀ → e ∈ Drawing.E rad.G ∧ ∃ v₀ w, v₀ ∈ D.P.Γ.V ∧ w ∈
      rad.Rstar ∧ closure e ∩ G₃.V = {cap.emb v₀, w} ∧ ∃ f₁ f₂ c₁ c₂, rad.PairOf e c₁ c₂ ∧
      D.P.Γ.IsSkEdgeIn f₁ c₁ ∧ D.P.Γ.IsSkEdgeIn f₂ c₂ ∧ v₀ ∈ tilde f₁ ∧ v₀ ∈ tilde f₂ ∧ ¬(t c₁ ↔ t
      c₂)) →
    ∀ (N : Drawing Shat),
    (Drawing.IsSubdrawing N rad.G) →
    (∀ x ∈ N.V, ∃ e ∈ Drawing.E N₀, x ∈ closure e) →
    (∀ {X : Hypergraph S (Set S)}, X ≤ Γ.toHypergraph → ∀ {c : Set S} {v : S}, c ∈
      X.edgeSet → v ∈ Γ.V → v ∈ tilde c → v ∈ X.vertexSet) →
    ∀ v ∈ Γ.V, cap.emb v ∈ N.V → v ∈ (A ∩ B).vertexSet := by
  intro Γ rad G₃ hsub hAB t N₀ hbs N hN hNV hincX v hv hvN
  obtain ⟨g, hg, hxg⟩ := hNV _ hvN
  have hG₃V : cap.emb v ∈ G₃.V := hsub.1 (hN.1 hvN)
  obtain ⟨-, v₀, w, hv₀, hw, hset, f₁, f₂, c₁, c₂, hp, h₁, h₂, ht₁, ht₂, hnt⟩ := hbs hg
  have hxg' : cap.emb v ∈ closure g ∩ G₃.V := ⟨hxg, hG₃V⟩
  rw [hset] at hxg'
  obtain rfl : v = v₀ := by
    rcases hxg' with h | h
    · exact cap.isEmbedding.injective h
    · exact absurd (show w ∈ Γ.hatV cap from h ▸ mem_image_of_mem _ hv) hw.2
  have hc₁ : v ∈ tilde c₁ := ⟨closure_mono h₁.subset ht₁.1, fun h ↦ Γ.disjoint_V h₁.1 h hv₀⟩
  have hc₂ : v ∈ tilde c₂ := ⟨closure_mono h₂.subset ht₂.1, fun h ↦ Γ.disjoint_V h₂.1 h hv₀⟩
  have e₁ := edge_cases hAB h₁.1
  have e₂ := edge_cases hAB h₂.1
  have hnt' : ¬ (c₁ ∈ A.edgeSet ↔ c₂ ∈ A.edgeSet) := hnt
  by_cases ha₁ : c₁ ∈ A.edgeSet
  · have hb₂ : c₂ ∈ B.edgeSet := by tauto
    exact ⟨hincX hAB.left_le ha₁ hv₀ hc₁, hincX hAB.right_le hb₂ hv₀ hc₂⟩
  · have hb₁ : c₁ ∈ B.edgeSet := by tauto
    have ha₂ : c₂ ∈ A.edgeSet := by tauto
    exact ⟨hincX hAB.left_le ha₂ hv₀ hc₂, hincX hAB.right_le hb₁ hv₀ hc₁⟩

/-- **The small side of a separation in `𝒯`.** -/
theorem exists_inside_cover (D : TangleDatum cap χ) {A B : Hypergraph S (Set S)} (hmem :
  (A, B) ∈ D.𝒯) (hord : separationOrder A B < D.rep) :
    ∃ N : Drawing Shat, N.IsSubdrawing D.rad.G ∧ (∀ C : Drawing Shat, C.IsCircuit
      → C.IsSubdrawing N → C.E.ncard < 2 * D.rep) ∧ (∀ v ∈ D.P.Γ.V, cap.emb v ∈ N.V → v ∈
        (A ∩ B).vertexSet) ∧
      ∀ e ∈ A.edgeSet, ∃ F : Drawing Shat, F.IsCircuit ∧ F.IsSubdrawing N ∧ cap.emb '' e ⊆ D.ins F
        := by
  classical
  have hS := χ.isSurface
  have h3 := D.P.fits.internally_three_connected
  set Γ := D.P.Γ with hΓ
  set rad := D.rad with hradDef
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hlc : LocallyConnectedSpace Shat := IsClosedSurface.locallyConnectedSpace hT
  have h2 := h3.hatRegions_isOpenDisc hS cap
  obtain ⟨H, G₃, hH, hrad, hmax, hsub, hhat⟩ := rad.exists_full hS h2 h3.1
  have hHE := hH.E_nonempty h3.1
  have hAB : Γ.toHypergraph.IsSeparation A B := D.isTangle.isSeparation hmem
  let t : Set S → Prop := (· ∈ A.edgeSet)
  let Z : Set (Set Shat) := colourSet cap Γ G₃ t
  have hZ : Z ⊆ G₃.R := fun _ h ↦ h.1
  let N₀ : Drawing Shat := boundaryDrawing G₃ Z
  have hbs : ∀ {e}, e ∈ N₀.E → _ := fun {e} he ↦ boundary_split hS hHE rad hH hrad hmax hsub hhat
    (t := t) (e := e) he
  let N : Drawing Shat := rad.G.span ∅ N₀.E
  have hN : N.IsSubdrawing rad.G := Drawing.span_isSubdrawing _ _ _
  have hNE : ∀ {e}, e ∈ N.E ↔ e ∈ N₀.E := fun {e} ↦ by
    change e ∈ (rad.G.span _ _).E ↔ _
    rw [rad.G.span_E]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, (hbs h).1⟩⟩
  have hNV : ∀ x ∈ N.V, ∃ e ∈ N₀.E, x ∈ closure e := by
    rintro x (hx | hx)
    · exact absurd hx.1 (notMem_empty x)
    · obtain ⟨e, ⟨he, -⟩, hxe⟩ := mem_iUnion₂.mp hx
      exact ⟨e, he, hxe.1⟩
  have hincX : ∀ {X : Hypergraph S (Set S)}, X ≤ Γ.toHypergraph → ∀ {c v}, c ∈ X.edgeSet → v ∈ Γ.V
    → v ∈ tilde c → v ∈ X.vertexSet := by
    intro X hX c v hc hv hvc
    have h₁ : v ∈ Γ.toHypergraph.ends c := ⟨hX.edgeSet_subset hc, hv, hvc⟩
    rw [hX.ends_eq c hc] at h₁
    exact X.vertex_mem_of_inc h₁
  have hmid : ∀ v ∈ Γ.V, cap.emb v ∈ N.V → v ∈ (A ∩ B).vertexSet := by
    exact boundary_vertex_in_both_sides (S := S) (Shat := Shat) (cap := cap) (β := β) (χ := χ) D
      (A := A) (B := B) rad G₃ hsub hAB N₀ hbs N hN hNV hincX
  have hshort : ∀ C : Drawing Shat, C.IsCircuit → C.IsSubdrawing N → C.E.ncard < 2 * D.rep := by
    intro C hC hCs
    have hCG₃ := (hCs.trans hN).trans hsub
    have hb := IsCircuit.ncard_le hC (P := H.V) fun e x y hl ↦ bipartite_of_preRadial hrad.2 e x y
      ((hCG₃.isLink_iff hl.1).mp hl)
    have hsubs : C.V ∩ H.V ⊆ cap.emb '' (A ∩ B).vertexSet := by
      rintro x ⟨hx, hxH⟩
      rw [hH.hV] at hxH
      obtain ⟨v, hv, rfl⟩ := hxH
      exact mem_image_of_mem _ (hmid v hv (hCs.1 hx))
    have hle₁ := ncard_le_ncard hsubs ((A ∩ B).vertexSet_finite.image _)
    have hle₂ := ncard_image_le (f := cap.emb) (A ∩ B).vertexSet_finite
    have : (C.V ∩ H.V).ncard ≤ separationOrder A B := hle₁.trans hle₂
    omega
  have hsl := D.isSlope (by omega)
  have hr₀ := GM11.theorem_4_4_proof hT hsl hN hshort
  set r₀ := univ \ insOf D.ins N with hr₀def
  have hopen : IsOpen r₀ := region_isOpen hr₀
  have hprec : IsPreconnected r₀ := region_isPreconnected hr₀
  have hno : ∀ s₁ ∈ Z, ∀ s₂ ∈ G₃.R \ Z, (s₁ ∩ r₀).Nonempty → (s₂ ∩ r₀).Nonempty → False := by
    intro s₁ h₁ s₂ h₂ m₁ m₂
    obtain ⟨e, he, y, hye, hyi⟩ := exists_boundary_edge hT hopen hprec h₁ hZ h₂ m₁ m₂
    have hyU : y ∈ N.U := (hNE.mpr he |> fun h ↦ (h.2.1 hye).1)
    exact hyi.2 (Or.inl hyU)
  have hreg : ∀ f, f ∈ arcComponentsIn (Γ.skU \ Γ.V) → ∃ s ∈ G₃.R, cap.emb '' f ⊆ s := by
    intro f hf
    have hg := hH.edge_iff.mpr ⟨f, hf, rfl⟩
    have hdis : Disjoint (cap.emb '' f) G₃.U := by
      refine disjoint_left.mpr fun y hy hyU ↦ ?_
      have hyD := hg.2.1 hy
      have : y ∈ H.U ∩ G₃.U := ⟨hyD.1, hyU⟩
      rw [show H.U ∩ G₃.U = H.V from hrad.2.1] at this
      exact hyD.2 this
    obtain ⟨y, hy⟩ := hg.1
    obtain ⟨s, hs, hys⟩ := exists_region_of_notMem (disjoint_left.mp hdis hy)
    exact ⟨s, hs, subset_region hs hg.2.2.1.isConnected.isPreconnected hdis hy hys⟩
  have hcol : ∀ {f c s}, Γ.IsSkEdgeIn f c → s ∈ G₃.R → cap.emb '' f ⊆ s → (s ∈ Z ↔ c ∈ A.edgeSet)
    := by
    intro f c s hfc hs hfs
    constructor
    · rintro ⟨-, f', c', h', hf', ht⟩
      rw [(colour_unique hH hrad hmax hHE hs hfc h' hfs hf').2]
      exact ht
    · exact fun h ↦ ⟨hs, f, c, hfc, hfs, h⟩
  have hcov : ∀ c ∈ Γ.E, (∀ f, Γ.IsSkEdgeIn f c → ∀ s ∈ G₃.R, cap.emb '' f ⊆ s → Disjoint s r₀)
    → ∃ C : Drawing Shat, C.IsCircuit ∧ C.IsSubdrawing N ∧ cap.emb '' c ⊆ D.ins C := by
    intro c hc hall
    obtain ⟨f, hf⟩ := Γ.exists_sk_in hc
    obtain ⟨s, hs, hfs⟩ := hreg f hf.mem
    obtain ⟨x, hx⟩ := hf.mem.1
    have hxs := hfs (mem_image_of_mem _ hx)
    have hdis : ∀ y ∈ c, cap.emb y ∉ rad.G.U := fun y hy hyG ↦ by
      have : cap.emb y ∈ Γ.hatU cap ∩ rad.G.U := ⟨mem_image_of_mem _ (hc.2.1 hy).1, hyG⟩
      rw [rad.isPreRadial.1] at this
      obtain ⟨z, hz, hzy⟩ := this
      obtain rfl := cap.isEmbedding.injective hzy
      exact (hc.2.1 hy).2 hz
    have hxN : cap.emb x ∈ insOf D.ins N := by
      by_contra hn
      exact disjoint_left.mp (hall f hf s hs hfs) hxs ⟨mem_univ _, hn⟩
    rcases hxN with hxU | hxC
    · exact absurd (hN.U_subset hxU) (hdis x (hf.subset hx))
    obtain ⟨C, ⟨hC, hCs⟩, hxC⟩ := mem_iUnion₂.mp hxC
    refine ⟨C, hC, hCs, ?_⟩
    have hlt := hshort C hC hCs
    have hfr : frontier (D.ins C) = C.U := by
      rw [subBd_eq_frontier', hsl.subBd_eq C hC (hCs.trans hN) hlt]
    have hconn : IsPreconnected (cap.emb '' c) := hc.2.2.1.isConnected.isPreconnected.image _
      cap.isEmbedding.continuous.continuousOn
    by_contra hcn
    obtain ⟨y, hyc, hyn⟩ := not_subset.mp hcn
    have hcl : IsClosed (D.ins C) := (hsl.isClosedDisc C hC (hCs.trans hN) hlt).isClosed
    have hint : ∀ z ∈ cap.emb '' c, z ∈ D.ins C → z ∈ interior (D.ins C) := by
      rintro _ ⟨q, hq, rfl⟩ hz
      by_contra hni
      have hzf : cap.emb q ∈ frontier (D.ins C) := ⟨subset_closure hz, hni⟩
      rw [hfr] at hzf
      exact hdis q hq ((hCs.trans hN).U_subset hzf)
    obtain ⟨z, -, hz₁, hz₂⟩ := hconn _ _ isOpen_interior hcl.isOpen_compl (fun z hz ↦ by
      by_cases hzI : z ∈ D.ins C
      · exact Or.inl (hint z hz hzI)
      · exact Or.inr hzI) ⟨_, mem_image_of_mem _ (hf.subset hx), hint _ (mem_image_of_mem _
          (hf.subset hx)) hxC⟩ ⟨y, hyc, hyn⟩
    exact hz₂ (interior_subset hz₁)
  obtain ⟨y, hyr, hyU⟩ := exists_notMem_U (Γ := G₃) hT hopen (region_nonempty hr₀)
  obtain ⟨s₀, hs₀, hys₀⟩ := exists_region_of_notMem hyU
  have hm₀ : (s₀ ∩ r₀).Nonempty := ⟨y, hys₀, hyr⟩
  refine ⟨N, hN, hshort, hmid, ?_⟩
  by_cases hcase : s₀ ∈ Z
  · exfalso
    have hBc : ∀ e ∈ B.edgeSet, ∃ C : Drawing Shat, C.IsCircuit ∧ C.IsSubdrawing N
      ∧ cap.emb '' e ⊆ D.ins C := by
      intro e he
      have heE : e ∈ Γ.E := hAB.right_le.edgeSet_subset he
      refine hcov e heE fun f hf s hs hfs ↦ disjoint_iff_inter_eq_empty.mpr ?_
      by_contra hne
      have hsZ : s ∉ Z := fun h ↦ by
        rcases edge_cases hAB heE with ⟨-, h'⟩ | ⟨h', -⟩
        · exact h' he
        · exact h' ((hcol hf hs hfs).mp h)
      exact hno s₀ hcase s ⟨hs, hsZ⟩ hm₀ (nonempty_iff_ne_empty.mpr hne)
    have : Nonempty (Drawing Shat) := ⟨N⟩
    choose! C hC₁ hC₂ hC₃ using hBc
    have hspec : ∀ e ∈ B.edgeSet, IsInsOf D.rad D.ord D.𝒯 (C e) (D.ins (C e)) := fun e he ↦
      D.ins_spec ⟨(hC₂ e he).trans hN, hC₁ e he⟩ (hshort _ (hC₁ e he) (hC₂ e he))
    have hpre := IsTangle.isPretangle D.isTangle
    let p : Set S → Hypergraph S (Set S) × Hypergraph S (Set S) := fun e ↦ (Γ.restrict
      (cap.emb ⁻¹' D.ins (C e)), Γ.restrict (cap.emb ⁻¹' closure (D.ins (C e))ᶜ))
    let L : List (Hypergraph S (Set S) × Hypergraph S (Set S)) := (A ∩ B, Γ.toHypergraph) ::
      B.edgeSet_finite.toFinset.toList.map p
    have hmemL : ∀ e ∈ B.edgeSet, p e ∈ L := fun e he ↦ List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨e, by simpa using he, rfl⟩)
    refine GM11.theorem_6_2_proof hpre hmem L ?_ ?_ ?_ ?_
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · have hrepLeOrd : D.rep ≤ D.ord := (tangleRep_spec D.rad D.ord D.𝒯).1
        exact mem_pretangle_inter hpre hAB (by omega)
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
        exact (hspec e (by simpa using he)).2.2.2.2
    · intro q hq x hx
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hx.1
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
        have he' : e ∈ B.edgeSet := by simpa using he
        obtain ⟨⟨hxV, hxi⟩, -, hxo⟩ := hx
        have hd := hspec e he'
        have hfr : frontier (D.ins (C e)) = (C e).U := by
          rw [IsClosedDisc.frontier_eq_discBd hT hd.2.2.1, hd.2.2.2.1]
        have hxf : cap.emb x ∈ frontier (D.ins (C e)) := by
          rw [frontier_eq_closure_inter_closure]
          exact ⟨subset_closure hxi, hxo⟩
        rw [hfr] at hxf
        exact hmid x hxV ((hC₂ e he').1 (mem_V_of_mem_U_sub ((hC₂ e he').trans hN) hxf
          (rad.isPreRadial.2.1 (mem_image_of_mem _ hxV))))
    · intro v hv
      by_cases hva : v ∈ A.vertexSet
      · exact ⟨_, List.mem_cons_self .., ⟨hva, hv⟩⟩
      have hvΓ : v ∈ Γ.V := hAB.right_le.vertexSet_subset hv
      obtain ⟨c, hc, hvc⟩ := exists_edge_incident hS h3 rad hvΓ
      have hvt : v ∈ tilde c := ⟨hvc, fun h ↦ Γ.disjoint_V hc h hvΓ⟩
      have hcB : c ∈ B.edgeSet := by
        rcases edge_cases hAB hc with ⟨h, -⟩ | ⟨-, h⟩
        · exact absurd (hincX hAB.left_le h hvΓ hvt) hva
        · exact h
      refine ⟨_, hmemL c hcB, hvΓ, ?_⟩
      have hcl : IsClosed (D.ins (C c)) := (hspec c hcB).2.2.1.isClosed
      exact hcl.closure_subset_iff.mpr (hC₃ c hcB) (((cap.isClosedEmbedding hS).closure_image_eq c)
        ▸ mem_image_of_mem _ hvc)
    · intro e he
      have heE : e ∈ Γ.E := hAB.right_le.edgeSet_subset he
      refine ⟨_, hmemL e he, heE, fun x hx ↦ hC₃ e he (mem_image_of_mem _ hx), ?_⟩
      rintro x ⟨hxt, -⟩
      have hcl : IsClosed (D.ins (C e)) := (hspec e he).2.2.1.isClosed
      exact hcl.closure_subset_iff.mpr (hC₃ e he) (((cap.isClosedEmbedding hS).closure_image_eq e)
        ▸ mem_image_of_mem _ hxt.1)
  · intro e he
    have heE : e ∈ Γ.E := hAB.left_le.edgeSet_subset he
    refine hcov e heE fun f hf s hs hfs ↦ disjoint_iff_inter_eq_empty.mpr ?_
    by_contra hne
    exact hno s ((hcol hf hs hfs).mpr he) s₀ ⟨hs₀, hcase⟩ (nonempty_iff_ne_empty.mpr hne) hm₀

end TangleDatum

end GraphMinor.GM19
