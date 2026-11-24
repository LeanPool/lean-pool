/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section7a

/-!
# Regions of a radial drawing

Each region of `Γ*` contains a unique edge of `Γ`, and the vertices of `Γ` on its closure are the
ends
of that edge. Graph Minors XI, Section 3, says this for its own paintings and drawings. For a
painting
of Graph Minors XIX we get it from the colouring of `Section8e.lean`: two regions of `G₃` of
different
colours are parted by an edge of `Γ*`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {Γ : Painting S}

/-- The facts about the regions of `Γ*`. -/
theorem RadialDrawing.region_facts (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected)
    (rad : RadialDrawing cap Γ) :
    (∀ s ∈ rad.G.R, ∃ e ∈ Γ.E, cap.emb '' e ⊆ s) ∧
    (∀ s ∈ rad.G.R, ∀ e ∈ Γ.E, ∀ f ∈ Γ.E, cap.emb '' e ⊆ s → cap.emb '' f ⊆ s → e = f) ∧
    ∀ s ∈ rad.G.R, ∀ e ∈ Γ.E, cap.emb '' e ⊆ s → ∀ v ∈ Γ.V, cap.emb v ∈ closure s →
      v ∈ closure e := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hlc : LocallyConnectedSpace Shat := IsClosedSurface.locallyConnectedSpace hT
  have h2 := h3.hatRegions_isOpenDisc hS cap
  obtain ⟨D, G₃, hD, hrad, hmax, hsub, hhat⟩ := rad.exists_full hS h2 h3.1
  have hDE := hD.E_nonempty hS h3.1
  have hF := regionFacts_of_radial hrad hT hmax hDE
  have hUsub : rad.G.U ⊆ G₃.U := fun x hx ↦ by
    by_cases hxV : x ∈ rad.G.V
    · exact G₃.V_subset_U (hsub.1 hxV)
    · obtain ⟨e, he, hxe⟩ := rad.G.exists_edge_of_mem hx hxV
      rw [G₃.U_eq]
      exact Or.inr (mem_iUnion₂.mpr ⟨e, hsub.2 he, subset_closure hxe⟩)
  -- A region of `G₃` that meets a region of `Γ*` lies in it.
  have hin : ∀ {s p : Set Shat}, s ∈ rad.G.R → p ∈ G₃.R → (p ∩ s).Nonempty → p ⊆ s := by
    intro s p hs hp ⟨x, hxp, hxs⟩
    exact subset_region hs (region_isPreconnected hp)
      (disjoint_left.mpr fun y hy h ↦ region_subset hp hy (hUsub h)) hxp hxs
  -- All regions of `G₃` in a region of `Γ*` have the same colour.
  have hsame : ∀ {s p q : Set Shat}, s ∈ rad.G.R → p ∈ G₃.R → q ∈ G₃.R → p ⊆ s → q ⊆ s →
      ∀ {f f' c c' : Set S}, Γ.IsSkEdgeIn f c → Γ.IsSkEdgeIn f' c' → cap.emb '' f ⊆ p →
        cap.emb '' f' ⊆ q → c = c' := by
    intro s p q hs hp hq hps hqs f f' c c' hc hc' hfp hfq
    by_contra hne
    let t : Set S → Prop := (· = c)
    have hpZ : p ∈ colourSet cap Γ G₃ t := ⟨hp, f, c, hc, hfp, rfl⟩
    have hqZ : q ∈ G₃.R \ colourSet cap Γ G₃ t := by
      refine ⟨hq, ?_⟩
      rintro ⟨-, f₂, c₂, h₂, hf₂, ht⟩
      exact hne (ht ▸ (colour_unique hS hD hrad hmax hDE hq hc' h₂ hfq hf₂).2).symm
    obtain ⟨xp, hxp⟩ := region_nonempty hp
    obtain ⟨xq, hxq⟩ := region_nonempty hq
    obtain ⟨e, he, y, hye, hys⟩ := exists_boundary_edge hT (region_isOpen hs)
      (region_isPreconnected hs) hpZ (fun _ h ↦ h.1) hqZ ⟨xp, hxp, hps hxp⟩ ⟨xq, hxq, hqs hxq⟩
    have heG := (boundary_split hS hDE rad hD hrad hmax hsub hhat he).1
    have hyU : y ∈ rad.G.U := by
      rw [rad.G.U_eq]
      exact Or.inr (mem_iUnion₂.mpr ⟨e, heG, subset_closure hye⟩)
    exact region_subset hs hys hyU
  -- An edge of `Γ` in `s` has an edge of `sk(Γ)` in a region of `G₃` in `s`.
  have hreg : ∀ {s : Set Shat} {e : Set S}, s ∈ rad.G.R → e ∈ Γ.E → cap.emb '' e ⊆ s →
      ∃ f p, Γ.IsSkEdgeIn f e ∧ p ∈ G₃.R ∧ p ⊆ s ∧ cap.emb '' f ⊆ p := by
    intro s e hs he hes
    obtain ⟨f, hf⟩ := Γ.exists_sk_in he
    have hg := (hD.edge_iff hS).mpr ⟨f, hf.mem, rfl⟩
    have hdis : Disjoint (cap.emb '' f) G₃.U := by
      refine disjoint_left.mpr fun y hy hyU ↦ ?_
      have hyD := hg.2.1 hy
      have : y ∈ D.U ∩ G₃.U := ⟨hyD.1, hyU⟩
      rw [show D.U ∩ G₃.U = D.V from hrad.2.1] at this
      exact hyD.2 this
    obtain ⟨y, hy⟩ := hg.1
    obtain ⟨p, hp, hyp⟩ := exists_region_of_notMem (disjoint_left.mp hdis hy)
    have hyf : y ∈ cap.emb '' e := image_mono hf.subset hy
    exact ⟨f, p, hf, hp, hin hs hp ⟨y, hyp, hes hyf⟩,
      subset_region hp hg.2.2.1.isConnected.isPreconnected hdis hy hyp⟩
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨y, hyO⟩ := region_nonempty hs
    obtain ⟨z, hzs, hzU⟩ := exists_notMem_U (Γ := G₃) hT (region_isOpen hs)
      ⟨y, hyO⟩
    obtain ⟨p, hp, hzp⟩ := exists_region_of_notMem hzU
    have hps := hin hs hp ⟨z, hzp, hzs⟩
    obtain ⟨f, c, hc, hfp⟩ := exists_colour hS hD hrad hmax hDE hp
    refine ⟨c, hc.1, ?_⟩
    obtain ⟨x, hx⟩ := hc.mem.1
    have hdis : Disjoint (cap.emb '' c) rad.G.U := by
      refine disjoint_left.mpr ?_
      rintro _ ⟨y, hy, rfl⟩ hyU
      have : cap.emb y ∈ Γ.hatU cap ∩ rad.G.U := ⟨mem_image_of_mem _ (hc.1.2.1 hy).1, hyU⟩
      rw [rad.isPreRadial.1] at this
      obtain ⟨y', hy', hyy⟩ := this
      obtain rfl := cap.isEmbedding.injective hyy
      exact (hc.1.2.1 hy).2 hy'
    exact subset_region hs (hc.1.2.2.1.isConnected.isPreconnected.image _
      cap.isEmbedding.continuous.continuousOn) hdis (mem_image_of_mem _ (hc.subset hx))
      (hps (hfp (mem_image_of_mem _ hx)))
  · intro s hs e he f hf hes hfs
    obtain ⟨a, p, ha, hp, hps, hap⟩ := hreg hs he hes
    obtain ⟨b, q, hb, hq, hqs, hbq⟩ := hreg hs hf hfs
    exact hsame hs hp hq hps hqs ha hb hap hbq
  · intro s hs e he hes v hv hvs
    obtain ⟨a, p, ha, hp, hps, hap⟩ := hreg hs he hes
    have hRfin := finite_R hT G₃
    have hcov : s ⊆ closure (⋃ q ∈ {q | q ∈ G₃.R ∧ q ⊆ s}, q) := by
      intro x hx
      refine mem_closure_iff.mpr fun O hO hxO ↦ ?_
      obtain ⟨y, ⟨hyO, hys⟩, hyU⟩ := exists_notMem_U (Γ := G₃) hT
        (hO.inter (region_isOpen hs)) ⟨x, hxO, hx⟩
      obtain ⟨q, hq, hyq⟩ := exists_region_of_notMem hyU
      exact ⟨y, hyO, mem_iUnion₂.mpr ⟨q, ⟨hq, hin hs hq ⟨y, hyq, hys⟩⟩, hyq⟩⟩
    have hv' := closure_minimal hcov isClosed_closure hvs
    have hfin : {q | q ∈ G₃.R ∧ q ⊆ s}.Finite := hRfin.subset fun _ h ↦ h.1
    rw [hfin.closure_biUnion] at hv'
    obtain ⟨q, ⟨hq, hqs⟩, hvq⟩ := mem_iUnion₂.mp hv'
    obtain ⟨f, c, hc, hfq⟩ := exists_colour hS hD hrad hmax hDE hq
    obtain rfl := hsame hs hp hq hps hqs ha hc hap hfq
    have hg := (hD.edge_iff hS).mpr ⟨f, hc.mem, rfl⟩
    have hvD : cap.emb v ∈ D.V := by
      rw [hD.hV]
      exact mem_image_of_mem _ hv
    have := hF.2.2 q hq _ hg hfq _ hvD hvq
    rw [(cap.isClosedEmbedding hS).closure_image_eq] at this
    obtain ⟨y, hy, hyv⟩ := this
    obtain rfl := cap.isEmbedding.injective hyv
    exact closure_mono hc.subset hy

end GraphMinor.GM19
