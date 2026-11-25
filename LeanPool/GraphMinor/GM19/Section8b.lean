/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Spokes
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Graph Minors XIX, Section 8: walking around a painting

This file gives the facts about `sk(Γ)` and `Γ*` behind (8.2) and (8.3). Each edge `e` of `Γ*` is
split according to a single pair `(c₁, c₂)` of edges of `Γ` (`PairOf.unique`). The pairs connect all
of `E(Γ)` (`edges_same`): around a vertex, consecutive edges of `sk(Γ)` are in one edge of `Γ` or
form
a pair, and `U(sk(Γ))` is connected because the regions of `sk(Γ)` are discs.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface unitInterval

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]

/-- A point of an `O`-arc is a limit of points of the `O`-arc outside a given finite set. -/
theorem mem_closure_sdiff_finite {T : Type} [TopologicalSpace T] {F W : Set T}
    (hF : IsOArc F) (hW : W.Finite) {v : T} (hv : v ∈ F) : v ∈ closure (F \ W) := by
  obtain ⟨φ⟩ := id hF
  have hinf : Infinite Circle := by
    have hn : Nontrivial Circle := ⟨1, Circle.exp Real.pi, fun h ↦ by
      have := congrArg (fun z : Circle ↦ (z : ℂ)) h
      simp at this
      norm_num at this⟩
    exact Set.infinite_univ_iff.mp (isPreconnected_univ.infinite_of_nontrivial Set.nontrivial_univ)
  rw [mem_closure_iff]
  intro O hO hvO
  by_contra hne
  have hsub : ∀ z : Circle, (φ z).1 ∈ O → (φ z).1 ∈ W := fun z hz ↦ by
    by_contra hn
    exact hne ⟨_, hz, (φ z).2, hn⟩
  let V : Set Circle := {z | (φ z).1 ∈ O}
  have hVo : IsOpen V := hO.preimage (continuous_subtype_val.comp φ.continuous)
  have hVf : V.Finite := by
    refine Set.Finite.of_finite_image (f := fun z ↦ (φ z).1) (hW.subset ?_) ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact hsub z hz
    · exact fun a _ b _ h ↦ φ.injective (Subtype.ext h)
  have hVc : IsClopen V := ⟨hVf.isClosed, hVo⟩
  have hVne : V.Nonempty := ⟨φ.symm ⟨v, hv⟩, by simpa [V] using hvO⟩
  have := hVc.eq_univ hVne
  rw [this] at hVf
  exact Set.infinite_univ hVf

namespace Painting

variable (Γ : Painting S)

omit [T2Space S] in
theorem IsSkEdgeIn.mem {Γ : Painting S} {f c : Set S} (h : Γ.IsSkEdgeIn f c) :
    f ∈ arcComponentsIn (Γ.skU \ Γ.V) := by
  obtain ⟨hc, ⟨h2, rfl⟩ | ⟨h3, hf⟩⟩ := h
  · exact Γ.two_mem_sk hc h2
  · obtain ⟨hdisc, hT, hfin⟩ := Γ.isDisc_of_three hc h3
    have hfsub : f ⊆ Γ.skU \ Γ.V := fun x hx ↦ by
      have hxb := (hf.2.1 hx)
      refine ⟨Or.inr (mem_iUnion₂.2 ⟨c, ⟨hc, h3⟩, hxb.1⟩), fun hxV ↦ hxb.2 ?_⟩
      exact ⟨discBd_subset _ hxb.1, fun hxc ↦ Γ.disjoint_V hc hxc hxV⟩
    refine ⟨hf.1, hfsub, hf.2.2.1, fun D hD hp hsub ↦ ?_⟩
    have hDc : D ⊆ c := by
      obtain ⟨c', hc', hDc'⟩ := exists_arcComp_superset hp
        (hD.trans (sdiff_subset_sdiff_left Γ.skU_subset))
      obtain ⟨x, hx⟩ := hf.1
      have hxc : x ∈ c := by
        have hxb := hf.2.1 hx
        by_contra hn
        exact hxb.2 ⟨discBd_subset _ hxb.1, hn⟩
      rwa [arcComp_eq_of_mem hc hc' hxc (hDc' (hsub hx))]
    refine hf.2.2.2 D (fun x hx ↦ ⟨Γ.mem_discBd_of_skU hc h3 (hDc hx) (hD hx).1,
      fun ht ↦ ?_⟩) hp hsub
    exact (hD hx).2 (Γ.tilde_subset_V hc ht)

omit [T2Space S] in
theorem IsSkEdgeIn.subset {Γ : Painting S} {f c : Set S} (h : Γ.IsSkEdgeIn f c) : f ⊆ c := by
  obtain ⟨hc, ⟨h2, rfl⟩ | ⟨h3, hf⟩⟩ := h
  · exact subset_rfl
  · intro x hx
    have hxb := hf.2.1 hx
    by_contra hn
    exact hxb.2 ⟨discBd_subset _ hxb.1, hn⟩

omit [T2Space S] in
theorem IsSkEdgeIn.unique {Γ : Painting S} {f c c' : Set S} (h : Γ.IsSkEdgeIn f c)
    (h' : Γ.IsSkEdgeIn f c') : c = c' := by
  obtain ⟨x, hx⟩ := (h.mem).1
  exact arcComp_eq_of_mem h.1 h'.1 (h.subset hx) (h'.subset hx)

omit [T2Space S] in
theorem exists_isSkEdgeIn {f : Set S} (hf : f ∈ arcComponentsIn (Γ.skU \ Γ.V)) :
    ∃ c, Γ.IsSkEdgeIn f c := by
  rcases Γ.sk_cases hf with ⟨h, h2⟩ | ⟨c, hc, h3, hsub, hbd⟩
  · exact ⟨f, h, Or.inl ⟨h2, rfl⟩⟩
  · refine ⟨c, hc, Or.inr ⟨h3, hf.1, fun x hx ↦ ⟨hbd hx, fun ht ↦ (hf.2.1 hx).2 ?_⟩, hf.2.2.1,
      fun D hD hp hs ↦ hf.2.2.2 D (fun x hx ↦ ?_) hp hs⟩⟩
    · exact Γ.tilde_subset_V hc ht
    · have hx' := hD hx
      refine ⟨Or.inr (mem_iUnion₂.2 ⟨c, ⟨hc, h3⟩, hx'.1⟩), fun hxV ↦ hx'.2 ?_⟩
      exact ⟨discBd_subset _ hx'.1, fun hxc ↦ Γ.disjoint_V hc hxc hxV⟩

/-- An end of an edge of `Γ` is an end of an edge of `sk(Γ)` inside it. -/
theorem exists_sk_at {c : Set S} (hc : c ∈ Γ.E) {v : S} (hv : v ∈ tilde c) :
    ∃ f, Γ.IsSkEdgeIn f c ∧ v ∈ tilde f := by
  rcases Γ.size_cases hc with h2 | h3
  · exact ⟨c, ⟨hc, Or.inl ⟨h2, rfl⟩⟩, hv⟩
  obtain ⟨hdisc, hT, hfin⟩ := Γ.isDisc_of_three hc h3
  have hvF : v ∈ discBd (closure c) := hT hv
  have hclA : v ∈ closure (discBd (closure c) \ tilde c) := mem_closure_sdiff_finite
    hdisc.isOArc_discBd
    hfin hvF
  obtain ⟨D, hDU, hDV⟩ := Γ.exists_skDrawing
  have hEfin : (arcComponentsIn (Γ.skU \ Γ.V)).Finite := by
    have := D.finite_edges
    rwa [hDU, hDV] at this
  let 𝓕 : Set (Set S) := {f | f ∈ arcComponentsIn (Γ.skU \ Γ.V) ∧ Γ.IsSkEdgeIn f c}
  have h𝓕 : 𝓕.Finite := hEfin.subset fun _ h ↦ h.1
  have hcover : discBd (closure c) \ tilde c ⊆ ⋃ f ∈ 𝓕, f := by
    rintro x ⟨hxF, hxt⟩
    have hxc : x ∈ c := by
      by_contra hn
      exact hxt ⟨discBd_subset _ hxF, hn⟩
    have hx : x ∈ Γ.skU \ Γ.V := ⟨Or.inr (mem_iUnion₂.2 ⟨c, ⟨hc, h3⟩, hxF⟩), Γ.disjoint_V hc hxc⟩
    obtain ⟨f, hf, hxf⟩ := exists_arcComp_superset (isPathConnected_singleton x)
      (singleton_subset_iff.2 hx)
    obtain ⟨c', hc'⟩ := Γ.exists_isSkEdgeIn hf
    have : c' = c := arcComp_eq_of_mem hc'.1 hc (hc'.subset (hxf rfl)) hxc
    exact mem_biUnion (x := f) ⟨hf, this ▸ hc'⟩ (hxf rfl)
  have hcl := closure_mono hcover hclA
  rw [h𝓕.closure_biUnion] at hcl
  obtain ⟨f, hf, hvf⟩ := mem_iUnion₂.mp hcl
  exact ⟨f, hf.2, hvf, fun hc' ↦ (hf.1.2.1 hc').2 (Γ.tilde_subset_V hc hv)⟩

end Painting

section Regions

variable {cap : IsCappedSurface S Shat} {Γ : Painting S} {D : Drawing Shat}

omit [T2Space S] in
/-- A region of `sk(Γ)` in `Σ̂` is a region of `Γ`, or the inside of the disc of an edge of size 3.
-/
theorem IsSkHat.region_cases (h : IsSkHat cap Γ D) {r : Set Shat}
  (hr : r ∈ D.R) :
    r ∈ Γ.hatRegions cap ∨ ∃ c ∈ Γ.E, (tilde c).ncard = 3 ∧ r ⊆ cap.emb '' closure c := by
  have hT := cap.isClosedSurface
  have : T2Space Shat := hT.2.1
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have hsub : D.U ⊆ Γ.hatU cap := by
    rw [h.hU]
    exact image_mono Γ.skU_subset
  obtain ⟨x, hx, rfl⟩ := hr
  by_cases hxU : x ∈ Γ.hatU cap
  · right
    obtain ⟨z, hzU, rfl⟩ := hxU
    have hzsk : z ∉ Γ.skU := fun hc ↦ hx.2 (by rw [h.hU]; exact mem_image_of_mem _ hc)
    have hzV : z ∉ Γ.V := fun hc ↦ hzsk (Or.inl (Or.inl hc))
    obtain ⟨c, hc, hzc⟩ := exists_arcComp_superset (F := Γ.U \ Γ.V)
      (isPathConnected_singleton z) (singleton_subset_iff.2 ⟨hzU, hzV⟩)
    have hzc' : z ∈ c := hzc rfl
    have h3 : (tilde c).ncard = 3 := by
      rcases Γ.size_cases hc with h2 | h3
      · exact absurd (Or.inl (Or.inr (mem_iUnion₂.2 ⟨c, ⟨hc, h2⟩, hzc'⟩))) hzsk
      · exact h3
    obtain ⟨hdisc, -⟩ := Γ.isDisc_of_three hc h3
    obtain ⟨hC, hCbd⟩ := isClosedDisc_image hdisc cap.isEmbedding
    have hopen := hC.isOpen_discInt hman
    have hbdU : discBd (cap.emb '' closure c) ⊆ D.U := by
      rw [hCbd, h.hU]
      exact image_mono fun w hw ↦ Or.inr (mem_iUnion₂.2 ⟨c, ⟨hc, h3⟩, hw⟩)
    have hyB : cap.emb z ∈ discInt (cap.emb '' closure c) :=
      ⟨mem_image_of_mem _ (subset_closure hzc'), fun hc' ↦ hx.2 (hbdU hc')⟩
    refine ⟨c, hc, h3, ?_⟩
    have hin : connectedComponentIn (univ \ D.U) (cap.emb z) ⊆ discInt (cap.emb '' closure c) := by
      refine isPreconnected_connectedComponentIn.subset_left_of_subset_union hopen
        hC.isClosed.isOpen_compl ?_ (fun w hw ↦ ?_) ⟨_, mem_connectedComponentIn hx, hyB⟩
      · exact disjoint_left.2 fun w hw hn ↦ hn hw.1
      · by_cases hwC : w ∈ cap.emb '' closure c
        · exact Or.inl ⟨hwC, fun hb ↦ (connectedComponentIn_subset _ _ hw).2 (hbdU hb)⟩
        · exact Or.inr hwC
    exact fun w hw ↦ (hin hw).1
  · left
    have hhat : connectedComponentIn (Γ.hatU cap)ᶜ x ∈ Γ.hatRegions cap := ⟨x, hxU, rfl⟩
    have hR := h.hatRegion_mem_R hhat
    have hxm : x ∈ connectedComponentIn (Γ.hatU cap)ᶜ x := mem_connectedComponentIn hxU
    have : connectedComponentIn (univ \ D.U) x = connectedComponentIn (Γ.hatU cap)ᶜ x :=
      GM11.region_eq_of_mem ⟨x, hx, rfl⟩ hR (mem_connectedComponentIn hx) hxm
    rw [this]
    exact hhat

end Regions

section Pairs

variable {cap : IsCappedSurface S Shat} {Γ : Painting S}

/-- `(c₁, c₂)` is the pair of edges of `Γ` that decides whether a separation splits `e ∈ E(Γ*)`. -/
def RadialDrawing.PairOf (rad : RadialDrawing cap Γ) (e : Set Shat) (c₁ c₂ : Set S) : Prop :=
  ∃ (v : S) (w : Shat), v ∈ Γ.V ∧ w ∈ rad.Rstar ∧ closure e ∩ rad.G.V = {cap.emb v, w} ∧
    ∃ f₁ f₂ : Set S, f₁ ≠ f₂ ∧ Γ.IsSkEdgeIn f₁ c₁ ∧ Γ.IsSkEdgeIn f₂ c₂ ∧
      v ∈ tilde f₁ ∧ v ∈ tilde f₂ ∧
      cap.emb '' f₁ ⊆ frontier (rad.regionOf w) ∧ cap.emb '' f₂ ⊆ frontier (rad.regionOf w)

omit [T2Space S] in
theorem RadialDrawing.splits_iff (rad : RadialDrawing cap Γ) {A B : Hypergraph S (Set S)}
    {e : Set Shat} : rad.Splits A B e ↔ ∃ c₁ c₂, rad.PairOf e c₁ c₂ ∧
      ((c₁ ∈ A.edgeSet ∧ c₂ ∈ B.edgeSet) ∨ (c₁ ∈ B.edgeSet ∧ c₂ ∈ A.edgeSet)) := by
  constructor
  · rintro ⟨v, w, hv, hw, hset, f₁, f₂, c₁, c₂, hne, h₁, h₂, h₃, h₄, h₅, h₆, h⟩
    exact ⟨c₁, c₂, ⟨v, w, hv, hw, hset, f₁, f₂, hne, h₁, h₂, h₃, h₄, h₅, h₆⟩, h⟩
  · rintro ⟨c₁, c₂, ⟨v, w, hv, hw, hset, f₁, f₂, hne, h₁, h₂, h₃, h₄, h₅, h₆⟩, h⟩
    exact ⟨v, w, hv, hw, hset, f₁, f₂, c₁, c₂, hne, h₁, h₂, h₃, h₄, h₅, h₆, h⟩

omit [T2Space S] in
theorem RadialDrawing.regionOf_mem (rad : RadialDrawing cap Γ) {w : Shat} (hw : w ∈ rad.Rstar) :
    rad.regionOf w ∈ Γ.hatRegions cap ∧ w ∈ rad.regionOf w := by
  obtain ⟨r₀, ⟨y, hy, rfl⟩, hwr₀⟩ := rad.isPreRadial.2.2.2.1 w hw
  have hwU : w ∈ (Γ.hatU cap)ᶜ := connectedComponentIn_subset _ _ hwr₀
  exact ⟨⟨w, hwU, rfl⟩, mem_connectedComponentIn hwU⟩

theorem RadialDrawing.PairOf.unique (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected)
    {rad : RadialDrawing cap Γ} {e : Set Shat} {c₁ c₂ c₁' c₂' : Set S} (h : rad.PairOf e c₁ c₂)
    (h' : rad.PairOf e c₁' c₂') : (c₁' = c₁ ∧ c₂' = c₂) ∨ (c₁' = c₂ ∧ c₂' = c₁) := by
  obtain ⟨v, w, hv, hw, hset, f₁, f₂, hne, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  obtain ⟨v', w', hv', hw', hset', f₁', f₂', hne', h₁', h₂', h₃', h₄', h₅', h₆'⟩ := h'
  have heq : ({cap.emb v, w} : Set Shat) = {cap.emb v', w'} := hset.symm.trans hset'
  have hm₁ : cap.emb v ∈ ({cap.emb v', w'} : Set Shat) := heq ▸ Or.inl rfl
  have hm₂ : w ∈ ({cap.emb v', w'} : Set Shat) := heq ▸ Or.inr rfl
  have hvv : v = v' := by
    rcases hm₁ with h | h
    · exact cap.isEmbedding.injective h
    · exact absurd (h ▸ mem_image_of_mem _ hv) hw'.2
  subst hvv
  have hww : w = w' := by
    rcases hm₂ with h | h
    · exact absurd (h ▸ mem_image_of_mem _ hv) hw.2
    · exact h
  subst hww
  obtain ⟨g₁, g₂, hg⟩ := sk_frontier_pair hS h3 (rad.regionOf_mem hw).1 hv
  have a₁ := hg f₁ h₁.mem h₃ h₅
  have a₂ := hg f₂ h₂.mem h₄ h₆
  have a₃ := hg f₁' h₁'.mem h₃' h₅'
  have a₄ := hg f₂' h₂'.mem h₄' h₆'
  have hcase : (f₁' = f₁ ∧ f₂' = f₂) ∨ (f₁' = f₂ ∧ f₂' = f₁) := by
    rcases a₁ with a₁ | a₁ <;> rcases a₂ with a₂ | a₂ <;> rcases a₃ with a₃ | a₃ <;>
      rcases a₄ with a₄ | a₄ <;> subst_vars <;> simp_all
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨h₁'.unique h₁, h₂'.unique h₂⟩
  · exact Or.inr ⟨h₁'.unique h₂, h₂'.unique h₁⟩

/-- Going around a vertex, a property of edges of `Γ` that the pairs do not change stays the same.
-/
theorem vertex_step (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected)
    (rad : RadialDrawing cap Γ) (t : Set S → Prop)
    (ht : ∀ e ∈ rad.G.E, ∀ c₁ c₂, rad.PairOf e c₁ c₂ → (t c₁ ↔ t c₂)) {v₀ : S} (hv₀ : v₀ ∈ Γ.V)
    {c c' : Set S} (hc : c ∈ Γ.E) (hc' : c' ∈ Γ.E) (hv : v₀ ∈ tilde c) (hv' : v₀ ∈ tilde c') :
    t c ↔ t c' := by
  classical
  obtain ⟨D, hD⟩ := exists_isSkHat hS cap Γ
  have hT := cap.isClosedSurface
  have : T2Space Shat := hT.2.1
  have : Nonempty Shat := ⟨cap.emb v₀⟩
  have hlc : LocallyConnectedSpace Shat := GM11.IsClosedSurface.locallyConnectedSpace hT
  have h2 := h3.hatRegions_isOpenDisc hS cap
  have hvD : cap.emb v₀ ∈ D.V := by
    rw [hD.hV]
    exact mem_image_of_mem _ hv₀
  obtain ⟨γ, hγ⟩ := GM11.exists_edgePar D
  have hclv : ∀ f : Set S, cap.emb v₀ ∈ closure (cap.emb '' f) → v₀ ∈ closure f := fun f h ↦ by
    rw [(cap.isClosedEmbedding hS).closure_image_eq] at h
    obtain ⟨x, hx, hxe⟩ := h
    exact cap.isEmbedding.injective hxe ▸ hx
  have hk : ∀ k : GM11.halfEdges D γ (cap.emb v₀), ∃ f c, cap.emb '' f = k.1.1 ∧
      Γ.IsSkEdgeIn f c ∧ v₀ ∈ tilde f := by
    rintro ⟨⟨E, b⟩, hE, hb⟩
    obtain ⟨f, hf, rfl⟩ := hD.edge_iff.mp hE
    obtain ⟨c, hc⟩ := Γ.exists_isSkEdgeIn hf
    refine ⟨f, c, rfl, hc, ?_⟩
    have := GM11.end_mem_closure hγ hE b
    rw [hb] at this
    exact ⟨hclv f this, fun hvf ↦ (hf.2.1 hvf).2 hv₀⟩
  choose g cl hgi hgc hgv using hk
  have hfind : ∀ f c, Γ.IsSkEdgeIn f c → v₀ ∈ tilde f →
      ∃ k, cl k = c := by
    intro f c hc hvf
    have hE : cap.emb '' f ∈ D.E := hD.edge_iff.mpr ⟨f, hc.mem, rfl⟩
    have hcl : cap.emb v₀ ∈ closure (cap.emb '' f) :=
      image_closure_subset_closure_image cap.isEmbedding.continuous (mem_image_of_mem _ hvf.1)
    obtain ⟨b, hb⟩ := GM11.exists_end_eq hγ hE hvD hcl
    let k : GM11.halfEdges D γ (cap.emb v₀) := ⟨(cap.emb '' f, b), hE, hb⟩
    refine ⟨k, ?_⟩
    have : g k = f := cap.isEmbedding.injective.image_injective (hgi k)
    have h₁ := hgc k
    rw [this] at h₁
    exact h₁.unique hc
  have hall : ∀ a b, t (cl a) ↔ t (cl b) := by
    have hfin : Finite (GM11.halfEdges D γ (cap.emb v₀)) :=
      (GM11.finite_halfEdges D γ _).to_subtype
    by_cases hc2 : 2 ≤ Nat.card (GM11.halfEdges D γ (cap.emb v₀))
    swap
    · have hsub : Subsingleton (GM11.halfEdges D γ (cap.emb v₀)) := by
        rw [← Finite.card_le_one_iff_subsingleton]
        omega
      intro a b
      rw [Subsingleton.elim a b]
    obtain ⟨next, ρ, P, W, Q, τ, hsec, -, -⟩ := exists_sectors' hT D hγ hvD hc2
    have hsurj : Function.Surjective next := Finite.injective_iff_surjective.mp hsec.corners.inj
    have hstep : ∀ k, t (cl k) ↔ t (cl (next k)) := by
      intro k
      by_cases hgg : g k = g (next k)
      · have h₁ := hgc k
        rw [hgg] at h₁
        rw [h₁.unique (hgc (next k))]
      have hrD := hsec.corners.region k
      have hk₁ : (next k).1.1 ⊆ closure (ρ k) := hsec.corners.left k
      have hk₂ : k.1.1 ⊆ closure (ρ k) := by
        obtain ⟨k', rfl⟩ := hsurj k
        exact hsec.corners.right k'
      rcases hD.region_cases hrD with hhat | ⟨c₀, hc₀, h₃₀, hsubr⟩
      · obtain ⟨w, ⟨hwr, hwV⟩, -⟩ := rad.isPreRadial.2.2.1 _ hhat
        have hdis : Disjoint (ρ k) (Γ.hatU cap) := by
          obtain ⟨y, hy, hyr⟩ := hhat
          refine disjoint_left.mpr fun z hz hzU ↦ ?_
          rw [← hyr] at hz
          exact connectedComponentIn_subset (Γ.hatU cap)ᶜ y hz hzU
        have hwR : w ∈ rad.Rstar :=
          ⟨hwV, fun hc ↦ disjoint_left.mp hdis hwr (image_mono Γ.V_subset hc)⟩
        have hreg : rad.regionOf w = ρ k := by
          obtain ⟨y, hy, hyr⟩ := hhat
          change connectedComponentIn (Γ.hatU cap)ᶜ w = ρ k
          rw [← hyr] at hwr ⊢
          exact (connectedComponentIn_eq hwr).symm
        have hfr : ∀ j, j.1.1 ⊆ closure (ρ k) → cap.emb '' g j ⊆ frontier (rad.regionOf w) := by
          intro j hj
          rw [hgi, hreg, (GM11.region_isOpen hrD).frontier_eq]
          intro x hx
          refine ⟨hj hx, fun hxr ↦ GM11.region_subset hrD hxr ?_⟩
          exact D.closure_subset_U j.2.1 (subset_closure hx)
        have hcl : cap.emb v₀ ∈ closure (rad.regionOf w) := by
          rw [hreg]
          refine closure_minimal ?_ isClosed_closure (image_closure_subset_closure_image
            cap.isEmbedding.continuous (mem_image_of_mem _ (hgv k).1))
          rw [hgi]
          exact hk₂
        obtain ⟨e, he, hset⟩ := rad.exists_spoke hS h2 h3.1 hwR hv₀ hcl
        exact ht e he _ _ ⟨v₀, w, hv₀, hwR, hset, g k, g (next k), hgg, hgc k, hgc _, hgv k, hgv _,
          hfr k hk₂, hfr _ hk₁⟩
      · have hC : IsClosed (cap.emb '' closure c₀) :=
          (cap.isClosedEmbedding hS).isClosedMap _ isClosed_closure
        have hcl : closure (ρ k) ⊆ cap.emb '' closure c₀ := closure_minimal hsubr hC
        have hcell : ∀ j, j.1.1 ⊆ closure (ρ k) → cl j = c₀ := by
          intro j hj
          have hm := hgc j
          obtain ⟨x, hx⟩ := hm.mem.1
          obtain ⟨y, hy, hyx⟩ := hcl (hj (hgi j ▸ mem_image_of_mem _ hx))
          obtain rfl := cap.isEmbedding.injective hyx
          have hxc : y ∈ c₀ := by
            by_contra hn
            exact (hm.mem.2.1 hx).2 (Γ.tilde_subset_V hc₀ ⟨hy, hn⟩)
          exact arcComp_eq_of_mem hm.1 hc₀ (hm.subset hx) hxc
        rw [hcell k hk₂, hcell _ hk₁]
    intro a b
    have hre := hsec.corners.reach a b
    induction hre with
    | refl => exact Iff.rfl
    | tail _ h ih =>
      subst h
      exact ih.trans (hstep _)
  obtain ⟨f, hf, hvf⟩ := Γ.exists_sk_at hc hv
  obtain ⟨f', hf', hvf'⟩ := Γ.exists_sk_at hc' hv'
  obtain ⟨k, rfl⟩ := hfind f c hf hvf
  obtain ⟨k', rfl⟩ := hfind f' c' hf' hvf'
  exact hall k k'

/-- Each vertex of `Γ` is an end of an edge of `Γ`, since the regions of `sk(Γ)` in `Σ̂` are discs.
-/
theorem exists_edge_incident (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected)
    (rad : RadialDrawing cap Γ) {y : S} (hyV : y ∈ Γ.V) : ∃ c ∈ Γ.E, y ∈ closure c := by
  have hT := cap.isClosedSurface
  have : T2Space Shat := hT.2.1
  have : ConnectedSpace Shat := cap.connected
  have h2 := h3.hatRegions_isOpenDisc hS cap
  obtain ⟨D, W, hDU, hDV, hD2, -, hG'⟩ := Γ.exists_hubDrawing hS cap h2
  have hD : IsSkHat cap Γ D := ⟨hDU, hDV⟩
  have hvD : cap.emb y ∈ D.V := by
    rw [hDV]
    exact mem_image_of_mem _ hyV
  obtain ⟨G', hpreG, -⟩ := hG' rad.G rad.isPreRadial
  have hrad : GM11.PreRad (GM11.PaintingOrDrawing.drawing D) G' := ⟨hD2, hpreG⟩
  obtain ⟨e, he, hye⟩ := GM11.exists_edge_at hrad hT (hD.E_nonempty h3.1) hvD
  obtain ⟨f, hf, rfl⟩ := hD.edge_iff.mp he
  obtain ⟨c, hc⟩ := Γ.exists_isSkEdgeIn hf
  rw [(cap.isClosedEmbedding hS).closure_image_eq] at hye
  obtain ⟨y', hy', hyy⟩ := hye
  obtain rfl := cap.isEmbedding.injective hyy
  exact ⟨c, hc.1, closure_mono hc.subset hy'⟩

/-- **The pairs connect `E(Γ)`.** A property of edges of `Γ` that the pairs do not change holds for
all
edges or for none. If it held for some and not others, then by `vertex_step` the two sets of edges
have no common end, so they split `U(sk(Γ))` into two disjoint closed sets, and that set is
connected
because its regions in `Σ̂` are discs. -/
theorem edges_same (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected)
    (rad : RadialDrawing cap Γ) (t : Set S → Prop)
    (ht : ∀ e ∈ rad.G.E, ∀ c₁ c₂, rad.PairOf e c₁ c₂ → (t c₁ ↔ t c₂)) {c c' : Set S} (hc : c ∈ Γ.E)
    (hc' : c' ∈ Γ.E) : t c ↔ t c' := by
  classical
  have hT := cap.isClosedSurface
  have : T2Space Shat := hT.2.1
  have : ConnectedSpace Shat := cap.connected
  have h2 := h3.hatRegions_isOpenDisc hS cap
  obtain ⟨D, W, hDU, hDV, hD2, -, -⟩ := Γ.exists_hubDrawing hS cap h2
  have hnon : ∀ c ∈ Γ.E, (Γ.skU ∩ closure c).Nonempty := by
    intro c hc
    obtain ⟨x, hx⟩ := hc.1
    obtain ⟨f, hf, hv⟩ : ∃ f, Γ.IsSkEdgeIn f c ∧ True := by
      rcases Γ.size_cases hc with h2' | h3'
      · exact ⟨c, ⟨hc, Or.inl ⟨h2', rfl⟩⟩, trivial⟩
      · obtain ⟨hdisc, hT', hfin⟩ := Γ.isDisc_of_three hc h3'
        obtain ⟨a, b, z, hab, -, -, hset⟩ := Set.ncard_eq_three.mp h3'
        obtain ⟨f, hf, -⟩ := Γ.exists_sk_at hc (show a ∈ tilde c from hset ▸ Or.inl rfl)
        exact ⟨f, hf, trivial⟩
    obtain ⟨y, hy⟩ := hf.mem.1
    exact ⟨y, (hf.mem.2.1 hy).1, subset_closure (hf.subset hy)⟩
  have hvertex : ∀ y ∈ Γ.skU, ∃ c ∈ Γ.E, y ∈ Γ.skU ∩ closure c := by
    intro y hy
    by_cases hyV : y ∈ Γ.V
    · obtain ⟨c, hc, hyc⟩ := exists_edge_incident hS h3 rad hyV
      exact ⟨c, hc, hy, hyc⟩
    · obtain ⟨f, hf, hyf⟩ := exists_arcComp_superset (F := Γ.skU \ Γ.V)
        (isPathConnected_singleton y) (singleton_subset_iff.2 ⟨hy, hyV⟩)
      obtain ⟨c, hc⟩ := Γ.exists_isSkEdgeIn hf
      exact ⟨c, hc.1, hy, subset_closure (hc.subset (hyf rfl))⟩
  let C₁ : Set Shat := cap.emb '' (⋃ c ∈ {c ∈ Γ.E | t c}, Γ.skU ∩ closure c)
  let C₂ : Set Shat := cap.emb '' (⋃ c ∈ {c ∈ Γ.E | ¬ t c}, Γ.skU ∩ closure c)
  have hcl : ∀ X : Set (Set S), X ⊆ Γ.E → IsClosed (cap.emb '' (⋃ c ∈ X, Γ.skU ∩ closure c)) := by
    intro X hX
    refine (cap.isClosedEmbedding hS).isClosedMap _ ?_
    exact (Γ.finite_edges.subset hX).isClosed_biUnion fun c _ ↦ Γ.isClosed_skU.inter
      isClosed_closure
  have hdis : Disjoint C₁ C₂ := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨x', hx', hxx⟩
    obtain rfl : x = x' := (cap.isEmbedding.injective hxx).symm
    obtain ⟨a, ⟨haE, hta⟩, -, hxa⟩ := mem_iUnion₂.mp hx
    obtain ⟨b, ⟨hbE, htb⟩, -, hxb⟩ := mem_iUnion₂.mp hx'
    have hab : a ≠ b := fun h ↦ htb (h ▸ hta)
    have hsplit : ∀ {a b : Set S}, a ∈ Γ.E → b ∈ Γ.E → a ≠ b → x ∈ closure a → x ∈ closure b →
        x ∉ a := by
      intro a b ha hb hne hxa hxb hxin
      rcases Γ.closure_subset hb hxb with h | h
      · exact hne (arcComp_eq_of_mem ha hb hxin h)
      · exact Γ.disjoint_V ha hxin h
    have hna := hsplit haE hbE hab hxa hxb
    have hnb := hsplit hbE haE hab.symm hxb hxa
    have hxV : x ∈ Γ.V := Γ.tilde_subset_V haE ⟨hxa, hna⟩
    exact htb ((vertex_step hS h3 rad t ht hxV haE hbE ⟨hxa, hna⟩ ⟨hxb, hnb⟩).mp hta)
  have hU : C₁ ∪ C₂ = D.U := by
    rw [hDU]
    apply Subset.antisymm
    · rintro _ (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · obtain ⟨a, -, ha, -⟩ := mem_iUnion₂.mp hx
        exact mem_image_of_mem _ ha
      · obtain ⟨a, -, ha, -⟩ := mem_iUnion₂.mp hx
        exact mem_image_of_mem _ ha
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨a, ha, hya⟩ := hvertex y hy
      by_cases hta : t a
      · exact Or.inl ⟨y, mem_iUnion₂.mpr ⟨a, ⟨ha, hta⟩, hya⟩, rfl⟩
      · exact Or.inr ⟨y, mem_iUnion₂.mpr ⟨a, ⟨ha, hta⟩, hya⟩, rfl⟩
  have key : ∀ a ∈ Γ.E, ∀ b ∈ Γ.E, t a → t b := by
    intro a ha b hb hta
    by_contra htb
    obtain ⟨x, hx⟩ := hnon a ha
    obtain ⟨y, hy⟩ := hnon b hb
    have hne : C₁.Nonempty := ⟨_, x, mem_iUnion₂.mpr ⟨a, ⟨ha, hta⟩, hx⟩, rfl⟩
    have hcl₁ : IsClosed C₁ := hcl {c ∈ Γ.E | t c} fun _ h => h.1
    have hcl₂ : IsClosed C₂ := hcl {c ∈ Γ.E | ¬t c} fun _ h => h.1
    have hempty := GM11.eq_empty_of_split hT hD2.2 hcl₁ hcl₂ hdis hU hne
    have hmem : cap.emb y ∈ C₂ := ⟨y, mem_iUnion₂.mpr ⟨b, ⟨hb, htb⟩, hy⟩, rfl⟩
    have hC₂ : C₂ = ∅ := hempty
    rw [hC₂] at hmem
    exact hmem
  exact ⟨key c hc c' hc', key c' hc' c hc⟩

end Pairs

end GraphMinor.GM19
