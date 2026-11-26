/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FragmentCut

/-!
# The fragments of a non-null-homotopic feature are simpler

We prove the step of (5.5), Graph Minors XIX, page 339. Let `K` lie in an `O`-arc `F` of `Σ̂` that
is not null-homotopic. We collapse each
pasted disc of `Σ̂` to a point. The image `F'` of `F` is an `O`-arc, and it is not null-homotopic,
since the collapse is homotopic to the
identity. Each piece of `Σ̂` cut along `F'` is simpler than `Σ̂`, by `exists_cut_simpler`. The
inside of a fragment is, up to a finite set,
the inside of such a piece. So its capping is the capping of the piece (`simpler_of_piece`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

variable {T : Type} [TopologicalSpace T] [T2Space T]

omit [T2Space T] in
/-- If a map homotopic to the identity carries the `O`-arc `F` onto a null-homotopic `O`-arc, then
`F` is null-homotopic. -/
theorem null_of_homotopic {c : C(T, T)} (hc : c.Homotopic (ContinuousMap.id T)) {F F' : Set T}
  (hF : IsOArc F) (hF' : c '' F = F')
    (hn : IsNullHomotopicOArc F') : IsNullHomotopicOArc F := by
  obtain ⟨φ⟩ := hF
  obtain ⟨φ', p, -, H, -, h0, h1⟩ := hn
  let l : C(Circle, T) := ⟨fun x ↦ (φ x).1, continuous_subtype_val.comp φ.continuous⟩
  have hmem : ∀ x, c (l x) ∈ F' := fun x ↦ hF' ▸ mem_image_of_mem _ (φ x).2
  let m : C(Circle, Circle) := ⟨fun x ↦ φ'.symm ⟨c (l x), hmem x⟩, φ'.symm.continuous.comp
    (Continuous.subtype_mk (by fun_prop) _)⟩
  have hm : ∀ x, (φ' (m x)).1 = c (l x) := fun x ↦ by
    change (φ' (φ'.symm _)).1 = _
    rw [φ'.apply_symm_apply]
  have h₁ : (ContinuousMap.id T).comp l |>.Homotopic (c.comp l) := (hc.symm).comp
    (ContinuousMap.Homotopic.refl l)
  let G : ContinuousMap.Homotopy (c.comp l) (ContinuousMap.const Circle p) :=
    { toFun := fun q ↦ H (m q.2, q.1)
      continuous_toFun := by fun_prop
      map_zero_left := fun x ↦ by
        change H (m x, 0) = c (l x)
        rw [h0]
        exact hm x
      map_one_left := fun x ↦ by
        change H (m x, 1) = p
        rw [h1]
        rfl }
  obtain ⟨G'⟩ := h₁.trans ⟨G⟩
  refine ⟨φ, p, mem_univ _, ⟨⟨fun q ↦ G' (q.2, q.1), by fun_prop⟩, fun _ ↦ mem_univ _,
    fun x ↦ ?_, fun x ↦ ?_⟩⟩
  · exact G'.apply_zero x
  · exact G'.apply_one x

theorem isOArc_of_injective_range {f : Circle → T} (hf : Continuous f)
  (hi : Function.Injective f) : IsOArc (range f) :=
  ⟨(hf.isClosedEmbedding hi).isEmbedding.toHomeomorph⟩

/-- A one to one map on an `O`-arc gives an `O`-arc. -/
theorem isOArc_image_injOn {c : T → T} (hc : Continuous c) {F : Set T} (hF : IsOArc F)
  (hi : InjOn c F) : IsOArc (c '' F) := by
  obtain ⟨φ⟩ := hF
  have : c '' F = range fun x ↦ c (φ x).1 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨φ.symm ⟨y, hy⟩, by simp⟩
    · rintro ⟨z, rfl⟩
      exact mem_image_of_mem _ (φ z).2
  rw [this]
  exact isOArc_of_injective_range (by fun_prop) fun x y he ↦ φ.injective (Subtype.ext (hi (φ x).2
    (φ y).2 he))

/-- A map on a line that is one to one, except that the two ends go to one point, gives an `O`-arc.
-/
theorem isOArc_image_line {c : T → T} (hc : Continuous c) {L : Set T} {a b : T}
  (hl : IsLineWithEnds L a b) (hab : c a = c b)
    (hi : ∀ x ∈ L, ∀ y ∈ L, c x = c y → x = y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a)) : IsOArc
      (c '' L) := by
  obtain ⟨f, h0, h1⟩ := id hl
  have hane : a ≠ b := hl.ne'
  let x : T := (f (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)).1
  have hxL : x ∈ L := (f _).2
  have hne : ∀ {r : unitInterval}, r ≠ ⟨1 / 2, by norm_num, by norm_num⟩ → (f r).1 ≠ x
    := fun hr he ↦ hr (f.injective (Subtype.ext he))
  have hxa : x ≠ a := fun he ↦ hne (r := 0) (fun h ↦ by have := congrArg Subtype.val h; norm_num
    at this) (h0.trans he.symm)
  have hxb : x ≠ b := fun he ↦ hne (r := 1) (fun h ↦ by have := congrArg Subtype.val h; norm_num
    at this) (h1.trans he.symm)
  obtain ⟨L₁, L₂, hL₁, hL₂, hun, hint⟩ := hl.split hxL hxa hxb
  have hnotb : b ∉ L₁ := fun h ↦ hxb (by
    have : b ∈ L₁ ∩ L₂ := ⟨h, hL₂.right_mem⟩
    rw [hint] at this
    exact this.symm)
  have hnota : a ∉ L₂ := fun h ↦ hxa (by
    have : a ∈ L₁ ∩ L₂ := ⟨hL₁.left_mem, h⟩
    rw [hint] at this
    exact this.symm)
  have hs₁ : L₁ ⊆ L := hun ▸ subset_union_left
  have hs₂ : L₂ ⊆ L := hun ▸ subset_union_right
  obtain ⟨u, hu, hur, hu0, hu1⟩ := hL₁.exists_arc
  obtain ⟨v, hv, hvr, hv0, hv1⟩ := hL₂.symm.exists_arc
  have huL : ∀ s, u s ∈ L₁ := fun s ↦ hur ▸ mem_range_self s
  have hvL : ∀ s, v s ∈ L₂ := fun s ↦ hvr ▸ mem_range_self s
  have hcu : InjOn c L₁ := fun p hp q hq he ↦ by
    rcases hi p (hs₁ hp) q (hs₁ hq) he with h | ⟨-, rfl⟩ | ⟨rfl, -⟩
    · exact h
    · exact absurd hq hnotb
    · exact absurd hp hnotb
  have hcv : InjOn c L₂ := fun p hp q hq he ↦ by
    rcases hi p (hs₂ hp) q (hs₂ hq) he with h | ⟨rfl, -⟩ | ⟨-, rfl⟩
    · exact h
    · exact absurd hp hnota
    · exact absurd hq hnota
  have ha₁ : IsArcMap (c ∘ u) := ⟨hc.comp hu.1, fun s t he ↦ hu.2 (hcu (huL s) (huL t) he)⟩
  have ha₂ : IsArcMap (c ∘ v) := ⟨hc.comp hv.1, fun s t he ↦ hv.2 (hcv (hvL s) (hvL t) he)⟩
  have hO := oArc_of_two_arcs ha₁ ha₂ (by simp [hu0, hv0, hab]) (by simp [hu1, hv1]) (by
    intro s t he
    have he' : c (u s) = c (v t) := he
    rcases hi _ (hs₁ (huL s)) _ (hs₂ (hvL t)) he' with h | ⟨h, h'⟩ | ⟨h, -⟩
    · have : u s ∈ L₁ ∩ L₂ := ⟨huL s, h ▸ hvL t⟩
      rw [hint] at this
      have h₁ : s = 1 := hu.2 (by rw [hu1]; exact this)
      have h₂ : t = 1 := hv.2 (by rw [hv1, ← h]; exact this)
      exact Or.inr ⟨h₁, h₂⟩
    · exact Or.inl ⟨hu.2 (by rw [h, hu0]), hv.2 (by rw [h', hv0])⟩
    · exact absurd (h ▸ huL s) hnotb)
  have heq : c '' L = range (c ∘ u) ∪ range (c ∘ v) := by
    rw [← hun, image_union, range_comp, range_comp, hur, hvr]
  rw [heq]
  exact hO

section Piece

variable {S Shat Y : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  [TopologicalSpace Y]
  [T2Space Y] {ψ : Y → S} {K : Drawing S}

omit [T2Space Y] in
/-- A capped fragment is the capping of a piece of `Σ̂` cut along `F'`, so it is simpler than `Σ̂`.
-/
theorem simpler_of_piece (hS : IsSurface S) (cap : IsCappedSurface S Shat) (hY : IsSurface Y)
  (hψ : IsCutMap ψ K.U) {c₀ : C(Shat, Shat)}
    {P₀ F' : Set Shat} (hc : IsCollapse c₀ cap.discs P₀) {S' : Type} [TopologicalSpace S'] (ψ' : S'
      → Shat) (hS' : IsSurface S')
    (hF'c : IsClosed F') (hcut : IsCutMap ψ' F') (hKF : ∀ x ∈ K.U, c₀ (cap.emb x) ∈ F')
      (hoff : ∀ x, x ∉ cap.discs ∪ cap.emb '' K.U → c₀ x ∉ F')
    (hsimple : ∀ C ∈ spaceComponents S', IsSimplerThan C Shat) (y : Y)
      (Shat₁ : Type) [TopologicalSpace Shat₁]
    (cap₁ : IsCappedSurface (connectedComponent y) Shat₁) : IsSimplerThan Shat₁ Shat := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have : CompactSpace Shat := hT.1
  have : CompactSpace Y := hY.1
  have : CompactSpace S' := hS'.1
  have : T2Space S' := hS'.2.1
  have : LocallyConnectedSpace S' := hS'.locallyConnected
  have : LocallyConnectedSpace Y := hY.locallyConnected
  have : Nonempty Shat := inferInstance
  have : CompactSpace S := hS.1
  have hbT : bd Shat = ∅ := cap.bd_empty
  have hbS' : ∀ {z : S'}, z ∈ bd S' → ψ' z ∈ F' := fun {z} hz ↦ by
    by_contra hn
    have := bd_of_bd_cutMap hcut hF'c hz hn
    rw [hbT] at this
    exact this
  have hF'S : ∀ {z : S'}, ψ' z ∈ F' → z ∈ bd S' := fun h ↦ hcut.2.2.2.2 h
  obtain ⟨y', hy'c, hy'i⟩ : ∃ y', y' ∈ connectedComponent y ∧ y' ∈ (bd Y)ᶜ := by
    obtain ⟨z, hz, hz'⟩ := (dense_interior' hY).inter_open_nonempty _ isOpen_connectedComponent ⟨y,
      mem_connectedComponent⟩
    exact ⟨z, hz, hz'⟩
  have hxK : ψ y' ∉ K.U := fun h ↦ hy'i (hψ.2.2.2.2 h)
  have hint' : IsInteriorPoint y' := by
    by_contra h
    exact hy'i h
  have hxb : ψ y' ∉ bd S := fun h ↦ h (isInteriorPoint_image hψ K.isClosed_U hint' hxK)
  have hxd : cap.emb (ψ y') ∉ cap.discs := fun h ↦ by
    have hc' : cap.emb (ψ y') ∈ cap.discsᶜ := by
      rw [show cap.discsᶜ = _ from cap.compl_eq_image]
      exact mem_image_of_mem _ hxb
    exact hc' h
  have hxZ : cap.emb (ψ y') ∉ cap.discs ∪ cap.emb '' K.U := by
    rintro (h | ⟨z, hz, he⟩)
    · exact hxd h
    · exact hxK (cap.isEmbedding.injective he ▸ hz)
  obtain ⟨w, hw⟩ := hcut.2.1 (c₀ (cap.emb (ψ y')))
  set C := connectedComponent w with hC
  have hCo : IsOpen C := isOpen_connectedComponent
  have hCcl : IsClopen C := ⟨isClosed_connectedComponent, hCo⟩
  have hCs : IsSurface C := isSurface_sub hS' hCcl
  have : ConnectedSpace C := Subtype.connectedSpace isConnected_connectedComponent
  have : T2Space C := inferInstance
  obtain ⟨CHat, _, ⟨capC⟩⟩ := exists_cappedSurface _ C hCs inferInstance rfl
  have : T2Space CHat := capC.isSurface.2.1
  have : ConnectedSpace CHat := capC.connected
  obtain ⟨eC, Q, hQ, hsC, htC, -⟩ := exists_cap_chart hCs capC
  have hbdC : ∀ {x : C}, x ∉ bd C → ψ' x.1 ∉ F' := fun {x} hx h ↦ hx ((mem_bd_sub hCo).2 (hF'S h))
  have hbdo : IsOpen (bd C)ᶜ := (cuff_statement C hCs).1.isOpen_compl
  obtain ⟨g, hgs, hgt, hgf⟩ := exists_oph (f := fun x : C ↦ ψ' x.1) (s := (bd C)ᶜ) (t :=
    (fun x : C ↦ ψ' x.1) '' (bd C)ᶜ) hbdo
    (hcut.1.comp continuous_subtype_val).continuousOn
    (fun a ha b hb he ↦ Subtype.ext (hcut.2.2.1 (hbdC ha) (hbdC hb) he))
    (fun u hu huo ↦ by
      have : (fun x : C ↦ ψ' x.1) '' u = ψ' '' (Subtype.val '' u) := by rw [image_image]
      rw [this]
      refine isOpen_image_of_isCutMap hcut ?_ (hCo.isOpenMap_subtype_val _ huo)
      rintro _ ⟨v, hv, rfl⟩
      exact hbdC (hu hv)) rfl
  set R := (fun x : C ↦ ψ' x.1) '' (bd C)ᶜ with hR
  have hRF : Disjoint R F' := disjoint_left.2 fun x ⟨v, hv, he⟩ hxF ↦ hbdC hv (by
    have h : ψ' v.1 = x := he
    rw [h]
    exact hxF)
  let d : OpenPartialHomeomorph Shat CHat := g.symm.trans' eC (by simp [hgs, hsC])
  have hds : d.source = R := by simp [d, hgt]
  have hdt : d.target = Qᶜ := by simp [d, htC]
  obtain ⟨e₀, hs₀, ht₀, he₀⟩ := hc.exists_oph
  let E : OpenPartialHomeomorph Shat CHat := e₀.trans d
  have hEs : ∀ x, x ∈ E.source ↔ x ∉ cap.discs ∧ c₀ x ∈ R := fun x ↦ by
    change x ∈ e₀.source ∩ e₀ ⁻¹' d.source ↔ _
    rw [hs₀, hds]
    constructor
    · rintro ⟨h, h'⟩
      exact ⟨h, he₀ h ▸ h'⟩
    · rintro ⟨h, h'⟩
      exact ⟨h, by rw [mem_preimage, he₀ h]; exact h'⟩
  set P : Set CHat := Q ∪ d '' (P₀ ∩ R) with hP
  have hPf : P.Finite := hQ.union ((hc.finite.subset inter_subset_left).image _)
  have hEt : E.target = Pᶜ := by
    ext z
    change z ∈ d.target ∩ d.symm ⁻¹' e₀.target ↔ _
    rw [hdt, ht₀, hP]
    constructor
    · rintro ⟨hz, hzP⟩ (h | ⟨u, hu, rfl⟩)
      · exact hz h
      · apply hzP
        rw [d.left_inv (hds ▸ hu.2)]
        exact hu.1
    · intro hz
      have hzQ : z ∉ Q := fun h ↦ hz (Or.inl h)
      refine ⟨hzQ, fun hzP ↦ hz (Or.inr ⟨d.symm z, ⟨hzP, ?_⟩, d.right_inv (hdt ▸ hzQ)⟩)⟩
      have := d.map_target (hdt ▸ hzQ : z ∈ d.target)
      rwa [hds] at this
  have hsub : cap.discs ∪ cap.emb '' K.U ⊆ E.sourceᶜ := by
    rintro x (hx | ⟨z, hz, rfl⟩) hxs
    · exact ((hEs x).1 hxs).1 hx
    · exact disjoint_left.1 hRF ((hEs _).1 hxs).2 (hKF z hz)
  have hdc : IsClosed cap.discs := (cuff_statement S hS).2.1.isClosed_biUnion fun _ _ ↦
    isClosed_closure
  have hKc : IsClosed (cap.emb '' K.U) := (K.isClosed_U.isCompact.image
    cap.isEmbedding.continuous).isClosed
  have hop : IsOpen (E.sourceᶜ \ (cap.discs ∪ cap.emb '' K.U)) := by
    set W := ψ' '' (Cᶜ ∩ (bd S')ᶜ) with hWdef
    have hWo : IsOpen W := isOpen_image_of_isCutMap hcut (fun z hz h ↦ hz.2 (hF'S h))
      (hCcl.compl.isOpen.inter (cuff_statement S' hS').1.isOpen_compl)
    have : E.sourceᶜ \ (cap.discs ∪ cap.emb '' K.U) = (cap.discs ∪ cap.emb '' K.U)ᶜ ∩ c₀ ⁻¹' W := by
      ext x
      constructor
      · rintro ⟨hx, hxZ'⟩
        refine ⟨hxZ', ?_⟩
        obtain ⟨v, hv⟩ := hcut.2.1 (c₀ x)
        have hvb : v ∉ bd S' := fun h ↦ hoff x hxZ' (hv ▸ hbS' h)
        refine ⟨v, ⟨fun hvC ↦ hx ((hEs x).2 ⟨fun h ↦ hxZ' (Or.inl h), ?_⟩), hvb⟩, hv⟩
        exact ⟨⟨v, hvC⟩, fun h ↦ hvb ((mem_bd_sub hCo).1 h), hv⟩
      · rintro ⟨hxZ', v, ⟨hvC, hvb⟩, hv⟩
        refine ⟨fun hxs ↦ ?_, hxZ'⟩
        obtain ⟨u, hu, hue⟩ := ((hEs x).1 hxs).2
        have hnF : ψ' v ∉ F' := hv ▸ hoff x hxZ'
        have heq : u.1 = v := hcut.2.2.1 (hbdC hu) hnF (hue.trans hv.symm)
        exact hvC (heq ▸ u.2)
    rw [this]
    exact (hdc.union hKc).isOpen_compl.inter (hWo.preimage c₀.continuous)
  obtain ⟨y₁, hy₁, hcap, -, -⟩ := exists_fragment_of_region hS cap hY hψ capC.isClosedSurface hPf E
    (compl_compl _).symm hEt hsub hop
  have hxsrc : cap.emb (ψ y') ∈ E.sourceᶜᶜ := by
    rw [compl_compl, hEs]
    refine ⟨hxd, ⟨w, mem_connectedComponent⟩, fun h ↦ ?_, hw⟩
    have := hbS' ((mem_bd_sub hCo).1 h)
    change ψ' w ∈ F' at this
    rw [hw] at this
    exact hoff _ hxZ this
  have hxin : ψ y' ∈ ψ '' connectedComponent y₁ := by
    rw [hy₁]
    exact subset_closure hxsrc
  obtain ⟨y₂, hy₂, he⟩ := hxin
  have hy₂e : y₂ = y' := hψ.2.2.1 (show ψ y₂ ∈ K.Uᶜ by rw [he]; exact hxK) hxK he
  have hcomp : connectedComponent y = connectedComponent y₁ := by
    rw [connectedComponent_eq hy'c]
    exact (connectedComponent_eq (hy₂e ▸ hy₂)).symm
  obtain ⟨f⟩ := hcap Shat₁ (hcomp ▸ cap₁)
  have hCmem : C ∈ spaceComponents S' := by
    rw [spaceComponents_eq]
    exact ⟨w, rfl⟩
  obtain ⟨a, b, c, a', b', c', ⟨e₁⟩, ⟨e₂⟩, h1, h2, h3⟩ := hsimple C hCmem
  have hc' : c' = 0 := by
    have := numCuffs_eq e₂
    rw [numCuffs_model] at this
    rw [← this, numCuffs, cuffs, hbT]
    simp [componentsIn]
  subst hc'
  obtain ⟨f'⟩ := capModel a b c CHat (capC.ofHomeo e₁.symm)
  exact ⟨a, b, 0, a', b', 0, ⟨f.trans f'⟩, ⟨e₂⟩, h1, h2, by omega⟩

end Piece

/-- **The step of the proof of (5.5)**, Graph Minors XIX, page 339: "For each fragment $\Sigma_1$
say, $\hat{\Sigma}_1$ is simpler than $\hat{\Sigma}_\chi$ because $U(F)$ is non-null-homotopic in
$\hat{\Sigma}$". -/
theorem cutSimpler : CutSimplerStatement := by
  classical
  intro S Shat _ _ _ _ cap K hS hlines hKne hKbd ⟨F, hF, hnull, hf⟩
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hfc : (cuffs S).Finite := (cuff_statement S hS).2.1
  have hSne : Nonempty S := by
    rcases hf with ⟨-, hO, -⟩ | ⟨s, -⟩
    · obtain ⟨φ⟩ := hO
      exact ⟨(φ 1).1⟩
    · exact ⟨s⟩
  have : ConnectedSpace S := by
    have h := (cap.isPreconnected_compl hfc subset_rfl).2
    rw [cap.compl_eq_image, cap.isEmbedding.isInducing.isPreconnected_image] at h
    have hc := h.closure
    rw [(dense_interior' hS).closure_eq] at hc
    exact { toPreconnectedSpace := ⟨hc⟩, toNonempty := hSne }
  let E : Set S → Set Shat := fun Θ ↦ closure (cap.cuffDisc Θ)
  have hdisj : (E '' cuffs S).PairwiseDisjoint id := by
    rintro _ ⟨Θ₁, h₁, rfl⟩ _ ⟨Θ₂, h₂, rfl⟩ hn
    exact cap.cuffDisc_disjoint Θ₁ h₁ Θ₂ h₂ fun h ↦ hn (h ▸ rfl)
  obtain ⟨c₀, P₀, q, hc, hq, -, hqi⟩ := exists_collapse hT (hfc.image E)
    (by rintro _ ⟨Θ, hΘ, rfl⟩; exact cap.cuffDisc_closedDisc Θ hΘ) hdisj
  have hUn : ⋃₀ (E '' cuffs S) = cap.discs := sUnion_image _ _
  rw [hUn] at hc
  have hsame : ∀ {x y}, c₀ x = c₀ y → x ≠ y → ∃ Θ ∈ cuffs S, x ∈ closure (cap.cuffDisc Θ)
    ∧ y ∈ closure (cap.cuffDisc Θ) := by
    intro x y he hne
    have hx : x ∈ cap.discs := by
      by_contra hx
      have hy : y ∉ cap.discs := fun hy ↦ hx (hc.preimage (by
        rw [mem_preimage, he]
        exact hc.mapsTo hy))
      exact hne (hc.injOn hx hy he)
    have hy : y ∈ cap.discs := hc.preimage (by rw [mem_preimage, ← he]; exact hc.mapsTo hx)
    obtain ⟨Θ₁, h₁, hx₁⟩ := mem_iUnion₂.1 hx
    obtain ⟨Θ₂, h₂, hy₂⟩ := mem_iUnion₂.1 hy
    have hE : E Θ₁ = E Θ₂ := hqi (mem_image_of_mem _ h₁) (mem_image_of_mem _ h₂) (by
      rw [← hq _ (mem_image_of_mem _ h₁) x hx₁, ← hq _ (mem_image_of_mem _ h₂) y hy₂, he])
    have hy₃ : y ∈ E Θ₂ := hy₂
    rw [← hE] at hy₃
    exact ⟨Θ₁, h₁, hx₁, hy₃⟩
  have hFdata : cap.emb '' K.U ⊆ F ∧ F ⊆ cap.discs ∪ cap.emb '' K.U ∧ IsOArc (c₀ '' F) ∧
      ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : T2Space Y) (ψ : Y → S), IsSurface Y
        ∧ IsCutMap ψ K.U ∧ HasSheets ψ K := by
    rcases hf with ⟨rfl, hO, hsing⟩ | ⟨s, t, Θ, hΘ, hst, hs, ht, hKb, hl, hsub, hrest⟩
    · refine ⟨Subset.rfl, subset_union_right, isOArc_image_injOn c₀.continuous hF ?_, ?_⟩
      · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ he
        by_contra hne
        obtain ⟨Θ, hΘ, h₁, h₂⟩ := hsame he hne
        rw [hsing ⟨ha, cap.bd_of_mem hΘ h₁⟩ ⟨hb, cap.bd_of_mem hΘ h₂⟩] at hne
        exact hne rfl
      · obtain ⟨Y, tY, t2, ψ, h₁, h₂, h₃⟩ := exists_cut_drawing (𝓐 := cuffs S ∪ {K.U}) (𝓛
        := ∅) hS hlines hKbd hKne
          (isCutFrame_of hS (finite_singleton _) finite_empty (fun C hC ↦ hC ▸ hO)
            (fun L hL ↦ absurd hL (notMem_empty L)))
          (by simp [sUnion_cuffs, union_comm])
        exact ⟨Y, tY, t2, ψ, h₁, h₂, h₃⟩
    · have hE := cap.mem_closure_emb hΘ hs
      have hE' := cap.mem_closure_emb hΘ ht
      have hline := hl.map_of_embedding cap.isEmbedding
      have hab : c₀ (cap.emb s) = c₀ (cap.emb t) := by
        rw [hq _ (mem_image_of_mem _ hΘ) _ hE, hq _ (mem_image_of_mem _ hΘ) _ hE']
      have himg : c₀ '' F = c₀ '' (cap.emb '' K.U) := by
        apply Subset.antisymm
        · rintro _ ⟨x, hx, rfl⟩
          by_cases hxK : x ∈ cap.emb '' K.U
          · exact mem_image_of_mem _ hxK
          · have hxE : x ∈ closure (cap.cuffDisc Θ) := subset_closure (hrest ⟨hx, hxK⟩)
            refine ⟨cap.emb s, mem_image_of_mem _ hl.left_mem, ?_⟩
            rw [hq _ (mem_image_of_mem _ hΘ) _ hE, hq _ (mem_image_of_mem _ hΘ) _ hxE]
        · exact image_mono hsub
      refine ⟨hsub, fun x hx ↦ ?_, ?_, ?_⟩
      · by_cases hxK : x ∈ cap.emb '' K.U
        · exact Or.inr hxK
        · exact Or.inl (mem_biUnion hΘ (subset_closure (hrest ⟨hx, hxK⟩)))
      · rw [himg]
        refine isOArc_image_line c₀.continuous hline hab ?_
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ he
        by_cases hne : cap.emb a = cap.emb b
        · exact Or.inl hne
        · obtain ⟨Θ', hΘ', h₁, h₂⟩ := hsame he hne
          have hma : a ∈ K.U ∩ bd S := ⟨ha, cap.bd_of_mem hΘ' h₁⟩
          have hmb : b ∈ K.U ∩ bd S := ⟨hb, cap.bd_of_mem hΘ' h₂⟩
          rw [hKb] at hma hmb
          rcases hma with rfl | hma <;> rcases hmb with rfl | hmb
          · exact absurd rfl hne
          · exact Or.inr (Or.inl ⟨rfl, by rw [mem_singleton_iff.1 hmb]⟩)
          · exact Or.inr (Or.inr ⟨by rw [mem_singleton_iff.1 hma], rfl⟩)
          · rw [mem_singleton_iff.1 hma, mem_singleton_iff.1 hmb] at hne
            exact absurd rfl hne
      · obtain ⟨Y, tY, t2, ψ, h₁, h₂, h₃⟩ := exists_cut_drawing (𝓐 := cuffs S ∪ ∅) (𝓛
        := {K.U}) hS hlines hKbd hKne
          (isCutFrame_of hS finite_empty (finite_singleton _) (fun C hC ↦ absurd hC
            (notMem_empty C))
            (fun L hL ↦ ⟨s, t, hst, hL ▸ hl, Or.inl (cuff_subset_bd ⟨Θ, hΘ⟩ hs), Or.inl
              (cuff_subset_bd ⟨Θ, hΘ⟩ ht)⟩))
          (by simp [sUnion_cuffs])
        exact ⟨Y, tY, t2, ψ, h₁, h₂, h₃⟩
  obtain ⟨hKF, hFsub, hF'O, Y, tY, t2, ψ, hY, hψ, hsheet⟩ := hFdata
  have hnn : ¬ IsNullHomotopicOArc (c₀ '' F) := fun h ↦ hnull (null_of_homotopic hc.homotopic hF
    rfl h)
  obtain ⟨S', tS', ψ', hS', hcut, hsimple⟩ := exists_cut_simpler hT hF'O hnn
  refine ⟨Y, tY, t2, ψ, hY, hψ, hsheet, fun y Shat₁ _ cap₁ ↦ ?_⟩
  refine simpler_of_piece hS cap hY hψ hc ψ' hS' hF'O.isCompact.isClosed (IsCutting.isCutMap hcut)
    (fun x hx ↦ mem_image_of_mem _ (hKF (mem_image_of_mem _ hx))) (fun x hx hxF ↦ ?_) hsimple y
      Shat₁ cap₁
  obtain ⟨f, hf', he⟩ := hxF
  by_cases hxf : f = x
  · exact hx (hxf ▸ hFsub hf')
  · obtain ⟨Θ, hΘ, -, h₂⟩ := hsame he hxf
    exact hx (Or.inl (mem_biUnion hΘ h₂))

end GraphMinor.GM19
