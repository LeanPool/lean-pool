/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CapMap
public import LeanPool.GraphMinor.GM07.Slit
public import LeanPool.GraphMinor.GM07.Open
import LeanPool.GraphMinor.GM19.Section6a

/-!
# What cutting along an edge does

Let `φ : Y → S` cut `S` along the closure of an edge `e` of `G`, and let `G'` be the graph left on
`Y`. This file holds the
facts that (7.1) and (7.2) share. A `G'`-normal set `A` that meets the new cuff only in vertices is
carried by `φ` one to one
to a `G`-normal set with the same number of vertices (`IsCutAlongEdge.image_facts`). Every
`G'`-normal set can be brought to this
form by a map homotopic to the identity (`IsCutAlongEdge.exists_push`). A closed disc that misses
`e` lifts to `Y`
(`IsCutAlongEdge.isClosedDisc_preimage`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Metric GraphMinor.Surface GraphMinor.GM11

universe u

local notation "𝕀" => unitInterval

variable {S Y : Type u} [TopologicalSpace S] [TopologicalSpace Y]

/-- A surface with a model other than `Σ(0, 0, 0)` is not a sphere. -/
theorem not_isSphere_of_model {T : Type u} [TopologicalSpace T] {a b c : ℕ} (h : Nonempty
  (T ≃ₜ SurfaceModel a b c))
    (hne : ¬ (a = 0 ∧ b = 0 ∧ c = 0)) : ¬ IsSphere T := by
  intro hs
  obtain ⟨e⟩ := h
  obtain ⟨e_s⟩ := id hs
  obtain ⟨e_m⟩ := GraphMinor.GM19.isSphere_model
  have hcrit := (modelCriterion.2 a b c 0 0 0).mp ⟨e.symm.trans (e_s.trans e_m.symm)⟩
  have hb : b = 0 := hcrit.2.2.mpr rfl
  omega

/-- A map homotopic to the identity keeps a set that is not planar not planar. -/
theorem planar_of_push (hY : IsSurface Y) [ConnectedSpace Y] {H : 𝕀 × Y → Y} (hH : Continuous H)
  (h0 : ∀ y, H (0, y) = y)
    {X : Set Y} (hX : IsSolid X) (hne : ¬ IsSphere Y ∨ X ≠ univ) (hp : IsPlanar ((fun y => H
      (1, y)) '' X)) : IsPlanar X := by
  have : CompactSpace Y := hY.1
  have : T2Space Y := hY.2.1
  obtain ⟨Δ, hΔ, hs⟩ := hp
  have h := isPlanar_of_homotopy hY (j := id) IsEmbedding.id hX (by simpa using hne) hH h0
    fun F _ hF => ⟨Δ, hΔ, fun y hy => hs (mem_image_of_mem _ (hF hy))⟩
  simpa using h

/-- The inner part of a pasted disc misses the surface. -/
theorem IsCappedCuff.image_ne_univ {T : Type u} [TopologicalSpace T] {C : Set Y} {j : Y
  → T} {D : Set T}
    (hc : IsCappedCuff C T j D) (X : Set Y) : j '' X ≠ univ := by
  intro he
  have : T2Space T := hc.isSurface.2.1
  obtain ⟨hh, g, cc⟩ := hc.isClosedDisc.exists_isChart
  have h1 : g 0 ∈ discInt D := by
    rw [discInt, mem_sdiff]
    refine ⟨cc.gm (by simp), fun hb => ?_⟩
    have h2 : hh (g 0) ∈ sphere (0 : ℂ) 1 := cc.bd ▸ mem_image_of_mem hh hb
    rw [cc.hg (by simp)] at h2
    simp at h2
  have h2 : g 0 ∈ j '' X := he ▸ mem_univ _
  obtain ⟨y, -, hy⟩ := h2
  have h3 : g 0 ∈ range j ∩ D := ⟨⟨y, hy⟩, h1.1⟩
  rw [hc.inter_eq, ← hc.discBd_eq] at h3
  exact h1.2 h3

/-- The same in a surface with a disc pasted on a cuff. -/
theorem planarCap_of_push (hY : IsSurface Y) [ConnectedSpace Y] {H : 𝕀 × Y → Y} (hH : Continuous H)
  (h0 : ∀ y, H (0, y) = y)
    {X C : Set Y} (hX : IsSolid X) (hp : IsPlanarInCappedCuff C ((fun y => H
      (1, y)) '' X)) : IsPlanarInCappedCuff C X := by
  have : CompactSpace Y := hY.1
  have : T2Space Y := hY.2.1
  obtain ⟨hC, ⟨T, tT, j, D, hc, Δ, hΔ, hs⟩, -⟩ := hp
  have hT := hc.isSurface
  have : T2Space T := hT.2.1
  have : ConnectedSpace T := hc.connectedSpace hY
  have hH' : Continuous fun q : 𝕀 × Y => j (H q) := hc.isEmbedding.continuous.comp hH
  refine isPlanarInCappedCuff_of_cap hY hc
    (isPlanar_of_homotopy hT hc.isEmbedding hX ?_ hH' (fun y => by rw [h0]) fun F _ hF =>
      ⟨Δ, hΔ, fun y hy => hs ⟨_, mem_image_of_mem _ (hF hy), rfl⟩⟩)
  exact .inr (IsCappedCuff.image_ne_univ hc X)

/-- An `O`-arc that surrounds a cuff still does so after a one to one map homotopic to the identity.
-/
theorem surrounds_of_push (hY : IsSurface Y) [ConnectedSpace Y] {H : 𝕀 × Y → Y} (hH : Continuous H)
  (h0 : ∀ y, H (0, y) = y)
    (hi : Function.Injective fun y => H (1, y)) {F C : Set Y} (hF : IsOArc F) (hne : ¬ IsSphere Y)
    (hs : SurroundsCuff F C) : SurroundsCuff ((fun y => H (1, y)) '' F) C := by
  have : CompactSpace Y := hY.1
  have : T2Space Y := hY.2.1
  have hFs : IsSolid F := isSolid_of_isOArc hY hF
  refine ⟨hs.1, ?_, fun hp => hs.2.2 (planar_of_push hY hH h0 hFs (.inl hne) hp)⟩
  obtain ⟨T, tT, j, D, hc, Δ, hΔ, hsub⟩ := hs.2.1.2.1
  have hT := hc.isSurface
  have : T2Space T := hT.2.1
  have : ConnectedSpace T := hc.connectedSpace hY
  have hρc : Continuous fun y => H (1, y) := hH.comp (continuous_const.prodMk continuous_id)
  have hρ : IsEmbedding fun y => H (1, y) := (hρc.isClosedEmbedding hi).isEmbedding
  have hemb : IsEmbedding fun y => j (H (1, y)) := hc.isEmbedding.comp hρ
  let H' : 𝕀 × Y → T := fun q => j (H (unitInterval.symm q.1, q.2))
  have hH' : Continuous H' := hc.isEmbedding.continuous.comp
    (hH.comp ((unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_snd))
  have hp := isPlanar_of_homotopy hT hemb hFs (.inr ?_) hH' (fun y => by simp [H']) fun F' _ hF' =>
    ⟨Δ, hΔ, fun y hy => by
      have h1 : j y ∈ Δ := hsub (mem_image_of_mem j (hF' hy))
      simpa [H', h0] using h1⟩
  · refine isPlanarInCappedCuff_of_cap hY hc ?_
    rwa [image_image]
  · have h2 := IsCappedCuff.image_ne_univ hc ((fun y => H (1, y)) '' F)
    rwa [image_image] at h2

/-- A one to one map on a compact solid set keeps it solid. -/
theorem isSolid_image_of_injOn [CompactSpace Y] [T2Space S] {f : Y → S}
  (hf : Continuous f) {Z : Set Y} (hZ : IsSolid Z)
    (hi : InjOn f Z) : IsSolid (f '' Z) := by
  have hcl : ∀ K : Set Y, IsClosed K → IsClosed (f '' K) := fun K hK =>
    (hK.isCompact.image hf).isClosed
  refine ⟨?_, hcl Z hZ.2⟩
  rintro _ ⟨z, hz, rfl⟩ U hU hzU
  obtain ⟨V, hVs, hzV, hVo, harc⟩ := hZ.1 z hz (f ⁻¹' U) (hU.preimage hf) hzU
  let W : Set S := (f '' (Z \ V))ᶜ
  have hWo : IsOpen W := (hcl _ (hZ.2.sdiff hVo)).isOpen_compl
  have hzW : f z ∈ W := by
    rintro ⟨x, ⟨hx, hxV⟩, he⟩
    exact hxV (hi hx hz he ▸ hzV)
  refine ⟨W ∩ U, inter_subset_right, ⟨hzW, hzU⟩, hWo.inter hU, ?_⟩
  have hin : ∀ {a}, a ∈ Z → f a ∈ W → a ∈ V := fun {a} ha hw => by
    by_contra hV
    exact hw ⟨a, ⟨ha, hV⟩, rfl⟩
  rintro _ ⟨⟨a, ha, rfl⟩, haW, -⟩ _ ⟨⟨b, hb, rfl⟩, hbW, -⟩ hab
  obtain ⟨L, hLs, g, h0, h1⟩ := harc a ⟨ha, hin ha haW⟩ b ⟨hb, hin hb hbW⟩ fun h => hab
    (congrArg f h)
  have hLZ : InjOn f L := hi.mono fun x hx => (hLs hx).1
  let k : 𝕀 → f '' L := fun t => ⟨f (g t).1, _, (g t).2, rfl⟩
  have hkc : Continuous k := Continuous.subtype_mk (hf.comp (continuous_subtype_val.comp
    g.continuous)) _
  have hkb : Function.Bijective k := by
    constructor
    · intro t t' he
      exact g.injective (Subtype.ext (hLZ (g t).2 (g t').2 (congrArg Subtype.val he)))
    · rintro ⟨_, x, hx, rfl⟩
      exact ⟨g.symm ⟨x, hx⟩, Subtype.ext (by simp [k])⟩
  refine ⟨f '' L, ?_, Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective k hkb) hkc, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, (hLs hx).1, rfl⟩, by
      intro hc
      obtain ⟨x', ⟨_, hx'⟩, he⟩ := hc
      exact hx' (hi ‹_› (hLs hx).1 he ▸ (hLs hx).2), hVs (hLs hx).2⟩
  · change f (g 0).1 = _
    rw [h0]
  · change f (g 1).1 = _
    rw [h1]

namespace IsCutAlongEdge

variable [T1Space S] {G : Drawing S} {e : Set S} {a b c : ℕ} {φ : Y → S} {G' : Drawing Y}

omit [T1Space S] in
theorem continuous (hc : IsCutAlongEdge G e a b c Y φ G') : Continuous φ
  := hc.quotientMap.continuous

omit [T1Space S] in
theorem surjective (hc : IsCutAlongEdge G e a b c Y φ G') : Function.Surjective φ
  := hc.quotientMap.surjective

omit [T1Space S] in
theorem notMem_V (hc : IsCutAlongEdge G e a b c Y φ G') {x : S} (hx : x ∈ e) : x ∉ G.V := fun hV =>
  (hc.mem_E.2.1 hx).2 hV

omit [T1Space S] in
theorem mem_U (hc : IsCutAlongEdge G e a b c Y φ G') {x : S} (hx : x ∈ e) : x ∈ G.U :=
  (hc.mem_E.2.1 hx).1

omit [T1Space S] in
theorem bd_inter (hc : IsCutAlongEdge G e a b c Y φ G') {x : S} (hx : x ∈ closure e) : x ∉ bd S
  := fun hb => by
  have : x ∈ closure e ∩ bd S := ⟨hx, hb⟩
  rw [hc.disjoint_bd] at this
  exact this

omit [T1Space S] in
/-- A `G'`-normal set that meets the new cuff only in vertices goes one to one to a `G`-normal set
with as many vertices. -/
theorem image_facts (hc : IsCutAlongEdge G e a b c Y φ G') {A : Set Y} (hA : G'.IsNormal A)
    (hN : A ∩ φ ⁻¹' closure e ⊆ G'.V) :
    InjOn φ A ∧ G.IsNormal (φ '' A) ∧ (G.V ∩ φ '' A).ncard = (G'.V ∩ A).ncard := by
  have hoff : ∀ {x}, x ∈ A → φ x ∉ e := fun {x} hx he => by
    have h1 : x ∈ G'.V := hN ⟨hx, subset_closure he⟩
    rw [hc.preimage_V] at h1
    exact hc.notMem_V he h1
  have hi : InjOn φ A := fun x hx y _ he => (hc.inj x y he).resolve_right (hoff hx)
  refine ⟨hi, ?_, ?_⟩
  · rintro _ ⟨⟨x, hx, rfl⟩, hU⟩
    have h1 : x ∈ G'.V := hA ⟨hx, by rw [hc.preimage_U]; exact ⟨hU, hoff hx⟩⟩
    rw [hc.preimage_V] at h1
    exact h1
  · have h1 : G.V ∩ φ '' A = φ '' (G'.V ∩ A) := by
      ext s
      constructor
      · rintro ⟨hV, x, hx, rfl⟩
        exact ⟨x, ⟨by rw [hc.preimage_V]; exact hV, hx⟩, rfl⟩
      · rintro ⟨x, ⟨hV, hx⟩, rfl⟩
        rw [hc.preimage_V] at hV
        exact ⟨hV, x, hx, rfl⟩
    rw [h1, (hi.mono inter_subset_right).ncard_image]

omit [T1Space S] in
theorem isCuff_new (hc : IsCutAlongEdge G e a b c Y φ G') : IsCuff (φ ⁻¹' closure e) := hc.newCuff

omit [T1Space S] in
/-- Each `G'`-normal set can be pushed off the new cuff, keeping its vertices. -/
theorem exists_push (hc : IsCutAlongEdge G e a b c Y φ G') :
    ∃ H : 𝕀 × Y → Y, Continuous H ∧ (∀ y, H (0, y) = y) ∧ (Function.Injective fun y => H (1, y)) ∧
      ∀ A : Set Y, G'.IsNormal A → G'.IsNormal ((fun y => H (1, y)) '' A) ∧
        ((fun y => H (1, y)) '' A) ∩ φ ⁻¹' closure e ⊆ G'.V ∧
        (G'.V ∩ (fun y => H (1, y)) '' A).ncard = (G'.V ∩ A).ncard := by
  obtain ⟨-, -, hO⟩ := cuff_statement.{u} Y hc.isSurface
  obtain ⟨f⟩ := hO _ hc.isCuff_new
  obtain ⟨H, hH, h0, hi, hfix, hback, hcuff⟩ := exists_taper hc.isSurface hc.isCuff_new f
    G'.isClosed_U
  refine ⟨H, hH, h0, hi, fun A hA => ?_⟩
  have h1 : ∀ x ∈ A, H (1, x) ∈ G'.U → H (1, x) ∈ G'.V := fun x hx hU => by
    have h2 := hback x hU
    rw [hfix x h2]
    exact hA ⟨hx, h2⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨⟨x, hx, rfl⟩, hU⟩
    exact h1 x hx hU
  · rintro _ ⟨⟨x, hx, rfl⟩, hN⟩
    exact h1 x hx (hcuff x hN)
  · congr 1
    ext s
    constructor
    · rintro ⟨hV, x, hx, rfl⟩
      have h2 := hback x (G'.V_subset_U hV)
      have h3 : H (1, x) = x := hfix x h2
      refine ⟨hV, ?_⟩
      change H (1, x) ∈ A
      rwa [h3]
    · rintro ⟨hV, hs⟩
      exact ⟨hV, s, hs, hfix s (G'.V_subset_U hV)⟩

omit [T1Space S] in
/-- The part of `bd Y` over `bd S` is a copy of `bd S`, and it lies apart from the new cuff. -/
theorem exists_bd_inverse (hc : IsCutAlongEdge G e a b c Y φ G') (hS : IsSurface S) :
    InjOn φ (φ ⁻¹' bd S) ∧ ∃ g : S → Y, ContinuousOn g (bd S) ∧ RightInvOn g φ (bd S) ∧ MapsTo g
      (bd S) (φ ⁻¹' bd S) := by
  have : CompactSpace Y := hc.isSurface.1
  have : T2Space S := hS.2.1
  have hi : InjOn φ (φ ⁻¹' bd S) := fun x hx y _ he =>
    (hc.inj x y he).resolve_right fun h => hc.bd_inter (subset_closure h) hx
  refine ⟨hi, ?_⟩
  have hK : IsCompact (φ ⁻¹' bd S) := ((isClosed_bd S).preimage hc.continuous).isCompact
  have : Nonempty Y := by
    obtain ⟨x, -⟩ := nonempty_of_ncard_ne_zero (s := tilde e) (by rw [hc.not_loop]; omega)
    exact ⟨(hc.surjective x).choose⟩
  obtain ⟨g, hgc, hgl⟩ := exists_inv_of_compactOn hK hc.continuous.continuousOn hi
  have him : φ '' (φ ⁻¹' bd S) = bd S := image_preimage_eq _ hc.surjective
  rw [him] at hgc
  have hr : RightInvOn g φ (bd S) := fun y hy => by
    obtain ⟨x, rfl⟩ := hc.surjective y
    rw [hgl (show x ∈ φ ⁻¹' bd S from hy)]
  exact ⟨g, hgc, hr, fun y hy => by
    change φ (g y) ∈ bd S
    rwa [hr hy]⟩

omit [T1Space S] in
/-- The component of `bd Y` at a point over `bd S` is the preimage of the component of `bd S`. -/
theorem component_eq (hc : IsCutAlongEdge G e a b c Y φ G') (hS : IsSurface S) {y : Y}
  (hy : φ y ∈ bd S) :
    connectedComponentIn (bd Y) y = φ ⁻¹' connectedComponentIn (bd S) (φ y) := by
  obtain ⟨hi, g, hgc, hgr, hgm⟩ := hc.exists_bd_inverse hS
  have hyb : y ∈ bd Y := by
    rw [hc.bd_eq]
    exact .inl hy
  have hsub : ∀ {K : Set S}, K ⊆ bd S → φ ⁻¹' K = g '' K := fun {K} hK => by
    ext x
    constructor
    · intro hx
      refine ⟨φ x, hx, hi (hgm (hK hx)) (hK hx) ?_⟩
      exact hgr (hK hx)
    · rintro ⟨s, hs, rfl⟩
      change φ (g s) ∈ K
      rwa [hgr (hK hs)]
  have hCb := connectedComponentIn_subset (bd S) (φ y)
  apply Subset.antisymm
  · have hP : IsClosed (φ ⁻¹' bd S) := (isClosed_bd S).preimage hc.continuous
    have hN : IsClosed (φ ⁻¹' closure e) := isClosed_closure.preimage hc.continuous
    have hconn : IsPreconnected (connectedComponentIn (bd Y) y) :=
      isPreconnected_connectedComponentIn
    have hsubP : connectedComponentIn (bd Y) y ⊆ φ ⁻¹' bd S := by
      intro x hx
      by_contra hxP
      have h1 := connectedComponentIn_subset _ _ hx
      rw [hc.bd_eq] at h1
      have hxN : x ∈ φ ⁻¹' closure e := h1.resolve_left hxP
      have hyin : y ∈ connectedComponentIn (bd Y) y := mem_connectedComponentIn hyb
      obtain ⟨z, -, hz1, hz2⟩ := isPreconnected_closed_iff.mp hconn _ _ hP hN (fun z hz => by
        have h2 := connectedComponentIn_subset _ _ hz
        rw [hc.bd_eq] at h2
        exact h2) ⟨y, hyin, hy⟩ ⟨x, hx, hxN⟩
      exact hc.bd_inter hz2 hz1
    have himg : IsPreconnected (φ '' connectedComponentIn (bd Y) y) := hconn.image _
      hc.continuous.continuousOn
    intro x hx
    exact himg.subset_connectedComponentIn ⟨y, mem_connectedComponentIn hyb, rfl⟩ (by
      rintro _ ⟨z, hz, rfl⟩
      exact hsubP hz) ⟨x, hx, rfl⟩
  · rw [hsub hCb]
    have hconn : IsPreconnected (g '' connectedComponentIn (bd S) (φ y)) :=
      isPreconnected_connectedComponentIn.image _ (hgc.mono hCb)
    refine hconn.subset_connectedComponentIn ?_ ?_
    · refine ⟨φ y, mem_connectedComponentIn hy, ?_⟩
      exact hi (hgm hy) hy (hgr hy)
    · rintro _ ⟨s, hs, rfl⟩
      rw [hc.bd_eq]
      exact .inl (hgm (hCb hs))

omit [T1Space S] in
/-- The two ways the cuffs of `Y` arise. -/
theorem cuff_cases (hc : IsCutAlongEdge G e a b c Y φ G') (hS : IsSurface S) {C : Set Y}
  (hC : C ∈ cuffs Y) :
    C = φ ⁻¹' closure e ∨ ∃ C₀ ∈ cuffs S, C = φ ⁻¹' C₀ := by
  obtain ⟨y, hy, rfl⟩ := hC
  have hyb := hy
  rw [hc.bd_eq] at hy
  rcases hy with hy | hy
  · exact .inr ⟨_, ⟨φ y, hy, rfl⟩, hc.component_eq hS hy⟩
  · obtain ⟨n, -, hn⟩ := hc.newCuff
    refine .inl ?_
    have hy' : y ∈ φ ⁻¹' closure e := hy
    rw [← hn] at hy' ⊢
    exact (connectedComponentIn_eq hy').symm

omit [T1Space S] in
/-- The cuffs of `S` lift. -/
theorem cuff_lift (hc : IsCutAlongEdge G e a b c Y φ G') (hS : IsSurface S) {C₀ : Set S}
  (hC : C₀ ∈ cuffs S) :
    φ ⁻¹' C₀ ∈ cuffs Y ∧ BijOn φ (φ ⁻¹' C₀) C₀ := by
  obtain ⟨hi, -⟩ := hc.exists_bd_inverse hS
  obtain ⟨s, hs, rfl⟩ := hC
  obtain ⟨y, rfl⟩ := hc.surjective s
  have hCb := connectedComponentIn_subset (bd S) (φ y)
  refine ⟨⟨y, ?_, hc.component_eq hS hs⟩, mapsTo_preimage _ _, hi.mono (preimage_mono hCb), ?_⟩
  · rw [hc.bd_eq]
    exact .inl hs
  · intro x hx
    obtain ⟨z, rfl⟩ := hc.surjective x
    exact ⟨z, hx, rfl⟩

end IsCutAlongEdge

end GraphMinor.GM07
