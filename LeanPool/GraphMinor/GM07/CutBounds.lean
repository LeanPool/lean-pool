/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CutEdge
import LeanPool.GraphMinor.GM19.Section6a

/-!
# Graph Minors VII, (7.1) and (7.2)

We prove that cutting along a good edge keeps `α` large (`cut_alpha_bound`) and keeps the graph
boundary-linked
(`cut_boundaryLinked`).

The tool is `IsCapPair`. Let `C₀` be a cuff of `S`. Paste a disc on `C₀` to get `T`, and paste a
disc on the cuff of `Y` over `C₀`
to get `T'`. The cutting map extends to `Ψ : T' → T`. It is one to one away from `e`, so closed
discs of `T` that miss `e` lift
to closed discs of `T'`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Metric GraphMinor.Surface GraphMinor.GM11

universe u

local notation "𝕀" => unitInterval

variable {S Y T T' : Type u} [TopologicalSpace S] [TopologicalSpace Y] [TopologicalSpace T]
  [TopologicalSpace T']

/-- A disc can be pasted on each cuff. -/
theorem exists_cappedCuff (hS : IsSurface S) {C : Set S} (hC : IsCuff C) :
    ∃ (T : Type u) (_ : TopologicalSpace T) (j : S → T) (D : Set T), IsCappedCuff C T j D ∧ bd T
      = j '' (bd S \ C) := by
  obtain ⟨T, t, j, D, h1, h2, h3, h4, h5, h6, h7⟩ := paste_disc.{u} S C hS hC
  exact ⟨T, t, j, D, ⟨hC, h1, h2.isEmbedding, h3, h6, h4, h5⟩, h7⟩

/-- A map keeps null-homotopy. -/
theorem null_comp {Z : Set Y} {c : C(Circle, Y)} (h : ClosedCurveIsNullHomotopicIn Z c) {m : Y → T}
  (hm : Continuous m)
    (hc : Continuous fun w => m (c w)) : ClosedCurveIsNullHomotopicIn univ ⟨fun w => m (c w), hc⟩
      := by
  obtain ⟨p, -, ψ, -, h2, h3⟩ := h
  refine ⟨m p, mem_univ _, ⟨fun q => m (ψ q), hm.comp ψ.continuous⟩, fun _ => mem_univ _,
    fun x => ?_, fun x => ?_⟩
  · simp [h2]
  · simp [h3]

/-- A curve in a closed disc is null-homotopic. -/
theorem null_of_disc {f : Circle → Y} (hf : Continuous f) {Δ : Set Y} (hΔ : IsClosedDisc Δ)
  (h : ∀ w, f w ∈ Δ) :
    ClosedCurveIsNullHomotopicIn Δ ⟨f, hf⟩ :=
  hΔ.isSimplyConnectedSet.2 ⟨f, hf⟩ (by
    rintro _ ⟨w, rfl⟩
    exact h w)

/-- A closed disc goes to a closed disc under a map one to one on it. -/
theorem isClosedDisc_image_of_injOn {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [T2Space B] {Δ : Set A}
    (hΔ : IsClosedDisc Δ) {f : A → B} (hf : Continuous f) (hi : InjOn f Δ) :
    IsClosedDisc (f '' Δ) ∧ discBd (f '' Δ) = f '' discBd Δ := by
  have : Nonempty A := by
    obtain ⟨h⟩ := id hΔ
    exact ⟨(h ⟨0, mem_closedBall_self zero_le_one⟩).1⟩
  obtain ⟨g, hgc, hgl⟩ := exists_inv_of_compactOn hΔ.isCompact hf.continuousOn hi
  exact hΔ.image hf.continuousOn hgc hgl

/-- A surface with a model is connected. -/
theorem connectedSpace_of_model {T : Type u} [TopologicalSpace T] {a b c : ℕ} (h : Nonempty
  (T ≃ₜ SurfaceModel a b c)) :
    ConnectedSpace T := by
  obtain ⟨e⟩ := h
  have := (modelCriterion.1 a b c).2
  exact e.symm.surjective.connectedSpace e.symm.continuous

/-- Pasting a disc on a surface with `3a + 3b + c ≥ 3` does not give a sphere. -/
theorem not_isSphere_cap (hS : IsSurface S) {a b c : ℕ} (h3 : 3 ≤ 3 * a + 3 * b + c) (h : Nonempty
  (S ≃ₜ SurfaceModel a b c))
    {C : Set S} {j : S → T} {D : Set T} (hc : IsCappedCuff C T j D) : ¬ IsSphere T := by
  have : CompactSpace S := hS.1
  have : T2Space T := hc.isSurface.2.1
  obtain ⟨e⟩ := h
  obtain ⟨h0, hm⟩ := paste_model hS hc.cuff hc.isSurface
    (hc.isEmbedding.continuous.isClosedEmbedding hc.isEmbedding.injective)
    hc.isClosedDisc hc.union_eq hc.inter_eq hc.discBd_eq e
  refine not_isSphere_of_model hm ?_
  omega

/-- A one to one map of a closed set onto a solid set: the set is solid too. -/
theorem isSolid_preimage_of_injOn [CompactSpace Y] [T2Space S] {f : Y → S} (hf : Continuous f)
  (hs : Function.Surjective f)
    {Z : Set S} (hZ : IsSolid Z) (hi : InjOn f (f ⁻¹' Z)) : IsSolid (f ⁻¹' Z) := by
  have hcl : ∀ K : Set Y, IsClosed K → IsClosed (f '' K) := fun K hK =>
    (hK.isCompact.image hf).isClosed
  have hZc : IsClosed (f ⁻¹' Z) := hZ.2.preimage hf
  refine ⟨?_, hZc⟩
  intro x hx U hU hxU
  let W : Set S := (f '' (f ⁻¹' Z \ U))ᶜ
  have hWo : IsOpen W := (hcl _ (hZc.sdiff hU)).isOpen_compl
  have hxW : f x ∈ W := by
    rintro ⟨y, ⟨hy, hyU⟩, he⟩
    exact hyU (hi hy hx he ▸ hxU)
  obtain ⟨V₀, hV₀, hxV, hVo, harc⟩ := hZ.1 (f x) hx W hWo hxW
  refine ⟨f ⁻¹' V₀ ∩ U, inter_subset_right, ⟨hxV, hxU⟩, (hVo.preimage hf).inter hU, ?_⟩
  rintro a ⟨ha, haV, -⟩ b ⟨hb, hbV, -⟩ hab
  obtain ⟨L, hLs, l, h0, h1⟩ := harc (f a) ⟨ha, haV⟩ (f b) ⟨hb, hbV⟩ fun h => hab (hi ha hb h)
  have hLc : IsClosed L := by
    have h := isCompact_range (continuous_subtype_val.comp l.continuous)
    rw [range_comp, l.surjective.range_eq, image_univ, Subtype.range_coe] at h
    exact h.isClosed
  have : CompactSpace (f ⁻¹' L) := isCompact_iff_compactSpace.mp (hLc.preimage hf).isCompact
  let k : f ⁻¹' L → L := fun p => ⟨f p.1, p.2⟩
  have hkc : Continuous k := Continuous.subtype_mk (hf.comp continuous_subtype_val) _
  have hinL : ∀ p : f ⁻¹' L, p.1 ∈ f ⁻¹' Z := fun p => (hLs p.2).1
  have hkb : Function.Bijective k := by
    constructor
    · intro p p' he
      exact Subtype.ext (hi (hinL p) (hinL p') (congrArg Subtype.val he))
    · rintro ⟨s, hs'⟩
      obtain ⟨p, rfl⟩ := hs s
      exact ⟨⟨p, hs'⟩, rfl⟩
  let kh : f ⁻¹' L ≃ₜ L := Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective k hkb) hkc
  have hlift : ∀ {p z}, p ∈ f ⁻¹' Z → f p = z → ∀ q : L, q.1 = z → (kh.symm q).1 = p
    := fun {p z} hp hz q hq => by
    apply hi (hinL _) hp
    have h5 : k (kh.symm q) = q := kh.apply_symm_apply q
    have h6 : f (kh.symm q).1 = q.1 := congrArg Subtype.val h5
    rw [h6, hq, hz]
  refine ⟨f ⁻¹' L, ?_, l.trans kh.symm, ?_, ?_⟩
  · intro p hp
    refine ⟨(hLs hp).1, (hLs hp).2, ?_⟩
    by_contra hpU
    exact hV₀ (hLs hp).2 ⟨p, ⟨(hLs hp).1, hpU⟩, rfl⟩
  · exact hlift ha rfl _ h0
  · exact hlift hb rfl _ h1

/-- The extension of the cutting map to the surfaces with discs pasted on a cuff `C₀` of `S` and on
the cuff over it. -/
structure IsCapPair (φ : Y → S) (e C₀ : Set S) (j : S → T) (D : Set T) (j' : Y → T') (D' : Set T')
  (Ψ : T' → T) : Prop where
  capS : IsCappedCuff C₀ T j D
  capY : IsCappedCuff (φ ⁻¹' C₀) T' j' D'
  bdY : bd T' = j' '' (bd Y \ φ ⁻¹' C₀)
  cont : Continuous Ψ
  comm : ∀ y, Ψ (j' y) = j (φ y)
  surj : Function.Surjective Ψ
  inj : ∀ x x', Ψ x = Ψ x' → x = x' ∨ Ψ x ∈ j '' e
  inner : MapsTo Ψ (discInt D') (discInt D)

/-- Edges are connected. -/
theorem isPreconnected_of_edge {G : Drawing S} {e : Set S} (he : e ∈ G.E) : IsPreconnected e :=
  he.2.2.1.isConnected.isPreconnected

namespace IsCutAlongEdge

variable [T1Space S] {G : Drawing S} {e : Set S} {a b c : ℕ} {φ : Y → S} {G' : Drawing Y}

omit [T1Space S] in
theorem exists_capPair (hc : IsCutAlongEdge G e a b c Y φ G') (hS : IsSurface S) {C₀ : Set S}
  (hC : C₀ ∈ cuffs S) :
    ∃ (T T' : Type u) (_ : TopologicalSpace T) (_ : TopologicalSpace T') (j : S → T) (D : Set T)
      (j' : Y → T') (D' : Set T')
      (Ψ : T' → T), IsCapPair φ e C₀ j D j' D' Ψ := by
  obtain ⟨hcuff, hb⟩ := hc.cuff_lift hS hC
  obtain ⟨T, tT, j, D, hcS, -⟩ := exists_cappedCuff hS hC
  obtain ⟨T', tT', j', D', hcY, hbdY⟩ := exists_cappedCuff hc.isSurface hcuff
  have : CompactSpace Y := hc.isSurface.1
  have : T2Space T' := hcY.isSurface.2.1
  have : T2Space T := hcS.isSurface.2.1
  have hne : (φ ⁻¹' C₀).Nonempty := by
    obtain ⟨y, hy, hye⟩ := hcuff
    exact ⟨y, hye ▸ mem_connectedComponentIn hy⟩
  obtain ⟨Ψ, hΨc, hΨj, hΨm, hΨi, hΨs, hΨo⟩ := exists_cap_map hcY hcS hc.continuous hb hne
  have hcov : ∀ x, x ∈ range j' ∨ x ∈ discInt D' := fun x => by
    rcases (hcY.union_eq.ge (mem_univ x)) with h | h
    · exact .inl h
    · by_cases hx : x ∈ discBd D'
      · rw [hcY.discBd_eq] at hx
        obtain ⟨y, -, rfl⟩ := hx
        exact .inl (mem_range_self y)
      · exact .inr ⟨h, hx⟩
  have hdis : ∀ y, ∀ x ∈ discInt D', j (φ y) ≠ Ψ x := fun y x hx he => by
    have h1 := hΨo hx
    rw [← he] at h1
    have h2 : j (φ y) ∈ range j ∩ D := ⟨mem_range_self _, h1.1⟩
    rw [hcS.inter_eq, ← hcS.discBd_eq] at h2
    exact h1.2 h2
  refine ⟨T, T', tT, tT', j, D, j', D', Ψ, hcS, hcY, hbdY, hΨc, hΨj, ?_, ?_, hΨo⟩
  · intro t
    rcases hcS.union_eq.ge (mem_univ t) with ⟨s, rfl⟩ | h
    · obtain ⟨y, rfl⟩ := hc.surjective s
      exact ⟨j' y, hΨj y⟩
    · obtain ⟨x, -, hx⟩ := hΨs h
      exact ⟨x, hx⟩
  · intro x x' he
    rcases hcov x with ⟨y, rfl⟩ | hx <;> rcases hcov x' with ⟨y', rfl⟩ | hx'
    · rw [hΨj, hΨj] at he
      rcases hc.inj y y' (hcS.isEmbedding.injective he) with h | h
      · exact .inl (congrArg j' h)
      · exact .inr (by rw [hΨj]; exact mem_image_of_mem j h)
    · rw [hΨj] at he
      exact (hdis y x' hx' he).elim
    · rw [hΨj] at he
      exact (hdis y' x hx he.symm).elim
    · exact .inl (hΨi hx.1 hx'.1 he)

end IsCutAlongEdge

/-- A closed disc of `T` that misses `e` lifts to `T'`. -/
theorem IsCapPair.lift {φ : Y → S} {e C₀ : Set S} {j : S → T} {D : Set T} {j' : Y
  → T'} {D' : Set T'} {Ψ : T' → T}
    (hp : IsCapPair φ e C₀ j D j' D' Ψ) {Δ : Set T} (hΔ : IsClosedDisc Δ) (hm : Disjoint Δ
      (j '' e)) :
    IsClosedDisc (Ψ ⁻¹' Δ) := by
  have : CompactSpace T' := hp.capY.isSurface.1
  have : T2Space T := hp.capS.isSurface.2.1
  refine (isClosedDisc_preimage_of_injOn hp.cont hp.surj hΔ fun x hx x' _ he => ?_).1
  exact (hp.inj x x' he).resolve_right (disjoint_left.mp hm hx)

/-- A set that is planar on `T'`: its `O`-arcs have images under `Ψ` in closed discs of `T` that
miss `e`. -/
theorem IsCapPair.planar_of_discs {φ : Y → S} {e C₀ : Set S} {j : S → T} {D : Set T} {j' : Y
  → T'} {D' : Set T'} {Ψ : T' → T}
    (hY : IsSurface Y) [ConnectedSpace Y] (hp : IsCapPair φ e C₀ j D j' D' Ψ)
    {X : Set Y} (hX : IsSolid X)
    (h : ∀ F, IsOArc F → F ⊆ X → ∃ Δ, IsClosedDisc Δ ∧ Disjoint Δ (j '' e) ∧ ∀ y ∈ F, j (φ y) ∈ Δ) :
    IsPlanarInCappedCuff (φ ⁻¹' C₀) X := by
  have : CompactSpace Y := hY.1
  have : T2Space Y := hY.2.1
  have hT' := hp.capY.isSurface
  have : ConnectedSpace T' := hp.capY.connectedSpace hY
  refine isPlanarInCappedCuff_of_cap hY hp.capY (isPlanar_of_null hT' hp.capY.isEmbedding hX
    (.inr (IsCappedCuff.image_ne_univ hp.capY X)) fun F hF hFX f hf hr hc => ?_)
  obtain ⟨Δ, hΔ, hm, hs⟩ := h F hF hFX
  have h1 := null_of_disc hc (hp.lift hΔ hm) fun w => by
    change Ψ (j' (f w)) ∈ Δ
    rw [hp.comm]
    exact hs _ (hr ▸ mem_range_self w)
  exact null_comp (m := id) (c := ⟨fun w => j' (f w), hc⟩) h1 continuous_id hc

section Bounds

variable [T1Space S] {G : Drawing S} {e : Set S} {a b c : ℕ} {φ : Y → S} {G' : Drawing Y}

/-- A near-planar push gives a near-planar set. -/
theorem nearPlanar_of_push (hY : IsSurface Y) [ConnectedSpace Y] (hns : ¬ IsSphere Y) {H : 𝕀 × Y
  → Y} (hH : Continuous H)
    (h0 : ∀ y, H (0, y) = y) {X : Set Y} (hX : IsSolid X) (hp : IsNearPlanar ((fun y => H
      (1, y)) '' X)) : IsNearPlanar X := by
  rcases hp with hp | ⟨C, hC, hp⟩
  · exact .inl (planar_of_push hY hH h0 hX (.inl hns) hp)
  · exact .inr ⟨C, hC, planarCap_of_push hY hH h0 hX hp⟩

omit [T1Space S] in
/-- A set of `Y` whose image is planar in `S` is planar in `Y` with a disc on the new cuff. -/
theorem IsCutAlongEdge.planarNew_of_planar (hc : IsCutAlongEdge G e a b c Y φ G')
  (hS : IsSurface S) [ConnectedSpace S]
    {X : Set Y} (hX : IsSolid X) (hns : ¬ IsSphere S) (hp : ∀ F, F ⊆ X
      → IsOArc F → IsPlanar (φ '' F)) :
    IsPlanarInCappedCuff (φ ⁻¹' closure e) X := by
  have hY := hc.isSurface
  have : CompactSpace Y := hY.1
  have : T2Space Y := hY.2.1
  obtain ⟨ι, E, H, hcap, hH, h0, h1⟩ := hc.uncut
  refine isPlanarInCappedCuff_of_cap hY hcap (isPlanar_of_homotopy hS hcap.isEmbedding hX
    (.inl hns) hH h0 fun F hF hFX => ?_)
  obtain ⟨Δ, hΔ, hs⟩ := hp F hFX hF
  exact ⟨Δ, hΔ, fun y hy => by
    rw [h1]
    exact hs (mem_image_of_mem φ hy)⟩

omit [T1Space S] in
/-- The key step of (7.1): a candidate of `G'` has at least `r` vertices. -/
theorem IsCutAlongEdge.candidate_ge (hc : IsCutAlongEdge G e a b c Y φ G')
  (hS : IsSurface S) [ConnectedSpace S]
    [ConnectedSpace Y] (hnsS : ¬ IsSphere S) (hnsY : ¬ IsSphere Y) {r : ℕ} (hr : 1 ≤ r)
    (hα : ∀ X, IsAlphaCandidate G X → r ≤ (X ∩ G.V).ncard) (hnot : ¬ e ⊆ allCuffsInsideSet G
      (r - 1)) {X : Set Y}
    (hX : IsAlphaCandidate G' X) : r ≤ (X ∩ G'.V).ncard := by
  have hYs := hc.isSurface
  have : CompactSpace Y := hYs.1
  have : T2Space Y := hYs.2.1
  have : T2Space S := hS.2.1
  obtain ⟨hXs, hXc, hXn, hXp⟩ := hX
  by_contra hlt
  push Not at hlt
  obtain ⟨H, hH, h0, hinj, hpush⟩ := hc.exists_push
  have hρc : Continuous fun y => H (1, y) := hH.comp (continuous_const.prodMk continuous_id)
  obtain ⟨hn, hN, hcnt⟩ := hpush X hXn
  obtain ⟨hi, hnorm, hcnt2⟩ := hc.image_facts hn hN
  have hX₁s := isSolid_image_of_injOn hρc hXs hinj.injOn
  have hX₁c := hXc.image _ hρc.continuousOn
  have hX₂s := isSolid_image_of_injOn hc.continuous hX₁s hi
  have hX₂c := hX₁c.image φ hc.continuous.continuousOn
  have hcount : (φ '' ((fun y => H (1, y)) '' X) ∩ G.V).ncard = (X ∩ G'.V).ncard := by
    rw [inter_comm, hcnt2, hcnt, inter_comm]
  have hnear : IsNearPlanar (φ '' ((fun y => H (1, y)) '' X)) := by
    by_contra hnp
    have := hα _ ⟨hX₂s, hX₂c, hnorm, hnp⟩
    omega
  refine hXp (nearPlanar_of_push hYs hnsY hH h0 hXs ?_)
  by_cases hpl : IsPlanar (φ '' ((fun y => H (1, y)) '' X))
  · obtain ⟨Δ, hΔ, hsub⟩ := hpl
    exact .inr ⟨_, hc.newCuff, hc.planarNew_of_planar hS hX₁s hnsS fun F hF _ => ⟨Δ, hΔ,
      (image_mono hF).trans hsub⟩⟩
  obtain ⟨C₀, hC₀, hcap⟩ := hnear.resolve_left hpl
  obtain ⟨T, T', tT, tT', j, D, j', D', Ψ, hp⟩ := hc.exists_capPair hS hC₀
  refine .inr ⟨_, (hc.cuff_lift hS hC₀).1, hp.planar_of_discs hYs hX₁s fun F hF hFX
    => ?_⟩
  have hT := hp.capS.isSurface
  have : T2Space T := hT.2.1
  have hj := hp.capS.isEmbedding
  have hF₂ : IsOArc (j '' (φ '' F)) := by
    obtain ⟨f⟩ := id hF
    obtain ⟨e', -⟩ := exists_param_image f (g := fun y => j (φ y)) (hj.continuous.comp
      hc.continuous)
      fun x hx y hy he => hi (hFX hx) (hFX hy) (hj.injective he)
    rw [image_image]
    exact ⟨e'⟩
  have hplan : IsPlanar (j '' (φ '' F)) := by
    obtain ⟨Δ, hΔ, hsub⟩ := hcap.2.2 T j D hp.capS
    exact ⟨Δ, hΔ, (image_mono (image_mono hFX)).trans hsub⟩
  have hnull := (isPlanar_iff_isNullHomotopicOArc_of_isOArc hT hF₂).mp hplan
  obtain ⟨Δ, hΔ, hbd⟩ := nullHomotopicOArc_bounds_disc hT hF₂ hnull
  refine ⟨Δ, hΔ, ?_, fun y hy => Surface.discBd_subset _ (hbd ▸ mem_image_of_mem j
    (mem_image_of_mem φ hy))⟩
  by_contra hmeet
  obtain ⟨_, hx, s, hs, rfl⟩ := not_disjoint_iff.mp hmeet
  refine hnot fun p hpe => ?_
  have heA : ∀ x ∈ e, x ∉ φ '' ((fun y => H (1, y)) '' X) := fun x hx hA =>
    hc.notMem_V hx (hnorm ⟨hA, hc.mem_U hx⟩)
  have hs' : s ∈ univ \ φ '' ((fun y => H (1, y)) '' X) := ⟨mem_univ _, heA s hs⟩
  have heK : e ⊆ connectedComponentIn (univ \ φ '' ((fun y => H (1, y)) '' X)) s :=
    (isPreconnected_of_edge hc.mem_E).subset_connectedComponentIn hs fun x hx
      => ⟨mem_univ _, heA x hx⟩
  have hKA := connectedComponentIn_subset (univ \ φ '' ((fun y => H (1, y)) '' X)) s
  have hside := IsClosedDisc.side hT.2.2 hΔ
    ((isPreconnected_connectedComponentIn (F := univ \ φ '' ((fun y => H (1, y)) '' X)) (x
      := s)).image j hj.continuous.continuousOn)
    (by
      rw [hbd, disjoint_left]
      rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, he⟩
      exact (hKA hz).2 ((hj.injective he) ▸ image_mono hFX hw))
  have hKd : j '' connectedComponentIn (univ \ φ '' ((fun y => H (1, y)) '' X)) s ⊆ Δ := by
    rcases hside with h | h
    · exact h.trans (discInt_subset Δ)
    · exact (disjoint_left.mp h (mem_image_of_mem j (heK hs)) hx).elim
  have hA : IsScriptASet G (r - 1) C₀ (φ '' ((fun y => H (1, y)) '' X)) :=
    ⟨hX₂s, hX₂c, hnorm, ⟨hC₀, hcap, hpl⟩, by rw [inter_comm, hcount]; omega⟩
  refine mem_iUnion₂.mpr ⟨C₀, ⟨hC₀, ?_⟩, ?_⟩
  · obtain ⟨z, hz⟩ := hX₂c.nonempty
    exact ⟨z, _, ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2⟩, hz⟩
  · exact ⟨_, ⟨_, hA, .inr ⟨⟨s, hs', rfl⟩, T, tT, j, D, Δ, hp.capS, hΔ, by
      rw [hbd]
      exact image_mono (image_mono hFX), hKd⟩⟩, heK hpe⟩

omit [T1Space S] in
/-- (7.1): candidates of `G` give candidates of `G'`. -/
theorem IsCutAlongEdge.candidate_preimage (hc : IsCutAlongEdge G e a b c Y φ G')
  (hS : IsSurface S) [ConnectedSpace S]
    (hnsS : ¬ IsSphere S) {X : Set S} (hX : IsAlphaCandidate G X) : IsAlphaCandidate G' (φ ⁻¹' X)
      := by
  have hYs := hc.isSurface
  have : CompactSpace Y := hYs.1
  have : T2Space Y := hYs.2.1
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  obtain ⟨hs, hcn, hn, hp⟩ := hX
  have hoff : ∀ x ∈ X, x ∉ e := fun x hx he => hc.notMem_V he (hn ⟨hx, hc.mem_U he⟩)
  have hi : InjOn φ (φ ⁻¹' X) := fun x hx y _ he => (hc.inj x y he).resolve_right (hoff _ hx)
  have hK : IsCompact (φ ⁻¹' X) := (hs.2.preimage hc.continuous).isCompact
  have : Nonempty Y := by
    obtain ⟨x, -⟩ := hcn.nonempty
    exact ⟨(hc.surjective x).choose⟩
  obtain ⟨g, hgc, hgl⟩ := exists_inv_of_compactOn hK hc.continuous.continuousOn hi
  have him : φ '' (φ ⁻¹' X) = X := image_preimage_eq _ hc.surjective
  rw [him] at hgc
  have hr : RightInvOn g φ X := fun y hy => by
    obtain ⟨x, rfl⟩ := hc.surjective y
    rw [hgl (show x ∈ φ ⁻¹' X from hy)]
  have hgim : g '' X = φ ⁻¹' X := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change φ (g y) ∈ X
      rwa [hr hy]
    · intro hx
      exact ⟨φ x, hx, hgl hx⟩
  refine ⟨isSolid_preimage_of_injOn hc.continuous hc.surjective hs hi, hgim ▸ hcn.image g hgc,
    ?_, fun hnp => hp ?_⟩
  · rintro x ⟨hx, hU⟩
    rw [hc.preimage_U] at hU
    rw [hc.preimage_V]
    exact hn ⟨hx, hU.1⟩
  have hlift : ∀ f : Circle → S, Continuous f → range f ⊆ X → Continuous fun w => g (f w)
    := fun f hf hr' =>
    hgc.comp_continuous hf fun w => hr' (mem_range_self w)
  have hgX : ∀ {f : Circle → S}, range f ⊆ X → ∀ w, φ (g (f w)) = f w := fun hr' w => hr (hr'
    (mem_range_self w))
  rcases hnp with ⟨Δ, hΔ, hsub⟩ | ⟨C, hC, hcap⟩
  · refine .inl ?_
    have h := isPlanar_of_null hS (j := id) IsEmbedding.id hs (.inl hnsS) fun F _ hFX f hf hrf hc'
      => by
      have h1 : range f ⊆ X := hrf.le.trans hFX
      have h2 := null_of_disc (hlift f hf h1) hΔ fun w => hsub (show φ (g (f w)) ∈ X by
        rw [hgX h1]
        exact h1 (mem_range_self w))
      have h3 := null_comp h2 hc.continuous (hc.continuous.comp (hlift f hf h1))
      convert h3 using 2
      ext w
      exact (hgX h1 w).symm
    simpa using h
  · rcases hc.cuff_cases hS hC with rfl | ⟨C₀, hC₀, rfl⟩
    · refine .inl ?_
      obtain ⟨ι, E, H, hcap', hH, h0, h1⟩ := hc.uncut
      obtain ⟨Δ, hΔ, hsub⟩ := hcap.2.2 S ι E hcap'
      have h := isPlanar_of_null hS (j := id) IsEmbedding.id hs (.inl hnsS) fun F _ hFX f hf hrf
        hc' => by
        have h1' : range f ⊆ X := hrf.le.trans hFX
        have h2 := null_of_homotopy_into_disc (H := fun q : 𝕀 × Y => H (unitInterval.symm q.1, q.2))
          (hH.comp ((unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_snd))
            (hlift f hf h1') hΔ fun w => by
            have hwX : φ (g (f w)) ∈ X := by
              rw [hgX h1']
              exact h1' (mem_range_self w)
            simpa [h0] using hsub (mem_image_of_mem ι hwX)
        convert h2 using 2
        ext w
        simp [h1, hgX h1' w]
      simpa using h
    · refine .inr ⟨C₀, hC₀, ?_⟩
      obtain ⟨T, T', tT, tT', j, D, j', D', Ψ, hp'⟩ := hc.exists_capPair hS hC₀
      obtain ⟨Δ, hΔ, hsub⟩ := hcap.2.2 T' j' D' hp'.capY
      have hT := hp'.capS.isSurface
      have : ConnectedSpace T := hp'.capS.connectedSpace hS
      refine isPlanarInCappedCuff_of_cap hS hp'.capS (isPlanar_of_null hT hp'.capS.isEmbedding hs
        (.inr (IsCappedCuff.image_ne_univ hp'.capS X)) fun F _ hFX f hf hrf hc' => ?_)
      have h1' : range f ⊆ X := hrf.le.trans hFX
      have hc2 : Continuous fun w => j' (g (f w)) := hp'.capY.isEmbedding.continuous.comp
        (hlift f hf h1')
      have h2 := null_of_disc hc2 hΔ fun w => hsub (mem_image_of_mem j' (show φ (g (f w)) ∈ X by
        rw [hgX h1']
        exact h1' (mem_range_self w)))
      have h3 := null_comp h2 hp'.cont (hp'.cont.comp hc2)
      convert h3 using 2
      ext w
      simp [hp'.comm, hgX h1' w]

omit [T1Space S] in
/-- Graph Minors VII, (7.1). -/
theorem IsCutAlongEdge.alpha_bound (hc : IsCutAlongEdge G e a b c Y φ G') (hS : IsSurface S)
  (h3 : 3 ≤ 3 * a + 3 * b + c)
    (hm : Nonempty (S ≃ₜ SurfaceModel a b c)) {r : ℕ} (hr : 2 ≤ r) (hα : 9 * r ≤ 2 * alpha G)
    (hnot : ¬ e ⊆ allCuffsInsideSet G (r - 1)) : r ≤ alpha G' := by
  have : ConnectedSpace S := connectedSpace_of_model hm
  have : ConnectedSpace Y := connectedSpace_of_model hc.homeo_model
  have hnsS : ¬ IsSphere S := not_isSphere_of_model hm (by omega)
  have hnsY : ¬ IsSphere Y := not_isSphere_of_model hc.homeo_model (by omega)
  have hne : {n : ℕ | ∃ X : Set S, IsAlphaCandidate G X ∧ (X ∩ G.V).ncard = n}.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have h0 : alpha G = 0 := by simp [alpha, h]
    omega
  obtain ⟨_, X₀, hX₀, -⟩ := hne
  have hαG : ∀ X, IsAlphaCandidate G X → r ≤ (X ∩ G.V).ncard := fun X hX => by
    have h1 : alpha G ≤ (X ∩ G.V).ncard := Nat.sInf_le ⟨X, hX, rfl⟩
    omega
  refine le_csInf ⟨_, _, hc.candidate_preimage hS hnsS hX₀, rfl⟩ ?_
  rintro _ ⟨X, hX, rfl⟩
  exact hc.candidate_ge hS hnsS hnsY (by omega) hαG hnot hX

omit [T1Space S] in
/-- The new cuff has two vertices. -/
theorem IsCutAlongEdge.ncard_new (hc : IsCutAlongEdge G e a b c Y φ G') :
  (G'.V ∩ φ ⁻¹' closure e).ncard = 2 := by
  have h1 : G'.V ∩ φ ⁻¹' closure e = φ ⁻¹' tilde e := by
    rw [GraphMinor.GM19.tilde_eq_inter_V G hc.mem_E, hc.preimage_V, inter_comm]
    rfl
  have hi : InjOn φ (φ ⁻¹' tilde e) := fun x hx y _ he => (hc.inj x y he).resolve_right fun h
    => hx.2 h
  rw [h1, ← hi.ncard_image, image_preimage_eq _ hc.surjective, hc.not_loop]

omit [T1Space S] in
theorem connectedComponentIn_subset_of_cuff {C₀ : Set S} (h : C₀ ∈ cuffs S) : C₀ ⊆ bd S := by
  obtain ⟨y, -, rfl⟩ := h
  exact connectedComponentIn_subset _ _

omit [T1Space S] in
/-- Graph Minors VII, (7.2). -/
theorem IsCutAlongEdge.boundaryLinked (hc : IsCutAlongEdge G e a b c Y φ G') (hS : IsSurface S)
  (h3 : 3 ≤ 3 * a + 3 * b + c)
    (hm : Nonempty (S ≃ₜ SurfaceModel a b c)) (hBL : IsBoundaryLinked G)
    (hno : ¬ ∃ A : Set S, G.IsNormal A ∧ IsNullHomotopicOArc A ∧ (G.V ∩ A).ncard ≤ 1
      ∧ IsInsideOArc e A) :
    IsBoundaryLinked G' := by
  have : ConnectedSpace S := connectedSpace_of_model hm
  have : ConnectedSpace Y := connectedSpace_of_model hc.homeo_model
  have hnsY : ¬ IsSphere Y := not_isSphere_of_model hc.homeo_model (by omega)
  have hYs := hc.isSurface
  have : CompactSpace Y := hYs.1
  have : T2Space Y := hYs.2.1
  have : T2Space S := hS.2.1
  refine ⟨hc.isProper, fun C hC F hFn hF hsur => ?_⟩
  obtain ⟨H, hH, h0, hinj, hpush⟩ := hc.exists_push
  have hρc : Continuous fun y => H (1, y) := hH.comp (continuous_const.prodMk continuous_id)
  obtain ⟨hn, hN, hcnt⟩ := hpush F hFn
  obtain ⟨hi, hnorm, hcnt2⟩ := hc.image_facts hn hN
  have hsur₁ := surrounds_of_push hYs hH h0 hinj hF hnsY hsur
  have hρe : IsEmbedding fun y => H (1, y) := (hρc.isClosedEmbedding hinj).isEmbedding
  have hF₁ : IsOArc ((fun y => H (1, y)) '' F) := GM11.isOArc_image hF hρc.continuousOn hinj.injOn
  rw [← hcnt, ← hcnt2]
  obtain ⟨f⟩ := id hF₁
  obtain ⟨e₂, he₂⟩ := exists_param_image f hc.continuous hi
  have hF₂ : IsOArc (φ '' ((fun y => H (1, y)) '' F)) := ⟨e₂⟩
  rcases hc.cuff_cases hS hC with rfl | ⟨C₀, hC₀, rfl⟩
  · rw [hc.ncard_new]
    by_contra hlt
    push Not at hlt
    have hnull : IsNullHomotopicOArc (φ '' ((fun y => H (1, y)) '' F)) := by
      obtain ⟨ι, E, H', hcap', hH', h0', h1'⟩ := hc.uncut
      obtain ⟨Δ, hΔ, hsub⟩ := hsur₁.2.1.2.2 S ι E hcap'
      refine ⟨e₂, ?_⟩
      have hfc : Continuous fun w => (f w).1 := continuous_subtype_val.comp f.continuous
      have h2 := null_of_homotopy_into_disc (H := fun q : 𝕀 × Y => H' (unitInterval.symm q.1, q.2))
        (hH'.comp ((unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_snd)) hfc
          hΔ fun w => by
          simpa [h0'] using hsub (mem_image_of_mem ι (f w).2)
      convert h2 using 2
      ext w
      simp [he₂, h1']
    obtain ⟨Δ, hΔ, hbd⟩ := nullHomotopicOArc_bounds_disc hS hF₂ hnull
    have heA : ∀ x ∈ e, x ∉ φ '' ((fun y => H (1, y)) '' F) := fun x hx hA =>
      hc.notMem_V hx (hnorm ⟨hA, hc.mem_U hx⟩)
    have hside := IsClosedDisc.side hS.2.2 hΔ (isPreconnected_of_edge hc.mem_E) (by
      rw [hbd, disjoint_left]
      exact heA)
    rcases hside with h | h
    · exact hno ⟨_, hnorm, hnull, by omega, fun x hx => .inl ⟨hnull, Δ, hΔ, hbd, (h hx).1,
        heA x hx⟩⟩
    · exfalso
      have hlift := (isClosedDisc_preimage_of_injOn hc.continuous hc.surjective hΔ fun x hx x' _ he
        =>
        (hc.inj x x' he).resolve_right (disjoint_right.mp h hx)).1
      refine hsur₁.2.2 ⟨_, hlift, ?_⟩
      intro y hy
      have h5 : φ y ∈ discBd Δ := by
        rw [hbd]
        exact mem_image_of_mem φ hy
      exact Surface.discBd_subset Δ h5
  · obtain ⟨hcuff, hb⟩ := hc.cuff_lift hS hC₀
    have hC'b : φ ⁻¹' C₀ ⊆ bd Y := fun y hy => by
      rw [hc.bd_eq]
      exact .inl (show φ y ∈ bd S from connectedComponentIn_subset_of_cuff hC₀ hy)
    have hC'N : φ ⁻¹' C₀ ∩ φ ⁻¹' closure e ⊆ G'.V := fun y hy =>
      (hc.bd_inter hy.2 (connectedComponentIn_subset_of_cuff hC₀ hy.1)).elim
    have hC'count : (G'.V ∩ φ ⁻¹' C₀).ncard = (G.V ∩ C₀).ncard := by
      have h1 := (hc.image_facts (A := φ ⁻¹' C₀) (fun y hy => hc.isProper ⟨hC'b hy.1, hy.2⟩)
        hC'N).2.2
      rw [image_preimage_eq _ hc.surjective] at h1
      exact h1.symm
    rw [hC'count]
    refine hBL.2 C₀ hC₀ _ hnorm hF₂ ?_
    obtain ⟨T, T', tT, tT', j, D, j', D', Ψ, hp⟩ := hc.exists_capPair hS hC₀
    have hT := hp.capS.isSurface
    have hT' := hp.capY.isSurface
    have : T2Space T := hT.2.1
    have : T2Space T' := hT'.2.1
    have : CompactSpace T' := hT'.1
    have : ConnectedSpace T := hp.capS.connectedSpace hS
    have hj := hp.capS.isEmbedding
    have hj' := hp.capY.isEmbedding
    have hF₃ : IsOArc (j' '' ((fun y => H (1, y)) '' F)) := GM11.isOArc_image hF₁
      hj'.continuous.continuousOn hj'.injective.injOn
    have hnull := (isPlanar_iff_isNullHomotopicOArc_of_isOArc hT' hF₃).mp
      (hsur₁.2.1.2.2 T' j' D' hp.capY)
    obtain ⟨Δ₆, hΔ₆, hbd₆⟩ := nullHomotopicOArc_bounds_disc hT' hF₃ hnull
    have hinjΨ : InjOn Ψ Δ₆ := by
      have hover : ∀ x ∈ Δ₆, Ψ x ∉ j '' e := by
        rintro x hx ⟨s, hs, hse⟩
        have hxr : x ∈ range j' := by
          by_contra hnr
          have hxD : x ∈ D' := (hp.capY.union_eq.ge (mem_univ x)).resolve_left hnr
          have hxi : x ∈ discInt D' := ⟨hxD, fun hb' => hnr (by
            rw [hp.capY.discBd_eq] at hb'
            exact image_subset_range _ _ hb')⟩
          have h1 := hp.inner hxi
          rw [← hse] at h1
          have h2 : j s ∈ range j ∩ D := ⟨mem_range_self s, h1.1⟩
          rw [hp.capS.inter_eq, ← hp.capS.discBd_eq] at h2
          exact h1.2 h2
        obtain ⟨y, rfl⟩ := hxr
        rw [hp.comm] at hse
        have hys : φ y = s := (hj.injective hse).symm ▸ rfl
        have hyN : y ∈ φ ⁻¹' closure e := by
          change φ y ∈ closure e
          rw [hys]
          exact subset_closure hs
        have hyb : j' y ∈ bd T' := by
          rw [hp.bdY]
          refine ⟨y, ⟨?_, ?_⟩, rfl⟩
          · rw [hc.bd_eq]
            exact .inr hyN
          · intro hyC
            exact hc.bd_inter hyN (connectedComponentIn_subset_of_cuff hC₀ hyC)
        have hyd : j' y ∈ discBd Δ₆ := by
          by_contra hnb
          exact hyb (isInteriorPoint_of_mem_discInt hT'.2.2 hΔ₆ ⟨hx, hnb⟩)
        rw [hbd₆] at hyd
        obtain ⟨y', hy', hee⟩ := hyd
        rw [hj'.injective hee] at hy'
        have h4 := hN ⟨hy', hyN⟩
        rw [hc.preimage_V] at h4
        exact hc.notMem_V (hys ▸ hs) h4
      exact fun x hx x' _ he => (hp.inj x x' he).resolve_right (hover x hx)
    obtain ⟨hΔ₇, hbd₇⟩ := isClosedDisc_image_of_injOn hΔ₆ hp.cont hinjΨ
    have hbd₈ : discBd (Ψ '' Δ₆) = j '' (φ '' ((fun y => H (1, y)) '' F)) := by
      rw [hbd₇, hbd₆, image_image, image_image, image_image, image_image]
      exact image_congr fun y _ => hp.comm _
    refine ⟨hC₀, isPlanarInCappedCuff_of_cap hS hp.capS ⟨_, hΔ₇, hbd₈ ▸ Surface.discBd_subset _⟩,
      fun hplan => ?_⟩
    have hnull₂ := (isPlanar_iff_isNullHomotopicOArc_of_isOArc hS hF₂).mp hplan
    obtain ⟨Δ₅, hΔ₅, hbd₅⟩ := nullHomotopicOArc_bounds_disc hS hF₂ hnull₂
    obtain ⟨hΔ₉, hbd₉⟩ := isClosedDisc_image_of_injOn hΔ₅ hj.continuous hj.injective.injOn
    have heq := eq_of_discBd_eq hT (not_isSphere_cap hS h3 hm hp.capS) hΔ₉ hΔ₇
      (by rw [hbd₉, hbd₅, hbd₈])
    have hsubr : Δ₆ ⊆ range j' := by
      intro x hx
      by_contra hnr
      have hxD : x ∈ D' := (hp.capY.union_eq.ge (mem_univ x)).resolve_left hnr
      have hxi : x ∈ discInt D' := ⟨hxD, fun hb' => hnr (by
        rw [hp.capY.discBd_eq] at hb'
        exact image_subset_range _ _ hb')⟩
      have h1 := hp.inner hxi
      have h2 : Ψ x ∈ j '' Δ₅ := heq ▸ mem_image_of_mem Ψ hx
      obtain ⟨s, -, hs⟩ := h2
      have h3' : Ψ x ∈ range j ∩ D := ⟨⟨s, hs⟩, h1.1⟩
      rw [hp.capS.inter_eq, ← hp.capS.discBd_eq] at h3'
      exact h1.2 h3'
    refine hsur₁.2.2 ⟨_, isClosedDisc_preimage_of_subset_range hj'.continuous hj'.injective hΔ₆
      hsubr, fun y hy => ?_⟩
    have h5 : j' y ∈ discBd Δ₆ := by
      rw [hbd₆]
      exact mem_image_of_mem j' hy
    exact Surface.discBd_subset Δ₆ h5

end Bounds

end GraphMinor.GM07
