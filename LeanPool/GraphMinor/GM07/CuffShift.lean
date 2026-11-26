/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CollarPush
public import LeanPool.GraphMinor.GM07.CylinderCap
public import LeanPool.GraphMinor.GM07.GoodEdge

/-!
# Moving a cuff to an `O`-arc

The first half of the step of Graph Minors VII, (6.1), page 238. The paper cuts `Σ` along an `O`-arc
`A` around a cuff `C`, keeps the part `Σ'` outside `A`, and says "Loosely, we regard $\Sigma'$ as a
subset of $\Sigma$". We make this exact by a map `h : Σ → Σ` onto the part outside `A` that is
homotopic to the identity and fixes the other cuffs (`IsCuffShift`). The graph `G'` of the paper is
the
preimage of `G` under `h`.

The paper does not say why `α(G') ≥ α(G)`. Since `h` is homotopic to the identity, the image of a
candidate of `G'` is a candidate of `G` with the same vertices (`alpha_le_of_shift`). Also `G'`
has some candidate, as any proper graph has (`exists_alphaCandidate`): two cuffs joined by a normal
line.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function GraphMinor.Surface GraphMinor.GM11

universe u

local notation "𝕀" => unitInterval

/-- The preimage of a drawing under a closed embedding whose range holds it. -/
theorem exists_pull_drawing {S : Type*} {T : Type*} [TopologicalSpace S] [TopologicalSpace T]
  [Nonempty S] {j : S → T} (hj : IsClosedEmbedding j)
    (Γ : Drawing T)
    (hU : Γ.U ⊆ range j) : ∃ G : Drawing S, G.U = j ⁻¹' Γ.U ∧ G.V = j ⁻¹' Γ.V ∧ IsMatched G Γ j ∅
      := by
  classical
  have hVr : Γ.V ⊆ range j := Γ.V_subset_U.trans hU
  have himU : j '' (j ⁻¹' Γ.U) = Γ.U := image_preimage_eq_of_subset hU
  have himV : j '' (j ⁻¹' Γ.V) = Γ.V := image_preimage_eq_of_subset hVr
  have hset : j '' (j ⁻¹' Γ.U \ j ⁻¹' Γ.V) = Γ.U \ Γ.V := by
    rw [image_sdiff hj.injective, himU, himV]
  have harc : ∀ {F : Set S}, arcComponentsIn (j '' F) = image j '' arcComponentsIn F := fun {F}
    => by
    refine arcComponentsIn_image (g := invFun j) hj.continuous.continuousOn ?_ fun x _
      => leftInverse_invFun hj.injective x
    rw [hj.isInducing.continuousOn_iff]
    refine continuousOn_id.congr ?_
    rintro _ ⟨x, -, rfl⟩
    simp [leftInverse_invFun hj.injective x]
  have hcl : ∀ e : Set S, closure (j '' e) = j '' closure e := fun e =>
    (image_closure_subset_closure_image hj.continuous).antisymm' (closure_minimal
      (image_mono subset_closure) (hj.isClosedMap _ isClosed_closure))
  have hE : ∀ e ∈ arcComponentsIn (j ⁻¹' Γ.U \ j ⁻¹' Γ.V), j '' e ∈ Γ.E := fun e he => by
    change j '' e ∈ arcComponentsIn (Γ.U \ Γ.V)
    rw [← hset, harc]
    exact mem_image_of_mem _ he
  have hpre : ∀ e : Set S, j ⁻¹' (j '' e) = e := fun e => preimage_image_eq _ hj.injective
  let G : Drawing S :=
    { U := j ⁻¹' Γ.U
      V := j ⁻¹' Γ.V
      V_subset_U := preimage_mono Γ.V_subset_U
      isClosed_U := Γ.isClosed_U.preimage hj.continuous
      finite_V := Γ.finite_V.preimage hj.injective.injOn
      finite_edges := Set.Finite.of_finite_image (Γ.finite_edges.subset (by
        rintro _ ⟨e, he, rfl⟩
        exact hE e he)) (image_injective.mpr hj.injective).injOn
      edge_cond := by
        intro e he
        have hcap : closure (j '' e) ∩ Γ.V = j '' (closure e ∩ j ⁻¹' Γ.V) := by
          rw [hcl, image_inter hj.injective, himV]
        rcases Γ.edge_cond _ (hE e he) with ⟨u, v, h1, h2, h3⟩ | ⟨u, h2, h3⟩
        · have hu : u ∈ Γ.V := (h2.ge (mem_insert _ _)).2
          have hv : v ∈ Γ.V := (h2.ge (mem_insert_of_mem _ rfl)).2
          obtain ⟨u', rfl⟩ := hVr hu
          obtain ⟨v', rfl⟩ := hVr hv
          refine .inl ⟨u', v', fun h => h1 (by rw [h]), ?_, ?_⟩
          · apply image_injective.mpr hj.injective
            rw [← hcap, h2, image_pair]
          · rw [hcl] at h3
            have := pull_line hj.isEmbedding h3 (image_subset_range _ _)
            rwa [hpre] at this
        · have hu : u ∈ Γ.V := (h2.ge rfl).2
          obtain ⟨u', rfl⟩ := hVr hu
          refine .inr ⟨u', ?_, ?_⟩
          · apply image_injective.mpr hj.injective
            rw [← hcap, h2, image_singleton]
          · rw [hcl] at h3
            have := pull_oArc hj.isEmbedding h3 (image_subset_range _ _)
            rwa [hpre] at this }
  refine ⟨G, rfl, rfl, hj.continuous, hj.injective.injOn, empty_subset _,
    fun _ _ => disjoint_empty _, by simpa using himU, by simpa using himV, ?_⟩
  change Γ.E = image j '' arcComponentsIn (j ⁻¹' Γ.U \ j ⁻¹' Γ.V)
  rw [← harc, hset]
  rfl

variable {S : Type u} [TopologicalSpace S]

/-- A map of `S` into itself that is homotopic to the identity, and fixes the points of all cuffs
but `C` during the homotopy. -/
structure IsCuffShift (C : Set S) (h : S → S) (Φ : 𝕀 × S → S) : Prop where
  cont : Continuous h
  contΦ : Continuous Φ
  inj : Injective h
  zero : ∀ x, Φ (0, x) = x
  one : ∀ x, Φ (1, x) = h x
  fix : ∀ x ∈ bd S, x ∉ C → h x = x ∧ ∀ t, Φ (t, x) = x

variable {C : Set S} {h : S → S} {Φ : 𝕀 × S → S} {T : Type u} [TopologicalSpace T]

theorem IsCuffShift.isClosedEmbedding [CompactSpace S] [T2Space S] (hs : IsCuffShift C h Φ) :
  IsClosedEmbedding h :=
  hs.cont.isClosedEmbedding hs.inj

/-- A solid set that is planar stays planar under the shift. -/
theorem IsCuffShift.planar_image [CompactSpace S] [T2Space S] (hs : IsCuffShift C h Φ)
  (hT : IsSurface T) [ConnectedSpace T] (hns : ¬ IsSphere T) {j : S → T}
    (hj : IsEmbedding j) {X : Set S} (hX : IsSolid X)
    (hp : IsPlanar (j '' X)) : IsPlanar (j '' (h '' X)) := by
  obtain ⟨Δ, hΔ, hs'⟩ := hp
  have h1 := isPlanar_of_homotopy (j := j ∘ h) (X := X) (H := fun q => j (Φ
    (unitInterval.symm q.1, q.2))) hT (hj.comp hs.isClosedEmbedding.isEmbedding) hX (.inl hns)
    (hj.continuous.comp (hs.contΦ.comp ((unitInterval.continuous_symm.comp continuous_fst).prodMk
      continuous_snd))) (fun y => by simp [hs.one])
    fun F _ hFX => ⟨Δ, hΔ, fun y hy => by
      have : Φ (unitInterval.symm 1, y) = y := by simp [hs.zero]
      simp only [this]
      exact hs' (mem_image_of_mem j (hFX hy))⟩
  rwa [image_comp] at h1

/-- A solid set is planar if its image under the shift is planar. -/
theorem IsCuffShift.planar_of_image [CompactSpace S] [T2Space S] (hs : IsCuffShift C h Φ)
  (hT : IsSurface T) [ConnectedSpace T] (hns : ¬ IsSphere T) {j : S → T}
    (hj : IsEmbedding j) {X : Set S} (hX : IsSolid X)
    (hp : IsPlanar (j '' (h '' X))) : IsPlanar (j '' X) := by
  obtain ⟨Δ, hΔ, hs'⟩ := hp
  refine isPlanar_of_homotopy (H := fun q => j (Φ q)) hT hj hX (.inl hns)
    (hj.continuous.comp hs.contΦ) (fun y => by simp [hs.zero])
    fun F _ hFX => ⟨Δ, hΔ, fun y hy => ?_⟩
  simp only [hs.one]
  exact hs' (mem_image_of_mem j (mem_image_of_mem h (hFX hy)))

variable {a b c : ℕ}

/-- Planarity in `Σ + CHat` is the same before and after the shift. -/
theorem IsCuffShift.planarInCap_iff (hS : IsSurface S) [ConnectedSpace S] (hs : IsCuffShift C h Φ)
  (habc : 3 ≤ 3 * a + 3 * b + c) (hm : Nonempty (S ≃ₜ SurfaceModel a b c)) {C₁ X : Set S}
    (hC₁ : IsCuff C₁)
    (hX : IsSolid X) : IsPlanarInCappedCuff C₁ (h '' X) ↔ IsPlanarInCappedCuff C₁ X := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  obtain ⟨T₁, tT, j, D, hc, -⟩ := exists_cappedCuff hS hC₁
  have hT := hc.isSurface
  have : ConnectedSpace T₁ := hc.connectedSpace hS
  have hns := not_isSphere_cap hS habc hm hc
  constructor
  · rintro ⟨-, -, h2⟩
    exact isPlanarInCappedCuff_of_cap hS hc (hs.planar_of_image hT hns hc.isEmbedding hX
      (h2 _ j D hc))
  · rintro ⟨-, -, h2⟩
    exact isPlanarInCappedCuff_of_cap hS hc (hs.planar_image hT hns hc.isEmbedding hX (h2 _ j D hc))

/-- Planarity in `Σ` is the same before and after the shift. -/
theorem IsCuffShift.planar_iff (hS : IsSurface S) [ConnectedSpace S] (hs : IsCuffShift C h Φ)
  (hns : ¬ IsSphere S) {X : Set S} (hX : IsSolid X) : IsPlanar (h '' X) ↔ IsPlanar X := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  constructor
  · intro hp
    simpa using hs.planar_of_image hS hns IsEmbedding.id hX (by simpa using hp)
  · intro hp
    simpa using hs.planar_image hS hns IsEmbedding.id hX (by simpa using hp)

theorem IsCuffShift.nearPlanar_iff (hS : IsSurface S) [ConnectedSpace S] (hs : IsCuffShift C h Φ)
  (habc : 3 ≤ 3 * a + 3 * b + c) (hm : Nonempty (S ≃ₜ SurfaceModel a b c))
    (hns : ¬ IsSphere S) {X : Set S}
    (hX : IsSolid X) : IsNearPlanar (h '' X) ↔ IsNearPlanar X := by
  unfold IsNearPlanar
  rw [hs.planar_iff hS hns hX]
  refine or_congr Iff.rfl (exists_congr fun C₁ => and_congr_right fun hC₁
    => hs.planarInCap_iff hS habc hm hC₁ hX)

theorem IsCuffShift.surrounds_iff (hS : IsSurface S) [ConnectedSpace S] (hs : IsCuffShift C h Φ)
  (habc : 3 ≤ 3 * a + 3 * b + c) (hm : Nonempty (S ≃ₜ SurfaceModel a b c))
    (hns : ¬ IsSphere S) {X C₁ : Set S}
    (hC₁ : C₁ ∈ cuffs S) (hX : IsSolid X) : SurroundsCuff (h '' X) C₁ ↔ SurroundsCuff X C₁ := by
  unfold SurroundsCuff
  rw [hs.planar_iff hS hns hX, hs.planarInCap_iff hS habc hm hC₁ hX]

/-- Every proper graph has a candidate for `α`, if there are two cuffs: the cuffs, joined by a
normal line. -/
theorem exists_alphaCandidate (hS : IsSurface S) [ConnectedSpace S] (habc : 3
  ≤ 3 * a + 3 * b + c) (hm : Nonempty (S ≃ₜ SurfaceModel a b c)) (hcyl : ¬ Nonempty
    (S ≃ₜ SurfaceModel 0 0 2))
    {G : Drawing S} (hG : G.IsProper) {C₁ C₂ : Set S} (h₁ : C₁ ∈ cuffs S) (h₂ : C₂ ∈ cuffs S)
      (hne : C₁ ≠ C₂) : ∃ X, IsAlphaCandidate G X := by
  have : T2Space S := hS.2.1
  have hsub : ∀ {C : Set S}, C ∈ cuffs S → C ⊆ bd S := fun hC =>
    connectedComponentIn_subset_of_cuff hC
  have hA₁ := isScriptASet_cuff hS habc hm hG h₁ le_rfl
  have hA₂ := isScriptASet_cuff hS habc hm hG h₂ le_rfl
  obtain ⟨x, hx⟩ := hA₁.2.1.1
  obtain ⟨y, hy⟩ := hA₂.2.1.1
  have hxy : x ≠ y := fun e => by
    have := cuffs_disjoint h₁ h₂ hne
    exact disjoint_left.mp this hx (e ▸ hy)
  have hnorm : ∀ {C : Set S}, C ⊆ bd S → ∀ {z}, z ∈ C → z ∈ (G.U \ G.V)ᶜ := fun hC z hz hU => hU.2
    (hG ⟨hC hz, hU.1⟩)
  obtain ⟨X₀, hX₀, hfin, -⟩ := distPoint_exists_arc hS hG hxy
  obtain ⟨P, hP, hPn, -⟩ := exists_normal_arc_of_lineWithEnds hS hG (hnorm (hsub h₁) hx) (hnorm
    (hsub h₂) hy) hX₀ hfin
  have hsolP : IsSolid P := isSolid_of_isLineWithEnds hS hP
  have hcP : IsPreconnected P := by
    obtain ⟨f, -, -⟩ := id hP
    have h3 := isPreconnected_range (continuous_subtype_val.comp f.continuous)
    rwa [range_comp, f.surjective.range_eq, image_univ, Subtype.range_coe] at h3
  have hxP : x ∈ P := by
    obtain ⟨f, h0, -⟩ := id hP
    rw [← h0]
    exact (f 0).2
  have hyP : y ∈ P := by
    obtain ⟨f, -, h0⟩ := id hP
    rw [← h0]
    exact (f 1).2
  have hsol : IsSolid (C₁ ∪ P ∪ C₂) := theorem_11_6_proof hS (theorem_11_6_proof hS hA₁.1 hsolP)
    hA₂.1
  have hconn : IsConnected (C₁ ∪ P ∪ C₂) := by
    refine ⟨⟨x, .inl (.inl hx)⟩, ?_⟩
    have h1 : IsPreconnected (C₁ ∪ P) := hA₁.2.1.2.union x hx hxP hcP
    exact h1.union y (.inr hyP) hy hA₂.2.1.2
  refine ⟨_, hsol, hconn, ?_, ?_⟩
  · rintro z ⟨(hz | hz) | hz, hU⟩
    · exact hG ⟨hsub h₁ hz, hU⟩
    · exact hPn ⟨hz, hU⟩
    · exact hG ⟨hsub h₂ hz, hU⟩
  · rintro (hp | ⟨C₀, hC₀, hp⟩)
    · exact hA₁.2.2.2.1.2.2 (IsPlanar.mono hp (fun z hz => .inl (.inl hz)))
    · by_cases he : C₀ = C₁
      · have hne' : C₂ ≠ C₀ := by rw [he]; exact hne.symm
        exact hcyl (surroundsCuff_and_planarInCappedCuff_imp_cylinder hS h₂ hC₀ hne'
          ((cuff_statement.{u} S hS).2.2 C₂ h₂) hA₂.2.2.2.1 (hp.mono fun z hz => .inr hz))
      · exact hcyl (surroundsCuff_and_planarInCappedCuff_imp_cylinder hS h₁ hC₀ (Ne.symm he)
          ((cuff_statement.{u} S hS).2.2 C₁ h₁) hA₁.2.2.2.1 (hp.mono fun z hz => .inl (.inl hz)))

section Graph

variable {G G' : Drawing S}

theorem image_inter_pull (hV : G'.V = h ⁻¹' G.V) (X : Set S) : G.V ∩ h '' X = h '' (G'.V ∩ X) := by
  rw [hV, inter_comm, inter_comm _ X]
  exact (image_inter_preimage h X G.V).symm

/-- The image of a candidate of `G'` is a candidate of `G` with as many vertices. -/
theorem alpha_le_of_shift (hS : IsSurface S) [ConnectedSpace S]
  (hs : IsCuffShift C h Φ) (habc : 3 ≤ 3 * a + 3 * b + c) (hm : Nonempty (S ≃ₜ SurfaceModel a b c))
    (hns : ¬ IsSphere S)
    (hU : G'.U = h ⁻¹' G.U) (hV : G'.V = h ⁻¹' G.V) (hex : ∃ X, IsAlphaCandidate G' X) : alpha G
      ≤ alpha G' := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  obtain ⟨X₀, hX₀⟩ := hex
  refine le_csInf ⟨_, X₀, hX₀, rfl⟩ ?_
  rintro _ ⟨X, ⟨h1, h2, h3, h4⟩, rfl⟩
  have hc : IsAlphaCandidate G (h '' X) := by
    refine ⟨isSolid_image_of_isClosedEmbedding hs.isClosedEmbedding h1, h2.image _
      hs.cont.continuousOn, ?_, fun hn => h4 ((hs.nearPlanar_iff hS habc hm hns h1).mp hn)⟩
    rintro _ ⟨⟨y, hy, rfl⟩, hyU⟩
    have : y ∈ G'.V := h3 ⟨hy, by rw [hU]; exact hyU⟩
    rw [hV] at this
    exact this
  refine (alpha_le_of_candidate hc).trans (le_of_eq ?_)
  rw [inter_comm, image_inter_pull hV, ncard_image_of_injective _ hs.inj, inter_comm]

/-- The preimage of `G` is boundary-linked, if `G` is, and no `O`-arc in the range of `h` around `C`
has fewer vertices than the new cuff. -/
theorem boundaryLinked_of_shift (hS : IsSurface S) [ConnectedSpace S]
  (hs : IsCuffShift C h Φ) (habc : 3 ≤ 3 * a + 3 * b + c) (hm : Nonempty (S ≃ₜ SurfaceModel a b c))
    (hns : ¬ IsSphere S)
    (hU : G'.U = h ⁻¹' G.U) (hV : G'.V = h ⁻¹' G.V) (hp : G'.IsProper) (hbl : IsBoundaryLinked G)
    (hCc : C ∈ cuffs S) (hmax : ∀ F, G.IsNormal F → IsOArc F → SurroundsCuff F C → F ⊆ range h →
      (G'.V ∩ C).ncard ≤ (G.V ∩ F).ncard) : IsBoundaryLinked G' := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  refine ⟨hp, fun C₁ hC₁ F hFn hFO hFs => ?_⟩
  have hsol : IsSolid F := isSolid_of_isOArc hS hFO
  have hnorm : G.IsNormal (h '' F) := by
    rintro _ ⟨⟨y, hy, rfl⟩, hyU⟩
    have : y ∈ G'.V := hFn ⟨hy, by rw [hU]; exact hyU⟩
    rw [hV] at this
    exact this
  have hO : IsOArc (h '' F) := by
    obtain ⟨f⟩ := id hFO
    exact ⟨f.trans (hs.isClosedEmbedding.isEmbedding.homeomorphImage F)⟩
  have hs' : SurroundsCuff (h '' F) C₁ := (hs.surrounds_iff hS habc hm hns hC₁ hsol).mpr hFs
  have hc : (G.V ∩ h '' F).ncard = (G'.V ∩ F).ncard := by
    rw [image_inter_pull hV, ncard_image_of_injective _ hs.inj]
  rw [← hc]
  by_cases he : C₁ = C
  · subst he
    exact hmax _ hnorm hO hs' (image_subset_range _ _)
  · have h1 := hbl.2 C₁ hC₁ _ hnorm hO hs'
    refine le_trans (le_of_eq ?_) h1
    congr 1
    ext x
    constructor
    · rintro ⟨hx, hxC⟩
      have hb : x ∈ bd S := connectedComponentIn_subset_of_cuff hC₁ hxC
      have hnC : x ∉ C := fun hxC' => disjoint_left.mp (cuffs_disjoint hC₁ hCc he) hxC hxC'
      rw [hV, mem_preimage, (hs.fix x hb hnC).1] at hx
      exact ⟨hx, hxC⟩
    · rintro ⟨hx, hxC⟩
      have hb : x ∈ bd S := connectedComponentIn_subset_of_cuff hC₁ hxC
      have hnC : x ∉ C := fun hxC' => disjoint_left.mp (cuffs_disjoint hC₁ hCc he) hxC hxC'
      refine ⟨?_, hxC⟩
      rw [hV, mem_preimage, (hs.fix x hb hnC).1]
      exact hx

end Graph

end GraphMinor.GM07
