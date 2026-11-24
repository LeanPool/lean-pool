/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section5a
public import LeanPool.GraphMinor.GM07.Section5b
public import LeanPool.GraphMinor.GM07.Section11b
public import LeanPool.GraphMinor.Surface.CutLift
public import LeanPool.GraphMinor.Surface.SurfaceGraph
import LeanPool.GraphMinor.GM19.Section6a
import LeanPool.GraphMinor.Surface.Epstein

/-!
# Graph Minors VII, Section 8: Schisms and Schismatic Sets (pages 241–242)

This file formalizes Section 8 of Robertson and Seymour,
*Graph Minors. VII. Disjoint Paths on a Surface*, J. Combin. Theory Ser. B **45** (1988), 212–254:
- `not_ssubset_of_isOArc`: no `O`-arc is a proper subset of another `O`-arc.
- `IsNearPlanar.mono`: monotonicity of `IsNearPlanar`.
- `theorem_5_1_of_not_isSphere`: (5.1) for any solid subset `X ⊆ S` when `¬ IsSphere S ∨ X ≠ univ`.
- `isPlanarInCappedCuff_iff_forall_isOArc`: a solid subset `X ⊆ S` is planar in `Σ + Ĉ` if and only
  if every `O`-arc `F ⊆ X` is planar in `Σ + Ĉ`.
- `isNearPlanar_iff_forall_not_isSchismatic`: "It is easy to verify, using (5.1) and (5.2), that if
  $X \subseteq \Sigma$ is solid and connected, then $X$ is near-planar if and only if no subset of
  $X$ is
  schismatic." (page 241).
- `exists_schismatic_of_isAlphaCandidate`: every `α(G)`-candidate `X` (`IsAlphaCandidate G X`) on a
  connected non-sphere surface contains a `G`-normal schismatic subset `Y ⊆ X` (providing the
  hypothesis `hcontains` of `GraphMinor.GM12.alpha_ge_of_schismatic_counts`).
- `alpha_eq_sInf_schismatic`: "Thus $\alpha(G)$ equals the minimum of $|V(G) \cap X|$, taken over
  all
  $G$-normal schismatic sets $X$" (page 241).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Function Topology Metric Filter unitInterval
open GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-! ## 1. Basic Properties of `O`-Arcs, `[0, 1]`-Arcs, and `X_i`-Arcs -/

/-- No `O`-arc in a Hausdorff space is a proper subset of another `O`-arc. -/
theorem not_ssubset_of_isOArc [T2Space S] {F F' : Set S}
    (hF : IsOArc F) (hF' : IsOArc F') :
    ¬ (F' ⊂ F) := by
  intro ⟨hsub, hnot⟩
  obtain ⟨x, hxF, hxF'⟩ := not_subset.mp hnot
  obtain ⟨y, hyF'⟩ := isOArc_nonempty hF'
  have hyF : y ∈ F := hsub hyF'
  have hxy : x ≠ y := fun h => hxF' (h ▸ hyF')
  obtain ⟨A, B, hA, hB, hAB_union, hAB_inter⟩ := hF.lines hxF hyF hxy
  have hG : IsGraph ({x, y} : Set S) ({A, B} : Set (Set S)) := by
    refine ⟨(finite_singleton y).insert x, (finite_singleton B).insert A, ?_, ?_⟩
    · rintro e (rfl | rfl)
      · exact ⟨x, y, hxy, hA, inter_eq_right.mpr
          (pair_subset hA.left_mem hA.right_mem)⟩
      · exact ⟨x, y, hxy, hB, inter_eq_right.mpr
          (pair_subset hB.left_mem hB.right_mem)⟩
    · rintro e (rfl | rfl) f (rfl | rfl) hne
      · exact (hne rfl).elim
      · exact hAB_inter.le
      · rw [inter_comm]
        exact hAB_inter.le
      · exact (hne rfl).elim
  have hF'_gr : F' ⊆ gr ({x, y} : Set S) ({A, B} : Set (Set S)) := by
    intro z hz
    rcases hAB_union ▸ hsub hz with hzA | hzB
    · exact Or.inr ⟨A, Or.inl rfl, hzA⟩
    · exact Or.inr ⟨B, Or.inr rfl, hzB⟩
  have hnot_A : ¬ (A ⊆ F') := fun h => hxF' (h hA.left_mem)
  have hnot_B : ¬ (B ⊆ F') := fun h => hxF' (h hB.left_mem)
  have hdisj_A : Disjoint (A \ {x, y}) F' :=
    (hG.edge_or hF' hF'_gr (Or.inl rfl)).resolve_left hnot_A
  have hdisj_B : Disjoint (B \ {x, y}) F' :=
    (hG.edge_or hF' hF'_gr (Or.inr rfl)).resolve_left hnot_B
  obtain ⟨z, hzF', hzy⟩ := hF'.exists_ne y
  have hzx : z ≠ x := fun h => hxF' (h ▸ hzF')
  have hz_not_xy : z ∉ ({x, y} : Set S) := by
    rw [mem_insert_iff, mem_singleton_iff]
    exact not_or.mpr ⟨hzx, hzy⟩
  rcases hAB_union ▸ hsub hzF' with hzA | hzB
  · exact disjoint_left.mp hdisj_A ⟨hzA, hz_not_xy⟩ hzF'
  · exact disjoint_left.mp hdisj_B ⟨hzB, hz_not_xy⟩ hzF'

/-- Every `[0, 1]`-arc in a Hausdorff space is solid (`IsSolid`). -/
theorem IsLineWithEnds.isSolid [T2Space S] {L : Set S} {u v : S}
    (hL : IsLineWithEnds L u v) : IsSolid L := by
  obtain ⟨f, _, _⟩ := hL
  let g : I → S := fun t => (f t).1
  have hg : Continuous g := continuous_subtype_val.comp f.continuous
  have hrange : L = range g := by
    ext x
    constructor
    · intro hx
      exact ⟨f.symm ⟨x, hx⟩, by simp [g]⟩
    · rintro ⟨t, rfl⟩
      exact (f t).2
  rw [hrange]
  exact ⟨isLocallyArcConnected_of_locJoin fun x hx => locJoin_range hg hx,
    (isCompact_range hg).isClosed⟩

/-- Every `[0, 1]`-arc is connected (`IsConnected`). -/
theorem IsLineWithEnds.isConnected {L : Set S} {u v : S}
    (hL : IsLineWithEnds L u v) : IsConnected L := by
  obtain ⟨f, _, _⟩ := hL
  let g : I → S := fun t => (f t).1
  have hg : Continuous g := continuous_subtype_val.comp f.continuous
  have hrange : L = range g := by
    ext x
    constructor
    · intro hx
      exact ⟨f.symm ⟨x, hx⟩, by simp [g]⟩
    · rintro ⟨t, rfl⟩
      exact (f t).2
  rw [hrange]
  exact isConnected_range hg

/-- Every `O`-arc is connected (`IsConnected`). -/
theorem IsOArc.isConnected {F : Set S} (hF : IsOArc F) : IsConnected F :=
  ⟨isOArc_nonempty hF, hF.isPreconnected⟩

private lemma isConnected_union {A B : Set S} (hA : IsConnected A) (hB : IsConnected B)
    (hne : (A ∩ B).Nonempty) : IsConnected (A ∪ B) := by
  obtain ⟨x, hxA, hxB⟩ := hne
  exact ⟨⟨x, Or.inl hxA⟩, hA.2.union x hxA hxB hB.2⟩

/-- Every `X₁`-arc in a surface is solid and connected. -/
theorem IsX1Arc.isSolid_and_isConnected (hS : IsSurface S) {X : Set S} (hX : IsX1Arc X) :
    IsSolid X ∧ IsConnected X := by
  have : T2Space S := hS.2.1
  obtain ⟨A₁, A₂, P, u, v, hA₁, hA₂, _, hP, huA₁, hvA₂, _, _, rfl⟩ := hX
  have hsol : IsSolid (A₁ ∪ A₂ ∪ P) :=
    theorem_11_6_proof hS (theorem_11_6_proof hS (IsOArc.isSolid hA₁) (IsOArc.isSolid hA₂))
      (IsLineWithEnds.isSolid hP)
  have hA₁P_conn : IsConnected (A₁ ∪ P) :=
    isConnected_union (IsOArc.isConnected hA₁) (IsLineWithEnds.isConnected hP)
      ⟨u, huA₁, hP.left_mem⟩
  have hconn : IsConnected (A₁ ∪ P ∪ A₂) :=
    isConnected_union hA₁P_conn (IsOArc.isConnected hA₂)
      ⟨v, Or.inr hP.right_mem, hvA₂⟩
  rw [union_right_comm] at hconn
  exact ⟨hsol, hconn⟩

/-- Every `X₂`-arc in a surface is solid and connected. -/
theorem IsX2Arc.isSolid_and_isConnected (hS : IsSurface S) {X : Set S} (hX : IsX2Arc X) :
    IsSolid X ∧ IsConnected X := by
  have : T2Space S := hS.2.1
  obtain ⟨A₁, A₂, u, hA₁, hA₂, hcap, rfl⟩ := hX
  have hu : u ∈ A₁ ∩ A₂ := hcap ▸ mem_singleton u
  exact ⟨theorem_11_6_proof hS (IsOArc.isSolid hA₁) (IsOArc.isSolid hA₂),
    isConnected_union (IsOArc.isConnected hA₁) (IsOArc.isConnected hA₂) ⟨u, hu.1, hu.2⟩⟩

/-- Every `X₃`-arc in a surface is solid and connected. -/
theorem IsX3Arc.isSolid_and_isConnected (hS : IsSurface S) {X : Set S} (hX : IsX3Arc X) :
    IsSolid X ∧ IsConnected X := by
  have : T2Space S := hS.2.1
  obtain ⟨P₁, P₂, P₃, u, v, _, hP₁, hP₂, hP₃, _, _, _, rfl⟩ := hX
  have hsol : IsSolid (P₁ ∪ P₂ ∪ P₃) :=
    theorem_11_6_proof hS (theorem_11_6_proof hS (IsLineWithEnds.isSolid hP₁)
      (IsLineWithEnds.isSolid hP₂))
      (IsLineWithEnds.isSolid hP₃)
  have h12 : IsConnected (P₁ ∪ P₂) :=
    isConnected_union (IsLineWithEnds.isConnected hP₁) (IsLineWithEnds.isConnected hP₂)
      ⟨u, hP₁.left_mem, hP₂.left_mem⟩
  have h123 : IsConnected (P₁ ∪ P₂ ∪ P₃) :=
    isConnected_union h12 (IsLineWithEnds.isConnected hP₃)
      ⟨u, Or.inl hP₁.left_mem, hP₃.left_mem⟩
  exact ⟨hsol, h123⟩

/-- Every schismatic subset of a surface is solid and connected. -/
theorem IsSchismatic.isSolid_and_isConnected (hS : IsSurface S) {X : Set S}
    (hX : IsSchismatic X) : IsSolid X ∧ IsConnected X := by
  have : T2Space S := hS.2.1
  rcases hX.1 with h | h | h | h
  · exact ⟨IsOArc.isSolid h, IsOArc.isConnected h⟩
  · exact h.isSolid_and_isConnected hS
  · exact h.isSolid_and_isConnected hS
  · exact h.isSolid_and_isConnected hS

/-- Monotonicity of `IsNearPlanar`. -/
theorem IsNearPlanar.mono {X Y : Set S} (hX : IsNearPlanar X) (hYX : Y ⊆ X) :
    IsNearPlanar Y := by
  rcases hX with hpl | ⟨C, hC, hcap⟩
  · exact Or.inl (IsPlanar.mono hpl hYX)
  · exact Or.inr ⟨C, hC, IsPlanarInCappedCuff.mono hcap hYX⟩

/-! ## 2. Planarity of Solid Sets in `Σ` and `Σ + Ĉ` via `O`-Arcs -/

/-- Graph Minors VII, (5.1) extended to all solid `X ⊆ S` when `¬ IsSphere S ∨ X ≠ univ`:
`X` is planar in `S` if and only if every `O`-arc `F ⊆ X` is planar in `S`. -/
theorem theorem_5_1_of_not_isSphere
    (hS : IsSurface S) [ConnectedSpace S] {X : Set S}
    (hns : ¬ IsSphere S ∨ X ≠ univ) (hX_solid : IsSolid X) :
    IsPlanar X ↔ ∀ F : Set S, IsOArc F → F ⊆ X → IsPlanar F := by
  have : T2Space S := hS.2.1
  constructor
  · intro hX F _ hFX
    exact IsPlanar.mono hX hFX
  · intro hall
    by_cases hX_ne : X ≠ univ
    · refine (theorem_5_1_proof hS hX_solid hX_ne).mpr fun F hF hFX => ?_
      exact (isPlanar_iff_isNullHomotopicOArc_of_isOArc hS hF).mp (hall F hF hFX)
    · have hns_S : ¬ IsSphere S := hns.resolve_right hX_ne
      have hX_univ : X = univ := not_ne_iff.mp hX_ne
      by_cases hbd : bd S = ∅
      · obtain ⟨F₀, hF₀, hF₀_nn⟩ :=
          GraphMinor.GM19.exists_not_nullHomotopic hS hbd hns_S
        exfalso
        exact hF₀_nn ((isPlanar_iff_isNullHomotopicOArc_of_isOArc hS hF₀).mp
          (hall F₀ hF₀ (hX_univ ▸ subset_univ F₀)))
      · refine isPlanar_of_solid_flat_bd_ne_empty hS hbd hX_solid ?_
        refine isFlat_of_forall_isNullHomotopicOArc hS fun F hFX hF => ?_
        exact (isPlanar_iff_isNullHomotopicOArc_of_isOArc hS hF).mp (hall F hF hFX)

/-- The image of a solid set `X ⊆ S` under the embedding `j : S → S'` of a capped cuff is solid
in `S'`. -/
theorem IsSolid.image_of_isCappedCuff (hS : IsSurface S) {C X : Set S}
    {S' : Type u} [TopologicalSpace S'] {j : S → S'} {D : Set S'}
    (hCap : IsCappedCuff C S' j D) (hX : IsSolid X) :
    IsSolid (j '' X) := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have : T2Space S' := hCap.isSurface.2.1
  have hj : IsEmbedding j := hCap.isEmbedding
  refine ⟨?_, (hX.2.isCompact.image hj.continuous).isClosed⟩
  rintro _ ⟨x, hxX, rfl⟩ A' hA'_open hjx_A'
  obtain ⟨A, hA_sub, hxA, hA_open, hXA_arc⟩ :=
    hX.1 x hxX (j ⁻¹' A') (hA'_open.preimage hj.continuous) hjx_A'
  obtain ⟨U', hU'_open, hU'_pre⟩ := hj.isInducing.isOpen_iff.mp hA_open
  refine ⟨U' ∩ A', inter_subset_right, ⟨mem_preimage.mp (hU'_pre.symm ▸ hxA), hjx_A'⟩,
    hU'_open.inter hA'_open, ?_⟩
  have heq : j '' X ∩ (U' ∩ A') = j '' (X ∩ A) := by
    ext y
    constructor
    · rintro ⟨⟨z, hzX, rfl⟩, hzU', _⟩
      exact ⟨z, ⟨hzX, hU'_pre ▸ hzU'⟩, rfl⟩
    · rintro ⟨z, ⟨hzX, hzA⟩, rfl⟩
      exact ⟨⟨z, hzX, rfl⟩, mem_preimage.mp (hU'_pre.symm ▸ hzA), hA_sub hzA⟩
  rw [heq]
  rintro _ ⟨z₁, hz₁, rfl⟩ _ ⟨z₂, hz₂, rfl⟩ hne
  obtain ⟨L, hL_sub, hL_line⟩ := hXA_arc z₁ hz₁ z₂ hz₂ (fun h => hne (congrArg j h))
  exact ⟨j '' L, image_mono hL_sub, hL_line.map_of_embedding hj⟩

/-- A solid subset `X ⊆ S` is planar in `Σ + Ĉ` (`IsPlanarInCappedCuff C X`) if and only if every
`O`-arc `F ⊆ X` is planar in `Σ + Ĉ`. -/
theorem isPlanarInCappedCuff_iff_forall_isOArc
    (hS : IsSurface S) [ConnectedSpace S] {C X : Set S}
    (hC : C ∈ cuffs S) (hX_solid : IsSolid X) :
    IsPlanarInCappedCuff C X ↔
      ∀ F : Set S, IsOArc F → F ⊆ X → IsPlanarInCappedCuff C F := by
  constructor
  · intro hX F _ hFX
    exact hX.mono hFX
  · intro hall
    have h_all : ∀ (S' : Type u) [TopologicalSpace S'] (j : S → S') (D : Set S'),
        IsCappedCuff C S' j D → IsPlanar (j '' X) := by
      intro S' _ j D hCap
      have hS' : IsSurface S' := hCap.isSurface
      have : T2Space S' := hS'.2.1
      have : T2Space S := hS.2.1
      have : ConnectedSpace S' := hCap.connectedSpace hS
      have hj : IsEmbedding j := hCap.isEmbedding
      have hjX_solid : IsSolid (j '' X) := IsSolid.image_of_isCappedCuff hS hCap hX_solid
      have hjX_ne : j '' X ≠ univ := by
        obtain ⟨hD_map, gD, cD⟩ := hCap.isClosedDisc.exists_isChart
        have hz₀ : gD 0 ∈ discInt D := by
          refine ⟨cD.gm (mem_closedBall_self zero_le_one), fun hbd => ?_⟩
          have h_sph : hD_map (gD 0) ∈ sphere (0 : ℂ) 1 :=
            cD.bd ▸ mem_image_of_mem hD_map hbd
          rw [cD.hg (mem_closedBall_self zero_le_one)] at h_sph
          simp at h_sph
        intro huniv
        have hz₀_mem : gD 0 ∈ j '' X := huniv ▸ mem_univ (gD 0)
        obtain ⟨x, _, h_eq⟩ := hz₀_mem
        have hmem_D : j x ∈ range j ∩ D := ⟨mem_range_self x, h_eq ▸ hz₀.1⟩
        rw [hCap.inter_eq, ← hCap.discBd_eq] at hmem_D
        exact hz₀.2 (h_eq ▸ hmem_D)
      refine (theorem_5_1_proof hS' hjX_solid hjX_ne).mpr fun F' hF' hF'jX => ?_
      have hF'_range : F' ⊆ range j := hF'jX.trans (image_subset_range j X)
      have hj_pre_oarc : IsOArc (j ⁻¹' F') := by
        obtain ⟨φ⟩ := id hF'
        have hex : ∀ z : Circle, ∃ x : S, j x = (φ z).1 := fun z => hF'_range (φ z).2
        choose g hg using hex
        have hg_cont : Continuous g := by
          rw [hj.continuous_iff]
          have : j ∘ g = Subtype.val ∘ φ := funext hg
          rw [this]
          exact continuous_subtype_val.comp φ.continuous
        have hg_inj : Function.Injective g := fun z₁ z₂ heq =>
          φ.injective (Subtype.ext (by rw [← hg z₁, ← hg z₂, heq]))
        have : CompactSpace S := hS.1
        have hg_emb : IsEmbedding g := (hg_cont.isClosedEmbedding hg_inj).isEmbedding
        have hrange_g : range g = j ⁻¹' F' := by
          ext x
          constructor
          · rintro ⟨z, rfl⟩
            change j (g z) ∈ F'
            rw [hg z]
            exact (φ z).2
          · intro hx
            exact ⟨φ.symm ⟨j x, hx⟩, hj.injective (by rw [hg]; simp)⟩
        rw [← hrange_g]
        exact ⟨hg_emb.toHomeomorph⟩
      have hj_pre_sub : j ⁻¹' F' ⊆ X := by
        intro x hx
        obtain ⟨y, hyX, hy_eq⟩ := hF'jX hx
        exact hj.injective hy_eq ▸ hyX
      have hj_img_eq : j '' (j ⁻¹' F') = F' := image_preimage_eq_iff.mpr hF'_range
      have hpl : IsPlanar F' :=
        hj_img_eq ▸ (hall (j ⁻¹' F') hj_pre_oarc hj_pre_sub).2.2 S' j D hCap
      exact (isPlanar_iff_isNullHomotopicOArc_of_isOArc hS' hF').mp hpl
    obtain ⟨c₀, _⟩ := isOArc_nonempty (cuff_isOArc hS hC)
    have : Nonempty S := ⟨c₀⟩
    obtain ⟨S', topS', j, D, hS', hj, hD, hunion, hinter, hbdD⟩ := paste_disc S C hS hC
    have hCap : IsCappedCuff C S' j D := ⟨hC, hS', hj.isEmbedding, hD, hbdD.1, hunion, hinter⟩
    exact ⟨hC, ⟨S', topS', j, D, hCap, h_all S' j D hCap⟩, h_all⟩

/-! ## 3. Connecting Disjoint `O`-Arcs and Non-Near-Planarity Criterion -/

/-- In a Hausdorff space, if `A₁, A₂` are nonempty disjoint closed subsets of an arc-connected set
`X`, there is a `[0, 1]`-arc `P ⊆ X` with ends `u ∈ A₁` and `v ∈ A₂` such that `P ∩ A₁ = {u}` and
`P ∩ A₂ = {v}`. -/
theorem exists_connecting_line_between_disjoint_closed [T2Space S] {X A₁ A₂ : Set S}
    (hX_arc : IsArcConnected X) (hA₁X : A₁ ⊆ X) (hA₂X : A₂ ⊆ X)
    (hA₁_closed : IsClosed A₁) (hA₂_closed : IsClosed A₂)
    (hA₁_ne : A₁.Nonempty) (hA₂_ne : A₂.Nonempty) (hdisj : Disjoint A₁ A₂) :
    ∃ P : Set S, ∃ u v : S,
      P ⊆ X ∧ u ∈ A₁ ∧ v ∈ A₂ ∧ IsLineWithEnds P u v ∧ P ∩ A₁ = {u} ∧ P ∩ A₂ = {v} := by
  obtain ⟨x₁, hx₁⟩ := hA₁_ne
  obtain ⟨x₂, hx₂⟩ := hA₂_ne
  have hx₁₂ : x₁ ≠ x₂ := fun h => disjoint_left.mp hdisj hx₁ (h ▸ hx₂)
  obtain ⟨L, hLX, e, he0, he1⟩ := hX_arc x₁ (hA₁X hx₁) x₂ (hA₂X hx₂) hx₁₂
  let γ : I → S := fun t => (e t).1
  have hγc : Continuous γ := continuous_subtype_val.comp e.continuous
  have hγ_inj : Function.Injective γ := Subtype.val_injective.comp e.injective
  have hγ_mem : ∀ t : I, γ t ∈ X := fun t => hLX (e t).2
  have hγ0 : γ 0 = x₁ := he0
  have hγ1 : γ 1 = x₂ := he1
  let K₁ : Set I := γ ⁻¹' A₂
  have hK₁_closed : IsClosed K₁ := hA₂_closed.preimage hγc
  have hK₁_ne : K₁.Nonempty := ⟨1, by change γ 1 ∈ A₂; rw [hγ1]; exact hx₂⟩
  let t₁ : I := sInf K₁
  have ht₁_mem : t₁ ∈ K₁ := hK₁_closed.csInf_mem hK₁_ne (OrderBot.bddBelow K₁)
  have hγt₁_A₂ : γ t₁ ∈ A₂ := ht₁_mem
  have ht₁_lt_not_A₂ : ∀ t : I, t < t₁ → γ t ∉ A₂ :=
    fun t hlt ht => not_lt_of_ge (csInf_le (OrderBot.bddBelow K₁) ht) hlt
  let K₀ : Set I := γ ⁻¹' A₁ ∩ Icc 0 t₁
  have hK₀_closed : IsClosed K₀ := (hA₁_closed.preimage hγc).inter isClosed_Icc
  have hK₀_ne : K₀.Nonempty :=
    ⟨0, by change γ 0 ∈ A₁; rw [hγ0]; exact hx₁,
      le_rfl, Subtype.mk_le_mk.mpr (unitInterval.nonneg t₁)⟩
  let t₀ : I := sSup K₀
  have ht₀_mem : t₀ ∈ K₀ := hK₀_closed.csSup_mem hK₀_ne (OrderTop.bddAbove K₀)
  have hγt₀_A₁ : γ t₀ ∈ A₁ := ht₀_mem.1
  have ht₀_lt_t₁ : t₀ < t₁ := by
    rcases eq_or_lt_of_le ht₀_mem.2.2 with heq | hlt
    · exfalso
      have : γ t₁ ∈ A₁ := heq ▸ hγt₀_A₁
      exact disjoint_left.mp hdisj this hγt₁_A₂
    · exact hlt
  refine ⟨γ '' Icc t₀ t₁, γ t₀, γ t₁, ?_, hγt₀_A₁, hγt₁_A₂,
    isLineWithEnds_image_Icc_of_injOn hγc ht₀_lt_t₁ hγ_inj.injOn, ?_, ?_⟩
  · rintro _ ⟨t, _, rfl⟩
    exact hγ_mem t
  · ext z
    simp only [mem_inter_iff, mem_image, mem_Icc, mem_singleton_iff]
    constructor
    · rintro ⟨⟨t, ⟨ht0, ht1⟩, rfl⟩, hγt_A₁⟩
      have ht_K₀ : t ∈ K₀ :=
        ⟨hγt_A₁, Subtype.mk_le_mk.mpr (unitInterval.nonneg t), ht1⟩
      have ht_le : t ≤ t₀ := le_csSup (OrderTop.bddAbove K₀) ht_K₀
      exact congrArg γ (le_antisymm ht_le ht0)
    · rintro rfl
      exact ⟨⟨t₀, ⟨le_rfl, ht₀_lt_t₁.le⟩, rfl⟩, hγt₀_A₁⟩
  · ext z
    simp only [mem_inter_iff, mem_image, mem_Icc, mem_singleton_iff]
    constructor
    · rintro ⟨⟨t, ⟨_, ht1⟩, rfl⟩, hγt_A₂⟩
      have ht_ge : t₁ ≤ t := csInf_le (OrderBot.bddBelow K₁) hγt_A₂
      exact congrArg γ (le_antisymm ht1 ht_ge)
    · rintro rfl
      exact ⟨⟨t₁, ⟨ht₀_lt_t₁.le, le_rfl⟩, rfl⟩, hγt₁_A₂⟩

/-- In a cylinder `S ≃ₜ SurfaceModel 0 0 2`, every subset `Z ⊆ S` is planar in `Σ + Ĉ` for every
cuff `C ∈ cuffs S`. -/
theorem isPlanarInCappedCuff_of_homeo_cylinder
    (hS : IsSurface S) [ConnectedSpace S]
    (hcyl : Nonempty (S ≃ₜ SurfaceModel 0 0 2))
    {C : Set S} (hC : C ∈ cuffs S) (Z : Set S) :
    IsPlanarInCappedCuff C Z := by
  have h_all : ∀ (S' : Type u) [TopologicalSpace S'] (j : S → S') (D : Set S'),
      IsCappedCuff C S' j D → IsPlanar (j '' Z) := by
    intro S' _ j D hCap
    obtain ⟨_, ⟨e₁⟩⟩ := cappedCuff_homeo_model hS hcyl hC hCap
    obtain ⟨eD₀⟩ := nonempty_disc_homeo
    have huniv_disc : IsClosedDisc (univ : Set S') :=
      ⟨((Homeomorph.Set.univ S').trans (e₁.trans eD₀)).symm⟩
    exact ⟨univ, huniv_disc, subset_univ _⟩
  obtain ⟨c₀, _⟩ := isOArc_nonempty (cuff_isOArc hS hC)
  have : Nonempty S := ⟨c₀⟩
  obtain ⟨S', topS', j, D, hS', hj, hD, hunion, hinter, hbdD⟩ := paste_disc S C hS hC
  have hCap : IsCappedCuff C S' j D := ⟨hC, hS', hj.isEmbedding, hD, hbdD.1, hunion, hinter⟩
  exact ⟨hC, ⟨S', topS', j, D, hCap, h_all S' j D hCap⟩, h_all⟩

/-- If `F₁ ⊆ Y` is an `O`-arc surrounding a cuff `C₁`, some subset `F₂ ⊆ S` is not planar in
`Σ + Ĉ₁` (witnessing `S ≇ Σ(0, 0, 2)`), and `Y` is not planar in `Σ + Ĉ₁`, then `Y` is not
near-planar (`¬ IsNearPlanar Y`). -/
theorem not_isNearPlanar_of_surroundsCuff_and_not_planarInCappedCuff
    (hS : IsSurface S) [ConnectedSpace S]
    {F₁ F₂ C₁ Y : Set S} (hF₁ : IsOArc F₁)
    (hF₁_surr : SurroundsCuff F₁ C₁) (hF₂_ncap : ¬ IsPlanarInCappedCuff C₁ F₂)
    (hF₁Y : F₁ ⊆ Y) (hY_ncap : ¬ IsPlanarInCappedCuff C₁ Y) :
    ¬ IsNearPlanar Y := by
  rintro (hY_pl | ⟨C, hC, hY_cap⟩)
  · exact hF₁_surr.2.2 (IsPlanar.mono hY_pl hF₁Y)
  · by_cases hCC₁ : C = C₁
    · exact hY_ncap (hCC₁ ▸ hY_cap)
    · have hF₁_capC : IsPlanarInCappedCuff C F₁ := hY_cap.mono hF₁Y
      have hcyl : Nonempty (S ≃ₜ SurfaceModel 0 0 2) :=
        surroundsCuff_and_planarInCappedCuff_imp_cylinder hS hF₁_surr.1 hC (Ne.symm hCC₁)
          hF₁ hF₁_surr hF₁_capC
      exact hF₂_ncap (isPlanarInCappedCuff_of_homeo_cylinder hS hcyl hF₁_surr.1 F₂)

/-- Union of an `O`-arc `F₁` and a `[0, 1]`-arc `P` with distinct ends `u, v` and `P ∩ F₁ = {u, v}`
is an `X₃`-arc (`IsX3Arc (F₁ ∪ P)`). -/
theorem isX3Arc_union_chord [T2Space S] {F₁ P : Set S} {u v : S}
    (hF₁ : IsOArc F₁) (huv : u ≠ v) (hP : IsLineWithEnds P u v)
    (hPF₁ : P ∩ F₁ = {u, v}) :
    IsX3Arc (F₁ ∪ P) := by
  have huF₁ : u ∈ F₁ := (hPF₁ ▸ mem_insert u {v} : u ∈ P ∩ F₁).2
  have hvF₁ : v ∈ F₁ := (hPF₁ ▸ mem_insert_of_mem u (mem_singleton v) : v ∈ P ∩ F₁).2
  obtain ⟨P₁, P₂, hP₁, hP₂, hP₁₂_union, hP₁₂_inter⟩ := hF₁.lines huF₁ hvF₁ huv
  have hP₁F₁ : P₁ ⊆ F₁ := hP₁₂_union ▸ subset_union_left
  have hP₂F₁ : P₂ ⊆ F₁ := hP₁₂_union ▸ subset_union_right
  have hP₁P : P₁ ∩ P = {u, v} := by
    refine Subset.antisymm ?_ (pair_subset ⟨hP₁.left_mem, hP.left_mem⟩ ⟨hP₁.right_mem,
      hP.right_mem⟩)
    intro z ⟨hzP₁, hzP⟩
    exact hPF₁ ▸ ⟨hzP, hP₁F₁ hzP₁⟩
  have hP₂P : P₂ ∩ P = {u, v} := by
    refine Subset.antisymm ?_ (pair_subset ⟨hP₂.left_mem, hP.left_mem⟩ ⟨hP₂.right_mem,
      hP.right_mem⟩)
    intro z ⟨hzP₂, hzP⟩
    exact hPF₁ ▸ ⟨hzP, hP₂F₁ hzP₂⟩
  exact ⟨P₁, P₂, P, u, v, huv, hP₁, hP₂, hP, hP₁₂_inter, hP₁P, hP₂P, hP₁₂_union ▸ rfl⟩

/-! ## 4. Interval Decomposition and Single-Chord Extraction on `F₁ ∪ F₂` -/

private noncomputable def leftEnd8 (U : Set ℝ) (t : ℝ) : ℝ :=
  sSup {s : ℝ | s ≤ t ∧ s ∉ U}

private noncomputable def rightEnd8 (U : Set ℝ) (t : ℝ) : ℝ :=
  sInf {s : ℝ | t ≤ s ∧ s ∉ U}

private lemma leftEnd8_props {U : Set ℝ} (hU_open : IsOpen U) (hU_sub : U ⊆ Ioo 0 1)
    {t : ℝ} (ht : t ∈ U) :
    0 ≤ leftEnd8 U t ∧ leftEnd8 U t ∉ U ∧ leftEnd8 U t < t ∧ Ioo (leftEnd8 U t) t ⊆ U := by
  let A : Set ℝ := {s : ℝ | s ≤ t ∧ s ∉ U}
  have h0_mem : (0 : ℝ) ∈ A :=
    ⟨(hU_sub ht).1.le, fun h0 => (hU_sub h0).1.ne rfl⟩
  have hA_ne : A.Nonempty := ⟨0, h0_mem⟩
  have hA_bdd : BddAbove A := ⟨t, fun _ hs => hs.1⟩
  have hA_closed : IsClosed A := isClosed_Iic.inter hU_open.isClosed_compl
  have ha_mem : leftEnd8 U t ∈ A := hA_closed.csSup_mem hA_ne hA_bdd
  have h0_le : 0 ≤ leftEnd8 U t := le_csSup hA_bdd h0_mem
  have ha_lt_t : leftEnd8 U t < t :=
    lt_of_le_of_ne ha_mem.1 (fun heq => ha_mem.2 (heq.symm ▸ ht))
  refine ⟨h0_le, ha_mem.2, ha_lt_t, fun s hs => ?_⟩
  by_contra hsU
  exact not_lt_of_ge (le_csSup hA_bdd ⟨hs.2.le, hsU⟩) hs.1

private lemma rightEnd8_props {U : Set ℝ} (hU_open : IsOpen U) (hU_sub : U ⊆ Ioo 0 1)
    {t : ℝ} (ht : t ∈ U) :
    rightEnd8 U t ≤ 1 ∧ rightEnd8 U t ∉ U ∧ t < rightEnd8 U t ∧ Ioo t (rightEnd8 U t) ⊆ U := by
  let B : Set ℝ := {s : ℝ | t ≤ s ∧ s ∉ U}
  have h1_mem : (1 : ℝ) ∈ B :=
    ⟨(hU_sub ht).2.le, fun h1 => (hU_sub h1).2.ne rfl⟩
  have hB_ne : B.Nonempty := ⟨1, h1_mem⟩
  have hB_bdd : BddBelow B := ⟨t, fun _ hs => hs.1⟩
  have hB_closed : IsClosed B := isClosed_Ici.inter hU_open.isClosed_compl
  have hb_mem : rightEnd8 U t ∈ B := hB_closed.csInf_mem hB_ne hB_bdd
  have hb_le_1 : rightEnd8 U t ≤ 1 := csInf_le hB_bdd h1_mem
  have ht_lt_b : t < rightEnd8 U t :=
    lt_of_le_of_ne hb_mem.1 (fun heq => hb_mem.2 (heq ▸ ht))
  refine ⟨hb_le_1, hb_mem.2, ht_lt_b, fun s hs => ?_⟩
  by_contra hsU
  exact not_lt_of_ge (csInf_le hB_bdd ⟨hs.1.le, hsU⟩) hs.2

private lemma Ioo_leftEnd8_rightEnd8_subset {U : Set ℝ} (hU_open : IsOpen U) (hU_sub : U ⊆ Ioo 0 1)
    {t : ℝ} (ht : t ∈ U) :
    Ioo (leftEnd8 U t) (rightEnd8 U t) ⊆ U := by
  intro s hs
  rcases lt_trichotomy s t with hlt | rfl | hgt
  · exact (leftEnd8_props hU_open hU_sub ht).2.2.2 ⟨hs.1, hlt⟩
  · exact ht
  · exact (rightEnd8_props hU_open hU_sub ht).2.2.2 ⟨hgt, hs.2⟩

private lemma interval8_eq_or_disjoint {U : Set ℝ} (hU_open : IsOpen U) (hU_sub : U ⊆ Ioo 0 1)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ U) (ht₂ : t₂ ∈ U) :
    (leftEnd8 U t₁ = leftEnd8 U t₂ ∧ rightEnd8 U t₁ = rightEnd8 U t₂) ∨
      (rightEnd8 U t₁ ≤ leftEnd8 U t₂ ∨ rightEnd8 U t₂ ≤ leftEnd8 U t₁) := by
  obtain ⟨_, ha₁_not, ha₁_lt, _⟩ := leftEnd8_props hU_open hU_sub ht₁
  obtain ⟨_, hb₁_not, hb₁_gt, _⟩ := rightEnd8_props hU_open hU_sub ht₁
  obtain ⟨_, ha₂_not, ha₂_lt, _⟩ := leftEnd8_props hU_open hU_sub ht₂
  obtain ⟨_, hb₂_not, hb₂_gt, _⟩ := rightEnd8_props hU_open hU_sub ht₂
  have hsub₁ := Ioo_leftEnd8_rightEnd8_subset hU_open hU_sub ht₁
  have hsub₂ := Ioo_leftEnd8_rightEnd8_subset hU_open hU_sub ht₂
  by_cases hsep : rightEnd8 U t₁ ≤ leftEnd8 U t₂ ∨ rightEnd8 U t₂ ≤ leftEnd8 U t₁
  · exact Or.inr hsep
  · left
    push Not at hsep
    have ha_eq : leftEnd8 U t₁ = leftEnd8 U t₂ := by
      rcases lt_trichotomy (leftEnd8 U t₁) (leftEnd8 U t₂) with hlt | heq | hgt
      · exfalso
        exact ha₂_not (hsub₁ ⟨hlt, hsep.1⟩)
      · exact heq
      · exfalso
        exact ha₁_not (hsub₂ ⟨hgt, hsep.2⟩)
    have hb_eq : rightEnd8 U t₁ = rightEnd8 U t₂ := by
      rcases lt_trichotomy (rightEnd8 U t₁) (rightEnd8 U t₂) with hlt | heq | hgt
      · exfalso
        exact hb₁_not (hsub₂ ⟨hsep.1, hlt⟩)
      · exact heq
      · exfalso
        exact hb₂_not (hsub₁ ⟨hsep.2, hgt⟩)
    exact ⟨ha_eq, hb_eq⟩

/-- Replacing a path `q : C(I, T)` on a subinterval `[a, b] ⊆ [0, 1]` (`0 ≤ a < b ≤ 1`) by a path
`β : C(I, T)` with `β 0 = q a` and `β 1 = q b`. -/
private noncomputable def replaceOnIcc {T : Type u} [TopologicalSpace T]
    (q : C(I, T)) (a b : ℝ) (hab : 0 ≤ a ∧ a < b ∧ b ≤ 1)
    (β : C(I, T)) (hβ0 : β 0 = q ⟨a, hab.1, hab.2.1.le.trans hab.2.2⟩)
    (hβ1 : β 1 = q ⟨b, hab.1.trans hab.2.1.le, hab.2.2⟩) : C(I, T) := by
  let scale (t : I) : I := projIcc 0 1 zero_le_one (((t : ℝ) - a) / (b - a))
  have hscale_cont : Continuous scale :=
    continuous_projIcc.comp ((continuous_subtype_val.sub continuous_const).div_const _)
  let f_mid : I → T := fun t => β (scale t)
  have hf_mid_cont : Continuous f_mid := β.continuous.comp hscale_cont
  let f_left : I → T := fun t => if (t : ℝ) ≤ a then q t else f_mid t
  have hf_left_cont : Continuous f_left := by
    refine Continuous.if_le q.continuous hf_mid_cont continuous_subtype_val continuous_const ?_
    intro t ht
    have h0 : scale t = 0 := by
      ext
      change max (0 : ℝ) (min 1 (((t : ℝ) - a) / (b - a))) = 0
      rw [ht, sub_self, zero_div, min_eq_right zero_le_one, max_self]
    change q t = β (scale t)
    rw [h0, hβ0]
    congr 1
    exact Subtype.ext ht
  let f : I → T := fun t => if (t : ℝ) ≤ b then f_left t else q t
  have hf_cont : Continuous f := by
    refine Continuous.if_le hf_left_cont q.continuous continuous_subtype_val continuous_const ?_
    intro t ht
    have hnot_le : ¬ ((t : ℝ) ≤ a) := by linarith [hab.2.1]
    have h1 : scale t = 1 := by
      ext
      change max (0 : ℝ) (min 1 (((t : ℝ) - a) / (b - a))) = 1
      have hdiv : ((t : ℝ) - a) / (b - a) = 1 := by
        rw [ht]
        exact div_self (sub_ne_zero.mpr hab.2.1.ne')
      rw [hdiv, min_self, max_eq_right zero_le_one]
    change f_left t = q t
    dsimp [f_left]
    simp only [hnot_le, ↓reduceIte]
    change β (scale t) = q t
    rw [h1, hβ1]
    congr 1
    exact Subtype.ext ht.symm
  exact ⟨f, hf_cont⟩

private lemma replaceOnIcc_apply_not_Ioo {T : Type u} [TopologicalSpace T]
    (q : C(I, T)) (a b : ℝ) (hab : 0 ≤ a ∧ a < b ∧ b ≤ 1)
    (β : C(I, T)) (hβ0 : β 0 = q ⟨a, hab.1, hab.2.1.le.trans hab.2.2⟩)
    (hβ1 : β 1 = q ⟨b, hab.1.trans hab.2.1.le, hab.2.2⟩)
    (t : I) (ht : (t : ℝ) ∉ Ioo a b) :
    replaceOnIcc q a b hab β hβ0 hβ1 t = q t := by
  dsimp [replaceOnIcc]
  by_cases htb : (t : ℝ) ≤ b
  · simp only [htb, ↓reduceIte]
    rcases eq_or_lt_of_le htb with htb_eq | htb_lt
    · have hnot_le : ¬ ((t : ℝ) ≤ a) := by linarith [hab.2.1]
      simp only [hnot_le, ↓reduceIte]
      have hdiv : ((t : ℝ) - a) / (b - a) = 1 := by
        rw [htb_eq]
        exact div_self (sub_ne_zero.mpr hab.2.1.ne')
      have h1 : projIcc 0 1 zero_le_one (((t : ℝ) - a) / (b - a)) = 1 := by
        ext
        change max (0 : ℝ) (min 1 (((t : ℝ) - a) / (b - a))) = 1
        rw [hdiv, min_self, max_eq_right zero_le_one]
      rw [h1, hβ1]
      congr 1
      exact Subtype.ext htb_eq.symm
    · have hta : (t : ℝ) ≤ a := by
        by_contra hgt
        exact ht ⟨not_le.mp hgt, htb_lt⟩
      simp only [hta, ↓reduceIte]
  · simp only [htb, ↓reduceIte]

private lemma replaceOnIcc_apply_mem_Icc {T : Type u} [TopologicalSpace T]
    (q : C(I, T)) (a b : ℝ) (hab : 0 ≤ a ∧ a < b ∧ b ≤ 1)
    (β : C(I, T)) (hβ0 : β 0 = q ⟨a, hab.1, hab.2.1.le.trans hab.2.2⟩)
    (hβ1 : β 1 = q ⟨b, hab.1.trans hab.2.1.le, hab.2.2⟩)
    (t : I) (ht : (t : ℝ) ∈ Icc a b) :
    replaceOnIcc q a b hab β hβ0 hβ1 t ∈ range β := by
  dsimp [replaceOnIcc]
  simp only [ht.2, ↓reduceIte]
  by_cases hta : (t : ℝ) ≤ a
  · simp only [hta, ↓reduceIte]
    have hta_eq : (t : ℝ) = a := le_antisymm hta ht.1
    have ht_eq : t = ⟨a, hab.1, hab.2.1.le.trans hab.2.2⟩ := Subtype.ext hta_eq
    rw [ht_eq, ← hβ0]
    exact mem_range_self 0
  · simp only [hta, ↓reduceIte]
    exact mem_range_self _

private lemma pathsHomotopicRelIn_trans {T : Type u} [TopologicalSpace T]
    {W : Set T} {γ₀ γ₁ γ₂ : C(I, T)}
    (h₁ : PathsHomotopicRelIn W γ₀ γ₁) (h₂ : PathsHomotopicRelIn W γ₁ γ₂) :
    PathsHomotopicRelIn W γ₀ γ₂ := by
  obtain ⟨H₁, hH₁W, hH₁0, hH₁1, hH₁s0, hH₁s1⟩ := h₁
  obtain ⟨H₂, hH₂W, hH₂0, hH₂1, hH₂s0, hH₂s1⟩ := h₂
  let t₁ : I × I → I × I :=
    fun p => (p.1, projIcc 0 1 zero_le_one (2 * (p.2 : ℝ)))
  let t₂ : I × I → I × I :=
    fun p => (p.1, projIcc 0 1 zero_le_one (2 * (p.2 : ℝ) - 1))
  have ht₁_cont : Continuous t₁ :=
    continuous_fst.prodMk (continuous_projIcc.comp (continuous_const.mul
      (continuous_subtype_val.comp continuous_snd)))
  have ht₂_cont : Continuous t₂ :=
    continuous_fst.prodMk (continuous_projIcc.comp
      ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).sub continuous_const))
  let f₁ : I × I → T := H₁ ∘ t₁
  let f₂ : I × I → T := H₂ ∘ t₂
  have hf₁_cont : Continuous f₁ := H₁.continuous.comp ht₁_cont
  have hf₂_cont : Continuous f₂ := H₂.continuous.comp ht₂_cont
  let H_fun : I × I → T :=
    fun p => if (p.2 : ℝ) ≤ 1 / 2 then f₁ p else f₂ p
  have hH_cont : Continuous H_fun := by
    refine Continuous.if_le hf₁_cont hf₂_cont
      (continuous_subtype_val.comp continuous_snd) continuous_const ?_
    intro p hp
    have hp1 : projIcc 0 1 zero_le_one (2 * (p.2 : ℝ)) = 1 := by
      rw [hp]; ext; simp
    have hp0 : projIcc 0 1 zero_le_one (2 * (p.2 : ℝ) - 1) = 0 := by
      rw [hp]; ext; simp
    change H₁ (p.1, projIcc 0 1 zero_le_one (2 * (p.2 : ℝ))) =
      H₂ (p.1, projIcc 0 1 zero_le_one (2 * (p.2 : ℝ) - 1))
    rw [hp1, hp0, hH₁1 p.1, hH₂0 p.1]
  refine ⟨⟨H_fun, hH_cont⟩, fun p => ?_, fun t => ?_, fun t => ?_, fun s => ?_, fun s => ?_⟩
  · dsimp [H_fun]
    split_ifs
    · exact hH₁W (t₁ p)
    · exact hH₂W (t₂ p)
  · have hle : ((0 : I) : ℝ) ≤ 1 / 2 := by norm_num
    have hp0 : projIcc 0 1 zero_le_one (2 * ((0 : I) : ℝ)) = 0 := by
      ext; change max (0 : ℝ) (min 1 (2 * 0)) = 0; norm_num
    change (if ((0 : I) : ℝ) ≤ 1 / 2 then f₁ (t, 0) else f₂ (t, 0)) = γ₀ t
    simp only [hle, ↓reduceIte]
    change H₁ (t, projIcc 0 1 zero_le_one (2 * ((0 : I) : ℝ))) = γ₀ t
    rw [hp0, hH₁0 t]
  · have hnot : ¬ (((1 : I) : ℝ) ≤ 1 / 2) := by norm_num
    have hp1 : projIcc 0 1 zero_le_one (2 * ((1 : I) : ℝ) - 1) = 1 := by
      ext; change max (0 : ℝ) (min 1 (2 * 1 - 1)) = 1; norm_num
    change (if ((1 : I) : ℝ) ≤ 1 / 2 then f₁ (t, 1) else f₂ (t, 1)) = γ₂ t
    simp only [hnot, ↓reduceIte]
    change H₂ (t, projIcc 0 1 zero_le_one (2 * ((1 : I) : ℝ) - 1)) = γ₂ t
    rw [hp1, hH₂1 t]
  · dsimp [H_fun]
    split_ifs
    · exact hH₁s0 _
    · exact (hH₂s0 _).trans (hH₁1 0).symm |>.trans (hH₁s0 1)
  · dsimp [H_fun]
    split_ifs
    · exact hH₁s1 _
    · exact (hH₂s1 _).trans (hH₁1 1).symm |>.trans (hH₁s1 1)

private lemma pathsHomotopicRelIn_replaceOnIcc {T : Type u} [TopologicalSpace T]
    {E : Set T} (hE : IsClosedDisc E)
    (q : C(I, T)) (a b : ℝ) (hab : 0 ≤ a ∧ a < b ∧ b ≤ 1)
    (β : C(I, T)) (hβ0 : β 0 = q ⟨a, hab.1, hab.2.1.le.trans hab.2.2⟩)
    (hβ1 : β 1 = q ⟨b, hab.1.trans hab.2.1.le, hab.2.2⟩)
    (hq_E : ∀ t : I, (t : ℝ) ∈ Icc a b → q t ∈ E)
    (hβ_E : range β ⊆ E) :
    PathsHomotopicRelIn univ q (replaceOnIcc q a b hab β hβ0 hβ1) := by
  let q' := replaceOnIcc q a b hab β hβ0 hβ1
  have hq'_E : ∀ t : I, (t : ℝ) ∈ Icc a b → q' t ∈ E :=
    fun t ht => hβ_E (replaceOnIcc_apply_mem_Icc q a b hab β hβ0 hβ1 t ht)
  obtain ⟨hE_map, gE_map, cE⟩ := hE.exists_isChart
  let K_mid : Set (I × I) := {p : I × I | (p.1 : ℝ) ∈ Icc a b}
  let K_out : Set (I × I) := {p : I × I | (p.1 : ℝ) ≤ a ∨ b ≤ (p.1 : ℝ)}
  have hK_mid_closed : IsClosed K_mid :=
    isClosed_Icc.preimage (continuous_subtype_val.comp continuous_fst)
  have hK_out_closed : IsClosed K_out :=
    (isClosed_Iic.union isClosed_Ici).preimage (continuous_subtype_val.comp continuous_fst)
  have hK_union : K_mid ∪ K_out = univ := by
    ext p
    simp only [K_mid, K_out, mem_union, mem_Icc, mem_univ, iff_true]
    change (a ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ b) ∨ ((p.1 : ℝ) ≤ a ∨ b ≤ (p.1 : ℝ))
    rcases le_total (p.1 : ℝ) a with h1 | h1
    · exact Or.inr (Or.inl h1)
    · rcases le_total (p.1 : ℝ) b with h2 | h2
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (Or.inr h2)
  let H_fun : I × I → T := by
    classical
    exact fun p =>
      if (p.1 : ℝ) ∈ Icc a b then
        gE_map ((1 - (p.2 : ℝ)) • hE_map (q p.1) + (p.2 : ℝ) • hE_map (q' p.1))
      else
        q p.1
  have hH_out : ∀ p ∈ K_out, H_fun p = q p.1 := by
    intro p hp
    dsimp [H_fun]
    split_ifs with h_in
    · have h_eq : q' p.1 = q p.1 :=
        replaceOnIcc_apply_not_Ioo q a b hab β hβ0 hβ1 p.1 (fun h_oo => by
          rcases hp with hle | hge
          · linarith [h_oo.1]
          · linarith [h_oo.2])
      change gE_map ((1 - (p.2 : ℝ)) • hE_map (q p.1) + (p.2 : ℝ) • hE_map (q' p.1)) = q p.1
      rw [h_eq, ← add_smul, sub_add_cancel, one_smul, cE.gh (hq_E p.1 h_in)]
    · rfl
  have hcont_mid : ContinuousOn H_fun K_mid := by
    have hcont_g : ContinuousOn
        (fun p : I × I =>
          gE_map ((1 - (p.2 : ℝ)) • hE_map (q p.1) + (p.2 : ℝ) • hE_map (q' p.1))) K_mid := by
      have hhq : ContinuousOn (fun p : I × I => hE_map (q p.1)) K_mid :=
        cE.hc.comp (q.continuous.comp continuous_fst).continuousOn (fun p hp => hq_E p.1 hp)
      have hhq' : ContinuousOn (fun p : I × I => hE_map (q' p.1)) K_mid :=
        cE.hc.comp (q'.continuous.comp continuous_fst).continuousOn (fun p hp => hq'_E p.1 hp)
      have hs : ContinuousOn (fun p : I × I => (p.2 : ℝ)) K_mid :=
        (continuous_subtype_val.comp continuous_snd).continuousOn
      have hL : ContinuousOn
          (fun p : I × I => (1 - (p.2 : ℝ)) • hE_map (q p.1) + (p.2 : ℝ) • hE_map (q' p.1)) K_mid :=
        ((continuousOn_const.sub hs).smul hhq).add (hs.smul hhq')
      refine cE.gc.comp hL fun p hp => ?_
      exact convex_closedBall (0 : ℂ) 1
        (cE.hm (hq_E p.1 hp)) (cE.hm (hq'_E p.1 hp))
        (sub_nonneg.mpr p.2.2.2) p.2.2.1 (sub_add_cancel 1 (p.2 : ℝ))
    refine hcont_g.congr fun p hp => ?_
    have hp_in : (p.1 : ℝ) ∈ Icc a b := hp
    dsimp [H_fun]
    simp only [hp_in, ↓reduceIte]
  have hcont_out : ContinuousOn H_fun K_out :=
    (q.continuous.comp continuous_fst).continuousOn.congr hH_out
  have hH_cont : Continuous H_fun := by
    rw [← continuousOn_univ, ← hK_union]
    exact hcont_mid.union_of_isClosed hcont_out hK_mid_closed hK_out_closed
  refine ⟨⟨H_fun, hH_cont⟩, fun _ => mem_univ _, fun t => ?_, fun t => ?_, fun s => ?_, fun s => ?_⟩
  · dsimp [H_fun]
    split_ifs with ht
    · change gE_map ((1 - (0 : ℝ)) • hE_map (q t) + (0 : ℝ) • hE_map (q' t)) = q t
      simp [cE.gh (hq_E t ht)]
    · rfl
  · dsimp [H_fun]
    split_ifs with ht
    · change gE_map ((1 - (1 : ℝ)) • hE_map (q t) + (1 : ℝ) • hE_map (q' t)) = q' t
      simp [cE.gh (hq'_E t ht)]
    · exact (replaceOnIcc_apply_not_Ioo q a b hab β hβ0 hβ1 t
        (fun h_oo => ht ⟨h_oo.1.le, h_oo.2.le⟩)).symm
  · exact hH_out (0, s) (Or.inl hab.1)
  · exact hH_out (1, s) (Or.inr hab.2.2)

private theorem closed_parameter_interval_covers_circle
    {S : Type u}
    [TopologicalSpace S]
    {F₂ : Set S}
    (φ₂ : Circle ≃ₜ ↑F₂)
    (z₀ : Circle)
    :
    let γ_R : ℝ → S := fun t => (φ₂ (z₀ * Circle.exp (2 * Real.pi * t))).1
    γ_R '' Icc 0 1 = F₂ := by
  intro γ_R
  ext x
  constructor
  · rintro ⟨t, _, rfl⟩
    exact (φ₂ (z₀ * Circle.exp (2 * Real.pi * t))).2
  · intro hxF₂
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    let w : Circle := z₀⁻¹ * φ₂.symm ⟨x, hxF₂⟩
    let r : ℝ := toIcoMod h2pi 0 (Complex.arg w) / (2 * Real.pi)
    have hr_mem : r ∈ Icc (0 : ℝ) 1 := by
      have h_ico := toIcoMod_mem_Ico h2pi 0 (Complex.arg w)
      refine ⟨div_nonneg h_ico.1 h2pi.le, (div_le_one h2pi).mpr (by linarith [h_ico.2])⟩
    have hexp_r : Circle.exp (2 * Real.pi * r) = w := by
      have h1 : 2 * Real.pi * r = toIcoMod h2pi 0 (Complex.arg w) := by
        dsimp [r]; field_simp
      rw [h1]
      have h2 : toIcoMod h2pi 0 (Complex.arg w) =
          Complex.arg w - toIcoDiv h2pi 0 (Complex.arg w) • (2 * Real.pi) := rfl
      have h3 : Circle.exp (toIcoMod h2pi 0 (Complex.arg w)) = Circle.exp (Complex.arg w) := by
        rw [h2, zsmul_eq_mul]
        exact Circle.exp_eq_exp.mpr ⟨-toIcoDiv h2pi 0 (Complex.arg w), by push_cast; ring⟩
      exact h3.trans (Circle.exp_arg w)
    refine ⟨r, hr_mem, ?_⟩
    change (φ₂ (z₀ * Circle.exp (2 * Real.pi * r))).1 = x
    rw [hexp_r]
    dsimp [w]
    rw [mul_inv_cancel_left, φ₂.apply_symm_apply]

private theorem circle_parameter_repeats_only_endpoints
    {S : Type u}
    [TopologicalSpace S]
    {F₂ : Set S}
    (φ₂ : Circle ≃ₜ ↑F₂)
    (z₀ : Circle)
    :
    let E_param : ℝ → Circle := fun t => z₀ * Circle.exp (2 * Real.pi * t)
    let γ_R : ℝ → S := fun t => (φ₂ (E_param t)).1
    ∀ (s t : ℝ), s ∈ Icc 0 1 → t ∈ Icc 0 1 →
      γ_R s = γ_R t → s = t ∨ s = 0 ∧ t = 1 ∨ s = 1 ∧ t = 0 := by
  intro E_param γ_R s t hs ht heq
  have hE_eq : E_param s = E_param t := φ₂.injective (Subtype.ext heq)
  have hexp_eq : Circle.exp (2 * Real.pi * s) = Circle.exp (2 * Real.pi * t) :=
    mul_left_cancel hE_eq
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hexp_eq
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hdiff : s - t = (m : ℝ) := by
    have : (2 * Real.pi) * (s - t) = (2 * Real.pi) * (m : ℝ) := by linarith
    exact mul_left_cancel₀ hpi.ne' this
  rcases lt_trichotomy m 0 with hlt | rfl | hgt
  · rcases eq_or_lt_of_le (show m ≤ -1 by omega) with rfl | hlt'
    · right; left
      have : s - t = -1 := by simpa using hdiff
      exact ⟨by linarith [hs.1, ht.2], by linarith [hs.1, ht.2]⟩
    · exfalso
      have : (m : ℝ) ≤ -2 := by exact_mod_cast (show m ≤ -2 by omega)
      linarith [hs.1, ht.2]
  · left
    have : s - t = 0 := by simpa using hdiff
    linarith
  · rcases eq_or_lt_of_le (show 1 ≤ m by omega) with rfl | hgt'
    · right; right
      have : s - t = 1 := by simpa using hdiff
      exact ⟨by linarith [hs.2, ht.1], by linarith [hs.2, ht.1]⟩
    · exfalso
      have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 2 ≤ m by omega)
      linarith [hs.2, ht.1]

private theorem component_of_arc_complement_is_chord
    {S : Type u}
    [TopologicalSpace S]
    {F₁ : Set S}
    {F₂ : Set S}
    [T2Space S]
    (γ_R : ℝ → S)
    (hγ_R_cont : Continuous γ_R)
    (hγ_R_mem : ∀ (t : ℝ), γ_R t ∈ F₂)
    (hγ_R_inj_diff : ∀ (s t : ℝ), s ∈ Icc 0 1 → t ∈ Icc 0 1 → γ_R s = γ_R t → s = t ∨ s = 0 ∧ t =
      1 ∨ s = 1 ∧ t = 0)
    (U : Set ℝ) (hU_eq : U = Ioo 0 1 ∩ γ_R ⁻¹' F₁ᶜ)
    (hU_open : IsOpen U)
    (hU_sub : U ⊆ Ioo 0 1)
    (hnot_U_mem_F₁ : ∀ t ∈ Icc 0 1, t ∉ U → γ_R t ∈ F₁)
    (h_full : ∀ t ∈ U, leftEnd8 U t = 0 → rightEnd8 U t ≠ 1) :
    ∀ t ∈ U, let a := leftEnd8 U t; let b := rightEnd8 U t; 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ γ_R a ≠ γ_R b
      ∧ IsLineWithEnds (γ_R '' Icc a b) (γ_R a) (γ_R b) ∧ γ_R '' Icc a b ∩ F₁ = {γ_R a, γ_R b} ∧
      γ_R '' Icc a b ⊆ F₂ := by
  intro t htU
  obtain ⟨ha0, ha_notU, ha_lt_t, _⟩ := leftEnd8_props hU_open hU_sub htU
  obtain ⟨hb1, hb_notU, ht_lt_b, _⟩ := rightEnd8_props hU_open hU_sub htU
  have hab : leftEnd8 U t < rightEnd8 U t := ha_lt_t.trans ht_lt_b
  have ha_Icc : leftEnd8 U t ∈ Icc (0 : ℝ) 1 := ⟨ha0, hab.le.trans hb1⟩
  have hb_Icc : rightEnd8 U t ∈ Icc (0 : ℝ) 1 := ⟨ha0.trans hab.le, hb1⟩
  have h_inj : InjOn γ_R (Icc (leftEnd8 U t) (rightEnd8 U t)) := by
    intro s₁ hs₁ s₂ hs₂ heq
    have hs₁_01 : s₁ ∈ Icc (0 : ℝ) 1 := ⟨ha0.trans hs₁.1, hs₁.2.trans hb1⟩
    have hs₂_01 : s₂ ∈ Icc (0 : ℝ) 1 := ⟨ha0.trans hs₂.1, hs₂.2.trans hb1⟩
    rcases hγ_R_inj_diff s₁ s₂ hs₁_01 hs₂_01 heq with h | ⟨hs0, ht1⟩ | ⟨hs1, ht0⟩
    · exact h
    · exfalso
      have ha_eq : leftEnd8 U t = 0 := le_antisymm (hs0 ▸ hs₁.1) ha0
      have hb_eq : rightEnd8 U t = 1 := le_antisymm hb1 (ht1 ▸ hs₂.2)
      exact h_full t htU ha_eq hb_eq
    · exfalso
      have ha_eq : leftEnd8 U t = 0 := le_antisymm (ht0 ▸ hs₂.1) ha0
      have hb_eq : rightEnd8 U t = 1 := le_antisymm hb1 (hs1 ▸ hs₁.2)
      exact h_full t htU ha_eq hb_eq
  have hne_ends : γ_R (leftEnd8 U t) ≠ γ_R (rightEnd8 U t) :=
    fun heq => hab.ne (h_inj (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) heq)
  have hline : IsLineWithEnds (γ_R '' Icc (leftEnd8 U t) (rightEnd8 U t))
      (γ_R (leftEnd8 U t)) (γ_R (rightEnd8 U t)) := by
    let a_I : I := ⟨leftEnd8 U t, ha_Icc⟩
    let b_I : I := ⟨rightEnd8 U t, hb_Icc⟩
    have hab_I : a_I < b_I := hab
    let γ_I : I → S := fun s => γ_R s.1
    have hγ_I_cont : Continuous γ_I := hγ_R_cont.comp continuous_subtype_val
    have hγ_I_inj : InjOn γ_I (Icc a_I b_I) :=
      fun s₁ hs₁ s₂ hs₂ heq => Subtype.ext (h_inj hs₁ hs₂ heq)
    have himg_eq : γ_I '' Icc a_I b_I = γ_R '' Icc (leftEnd8 U t) (rightEnd8 U t) := by
      ext x
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact ⟨s.1, hs, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨⟨s, ha0.trans hs.1, hs.2.trans hb1⟩, hs, rfl⟩
    rw [← himg_eq]
    exact isLineWithEnds_image_Icc_of_injOn hγ_I_cont hab_I hγ_I_inj
  have hinter_F₁ : (γ_R '' Icc (leftEnd8 U t) (rightEnd8 U t)) ∩ F₁ =
      {γ_R (leftEnd8 U t), γ_R (rightEnd8 U t)} := by
    ext x
    simp only [mem_inter_iff, mem_image, mem_Icc, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨⟨s, ⟨hsa, hsb⟩, rfl⟩, hγs_F₁⟩
      rcases eq_or_lt_of_le hsa with rfl | hsa_lt
      · exact Or.inl rfl
      · rcases eq_or_lt_of_le hsb with rfl | hsb_lt
        · exact Or.inr rfl
        · exfalso
          have hsU : s ∈ U :=
            Ioo_leftEnd8_rightEnd8_subset hU_open hU_sub htU ⟨hsa_lt, hsb_lt⟩
          exact (hU_eq ▸ hsU).2 hγs_F₁
    · rintro (rfl | rfl)
      · exact ⟨⟨leftEnd8 U t, ⟨le_rfl, hab.le⟩, rfl⟩,
          hnot_U_mem_F₁ _ ha_Icc ha_notU⟩
      · exact ⟨⟨rightEnd8 U t, ⟨hab.le, le_rfl⟩, rfl⟩,
          hnot_U_mem_F₁ _ hb_Icc hb_notU⟩
  refine ⟨ha0, hab, hb1, hne_ends, hline, hinter_F₁, ?_⟩
  rintro _ ⟨s, _, rfl⟩
  exact hγ_R_mem s

private theorem replace_finitely_many_chords_by_boundary_paths
    {S : Type u}
    [TopologicalSpace S]
    {F₁ : Set S}
    {F₂ : Set S}
    {C₁ : Set S}
    (γ_R : ℝ → S)
    (U : Set ℝ)
    (hU_open : IsOpen U)
    (hU_sub : U ⊆ Ioo 0 1)
    (hnot_U_mem_F₁ : ∀ t ∈ Icc 0 1, t ∉ U → γ_R t ∈ F₁)
    (hchord_of_mem_U : ∀ t ∈ U, let a := leftEnd8 U t; let b := rightEnd8 U t; 0 ≤ a ∧ a < b ∧ b ≤
      1 ∧ γ_R a ≠ γ_R b ∧ IsLineWithEnds (γ_R '' Icc a b) (γ_R a) (γ_R b) ∧ γ_R '' Icc a b ∩ F₁ =
      {γ_R a, γ_R b} ∧ γ_R '' Icc a b ⊆ F₂)
    (hall_planar : ∀ (P : Set S) (u v : S), P ⊆ F₂ → u ≠ v → IsLineWithEnds P u v → P ∩ F₁ = {u,
      v} → IsPlanarInCappedCuff C₁ (F₁ ∪ P))
    (S' : Type u)
    [TopologicalSpace S']
    (j : S → S')
    (D : Set S')
    (hCap : IsCappedCuff C₁ S' j D)
    [T2Space S']
    (hjF₁_oarc : IsOArc (j '' F₁))
    (W : Set S')
    (hjF₁_W : j '' F₁ ⊆ W)
    (q₀ : C(I, S')) (hq₀ : ∀ s : I, q₀ s = j (γ_R s.1)) :
    ∀ (G : Finset ℝ), (∀ t ∈ G, t ∈ U) → ∃ q, PathsHomotopicRelIn univ q₀ q ∧ (∀ (s : ↑I), (∀ t ∈
      G, ↑s ∉ Ioo (leftEnd8 U t) (rightEnd8 U t)) → q s = q₀ s) ∧ ∀ (s : ↑I), (∃ t ∈ G, ↑s ∈ Ioo
      (leftEnd8 U t) (rightEnd8 U t)) → q s ∈ W := by
  intro G
  induction G using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨q₀, PathsHomotopicRelIn.refl (subset_univ _),
      fun _ _ => rfl, fun _ ⟨_, ht, _⟩ => (Finset.notMem_empty _ ht).elim⟩
  | @insert t₀ G ht₀_notG ih =>
    intro hG_U
    have ht₀U : t₀ ∈ U := hG_U t₀ (Finset.mem_insert_self t₀ G)
    obtain ⟨q₁, hhom₁, hq₁_out, hq₁_in⟩ :=
      ih (fun t ht => hG_U t (Finset.mem_insert_of_mem ht))
    let a := leftEnd8 U t₀
    let b := rightEnd8 U t₀
    by_cases h_already : ∃ t ∈ G, leftEnd8 U t = a ∧ rightEnd8 U t = b
    · obtain ⟨t', ht'G, ha_eq, hb_eq⟩ := h_already
      refine ⟨q₁, hhom₁, fun s hs => hq₁_out s (fun t ht => hs t (Finset.mem_insert_of_mem ht)),
        fun s ⟨t, ht_ins, hs_oo⟩ => ?_⟩
      rcases Finset.mem_insert.mp ht_ins with rfl | htG
      · exact hq₁_in s ⟨t', ht'G, by rwa [ha_eq, hb_eq]⟩
      · exact hq₁_in s ⟨t, htG, hs_oo⟩
    · push Not at h_already
      have hdisj_G : ∀ t ∈ G, rightEnd8 U t ≤ a ∨ b ≤ leftEnd8 U t := by
        intro t htG
        rcases interval8_eq_or_disjoint hU_open hU_sub (hG_U t (Finset.mem_insert_of_mem htG))
          ht₀U
          with ⟨ha_eq, hb_eq⟩ | hsep
        · exact (h_already t htG ha_eq hb_eq).elim
        · exact hsep
      obtain ⟨ha0, hab, hb1, hne_ends, hline, hinter_F₁, hP_sub_F₂⟩ :=
        hchord_of_mem_U t₀ ht₀U
      let P := γ_R '' Icc a b
      have hcap_P : IsPlanarInCappedCuff C₁ (F₁ ∪ P) :=
        hall_planar P (γ_R a) (γ_R b) hP_sub_F₂ hne_ends hline hinter_F₁
      obtain ⟨E_disc, hE_disc, hjF₁P_sub_E⟩ := hcap_P.2.2 S' j D hCap
      have ha_F₁ : γ_R a ∈ F₁ :=
        hnot_U_mem_F₁ a ⟨ha0, hab.le.trans hb1⟩ (leftEnd8_props hU_open hU_sub ht₀U).2.1
      have hb_F₁ : γ_R b ∈ F₁ :=
        hnot_U_mem_F₁ b ⟨ha0.trans hab.le, hb1⟩ (rightEnd8_props hU_open hU_sub ht₀U).2.1
      obtain ⟨β, hβ_range, hβ0_eq, hβ1_eq⟩ :=
        exists_path_of_isArcConnected (IsOArc.isArcConnected hjF₁_oarc)
          (mem_image_of_mem j ha_F₁) (mem_image_of_mem j hb_F₁)
      have hq₁_eq_on_ab : ∀ s : I, (s : ℝ) ∈ Icc a b → q₁ s = q₀ s := by
        intro s hs
        refine hq₁_out s fun t htG hs_oo => ?_
        rcases hdisj_G t htG with hle | hge
        · linarith [hs.1, hs_oo.2]
        · linarith [hs.2, hs_oo.1]
      let a_I : I := ⟨a, ha0, hab.le.trans hb1⟩
      let b_I : I := ⟨b, ha0.trans hab.le, hb1⟩
      have hβ0 : β 0 = q₁ a_I :=
        hβ0_eq.trans ((hq₁_eq_on_ab a_I (left_mem_Icc.mpr hab.le)).trans (hq₀ a_I)).symm
      have hβ1 : β 1 = q₁ b_I :=
        hβ1_eq.trans ((hq₁_eq_on_ab b_I (right_mem_Icc.mpr hab.le)).trans (hq₀ b_I)).symm
      have hq₁_E : ∀ s : I, (s : ℝ) ∈ Icc a b → q₁ s ∈ E_disc := by
        intro s hs
        rw [hq₁_eq_on_ab s hs, hq₀]
        exact hjF₁P_sub_E (mem_image_of_mem j (Or.inr ⟨s.1, hs, rfl⟩))
      have hβ_E : range β ⊆ E_disc :=
        hβ_range.trans ((image_mono subset_union_left).trans hjF₁P_sub_E)
      let q₂ := replaceOnIcc q₁ a b ⟨ha0, hab, hb1⟩ β hβ0 hβ1
      have hhom₂ : PathsHomotopicRelIn univ q₁ q₂ :=
        pathsHomotopicRelIn_replaceOnIcc hE_disc q₁ a b ⟨ha0, hab, hb1⟩ β hβ0 hβ1 hq₁_E hβ_E
      refine ⟨q₂, pathsHomotopicRelIn_trans hhom₁ hhom₂, ?_, ?_⟩
      · intro s hs
        have hs_not_ab : (s : ℝ) ∉ Ioo a b := hs t₀ (Finset.mem_insert_self t₀ G)
        rw [replaceOnIcc_apply_not_Ioo q₁ a b ⟨ha0, hab, hb1⟩ β hβ0 hβ1 s hs_not_ab]
        exact hq₁_out s (fun t htG => hs t (Finset.mem_insert_of_mem htG))
      · intro s ⟨t, ht_ins, hs_oo⟩
        rcases Finset.mem_insert.mp ht_ins with rfl | htG
        · exact hjF₁_W (hβ_range (replaceOnIcc_apply_mem_Icc q₁ a b ⟨ha0, hab, hb1⟩
            β hβ0 hβ1 s ⟨hs_oo.1.le, hs_oo.2.le⟩))
        · have hs_not_ab : (s : ℝ) ∉ Ioo a b := by
            intro hs_ab
            rcases hdisj_G t htG with hle | hge
            · linarith [hs_oo.2, hs_ab.1]
            · linarith [hs_oo.1, hs_ab.2]
          rw [replaceOnIcc_apply_not_Ioo q₁ a b ⟨ha0, hab, hb1⟩ β hβ0 hβ1 s hs_not_ab]
          exact hq₁_in s ⟨t, htG, hs_oo⟩

private theorem range_of_rotated_circle_embedding
    {S : Type u}
    [TopologicalSpace S]
    {F₂ : Set S}
    (φ₂ : Circle ≃ₜ ↑F₂)
    (z₀ : Circle)
    (S' : Type u)
    (j : S → S') :
    range (fun w => j ↑(φ₂ (z₀ * w))) = j '' F₂ := by
  let f_emb := fun w => j ↑(φ₂ (z₀ * w))
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    exact mem_image_of_mem j (φ₂ (z₀ * w)).2
  · rintro ⟨x, hxF₂, rfl⟩
    refine ⟨z₀⁻¹ * φ₂.symm ⟨x, hxF₂⟩, ?_⟩
    dsimp [f_emb]
    rw [mul_inv_cancel_left, φ₂.apply_symm_apply]

/-- If two `O`-arcs `F₁, F₂` in a connected surface `S` satisfy `SurroundsCuff F₁ C₁`,
`¬ IsPlanarInCappedCuff C₁ F₂`, and `(F₁ ∩ F₂).Nonempty`, then either `F₁ ∩ F₂ = {u}` is a
singleton, or there is a `[0, 1]`-arc `P ⊆ F₂` with distinct ends `u, v ∈ F₁` and `P ∩ F₁ = {u, v}`
such that `¬ IsPlanarInCappedCuff C₁ (F₁ ∪ P)`. -/
theorem exists_chord_not_planarInCappedCuff_of_inter_nonempty
    (hS : IsSurface S)
    {F₁ F₂ C₁ : Set S} (hF₁ : IsOArc F₁) (hF₂ : IsOArc F₂)
    (hF₁_surr : SurroundsCuff F₁ C₁) (hF₂_ncap : ¬ IsPlanarInCappedCuff C₁ F₂)
    (hinter_ne : (F₁ ∩ F₂).Nonempty) :
    (∃ u : S, F₁ ∩ F₂ = {u}) ∨
      (∃ P : Set S, ∃ u v : S,
        P ⊆ F₂ ∧ u ≠ v ∧ IsLineWithEnds P u v ∧ P ∩ F₁ = {u, v} ∧
          ¬ IsPlanarInCappedCuff C₁ (F₁ ∪ P)) := by
  classical
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  obtain ⟨u₀, hu₀F₁, hu₀F₂⟩ := hinter_ne
  obtain ⟨φ₂⟩ := id hF₂
  let z₀ : Circle := φ₂.symm ⟨u₀, hu₀F₂⟩
  have hφ₂_z₀ : (φ₂ z₀).1 = u₀ := by simp [z₀]
  let E_param : ℝ → Circle := fun t => z₀ * Circle.exp (2 * Real.pi * t)
  have hE_cont : Continuous E_param :=
    continuous_const.mul (Circle.exp.continuous.comp (continuous_const.mul continuous_id))
  let γ_R : ℝ → S := fun t => (φ₂ (E_param t)).1
  have hγ_R_cont : Continuous γ_R :=
    continuous_subtype_val.comp (φ₂.continuous.comp hE_cont)
  have hγ_R_0 : γ_R 0 = u₀ := by
    change (φ₂ (z₀ * Circle.exp (2 * Real.pi * 0))).1 = u₀
    simp [hφ₂_z₀]
  have hγ_R_1 : γ_R 1 = u₀ := by
    change (φ₂ (z₀ * Circle.exp (2 * Real.pi * 1))).1 = u₀
    rw [mul_one, Circle.exp_two_pi, mul_one, hφ₂_z₀]
  have hγ_R_mem : ∀ t : ℝ, γ_R t ∈ F₂ := fun t => (φ₂ (E_param t)).2
  have hγ_R_surj : γ_R '' Icc 0 1 = F₂ := by
    exact closed_parameter_interval_covers_circle (S := S) (F₂ := F₂) φ₂ z₀
  have hγ_R_inj_diff : ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      γ_R s = γ_R t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
    exact circle_parameter_repeats_only_endpoints (S := S) (F₂ := F₂) φ₂ z₀
  let U : Set ℝ := Ioo (0 : ℝ) 1 ∩ γ_R ⁻¹' F₁ᶜ
  have hU_open : IsOpen U := isOpen_Ioo.inter (hF₁.isCompact.isClosed.isOpen_compl.preimage
    hγ_R_cont)
  have hU_sub : U ⊆ Ioo 0 1 := inter_subset_left
  have hnot_U_mem_F₁ : ∀ t ∈ Icc (0 : ℝ) 1, t ∉ U → γ_R t ∈ F₁ := by
    intro t ht hnotU
    rcases eq_or_lt_of_le ht.1 with rfl | h0
    · exact hγ_R_0 ▸ hu₀F₁
    · rcases eq_or_lt_of_le ht.2 with rfl | h1
      · exact hγ_R_1 ▸ hu₀F₁
      · by_contra hnotF₁
        exact hnotU ⟨⟨h0, h1⟩, hnotF₁⟩
  by_cases h_full : ∃ t ∈ U, leftEnd8 U t = 0 ∧ rightEnd8 U t = 1
  · left
    obtain ⟨t₀, ht₀U, hl0, hr1⟩ := h_full
    have hIoo_sub : Ioo (0 : ℝ) 1 ⊆ U := by
      have h := Ioo_leftEnd8_rightEnd8_subset hU_open hU_sub ht₀U
      rwa [hl0, hr1] at h
    refine ⟨u₀, Subset.antisymm ?_ (singleton_subset_iff.mpr ⟨hu₀F₁, hu₀F₂⟩)⟩
    rintro x ⟨hxF₁, hxF₂⟩
    rw [← hγ_R_surj] at hxF₂
    obtain ⟨t, ht, rfl⟩ := hxF₂
    rcases eq_or_lt_of_le ht.1 with rfl | h0
    · exact mem_singleton_iff.mpr hγ_R_0
    · rcases eq_or_lt_of_le ht.2 with rfl | h1
      · exact mem_singleton_iff.mpr hγ_R_1
      · exfalso
        exact (hIoo_sub ⟨h0, h1⟩).2 hxF₁
  · right
    push Not at h_full
    have hchord_of_mem_U : ∀ t ∈ U,
        let a := leftEnd8 U t
        let b := rightEnd8 U t
        0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ γ_R a ≠ γ_R b ∧
        IsLineWithEnds (γ_R '' Icc a b) (γ_R a) (γ_R b) ∧
        (γ_R '' Icc a b) ∩ F₁ = {γ_R a, γ_R b} ∧
        γ_R '' Icc a b ⊆ F₂ := by
      exact component_of_arc_complement_is_chord (S := S) (F₁ := F₁) (F₂ := F₂) γ_R hγ_R_cont
        hγ_R_mem hγ_R_inj_diff U rfl hU_open hU_sub hnot_U_mem_F₁ h_full
    by_contra! hall_planar
    obtain ⟨S', topS', j, D, hCap, hF₂_npl_S'⟩ :
        ∃ (S' : Type u) (_ : TopologicalSpace S') (j : S → S') (D : Set S'),
          IsCappedCuff C₁ S' j D ∧ ¬ IsPlanar (j '' F₂) := by
      by_contra! h_all_S'
      have hC₁ : C₁ ∈ cuffs S := hF₁_surr.1
      obtain ⟨c₀, _⟩ := isOArc_nonempty (cuff_isOArc hS hC₁)
      have : Nonempty S := ⟨c₀⟩
      obtain ⟨S', topS', j, D, hS', hj, hD, hunion, hinter, hbdD⟩ := paste_disc S C₁ hS hC₁
      have hCap : IsCappedCuff C₁ S' j D := ⟨hC₁, hS', hj.isEmbedding, hD, hbdD.1, hunion, hinter⟩
      exact hF₂_ncap ⟨hC₁, ⟨S', topS', j, D, hCap, h_all_S' S' topS' j D hCap⟩,
        fun S'' topS'' j' D' hCap' => h_all_S' S'' topS'' j' D' hCap'⟩
    have hS' : IsSurface S' := hCap.isSurface
    have : T2Space S' := hS'.2.1
    have hj : IsEmbedding j := hCap.isEmbedding
    have hjF₁_oarc : IsOArc (j '' F₁) :=
      isOArc_image hF₁ hj.continuous.continuousOn hj.injective.injOn
    have hjF₂_oarc : IsOArc (j '' F₂) :=
      isOArc_image hF₂ hj.continuous.continuousOn hj.injective.injOn
    obtain ⟨Δ₁, hΔ₁_disc, hjF₁_sub_Δ₁⟩ := hF₁_surr.2.1.2.2 S' j D hCap
    have hjF₁_flat : IsFlat (j '' F₁) := by
      refine isFlat_of_forall_isNullHomotopicOArc hS' fun F' hF' hF'_oarc => ?_
      exact isNullHomotopicOArcIn_of_subset_disc hF'_oarc (subset_univ Δ₁) hΔ₁_disc
        (hF'.trans hjF₁_sub_Δ₁)
    obtain ⟨W, hjF₁_W, hW_open, hW_flat, _, _⟩ :=
      theorem_11_5_proof hS' hjF₁_flat (IsOArc.isSolid hjF₁_oarc).1
    let q₀ : C(I, S') := ⟨fun t => j (γ_R t.1), hj.continuous.comp (hγ_R_cont.comp
      continuous_subtype_val)⟩
    have hq₀_01 : q₀ 1 = q₀ 0 := by
      change j (γ_R 1) = j (γ_R 0)
      rw [hγ_R_1, hγ_R_0]
    let K : Set ℝ := Icc (0 : ℝ) 1 ∩ (j ∘ γ_R) ⁻¹' Wᶜ
    have hK_compact : IsCompact K :=
      IsCompact.inter_right isCompact_Icc (hW_open.isClosed_compl.preimage
        (hj.continuous.comp hγ_R_cont))
    have hK_sub_U : K ⊆ U := by
      rintro t ⟨ht_Icc, ht_notW⟩
      by_contra ht_notU
      exact ht_notW (hjF₁_W (mem_image_of_mem j (hnot_U_mem_F₁ t ht_Icc ht_notU)))
    have hK_cov : K ⊆ ⋃ t ∈ U, Ioo (leftEnd8 U t) (rightEnd8 U t) := by
      intro t htK
      have htU : t ∈ U := hK_sub_U htK
      obtain ⟨_, _, ha_lt, _⟩ := leftEnd8_props hU_open hU_sub htU
      obtain ⟨_, _, hb_gt, _⟩ := rightEnd8_props hU_open hU_sub htU
      exact mem_iUnion₂.mpr ⟨t, htU, ha_lt, hb_gt⟩
    obtain ⟨F_K, hF_K_U, hF_K_fin, hK_sub_FK⟩ :=
      hK_compact.elim_finite_subcover_image
        (b := U) (c := fun t : ℝ => Ioo (leftEnd8 U t) (rightEnd8 U t))
        (fun _ _ => isOpen_Ioo) hK_cov
    -- Deduplicate by interval `(leftEnd8 U t, rightEnd8 U t)` and induct on `Finset`
    have h_step : ∀ (G : Finset ℝ), (∀ t ∈ G, t ∈ U) →
        ∃ q : C(I, S'),
          PathsHomotopicRelIn univ q₀ q ∧
          (∀ s : I, (∀ t ∈ G, (s : ℝ) ∉ Ioo (leftEnd8 U t) (rightEnd8 U t)) → q s = q₀ s) ∧
          (∀ s : I, (∃ t ∈ G, (s : ℝ) ∈ Ioo (leftEnd8 U t) (rightEnd8 U t)) → q s ∈ W) := by
      exact replace_finitely_many_chords_by_boundary_paths (S := S) (F₁ := F₁) (F₂ := F₂) (C₁ :=
        C₁) γ_R U hU_open hU_sub hnot_U_mem_F₁ hchord_of_mem_U hall_planar S' j D hCap hjF₁_oarc W
        hjF₁_W q₀ (fun _ => rfl)
    have hFK_sub : ∀ t ∈ hF_K_fin.toFinset, t ∈ U :=
      fun t ht => hF_K_U (hF_K_fin.mem_toFinset.mp ht)
    obtain ⟨q_final, ⟨H, hH_univ, hH0, hH1, hHs0, hHs1⟩, hq_final_out, hq_final_in⟩ :=
      h_step hF_K_fin.toFinset hFK_sub
    have hq_final_W : range q_final ⊆ W := by
      rintro _ ⟨s, rfl⟩
      by_cases hsK : (s : ℝ) ∈ K
      · obtain ⟨t, htFK, hs_oo⟩ := mem_iUnion₂.mp (hK_sub_FK hsK)
        exact hq_final_in s ⟨t, hF_K_fin.mem_toFinset.mpr htFK, hs_oo⟩
      · by_cases hs_in : ∃ t ∈ hF_K_fin.toFinset, (s : ℝ) ∈ Ioo (leftEnd8 U t) (rightEnd8 U t)
        · exact hq_final_in s hs_in
        · push Not at hs_in
          rw [hq_final_out s hs_in]
          change j (γ_R s.1) ∈ W
          by_contra hs_notW
          exact hsK ⟨s.2, hs_notW⟩
    have hq_final_01 : q_final 1 = q_final 0 := by
      rw [← hH1 1, hHs1 1, hq₀_01, ← hHs0 1, hH1 0]
    let ψ₀ : C(Circle, S') := concatLoop one_pos (fun _ => q₀) (fun _ => hq₀_01)
    let ψ₁ : C(Circle, S') := concatLoop one_pos (fun _ => q_final) (fun _ => hq_final_01)
    have hhom : ClosedCurvesHomotopicIn univ ψ₀ ψ₁ :=
      concatLoop_homotopic one_pos (fun _ => q₀) (fun _ => q_final)
        (fun _ => hq₀_01) (fun _ => hq_final_01) (fun _ => H)
        (fun _ p => hH_univ p) (fun _ t => hH0 t) (fun _ t => hH1 t)
        (fun _ s => (hHs1 s).trans hq₀_01 |>.trans (hHs0 s).symm)
    have hψ₁_W : range ψ₁ ⊆ W := by
      rw [range_concatLoop]
      rintro _ ⟨_, ⟨_, rfl⟩, hy⟩
      exact hq_final_W hy
    have hψ₁_null : ClosedCurveIsNullHomotopicIn univ ψ₁ := hW_flat ψ₁ hψ₁_W
    have hψ₀_null : ClosedCurveIsNullHomotopicIn univ ψ₀ :=
      null_of_homotopic subset_rfl hhom hψ₁_null
    let f_emb : Circle → S' := fun w => j (φ₂ (z₀ * w)).1
    have hf_emb_cont : Continuous f_emb :=
      hj.continuous.comp (continuous_subtype_val.comp (φ₂.continuous.comp
        (continuous_const.mul continuous_id)))
    have hf_emb_inj : Function.Injective f_emb := fun w₁ w₂ heq =>
      mul_left_cancel (φ₂.injective (Subtype.ext (hj.injective heq)))
    have hrange_f_emb : range f_emb = j '' F₂ := by
      exact range_of_rotated_circle_embedding (S := S) (F₂ := F₂) φ₂ z₀ S' j
    have hψ₀_eq : ψ₀ = ⟨f_emb, hf_emb_cont⟩ := by
      ext w
      have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
      let r : ℝ := toIcoMod h2pi 0 (Complex.arg w) / (2 * Real.pi)
      have hr_mem : r ∈ Icc (0 : ℝ) 1 := by
        have h_ico := toIcoMod_mem_Ico h2pi 0 (Complex.arg w)
        refine ⟨div_nonneg h_ico.1 h2pi.le, (div_le_one h2pi).mpr (by linarith [h_ico.2])⟩
      let t : I := ⟨r, hr_mem⟩
      let w_t : Circle := Circle.exp (2 * Real.pi * (((0 : Fin 1).1 : ℝ) + (t : ℝ)) / ((1 : ℕ) : ℝ))
      have hexp_t : w_t = w := by
        have h1 : 2 * Real.pi * (((0 : Fin 1).1 : ℝ) + (t : ℝ)) / ((1 : ℕ) : ℝ) =
            toIcoMod h2pi 0 (Complex.arg w) := by
          have ht_eq : (t : ℝ) = r := rfl
          rw [ht_eq]
          dsimp [r]
          simp [mul_div_cancel₀ _ h2pi.ne']
        change Circle.exp (2 * Real.pi * (((0 : Fin 1).1 : ℝ) + (t : ℝ)) / ((1 : ℕ) : ℝ)) = w
        rw [h1]
        have h2 : toIcoMod h2pi 0 (Complex.arg w) =
            Complex.arg w - toIcoDiv h2pi 0 (Complex.arg w) • (2 * Real.pi) := rfl
        have h3 : Circle.exp (toIcoMod h2pi 0 (Complex.arg w)) = Circle.exp (Complex.arg w) := by
          rw [h2, zsmul_eq_mul]
          exact Circle.exp_eq_exp.mpr ⟨-toIcoDiv h2pi 0 (Complex.arg w), by push_cast; ring⟩
        exact h3.trans (Circle.exp_arg w)
      have hpiece : ψ₀ w_t = q₀ t :=
        concatLoop_exp_piece one_pos (fun _ => q₀) (fun _ => hq₀_01) 0 t
      change ψ₀ w = f_emb w
      rw [← hexp_t, hpiece]
      change j (φ₂ (z₀ * Circle.exp (2 * Real.pi * (t : ℝ)))).1 = f_emb w_t
      dsimp [f_emb, w_t]
      congr 3
      congr 1
      simp
    have hjF₂_null : IsNullHomotopicOArc (j '' F₂) := by
      rw [← hrange_f_emb]
      have hemb : IsEmbedding f_emb := (hf_emb_cont.isClosedEmbedding hf_emb_inj).isEmbedding
      exact ⟨hemb.toHomeomorph, hψ₀_eq ▸ hψ₀_null⟩
    exact hF₂_npl_S' ((isPlanar_iff_isNullHomotopicOArc_of_isOArc hS' hjF₂_oarc).mpr hjF₂_null)

/-! ## 5. Main Section 8 Characterization and Consequences for `α(G)` -/

/-- Graph Minors VII, Section 8 (page 241):
"It is easy to verify, using (5.1) and (5.2), that if $X \subseteq \Sigma$ is solid and connected,
then $X$ is near-planar if and only if no subset of $X$ is schismatic." -/
theorem isNearPlanar_iff_forall_not_isSchismatic
    (hS : IsSurface S) [ConnectedSpace S] {X : Set S}
    (hns : ¬ IsSphere S ∨ X ≠ univ)
    (hX_solid : IsSolid X) (hX_conn : IsConnected X) :
    IsNearPlanar X ↔ ∀ Y : Set S, Y ⊆ X → ¬ IsSchismatic Y := by
  have : T2Space S := hS.2.1
  constructor
  · intro hX Y hYX hY_sch
    exact hY_sch.2.1 (hX.mono hYX)
  · intro hall_not_sch
    by_contra hX_nnp
    by_cases hex_oarc : ∃ F : Set S, IsOArc F ∧ F ⊆ X ∧ ¬ IsNearPlanar F
    · obtain ⟨F, hF, hFX, hF_nnp⟩ := hex_oarc
      exact hall_not_sch F hFX
        ⟨Or.inl hF, hF_nnp, fun F' hF' hF'_ss => (not_ssubset_of_isOArc hF hF' hF'_ss).elim⟩
    · push Not at hex_oarc
      have hX_npl : ¬ IsPlanar X := fun hpl => hX_nnp (Or.inl hpl)
      have hex_F₁ : ∃ F₁ : Set S, IsOArc F₁ ∧ F₁ ⊆ X ∧ ¬ IsPlanar F₁ := by
        by_contra! hall_pl
        exact hX_npl ((theorem_5_1_of_not_isSphere hS hns hX_solid).mpr hall_pl)
      obtain ⟨F₁, hF₁, hF₁X, hF₁_npl⟩ := hex_F₁
      obtain ⟨C₁, hC₁, hF₁_cap⟩ := (hex_oarc F₁ hF₁ hF₁X).resolve_left hF₁_npl
      have hF₁_surr : SurroundsCuff F₁ C₁ := ⟨hC₁, hF₁_cap, hF₁_npl⟩
      have hX_ncap : ¬ IsPlanarInCappedCuff C₁ X :=
        fun hcap => hX_nnp (Or.inr ⟨C₁, hC₁, hcap⟩)
      have hex_F₂ : ∃ F₂ : Set S, IsOArc F₂ ∧ F₂ ⊆ X ∧ ¬ IsPlanarInCappedCuff C₁ F₂ := by
        by_contra! hall_cap
        exact hX_ncap ((isPlanarInCappedCuff_iff_forall_isOArc hS hC₁ hX_solid).mpr hall_cap)
      obtain ⟨F₂, hF₂, hF₂X, hF₂_ncap⟩ := hex_F₂
      by_cases hdisj : Disjoint F₁ F₂
      · have hX_arc : IsArcConnected X := theorem_11_4_proof hS hX_conn hX_solid.1
        obtain ⟨P, u, v, hPX, huF₁, hvF₂, hP_line, hPF₁, hPF₂⟩ :=
          exists_connecting_line_between_disjoint_closed hX_arc hF₁X hF₂X
            hF₁.isCompact.isClosed hF₂.isCompact.isClosed
            (isOArc_nonempty hF₁) (isOArc_nonempty hF₂) hdisj
        let Y := F₁ ∪ F₂ ∪ P
        have hYX : Y ⊆ X := union_subset (union_subset hF₁X hF₂X) hPX
        have hY_x1 : IsX1Arc Y :=
          ⟨F₁, F₂, P, u, v, hF₁, hF₂, hdisj, hP_line, huF₁, hvF₂, hPF₁, hPF₂, rfl⟩
        have hY_ncap : ¬ IsPlanarInCappedCuff C₁ Y :=
          fun hcap => hF₂_ncap (hcap.mono (subset_union_right.trans subset_union_left))
        have hY_nnp : ¬ IsNearPlanar Y :=
          not_isNearPlanar_of_surroundsCuff_and_not_planarInCappedCuff hS hF₁ hF₁_surr hF₂_ncap
            (subset_union_left.trans subset_union_left) hY_ncap
        exact hall_not_sch Y hYX
          ⟨Or.inr (Or.inl hY_x1), hY_nnp, fun F' hF' hF'Y => hex_oarc F' hF' (hF'Y.1.trans hYX)⟩
      · rw [not_disjoint_iff_nonempty_inter] at hdisj
        rcases exists_chord_not_planarInCappedCuff_of_inter_nonempty hS hF₁ hF₂
            hF₁_surr hF₂_ncap hdisj with ⟨u, h_single⟩ | ⟨P, u, v, hPF₂, huv, hP_line, hPF₁,
              hY_ncap⟩
        · let Y := F₁ ∪ F₂
          have hYX : Y ⊆ X := union_subset hF₁X hF₂X
          have hY_x2 : IsX2Arc Y := ⟨F₁, F₂, u, hF₁, hF₂, h_single, rfl⟩
          have hY_ncap : ¬ IsPlanarInCappedCuff C₁ Y :=
            fun hcap => hF₂_ncap (hcap.mono subset_union_right)
          have hY_nnp : ¬ IsNearPlanar Y :=
            not_isNearPlanar_of_surroundsCuff_and_not_planarInCappedCuff hS hF₁ hF₁_surr hF₂_ncap
              subset_union_left hY_ncap
          exact hall_not_sch Y hYX
            ⟨Or.inr (Or.inr (Or.inl hY_x2)), hY_nnp,
              fun F' hF' hF'Y => hex_oarc F' hF' (hF'Y.1.trans hYX)⟩
        · let Y := F₁ ∪ P
          have hYX : Y ⊆ X := union_subset hF₁X (hPF₂.trans hF₂X)
          have hY_x3 : IsX3Arc Y := isX3Arc_union_chord hF₁ huv hP_line hPF₁
          have hY_nnp : ¬ IsNearPlanar Y :=
            not_isNearPlanar_of_surroundsCuff_and_not_planarInCappedCuff hS hF₁ hF₁_surr hF₂_ncap
              subset_union_left hY_ncap
          exact hall_not_sch Y hYX
            ⟨Or.inr (Or.inr (Or.inr hY_x3)), hY_nnp,
              fun F' hF' hF'Y => hex_oarc F' hF' (hF'Y.1.trans hYX)⟩

/-- Every `α(G)`-candidate `X` (`IsAlphaCandidate G X`) with `¬ IsSphere S ∨ X ≠ univ` contains a
`G`-normal schismatic subset `Y ⊆ X`. -/
theorem exists_schismatic_of_isAlphaCandidate_of_ne_univ
    (hS : IsSurface S) [ConnectedSpace S] (G : Drawing S) {X : Set S}
    (hns : ¬ IsSphere S ∨ X ≠ univ)
    (hX : IsAlphaCandidate G X) :
    ∃ Y : Set S, Y ⊆ X ∧ IsSchismatic Y ∧ G.IsNormal Y := by
  obtain ⟨hX_solid, hX_conn, hX_norm, hX_nnp⟩ := hX
  have hnot_all : ¬ (∀ Y : Set S, Y ⊆ X → ¬ IsSchismatic Y) :=
    fun hall => hX_nnp ((isNearPlanar_iff_forall_not_isSchismatic hS hns hX_solid hX_conn).mpr hall)
  push Not at hnot_all
  obtain ⟨Y, hYX, hY_sch⟩ := hnot_all
  exact ⟨Y, hYX, hY_sch, fun z ⟨hzY, hzU⟩ => hX_norm ⟨hYX hzY, hzU⟩⟩

/-- On any connected surface `S` that is not a 2-sphere (`¬ IsSphere S`), every `α(G)`-candidate
`X` (`IsAlphaCandidate G X`) contains a `G`-normal schismatic subset `Y ⊆ X`.
This provides the hypothesis `hcontains` of `GraphMinor.GM12.alpha_ge_of_schismatic_counts`. -/
theorem exists_schismatic_of_isAlphaCandidate
    (hS : IsSurface S) [ConnectedSpace S] (hns : ¬ IsSphere S)
    (G : Drawing S) :
    ∀ X : Set S, IsAlphaCandidate G X →
      ∃ Y : Set S, Y ⊆ X ∧ IsSchismatic Y ∧ G.IsNormal Y :=
  fun _ hX => exists_schismatic_of_isAlphaCandidate_of_ne_univ hS G (Or.inl hns) hX

/-- Every `G`-normal schismatic set `Y` in a surface `S` is an `α(G)`-candidate
(`IsAlphaCandidate G Y`). -/
theorem IsSchismatic.isAlphaCandidate
    (hS : IsSurface S) {G : Drawing S} {Y : Set S}
    (hY : IsSchismatic Y) (hnorm : G.IsNormal Y) :
    IsAlphaCandidate G Y := by
  obtain ⟨hsol, hconn⟩ := hY.isSolid_and_isConnected hS
  exact ⟨hsol, hconn, hnorm, hY.2.1⟩

/-- Graph Minors VII, Section 8 (page 241):
"Thus $\alpha(G)$ equals the minimum of $|V(G) \cap X|$, taken over all $G$-normal schismatic sets
$X$; and this provides us with an alternative definition of $\alpha(G)$." -/
theorem alpha_eq_sInf_schismatic
    (hS : IsSurface S) [ConnectedSpace S] (hns : ¬ IsSphere S)
    (G : Drawing S) :
    alpha G = sInf {(G.V ∩ X).ncard | (X : Set S) (_ : IsSchismatic X ∧ G.IsNormal X)} := by
  let S_cand : Set ℕ := {n : ℕ | ∃ X : Set S, IsAlphaCandidate G X ∧ (X ∩ G.V).ncard = n}
  let S_sch : Set ℕ := {(G.V ∩ X).ncard | (X : Set S) (_ : IsSchismatic X ∧ G.IsNormal X)}
  change sInf S_cand = sInf S_sch
  have h_sub : S_sch ⊆ S_cand := by
    rintro _ ⟨Y, ⟨hY_sch, hY_norm⟩, rfl⟩
    exact ⟨Y, hY_sch.isAlphaCandidate hS hY_norm, by rw [inter_comm]⟩
  by_cases hne : S_cand.Nonempty
  · obtain ⟨_, ⟨X₀, hX₀, rfl⟩⟩ := hne
    obtain ⟨Y₀, _, hY₀_sch, hY₀_norm⟩ :=
      exists_schismatic_of_isAlphaCandidate hS hns G X₀ hX₀
    have hne_sch : S_sch.Nonempty := ⟨(G.V ∩ Y₀).ncard, Y₀, ⟨hY₀_sch, hY₀_norm⟩, rfl⟩
    refine le_antisymm (csInf_le_csInf (OrderBot.bddBelow S_cand) hne_sch h_sub) ?_
    obtain ⟨X, hX, hk_eq⟩ := Nat.sInf_mem (⟨_, X₀, hX₀, rfl⟩ : S_cand.Nonempty)
    rw [← hk_eq, inter_comm]
    obtain ⟨Y, hYX, hY_sch, hY_norm⟩ :=
      exists_schismatic_of_isAlphaCandidate hS hns G X hX
    have hle : (G.V ∩ Y).ncard ≤ (G.V ∩ X).ncard :=
      ncard_le_ncard (inter_subset_inter_right G.V hYX) (G.finite_V.inter_of_left X)
    have hY_mem : (G.V ∩ Y).ncard ∈ S_sch := ⟨Y, ⟨hY_sch, hY_norm⟩, rfl⟩
    exact (Nat.sInf_le hY_mem).trans hle
  · have h_cand_emp : S_cand = ∅ := not_nonempty_iff_eq_empty.mp hne
    have h_sch_emp : S_sch = ∅ := eq_empty_of_subset h_sub h_cand_emp
    rw [h_cand_emp, h_sch_emp]

end GraphMinor.GM07
