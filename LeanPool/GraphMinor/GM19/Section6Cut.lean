/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section6a
public import LeanPool.GraphMinor.GM17.CapSide
public import LeanPool.GraphMinor.Surface.CapCoh

/-!
# One side of a curve that bounds no disc

Let `F` be an `O`-arc of a connected closed surface `S` that bounds no closed disc, and let `Z` be a
connected set off `F`. We cut along `F`, keep the side with `Z`, and cap all its cuffs
(`exists_simpler_side`). The result is a connected closed surface that holds a copy of `Z`, and
which has fewer classes of local cocycles than `S`.

This is how the proof of Graph Minors XIX, (6.5) (page 341) gets a surface of larger Euler
characteristic.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM17

local notation "K" => ZMod 2

/-- What we want from a side of `F`. -/
def SideResult (S : Type) [TopologicalSpace S] (Z : Set S) : Prop :=
  ∃ (T : Type) (_ : TopologicalSpace T) (_ : ConnectedSpace T) (ι : S → T) (ι' : T
    → S), IsClosedSurface T ∧ ContinuousOn ι Z ∧
    ContinuousOn ι' (ι '' Z) ∧ LeftInvOn ι' ι Z ∧ ∀ κ κ₁ : ℕ, Nat.card (KCl S K) = 2 ^ κ → Nat.card
      (KCl T K) = 2 ^ κ₁ → κ₁ < κ

variable {Y S : Type} [TopologicalSpace Y] [TopologicalSpace S]

theorem continuousOn_invFun_range {A B : Type} [TopologicalSpace A] [TopologicalSpace B] [Nonempty
  A] {J : A → B} (hJ : IsEmbedding J) :
    ContinuousOn (Function.invFun J) (range J) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have he : (range J).domRestrict (Function.invFun J) = hJ.toHomeomorph.symm := by
    funext t
    obtain ⟨y, rfl⟩ := hJ.toHomeomorph.surjective t
    rw [Homeomorph.symm_apply_apply]
    exact Function.leftInverse_invFun hJ.injective y
  rw [he]
  exact hJ.toHomeomorph.symm.continuous

/-- Capping the side `W` of the cut. -/
theorem side_result_of_cap [CompactSpace Y] (hT : IsClosedSurface S)
  {ψ : Y → S} {F Z : Set S} (hψ : IsCutting ψ F) (hY : IsSurface Y)
    (hFc : IsClosed F) {W : Set Y} (hW : IsClopen W) (hc : ConnectedSpace W)
    (hB : IsOArc ((ψ ∘ (Subtype.val : W → Y)) ⁻¹' F) ∨ ∃ P P', Disjoint P P' ∧ P ∪ P' = (ψ ∘
      (Subtype.val : W → Y)) ⁻¹' F ∧ IsOArc P ∧ IsOArc P')
    (hsimp : ∀ (V : Type) [TopologicalSpace V], CapDrops W V → IsSimplerThan V S) (hZ : Z ⊆ range
      (ψ ∘ (Subtype.val : W → Y)) \ F) :
    SideResult S Z := by
  have ht2S : T2Space S := hT.2.1
  have hm := cutMap_sub hψ hFc hW
  have hsurf := isSurface_sub hY hW
  have hcW : CompactSpace W := hsurf.1
  have ht2W : T2Space W := hsurf.2.1
  obtain ⟨V, tV, j, hV, hconnV, hj, -, hdrop⟩ := cap_lifts hsurf hm.bdF hB
  have ht2V : T2Space V := hV.2.1
  obtain ⟨a, b, c, a', b', c', ⟨e⟩, ⟨e'⟩, h1, h2, h3⟩ := hsimp V hdrop
  obtain ⟨T, tT, j', C, hT₁, hj', hC, hu, hi, hconn, 𝓓, hf, hU, hd, hdj⟩ := exists_capAll_discs V hV
  have hbdS : bd S = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx => hx (hT.2.2 x)
  obtain rfl : c' = 0 := model_c_eq_zero e' hbdS
  have ht2T : T2Space T := hT₁.2.1
  obtain ⟨f, hfi⟩ := kCl_cap_injective hj' hu hi hf hU hd hdj
  have hJ : IsClosedEmbedding (j' ∘ j) := hj'.comp hj
  obtain ⟨σ, hσc, hσ₁, hσ₂⟩ := hm.exists_sec
  refine ⟨T, tT, hconn hconnV, (j' ∘ j) ∘ σ, (ψ ∘ Subtype.val) ∘ Function.invFun (j' ∘ j), hT₁,
    ?_, ?_, ?_, ?_⟩
  · exact hJ.continuous.comp_continuousOn (hσc.mono hZ)
  · refine (hψ.1.comp continuous_subtype_val).comp_continuousOn ((continuousOn_invFun_range
    hJ.isEmbedding).mono ?_)
    rintro _ ⟨z, -, rfl⟩
    exact ⟨_, rfl⟩
  · intro z hz
    change (ψ ∘ Subtype.val) (Function.invFun (j' ∘ j) ((j' ∘ j) (σ z))) = z
    rw [Function.leftInverse_invFun hJ.injective (σ z)]
    exact hσ₁ z (hZ hz)
  · intro κ κ₁ hκ hκ₁
    have h4 := card_kCl_of_model e
    have h5 := card_kCl_of_model e'
    have hfin : Finite (KCl V K) := Nat.finite_of_card_ne_zero (by rw [h4]; positivity)
    have h6 := Nat.card_le_card_of_injective f hfi
    rw [hκ₁, h4] at h6
    rw [hκ] at h5
    have h7 : κ₁ ≤ 2 * a + b := (Nat.pow_le_pow_iff_right (by norm_num)).mp h6
    have h8 : κ = 2 * a' + b' := Nat.pow_right_injective (le_refl 2) h5
    omega

/-- The case where the cut has two sides, and `Z` lies in the first. -/
theorem side_result_two [CompactSpace Y] (hT : IsClosedSurface S) [ConnectedSpace S] {ψ
  : Y → S} {F Z : Set S} (hY : IsSurface Y) (hO : IsOArc F)
    (hFc : IsClosed F) (hnn : ¬ ∃ Δ, IsClosedDisc Δ ∧ discBd Δ = F) {W₁ W₂ X X' : Set Y}
      (T : TwoSides ψ F W₁ W₂ X X') (hOX : IsOArc X) (hOX' : IsOArc X')
    (hne : W₁ ≠ W₂) (hsc : spaceComponents Y = {W₁, W₂}) (hc₁ : ConnectedSpace W₁)
      (hc₂ : ConnectedSpace W₂)
    (hcase : CutIsSimpler Y S ∨ CutHasCopy Y S ClosedCylinder ∨ CutHasDisc Y) (hZ : Z ⊆ range (ψ ∘
      (Subtype.val : W₁ → Y)) \ F) : SideResult S Z := by
  have hS : IsSurface S := hT.isSurface
  have ht2S : T2Space S := hT.2.1
  have hcS : CompactSpace S := hT.1
  have hnod₁ : ¬ Nonempty (W₁ ≃ₜ ClosedUnitDisc) := fun ⟨e⟩ => hnn ⟨_, (T.disc hO e).1,
    (T.disc hO e).2.1⟩
  have hnod₂ : ¬ Nonempty (W₂ ≃ₜ ClosedUnitDisc) := fun ⟨e⟩ => hnn ⟨_, (T.symm.disc hO e).1,
    (T.symm.disc hO e).2.1⟩
  obtain ⟨φ'⟩ := id hOX'
  have hs := side_tri hS (W := W₂) (W' := W₁) (X := X') hne.symm (by rw [hsc, pair_comm]) ⟨_,
    (φ' 1).2, T.hX' (φ' 1).2⟩ hOX' T.hbd' hY T.c₂ hc₂ hcase
    fun h => absurd h hnod₁
  have hsimp := hs.resolve_left hnod₂
  have hfib : (ψ ∘ (Subtype.val : W₁ → Y)) ⁻¹' F = Subtype.val ⁻¹' X := by
    ext y
    change ψ y.1 ∈ F ↔ y.1 ∈ X
    constructor
    · intro h
      rcases (T.hun.symm.subset h : y.1 ∈ X ∪ X') with h1 | h1
      · exact h1
      · exact absurd (T.hX' h1) (disjoint_left.mp T.hd y.2)
    · exact fun h => T.hun.subset (Or.inl h)
  exact side_result_of_cap hT T.hψ hY hFc T.c₁ hc₁ (.inl (hfib ▸ isOArc_preimage hOX T.hX)) hsimp hZ

/-- **One side of a curve.** Let `F` be an `O`-arc of a connected closed surface that bounds no
closed disc, and let `Z` be a nonempty connected set off `F`. Then `Z` embeds in a connected closed
surface with fewer classes of local cocycles. -/
theorem exists_simpler_side (hT : IsClosedSurface S) [ConnectedSpace S] {F Z : Set S}
  (hO : IsOArc F) (hnn : ¬ ∃ Δ, IsClosedDisc Δ ∧ discBd Δ = F)
    (hZ : IsPreconnected Z) (hd : Disjoint Z F) : SideResult S Z := by
  have hS : IsSurface S := hT.isSurface
  have ht2S : T2Space S := hT.2.1
  have hcS : CompactSpace S := hT.1
  have hbdS : bd S = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx => hx (hT.2.2 x)
  have hdb : Disjoint F (bd S) := by rw [hbdS]; exact disjoint_empty _
  have hFc : IsClosed F := by
    obtain ⟨φ⟩ := id hO
    have hc : IsCompact F := by
      rw [isCompact_iff_compactSpace]
      exact φ.compactSpace
    exact hc.isClosed
  obtain ⟨Y, tY, ψ, hY, hψ, hcase, hlift⟩ := cutOArc.{0} S F hS ‹_› hO hdb
  have ht2Y : T2Space Y := hY.2.1
  have hcY : CompactSpace Y := hY.1
  have hconnected : ConnectedSpace Y → (IsOArc (ψ ⁻¹' F) ∨ ∃ P P', Disjoint P P' ∧ P ∪ P' = ψ ⁻¹' F
    ∧ IsOArc P ∧ IsOArc P') → SideResult S Z := by
    intro hYc hB
    have hone : ∀ C ∈ spaceComponents Y, C = univ := fun C hC => by
      rw [spaceComponents_eq] at hC
      obtain ⟨y, rfl⟩ := hC
      exact PreconnectedSpace.connectedComponent_eq_univ y
    obtain ⟨y₀⟩ : Nonempty Y := inferInstance
    have hunivc : univ ∈ spaceComponents Y := by
      rw [spaceComponents_eq]
      exact ⟨y₀, PreconnectedSpace.connectedComponent_eq_univ y₀⟩
    have hs : IsSimplerThan (univ : Set Y) S := by
      rcases hcase with h | ⟨C₁, C₂, hneC, heq, -, -⟩ | ⟨C₁, C₂, hneC, heq, -⟩
      · exact h.2 univ hunivc
      · exact absurd ((hone C₁ (heq ▸ mem_insert _ _)).trans (hone C₂
        (heq ▸ mem_insert_of_mem _ rfl)).symm) hneC
      · exact absurd ((hone C₁ (heq ▸ mem_insert _ _)).trans (hone C₂
        (heq ▸ mem_insert_of_mem _ rfl)).symm) hneC
    have hcu : ConnectedSpace ↥(univ : Set Y) := (Homeomorph.Set.univ
      Y).symm.surjective.connectedSpace (Homeomorph.Set.univ Y).symm.continuous
    have hB' : IsOArc ((ψ ∘ (Subtype.val : ↥(univ : Set Y) → Y)) ⁻¹' F) ∨ ∃ P P', Disjoint P P'
      ∧ P ∪ P' = (ψ ∘ (Subtype.val : ↥(univ : Set Y) → Y)) ⁻¹' F ∧ IsOArc P ∧ IsOArc P' := by
      rcases hB with h | ⟨P, P', hdj, hu, h1, h2⟩
      · exact .inl (isOArc_preimage h (subset_univ _))
      · refine .inr ⟨_, _, hdj.preimage Subtype.val, ?_, isOArc_preimage h1 (subset_univ _),
          isOArc_preimage h2 (subset_univ _)⟩
        rw [← preimage_union, hu, preimage_comp]
    refine side_result_of_cap hT hψ hY hFc isClopen_univ hcu hB' (fun V _ hV => ?_) fun z hz => ?_
    · obtain ⟨a, b, c, a₁, b₁, c₁, h1, h2, h3, h4, h5⟩ := hs
      obtain ⟨c₂, h6, h7⟩ := hV a b c h1
      exact ⟨a, b, c₂, a₁, b₁, c₁, h7, h2, h3, h4, by omega⟩
    · obtain ⟨y, rfl⟩ := hψ.2.1 z
      exact ⟨⟨⟨y, mem_univ _⟩, rfl⟩, disjoint_left.mp hd hz⟩
  rcases hlift with ⟨X, X', hdX, hun, hOX, hOX', bX, bX'⟩ | hQ
  swap
  · obtain ⟨φ⟩ := id hQ
    have hp := hQ.isPreconnected
    rcases cut_comps hψ hY hp hp (union_self _) (φ 1).2 (φ 1).2 with hYc | ⟨W₁, W₂, -, -, h1, h2,
      -, -, -, hdW, -, -⟩
    · exact hconnected hYc (.inl hQ)
    · exact absurd (h2 (φ 1).2) (disjoint_left.mp hdW (h1 (φ 1).2))
  obtain ⟨φ⟩ := id hOX
  obtain ⟨φ'⟩ := id hOX'
  rcases cut_comps hψ hY hOX.isPreconnected hOX'.isPreconnected hun (φ 1).2
    (φ' 1).2 with hYc | ⟨W₁, W₂, hne', hsc, hX₁, hX₂, hW₁, hW₂, hU, hdW, hc₁, hc₂⟩
  · exact hconnected hYc (.inr ⟨X, X', hdX, hun, hOX, hOX'⟩)
  have hbX : X ⊆ bd Y := fun y hy => hψ.2.2.2.2 (hun.subset (.inl hy))
  have hbX' : X' ⊆ bd Y := fun y hy => hψ.2.2.2.2 (hun.subset (.inr hy))
  have T : TwoSides ψ F W₁ W₂ X X' := ⟨hψ, hW₁, hW₂, hU, hdW, hX₁, hX₂, hun, bX, bX', hbX, hbX'⟩
  have hm₁ := cutMap_sub hψ hFc hW₁
  have hm₂ := cutMap_sub hψ hFc hW₂
  let P₁ := range (ψ ∘ (Subtype.val : W₁ → Y)) \ F
  let P₂ := range (ψ ∘ (Subtype.val : W₂ → Y)) \ F
  have hPd : Disjoint P₁ P₂ := by
    rw [disjoint_left]
    rintro _ ⟨⟨y, rfl⟩, h1⟩ ⟨⟨y', he⟩, -⟩
    have he' : ψ y'.1 = ψ y.1 := he
    have hy'F : y'.1 ∈ ψ ⁻¹' Fᶜ := by rwa [mem_preimage, he']
    have h2 : y'.1 = y.1 := hψ.2.2.1 hy'F h1 he'
    exact disjoint_left.mp hdW y.2 (h2 ▸ y'.2)
  have hPc : Z ⊆ P₁ ∪ P₂ := fun x hx => by
    have hxF := disjoint_left.mp hd hx
    obtain ⟨y, rfl⟩ := hψ.2.1 x
    rcases (hU ▸ mem_univ y : y ∈ W₁ ∪ W₂) with h | h
    · exact .inl ⟨⟨⟨y, h⟩, rfl⟩, hxF⟩
    · exact .inr ⟨⟨⟨y, h⟩, rfl⟩, hxF⟩
  rcases hZ.subset_or_subset hm₁.isOpen hm₂.isOpen hPd hPc with h | h
  · exact side_result_two hT hY hO hFc hnn T hOX hOX' hne' hsc hc₁ hc₂ hcase h
  · exact side_result_two hT hY hO hFc hnn T.symm hOX' hOX hne'.symm (by rw [hsc,
      pair_comm]) hc₂ hc₁ hcase h

end GraphMinor.GM19
