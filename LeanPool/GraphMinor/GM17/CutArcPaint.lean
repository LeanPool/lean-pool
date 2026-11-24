/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.CutSide
public import LeanPool.GraphMinor.Surface.CutIArc
public import LeanPool.GraphMinor.Surface.ModelCriterion

/-!
# Cutting a painted surface along a normal `I`-arc

We prove `CutNormalIArcPaintingStatement`, the surface part of (5.3) of Graph Minors XVII (page
172). We cut along the arc with `cutIArc`.
If the cut surface is connected, then `CutSetup.cutSide` gives the painting of the first case. If it
has two parts, then each part
either is simpler than the surface, or it is a closed disc and then its image in the surface is a
disc cut off by the arc.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface

variable {Y S : Type} [TopologicalSpace Y] [TopologicalSpace S]

theorem cut_encard_le {ψ : Y → S} {F : Set S} (h : IsCutting ψ F) {x : S} (hx : x ∈ F) :
  (ψ ⁻¹' {x}).encard ≤ 2 := by
  obtain ⟨a, b, hab, he⟩ := Set.ncard_eq_two.mp (h.2.2.2.1 x hx)
  rw [he, encard_pair hab]

/-- The restriction of a cut to a clopen set. -/
theorem cutMap_sub [CompactSpace Y] [T2Space S] {ψ : Y → S} {F : Set S} (h : IsCutting ψ F)
  (hF : IsClosed F) {W : Set Y} (hW : IsClopen W) :
    CutMap (ψ ∘ (Subtype.val : W → Y)) F := by
  refine ⟨h.1.comp continuous_subtype_val, ?_, ?_, hF, ?_, ?_⟩
  · intro y hy y' hy' he
    exact Subtype.ext (h.2.2.1 hy hy' he)
  · have he : range (ψ ∘ (Subtype.val : W → Y)) \ F = (ψ '' Wᶜ ∪ F)ᶜ := by
      ext x
      constructor
      · rintro ⟨⟨y, rfl⟩, hxF⟩
        rintro (⟨y', hy', he⟩ | h1)
        · have hyF : y' ∈ ψ ⁻¹' Fᶜ := by rwa [mem_preimage, he]
          have hyEq := h.2.2.1 (show y.1 ∈ ψ ⁻¹' Fᶜ from hxF) hyF he.symm
          exact hy' (hyEq ▸ y.2)
        · exact hxF h1
      · intro hx
        obtain ⟨y, rfl⟩ := h.2.1 x
        have hyW : y ∈ W := by
          by_contra hn
          exact hx (.inl ⟨y, hn, rfl⟩)
        exact ⟨⟨⟨y, hyW⟩, rfl⟩, fun h1 => hx (.inr h1)⟩
    rw [he]
    exact ((hW.2.isClosed_compl.isCompact.image h.1).isClosed.union hF).isOpen_compl
  · intro x hx
    have hs : Subtype.val '' ((ψ ∘ (Subtype.val : W → Y)) ⁻¹' {x}) ⊆ ψ ⁻¹' {x} := by
      rintro _ ⟨y, hy, rfl⟩
      exact hy
    rw [← Subtype.val_injective.injOn.encard_image]
    exact (encard_le_encard hs).trans (cut_encard_le h hx)
  · intro y hy
    exact (mem_bd_sub hW.2).mpr (h.2.2.2.2 hy)

variable [CompactSpace S] [T2Space S]

omit [CompactSpace S] in
/-- What one part of the cut surface gives. -/
theorem side_facts [CompactSpace Y] [T2Space Y] (hS : IsSurface S) (hY : IsSurface Y) {ψ : Y
  → S} {F : Set S} (hψ : IsCutting ψ F) {Γ : Painting S} {n₁ n₂ : S}
    (hnorm : Γ.IsNormal F) (hFl : IsLineWithEnds F n₁ n₂) (hb : F ∩ bd S = {n₁, n₂})
      (hint : ∀ c ∈ Γ.C, Γ.IsInternalCell c → Disjoint (tilde c) F)
    {W : Set Y} (hW : IsClopen W) {Ks₀ : Set (Set Y)} (hfin : Ks₀.Finite) (hne : Ks₀.Nonempty)
      (hsub : ∀ K ∈ Ks₀, K ⊆ W) (hcov : ⋃₀ Ks₀ = ψ ⁻¹' F ∩ W)
    (hdis : Ks₀.PairwiseDisjoint id) (hK : ∀ K ∈ Ks₀, BijOn ψ K F ∧ ∃ u v, IsLineWithEnds K u v
      ∧ ψ u = n₁ ∧ ψ v = n₂) :
    (∃ (ι : S → W) (Γ' : Painting W), IsCutSidePainting S Γ F (keepCells Γ (ψ ∘ (Subtype.val : W
      → Y)) F) W ι Γ') ∧ (cuffs W).Nonempty := by
  obtain ⟨K₀, hK₀⟩ := hne
  have hFc : IsClosed F := hFl.isCompact.isClosed
  have hmap := cutMap_sub hψ hFc hW
  have hneW : Nonempty W := by
    obtain ⟨u, v, hl, -⟩ := (hK K₀ hK₀).2
    exact ⟨⟨u, hsub K₀ hK₀ hl.left_mem⟩⟩
  let Ks : Set (Set W) := (fun K => Subtype.val ⁻¹' K) '' Ks₀
  have hpull : ∀ K₁ ∈ Ks, ∃ u v, IsLineWithEnds K₁ u v ∧ (ψ ∘ Subtype.val) u = n₁ ∧
    (ψ ∘ Subtype.val) v = n₂ := by
    rintro _ ⟨K, hKs, rfl⟩
    obtain ⟨-, u, v, hl, hu, hv⟩ := hK K hKs
    obtain ⟨u', v', rfl, rfl, hl'⟩ := hl.pull (j := (Subtype.val : W → Y)) IsEmbedding.subtypeVal
      (by rw [Subtype.range_val]; exact hsub K hKs)
    exact ⟨u', v', hl', hu, hv⟩
  choose! e₁ e₂ hl' he₁ he₂ using hpull
  have hL : LiftData (ψ ∘ (Subtype.val : W → Y)) F n₁ n₂ Ks e₁ e₂ := by
    refine ⟨hfin.image _, hl', ?_, he₁, he₂, ?_, ?_⟩
    · rintro _ ⟨K, hKs, rfl⟩
      obtain ⟨hb1, -⟩ := hK K hKs
      refine ⟨fun y hy => hb1.1 hy, fun y hy y' hy' he => Subtype.ext (hb1.2.1 hy hy' he),
        fun x hx => ?_⟩
      obtain ⟨y, hy, rfl⟩ := hb1.2.2 hx
      exact ⟨⟨y, hsub K hKs hy⟩, hy, rfl⟩
    · rintro _ ⟨K, hKs, rfl⟩ _ ⟨K', hKs', rfl⟩ hne
      have hkk : K ≠ K' := fun he => hne (by rw [he])
      exact Disjoint.preimage _ (hdis hKs hKs' hkk)
    · ext y
      constructor
      · rintro ⟨_, ⟨K, hKs, rfl⟩, hy⟩
        exact (hcov.subset ⟨K, hKs, hy⟩).1
      · intro hy
        obtain ⟨K, hKs, hyK⟩ := hcov.symm.subset (⟨hy, y.2⟩ : y.1 ∈ ψ ⁻¹' F ∩ W)
        exact ⟨_, ⟨K, hKs, rfl⟩, hyK⟩
  have hsurf := isSurface_sub hY hW
  have hsetup : CutSetup Γ (ψ ∘ (Subtype.val : W → Y)) F n₁ n₂ Ks e₁ e₂
    := ⟨hmap, hL, hS, hsurf, hnorm, hFl, hb, hint⟩
  refine ⟨hsetup.cutSide ⟨K₀, hK₀, rfl⟩, ?_⟩
  have hl0 := hl' _ ⟨K₀, hK₀, rfl⟩
  have hb0 := hmap.bdF (show e₁ _ ∈ _ from by
    have h1 : (ψ ∘ Subtype.val) (e₁ (Subtype.val ⁻¹' K₀)) = n₁ := he₁ _ ⟨K₀, hK₀, rfl⟩
    rw [mem_preimage, h1]
    exact hFl.left_mem)
  exact ⟨_, _, hb0, rfl⟩

omit [CompactSpace S] in
/-- A disc part of the cut surface gives a disc in the surface. -/
theorem side_disc [CompactSpace Y] (_hS : IsSurface S) {ψ : Y
  → S} {F : Set S} {W : Set Y} {Γ : Painting S} (hmap : CutMap (ψ ∘ (Subtype.val : W → Y)) F)
    (hnorm : Γ.IsNormal F) (hW : IsClosed W) (hinj : InjOn ψ W) (hsurj : F ⊆ ψ '' W) [Nonempty W]
      (e : W ≃ₜ ClosedUnitDisc) :
    ∃ Δ : Set S, IsClosedDisc Δ ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd S ∧ {c ∈ Γ.C | c ⊆ Δ}
      = keepCells Γ (ψ ∘ (Subtype.val : W → Y)) F := by
  have hcomp : CompactSpace W := isCompact_iff_compactSpace.mp hW.isCompact
  have hi : Function.Injective (ψ ∘ (Subtype.val : W → Y)) := fun y y' he => Subtype.ext
    (hinj y.2 y'.2 he)
  have hE : IsEmbedding (ψ ∘ (Subtype.val : W → Y)) := (hmap.cont.isClosedEmbedding hi).isEmbedding
  let E : W ≃ₜ range (ψ ∘ (Subtype.val : W → Y)) := hE.toHomeomorph
  have hbd : discBd (range (ψ ∘ (Subtype.val : W → Y))) = (ψ ∘ Subtype.val) '' bd W := by
    rw [discBd, ← image_bd_homeomorph E, image_image]
    rfl
  refine ⟨range (ψ ∘ (Subtype.val : W → Y)), ⟨e.symm.trans E⟩, ?_, ?_, ?_⟩
  · rw [hbd]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hsurj hx
    exact ⟨⟨y, hy⟩, hmap.bdF hx, rfl⟩
  · rw [hbd]
    rintro _ ⟨y, hy, rfl⟩
    by_cases hF : (ψ ∘ Subtype.val) y ∈ F
    · exact .inl hF
    · exact .inr ((hmap.mem_bd_iff hF).mp hy)
  · ext c
    constructor
    · rintro ⟨hc, hs⟩
      exact ⟨hc, fun x hx => ⟨hs hx, fun hxF => (arcComponentsIn_subset hc hx).2 (hnorm ⟨hxF,
        (arcComponentsIn_subset hc hx).1⟩)⟩⟩
    · rintro ⟨hc, hs⟩
      exact ⟨hc, fun x hx => (hs hx).1⟩

omit [CompactSpace S] [T2Space S] in
/-- A closed disc is simpler than a connected surface with a cuff that is not a closed disc. -/
theorem disc_simpler {D : Type} [TopologicalSpace D] [ConnectedSpace S] (hS : IsSurface S)
  (e : D ≃ₜ ClosedUnitDisc) (hn : ¬ Nonempty (S ≃ₜ ClosedUnitDisc))
    (hc : (cuffs S).Nonempty) : IsSimplerThan D S := by
  obtain ⟨a', b', c', ⟨e'⟩⟩ := classification.{0} S hS ‹_›
  obtain ⟨d⟩ := nonempty_disc_homeo
  have hc0 : c' ≠ 0 := by
    rintro rfl
    obtain ⟨ht, f, hf⟩ := presents_ew a' b' 0
    have h1 := ncard_cuffs hf
    rw [← ncard_cuffs_congr e'] at h1
    have h2 := (Set.ncard_pos (cuff_statement.{0} S hS).2.1).mpr hc
    omega
  have h1 : ¬ (a' = 0 ∧ b' = 0 ∧ c' = 1) := by
    rintro ⟨rfl, rfl, rfl⟩
    exact hn ⟨e'.trans d⟩
  exact ⟨0, 0, 1, a', b', c', ⟨e.trans d.symm⟩, ⟨e'⟩, by omega, by omega, by omega⟩

/-- The surface part of (5.3) of Graph Minors XVII, page 172. -/
theorem cutNormalIArc : CutNormalIArcPaintingStatement := by
  unfold CutNormalIArcPaintingStatement
  intro S _ hcS ht2 hconn hS Γ F n₁ n₂ hnorm hFl hb hint
  have hne := hFl.ne'
  obtain ⟨Y, tY, ψ, hY, hψ, h1, h2, X, X', hd, hun, lX, lX', bX, bX'⟩
    := cutIArc.{0} S F n₁ n₂ hS hconn hne hb hFl
  have ht2Y : T2Space Y := hY.2.1
  have hcY : CompactSpace Y := hY.1
  have hends : ∀ {K : Set Y}, IsLine K → BijOn ψ K F → ∃ u v, IsLineWithEnds K u v ∧ ψ u = n₁ ∧ ψ v
    = n₂ := by
    intro K hl hbj
    obtain ⟨f⟩ := hl
    have hline : IsLineWithEnds K (f 0) (f 1) := ⟨f, rfl, rfl⟩
    obtain ⟨a, ha, hr, h0, h1'⟩ := hline.exists_arc
    have harc : IsArcMap (ψ ∘ a) := ⟨hψ.1.comp ha.1, fun s t he => ha.2 (hbj.injOn
      (hr ▸ mem_range_self s) (hr ▸ mem_range_self t) he)⟩
    have h3 := harc.isLineWithEnds
    rw [range_comp, hr, hbj.image_eq] at h3
    have h4 := (lineEnds_eq h3).symm.trans (lineEnds_eq hFl)
    simp only [Function.comp, h0, h1'] at h4
    rcases Set.pair_eq_pair_iff.mp h4 with ⟨h5, h6⟩ | ⟨h5, h6⟩
    · exact ⟨_, _, hline, h5, h6⟩
    · exact ⟨_, _, hline.symm, h6, h5⟩
  obtain ⟨x0, x1, hlX, hx0, hx1⟩ := hends lX bX
  obtain ⟨y0, y1, hlX', hy0, hy1⟩ := hends lX' bX'
  have pX := isPreconnected_line hlX
  have pX' := isPreconnected_line hlX'
  have hn₁b : n₁ ∈ bd S := (show n₁ ∈ F ∩ bd S from hb ▸ mem_insert _ _).2
  have hcuffS : (cuffs S).Nonempty := ⟨_, n₁, hn₁b, rfl⟩
  have hFc : IsClosed F := hFl.isCompact.isClosed
  rcases cut_comps hψ hY pX pX' hun hlX.left_mem hlX'.left_mem with hYc | ⟨W₁, W₂, hne', hsc, hX₁,
    hX₂, hW₁, hW₂, hU, hdW, hc₁, hc₂⟩
  · left
    have hone : ∀ C ∈ spaceComponents Y, C = univ := fun C hC => by
      rw [spaceComponents_eq] at hC
      obtain ⟨y, rfl⟩ := hC
      exact PreconnectedSpace.connectedComponent_eq_univ y
    have hunivc : univ ∈ spaceComponents Y := by
      rw [spaceComponents_eq]
      exact ⟨x0, PreconnectedSpace.connectedComponent_eq_univ x0⟩
    have hsimp : IsSimplerThan (univ : Set Y) S := by
      by_cases hs : connectedComponentIn (bd S) n₁ = connectedComponentIn (bd S) n₂
      · rcases h2 hs with hc | ⟨C₁, C₂, hneC, heq, -, -⟩
        · exact hc.2 univ hunivc
        · exfalso
          exact hneC ((hone C₁ (heq ▸ mem_insert _ _)).trans (hone C₂
            (heq ▸ mem_insert_of_mem _ rfl)).symm)
      · obtain ⟨-, a, b, c, ⟨e⟩, ⟨e'⟩⟩ := h1 hs
        exact ⟨a, b, c, a, b, c + 1, ⟨(Homeomorph.Set.univ Y).trans e'⟩, ⟨e⟩, le_rfl, le_rfl,
          by omega⟩
    obtain ⟨⟨ι, Γ', hp⟩, hcuf⟩ := side_facts (W := univ) (Ks₀ := {X, X'}) hS hY hψ hnorm hFl hb
      hint isClopen_univ (by simp) (by simp) (fun _ _ => subset_univ _)
      (by rw [sUnion_pair, hun, inter_univ])
      (by
        rintro K (rfl | rfl) K' (rfl | rfl) hne2
        · exact absurd rfl hne2
        · exact hd
        · exact hd.symm
        · exact absurd rfl hne2)
      (by
        rintro K (rfl | rfl)
        · exact ⟨bX, x0, x1, hlX, hx0, hx1⟩
        · exact ⟨bX', y0, y1, hlX', hy0, hy1⟩)
    have hkeep : keepCells Γ (ψ ∘ (Subtype.val : ↥(univ : Set Y) → Y)) F = Γ.C := by
      ext c
      refine ⟨fun h => h.1, fun hc => ⟨hc, fun x hx => ⟨?_, fun hxF =>
        (arcComponentsIn_subset hc hx).2 (hnorm ⟨hxF, (arcComponentsIn_subset hc hx).1⟩)⟩⟩⟩
      obtain ⟨y, rfl⟩ := hψ.2.1 x
      exact ⟨⟨y, trivial⟩, rfl⟩
    rw [hkeep] at hp
    exact ⟨(univ : Set Y), inferInstance, isCompact_iff_compactSpace.mp isCompact_univ,
      inferInstance, isConnected_iff_connectedSpace.mp isConnected_univ, ι, Γ',
      isSurface_sub hY isClopen_univ, hsimp, hcuf, hp⟩
  · right
    have hdis₁ : ∀ y ∈ X', y ∉ W₁ := fun y hy hyW => disjoint_left.mp hdW hyW (hX₂ hy)
    have hdis₂ : ∀ y ∈ X, y ∉ W₂ := fun y hy hyW => disjoint_right.mp hdW hyW (hX₁ hy)
    have hcov₁ : ψ ⁻¹' F ∩ W₁ = X := by
      apply subset_antisymm
      · rintro y ⟨hy, hyW⟩
        exact ((hun ▸ hy : y ∈ X ∪ X').resolve_right fun h => hdis₁ y h hyW)
      · intro y hy
        exact ⟨hun ▸ .inl hy, hX₁ hy⟩
    have hcov₂ : ψ ⁻¹' F ∩ W₂ = X' := by
      apply subset_antisymm
      · rintro y ⟨hy, hyW⟩
        exact ((hun ▸ hy : y ∈ X ∪ X').resolve_left fun h => hdis₂ y h hyW)
      · intro y hy
        exact ⟨hun ▸ .inr hy, hX₂ hy⟩
    have hfacts : ∀ {W K : Set Y}, IsClopen W → K ⊆ W → ψ ⁻¹' F ∩ W = K → BijOn ψ K F →
      (∃ u v, IsLineWithEnds K u v ∧ ψ u = n₁ ∧ ψ v = n₂) → ConnectedSpace W →
        (IsSimplerThan W S → ∃ (S' : Type) (_ : TopologicalSpace S') (_ : CompactSpace S')
          (_ : T2Space S') (_ : ConnectedSpace S') (ι : S → S') (Γ' : Painting S'),
          IsSurface S' ∧ IsSimplerThan S' S ∧ (cuffs S').Nonempty ∧ IsCutSidePainting S Γ F
            (keepCells Γ (ψ ∘ (Subtype.val : W → Y)) F) S' ι Γ') ∧
        (Nonempty (W ≃ₜ ClosedUnitDisc) → ∃ Δ : Set S, IsClosedDisc Δ ∧ F ⊆ discBd Δ
          ∧ discBd Δ ⊆ F ∪ bd S ∧ {c ∈ Γ.C | c ⊆ Δ} = keepCells Γ (ψ ∘ (Subtype.val : W → Y)) F)
            := by
      intro W K hW hKW hcov hbj hex hcn
      constructor
      · intro hsimp
        obtain ⟨⟨ι, Γ', hp⟩, hcuf⟩ := side_facts (W := W) (Ks₀ := {K}) hS hY hψ hnorm hFl hb hint
          hW (by simp) (by simp)
          (by rintro _ rfl; exact hKW) (by rw [sUnion_singleton, hcov]) (by simp)
            (by rintro _ rfl; exact ⟨hbj, hex⟩)
        exact ⟨W, inferInstance, isCompact_iff_compactSpace.mp hW.1.isCompact, inferInstance,
          hcn, ι, Γ', isSurface_sub hY hW, hsimp, hcuf, hp⟩
      · rintro ⟨e⟩
        have hinj : InjOn ψ W := by
          intro y hy y' hy' he
          by_cases hF : ψ y ∈ F
          · exact hbj.injOn (hcov ▸ ⟨hF, hy⟩) (hcov ▸ ⟨(he ▸ hF : ψ y' ∈ F), hy'⟩) he
          · exact hψ.2.2.1 hF (by rw [mem_preimage, ← he]; exact hF) he
        have : Nonempty W := ⟨e.symm ⟨0, by simp [ClosedUnitDisc]⟩⟩
        exact side_disc hS (cutMap_sub hψ hFc hW) hnorm hW.1 hinj (fun x hx => by
          obtain ⟨y, hy, rfl⟩ := hbj.surjOn hx
          exact ⟨y, hKW hy, rfl⟩) e
    obtain ⟨hp₁, hq₁⟩ := hfacts hW₁ hX₁ hcov₁ bX ⟨x0, x1, hlX, hx0, hx1⟩ hc₁
    obtain ⟨hp₂, hq₂⟩ := hfacts hW₂ hX₂ hcov₂ bX' ⟨y0, y1, hlX', hy0, hy1⟩ hc₂
    have hm₁ := cutMap_sub hψ hFc hW₁
    have hm₂ := cutMap_sub hψ hFc hW₂
    have hdR : Disjoint (range (ψ ∘ (Subtype.val : W₁ → Y)) \ F) (range (ψ ∘ (Subtype.val : W₂
      → Y)) \ F) := by
      rw [disjoint_left]
      rintro _ ⟨⟨y, rfl⟩, hF⟩ ⟨⟨y', he⟩, -⟩
      have he' : ψ y'.1 = ψ y.1 := he
      have h5 := hψ.2.2.1 (show y'.1 ∈ ψ ⁻¹' Fᶜ by rw [mem_preimage, he']; exact hF) hF he'
      exact disjoint_left.mp hdW y.2 (h5 ▸ y'.2)
    have hcov : ∀ x, x ∉ F → x ∈ (range (ψ ∘ (Subtype.val : W₁ → Y)) \ F) ∪ (range (ψ ∘
      (Subtype.val : W₂ → Y)) \ F) := fun x hx => by
      obtain ⟨y, rfl⟩ := hψ.2.1 x
      rcases (hU ▸ mem_univ y : y ∈ W₁ ∪ W₂) with hy | hy
      · exact .inl ⟨⟨⟨y, hy⟩, rfl⟩, hx⟩
      · exact .inr ⟨⟨⟨y, hy⟩, rfl⟩, hx⟩
    have hoff : ∀ c ∈ Γ.C, ∀ x ∈ c, x ∉ F := fun c hc x hx hxF => (arcComponentsIn_subset hc hx).2
      (hnorm ⟨hxF, (arcComponentsIn_subset hc hx).1⟩)
    have hcase : ∀ c ∈ Γ.C, c ∈ keepCells Γ (ψ ∘ (Subtype.val : W₁ → Y)) F ∨ c ∈ keepCells Γ (ψ ∘
      (Subtype.val : W₂ → Y)) F := fun c hc => by
      rcases (arcComponentsIn_isPathConnected hc).isConnected.isPreconnected.subset_or_subset
        hm₁.isOpen hm₂.isOpen hdR (fun x hx => hcov x (hoff c hc x hx)) with h5 | h5
      · exact .inl ⟨hc, h5⟩
      · exact .inr ⟨hc, h5⟩
    have hrc₁ : IsClosed (range (ψ ∘ (Subtype.val : W₁ → Y))) := by
      have := isCompact_iff_compactSpace.mp hW₁.1.isCompact
      exact (isCompact_range hm₁.cont).isClosed
    have hrc₂ : IsClosed (range (ψ ∘ (Subtype.val : W₂ → Y))) := by
      have := isCompact_iff_compactSpace.mp hW₂.1.isCompact
      exact (isCompact_range hm₂.cont).isClosed
    refine ⟨keepCells Γ (ψ ∘ (Subtype.val : W₁ → Y)) F, keepCells Γ (ψ ∘ (Subtype.val : W₂
      → Y)) F, fun c hc => hc.1, ?_, ?_, ?_⟩
    · ext c
      constructor
      · intro hc
        refine ⟨hc.1, fun hc₁ => ?_⟩
        obtain ⟨x, hx⟩ := arcComponentsIn_nonempty hc.1
        exact disjoint_left.mp hdR (hc₁.2 hx) (hc.2 hx)
      · rintro ⟨hc, hn⟩
        exact (hcase c hc).resolve_left hn
    · intro c₁ hc₁ c₂ hc₂ x hx
      by_contra hxF
      have h5 : x ∈ range (ψ ∘ (Subtype.val : W₁ → Y)) := closure_minimal (fun z hz =>
        (hc₁.2 hz).1) hrc₁ hx.1.1
      have h6 : x ∈ range (ψ ∘ (Subtype.val : W₂ → Y)) := closure_minimal (fun z hz =>
        (hc₂.2 hz).1) hrc₂ hx.2.1
      exact disjoint_left.mp hdR ⟨h5, hxF⟩ ⟨h6, hxF⟩
    · have hW₁c : W₁ ∈ spaceComponents Y := hsc ▸ mem_insert _ _
      have hW₂c : W₂ ∈ spaceComponents Y := hsc ▸ mem_insert_of_mem _ rfl
      by_cases hs : connectedComponentIn (bd S) n₁ = connectedComponentIn (bd S) n₂
      · rcases h2 hs with hc | ⟨C₁, C₂, hneC, heq, ⟨d⟩, ⟨s⟩⟩
        · exact ⟨.inr (hp₂ (hc.2 W₂ hW₂c)), .inr (hp₁ (hc.2 W₁ hW₁c))⟩
        · rcases Set.pair_eq_pair_iff.mp (hsc.symm.trans heq) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · refine ⟨.inl (hq₁ ⟨d⟩), ?_⟩
            by_cases hD : Nonempty (S ≃ₜ ClosedUnitDisc)
            · obtain ⟨e⟩ := hD
              exact .inl (hq₂ ⟨s.trans e⟩)
            · exact .inr (hp₁ (disc_simpler hS d hD hcuffS))
          · refine ⟨?_, .inl (hq₂ ⟨d⟩)⟩
            by_cases hD : Nonempty (S ≃ₜ ClosedUnitDisc)
            · obtain ⟨e⟩ := hD
              exact .inl (hq₁ ⟨s.trans e⟩)
            · exact .inr (hp₂ (disc_simpler hS d hD hcuffS))
      · exfalso
        obtain ⟨hYc, -⟩ := h1 hs
        have hone : ∀ C ∈ spaceComponents Y, C = univ := fun C hC => by
          rw [spaceComponents_eq] at hC
          obtain ⟨y, rfl⟩ := hC
          exact PreconnectedSpace.connectedComponent_eq_univ y
        exact hne' ((hone W₁ hW₁c).trans (hone W₂ hW₂c).symm)

end GraphMinor.GM17
