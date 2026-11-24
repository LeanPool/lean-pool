/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.PaintTransfer
public import LeanPool.GraphMinor.GM17.CutArcPaint
public import LeanPool.GraphMinor.Surface.CutOArc

/-!
# Cutting a painted surface along a curve off the paint

Let `F` be an `O`-arc off `U(Γ)`. We cut along `F` with `cutOArc` and paste discs on the new cuffs
(`cap_lifts`). Each part then carries the cells on
its side (`side_cut`). This is the case of `CutNormalOArcPaintingStatement` where `F` meets no node
(`cut_off_paint`). The count of the surfaces is
in `side_tri`: a part after capping is simpler than the surface, unless the other part is a closed
disc.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface

variable {Y S : Type} [TopologicalSpace Y] [TopologicalSpace S]

/-- The number of cuffs falls and the rest of the model stays. -/
def CapDrops (W W' : Type) [TopologicalSpace W] [TopologicalSpace W'] : Prop :=
  ∀ a b c : ℕ, Nonempty (W ≃ₜ SurfaceModel a b c) → ∃ c' < c, Nonempty (W' ≃ₜ SurfaceModel a b c')

theorem isOArc_preimage {W : Set Y} {X : Set Y} (hO : IsOArc X) (hs : X ⊆ W) : IsOArc
  (Subtype.val ⁻¹' X : Set W) := by
  obtain ⟨φ⟩ := hO
  have he : Subtype.val '' (Subtype.val ⁻¹' X : Set W) = X := by
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hs]
  exact ⟨(φ.trans (Homeomorph.setCongr he.symm)).trans (IsEmbedding.subtypeVal.homeomorphImage
    _).symm⟩

theorem oarc_cuff (hY : IsSurface Y) {X : Set Y} (hO : IsOArc X) (hb : X ⊆ bd Y) : X ∈ cuffs Y := by
  have ht2 : T2Space Y := hY.2.1
  obtain ⟨φ⟩ := id hO
  have hx : (φ 1).1 ∈ X := (φ 1).2
  have hc : connectedComponentIn (bd Y) (φ 1).1 ∈ cuffs Y := ⟨_, hb hx, rfl⟩
  obtain ⟨φ'⟩ := (cuff_statement.{0} Y hY).2.2 _ hc
  have h1 := oarc_eq φ' hO (hO.isPreconnected.subset_connectedComponentIn hx hb)
  exact h1 ▸ hc

/-- Capping one cuff. -/
theorem cap_one [ConnectedSpace Y] (hY : IsSurface Y) {C : Set Y} (hC : C ∈ cuffs Y) :
    ∃ (W : Type) (_ : TopologicalSpace W) (j : Y → W), IsSurface W ∧ ConnectedSpace W
      ∧ IsClosedEmbedding j ∧ bd W = j '' (bd Y \ C) ∧ CapDrops Y W := by
  obtain ⟨W, tW, j, Δ, hW, hj, hΔ, hcov, hmeet, hΔb, hbd⟩ := paste_disc.{0} Y C hY hC
  obtain ⟨a, b, c, ⟨e⟩⟩ := classification.{0} Y hY ‹_›
  obtain ⟨-, ⟨e'⟩⟩ := paste_model hY hC hW hj hΔ hcov hmeet hΔb e
  have hconn : ConnectedSpace W := by
    have := (isSurface_model a b (c - 1)).2
    exact e'.symm.surjective.connectedSpace e'.symm.continuous
  refine ⟨W, tW, j, hW, hconn, hj, hbd, fun a' b' c' he => ?_⟩
  obtain ⟨e2⟩ := he
  obtain ⟨h0, ⟨e3⟩⟩ := paste_model hY hC hW hj hΔ hcov hmeet hΔb e2
  exact ⟨c' - 1, by omega, ⟨e3⟩⟩

theorem image_cuff (_hY : IsSurface Y) {C : Set Y} (_hC : C ∈ cuffs Y) {W : Type} [TopologicalSpace
  W] {j : Y → W} (hj : IsClosedEmbedding j) (hbd : bd W = j '' (bd Y \ C))
    {C' : Set Y} (hC' : C' ∈ cuffs Y) (hd : Disjoint C C') (hO : IsOArc C')
      (hW : IsSurface W) : j '' C' ∈ cuffs W := by
  have hO' : IsOArc (j '' C') := by
    obtain ⟨φ⟩ := hO
    exact ⟨φ.trans (hj.isEmbedding.homeomorphImage _)⟩
  refine oarc_cuff hW hO' ?_
  rw [hbd]
  refine image_mono fun x hx => ⟨?_, fun h => disjoint_left.mp hd h hx⟩
  obtain ⟨y, -, rfl⟩ := hC'
  exact connectedComponentIn_subset _ _ hx

/-- Capping the cuffs in `B`, which are one `O`-arc or two disjoint ones. -/
theorem cap_lifts [ConnectedSpace Y] (hY : IsSurface Y) {B : Set Y} (hb : B ⊆ bd Y) (hB : IsOArc B
  ∨ ∃ P P', Disjoint P P' ∧ P ∪ P' = B ∧ IsOArc P ∧ IsOArc P') :
    ∃ (W : Type) (_ : TopologicalSpace W) (j : Y → W), IsSurface W ∧ ConnectedSpace W
      ∧ IsClosedEmbedding j ∧ bd W = j '' (bd Y \ B) ∧ CapDrops Y W := by
  rcases hB with hB | ⟨P, P', hd, rfl, hP, hP'⟩
  · exact cap_one hY (oarc_cuff hY hB hb)
  · have hC := oarc_cuff hY hP fun x hx => hb (.inl hx)
    have hC' := oarc_cuff hY hP' fun x hx => hb (.inr hx)
    obtain ⟨W, tW, j, hW, hc, hj, hbd, hdrop⟩ := cap_one hY hC
    obtain ⟨W', tW', j', hW', hc', hj', hbd', hdrop'⟩ := cap_one hW (image_cuff hY hC hj hbd hC' hd
      hP' hW)
    refine ⟨W', tW', j' ∘ j, hW', hc', hj'.comp hj, ?_, fun a b c he => ?_⟩
    · rw [hbd', hbd, image_comp, ← image_sdiff hj.injective, sdiff_sdiff]
    · obtain ⟨c₁, h1, he1⟩ := hdrop a b c he
      obtain ⟨c₂, h2, he2⟩ := hdrop' a b c₁ he1
      exact ⟨c₂, h2.trans h1, he2⟩

variable [CompactSpace S] [T2Space S]

/-- One side of the cut, after capping, carries the cells on that side. -/
theorem side_cut [CompactSpace Y] (hS : IsSurface S) {Γ : Painting S} {ψ : Y
  → S} {F : Set S} (hd : Disjoint F Γ.U) (hmap : CutMap ψ F) {W : Type}
    [TopologicalSpace W] [T2Space W] {j : Y → W} (hj : IsClosedEmbedding j)
      (hbd : bd W = j '' (bd Y \ ψ ⁻¹' F)) {L : Set Y} {u v : Y}
    (hL : IsLineWithEnds L u v) (hLF : L ⊆ ψ ⁻¹' F) (hne : (keepCells Γ ψ F).Nonempty) : ∃ (ι : S
      → W) (Γ' : Painting W), IsCutSidePainting S Γ ∅ (keepCells Γ ψ F) W ι Γ' := by
  classical
  have hneY : Nonempty Y := ⟨u⟩
  obtain ⟨σ, hσc, hσ₁, hσ₂⟩ := hmap.exists_sec
  let R : Set S := range ψ \ F
  obtain ⟨a, ha, hr, rfl, rfl⟩ := hL.exists_arc
  have harc : IsArcMap (j ∘ a) := ⟨hj.continuous.comp ha.1, hj.injective.comp ha.2⟩
  obtain ⟨g, hg, hgm⟩ := exists_inj_line hS harc.isLineWithEnds
  let ι : S → W := fun x => if x ∈ R then j (σ x) else g x
  have hιR : ∀ x ∈ R, ι x = j (σ x) := fun x hx => ite_eq_left hx
  have hιn : ∀ x, x ∉ R → ι x = g x := fun x hx => ite_eq_right hx
  have hgB : ∀ x, ∃ y, g x = j y ∧ ψ y ∈ F := fun x => by
    obtain ⟨t, ht⟩ := (hgm x).1
    exact ⟨a t, ht.symm, hLF (hr ▸ mem_range_self t)⟩
  have hσF : ∀ x ∈ R, ψ (σ x) ∉ F := fun x hx => by
    rw [hσ₁ x hx]
    exact hx.2
  have hcross : ∀ x x', x ∈ R → ι x ≠ g x' := fun x x' hx he => by
    obtain ⟨y, hy, hyF⟩ := hgB x'
    rw [hιR x hx, hy] at he
    exact hσF x hx (hj.injective he ▸ hyF)
  have hinj : Function.Injective ι := by
    intro x x' he
    by_cases hx : x ∈ R <;> by_cases hx' : x' ∈ R
    · rw [hιR x hx, hιR x' hx'] at he
      rw [← hσ₁ x hx, hj.injective he, hσ₁ x' hx']
    · exact absurd (he.trans (hιn x' hx')) (hcross x x' hx)
    · exact absurd (he.symm.trans (hιn x hx)) (hcross x' x hx')
    · rw [hιn x hx, hιn x' hx'] at he
      exact hg he
  have hrc : IsClosed (range ψ) := (isCompact_range hmap.cont).isClosed
  let A : Set S := Γ.U ∩ range ψ
  have hAR : A ⊆ R := fun x hx => ⟨hx.2, fun h => disjoint_left.mp hd h hx.1⟩
  have hconn : ∀ D : Set S, IsPreconnected D → D ⊆ Γ.U → (D ∩ A).Nonempty → D ⊆ A := by
    intro D hD hDU ⟨x, hxD, hxA⟩
    have hsub : D ⊆ R ∪ (range ψ)ᶜ := fun y hy => by
      by_cases hr : y ∈ range ψ
      · exact .inl (hAR ⟨hDU hy, hr⟩)
      · exact .inr hr
    have h1 := hD.subset_left_of_subset_union hmap.isOpen hrc.isOpen_compl
      (disjoint_left.mpr fun x hx hx' => hx' hx.1) hsub ⟨x, hxD, hAR hxA⟩
    exact fun y hy => ⟨hDU hy, (h1 hy).1⟩
  have hcont : ContinuousOn ι A := by
    refine ContinuousOn.congr (f := j ∘ σ) (hj.continuous.comp_continuousOn
      (hσc.mono hAR)) fun x hx => hιR x (hAR hx)
  have hbdR : ∀ x ∈ R, σ x ∈ bd Y ↔ x ∈ bd S := fun x hx => by
    rw [hmap.mem_bd_iff (hσF x hx), hσ₁ x hx]
  have hb : bd W ⊆ ι '' A := by
    rw [hbd]
    rintro _ ⟨w, ⟨hw, hwF⟩, rfl⟩
    have hR : ψ w ∈ R := ⟨⟨w, rfl⟩, hwF⟩
    refine ⟨ψ w, ⟨Γ.bd_subset ((hmap.mem_bd_iff hwF).mp hw), w, rfl⟩, ?_⟩
    rw [hιR _ hR, hσ₂ w hwF]
  have hbd' : ∀ x ∈ A, ι x ∈ bd W ↔ x ∈ bd S := fun x hx => by
    have hR := hAR hx
    rw [hιR x hR, hbd, hj.injective.mem_set_image]
    constructor
    · exact fun h => (hbdR x hR).mp h.1
    · exact fun h => ⟨(hbdR x hR).mpr h, hσF x hR⟩
  have hset : {c ∈ Γ.C | c ⊆ A} = keepCells Γ ψ F := by
    ext c
    constructor
    · rintro ⟨hc, hs⟩
      exact ⟨hc, hs.trans hAR⟩
    · rintro ⟨hc, hs⟩
      exact ⟨hc, fun x hx => ⟨(arcComponentsIn_subset hc hx).1, (hs hx).1⟩⟩
  have hneA : ∃ c ∈ Γ.C, c ⊆ A := by
    obtain ⟨c, hc⟩ := hset.symm ▸ hne
    exact ⟨c, hc.1, hc.2⟩
  obtain ⟨Γ', hp⟩ := cutSide_of_part hS (Γ.isClosed_U.inter hrc) inter_subset_left hconn hinj hcont
    hb hbd' hneA
  exact ⟨ι, Γ', hset ▸ hp⟩

omit [CompactSpace S] in
/-- A side of a cut that is a closed disc gives a disc in the surface, with boundary the curve. -/
theorem side_disc_image {ψ : Y → S} {F : Set S} {W : Set Y} {Γ : Painting S} [CompactSpace Y]
  (_hS : IsSurface S) (hmap : CutMap (ψ ∘ (Subtype.val : W → Y)) F)
    (hO : IsOArc F) (hnorm : Γ.IsNormal F) (hW : IsClosed W) (hinj : InjOn ψ W)
      (hsurj : F ⊆ ψ '' W) (e : W ≃ₜ ClosedUnitDisc) :
    IsClosedDisc (range (ψ ∘ (Subtype.val : W → Y))) ∧ discBd (range (ψ ∘ (Subtype.val : W → Y)))
      = F ∧
      {c ∈ Γ.C | c ⊆ range (ψ ∘ (Subtype.val : W → Y))} = keepCells Γ (ψ ∘ (Subtype.val : W → Y)) F
        := by
  have hcomp : CompactSpace W := isCompact_iff_compactSpace.mp hW.isCompact
  have hi : Function.Injective (ψ ∘ (Subtype.val : W → Y)) := fun y y' he => Subtype.ext
    (hinj y.2 y'.2 he)
  have hE : IsEmbedding (ψ ∘ (Subtype.val : W → Y)) := (hmap.cont.isClosedEmbedding hi).isEmbedding
  let E : W ≃ₜ range (ψ ∘ (Subtype.val : W → Y)) := hE.toHomeomorph
  have hD : IsClosedDisc (range (ψ ∘ (Subtype.val : W → Y))) := ⟨e.symm.trans E⟩
  have hbd : discBd (range (ψ ∘ (Subtype.val : W → Y))) = (ψ ∘ Subtype.val) '' bd W := by
    rw [discBd, ← image_bd_homeomorph E, image_image]
    rfl
  refine ⟨hD, ?_, ?_⟩
  · have hs : F ⊆ discBd (range (ψ ∘ (Subtype.val : W → Y))) := by
      rw [hbd]
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hsurj hx
      exact ⟨⟨y, hy⟩, hmap.bdF hx, rfl⟩
    obtain ⟨φ⟩ := hD.isOArc_discBd
    exact (oarc_eq φ hO hs).symm
  · ext c
    constructor
    · rintro ⟨hc, hs⟩
      exact ⟨hc, fun x hx => ⟨hs hx, fun hxF => (arcComponentsIn_subset hc hx).2 (hnorm ⟨hxF,
        (arcComponentsIn_subset hc hx).1⟩)⟩⟩
    · rintro ⟨hc, hs⟩
      exact ⟨hc, fun x hx => (hs hx).1⟩

theorem cuffs_model {X : Type} [TopologicalSpace X] {a b c : ℕ} (e : X ≃ₜ SurfaceModel a b c) :
  (cuffs X).ncard = c := by
  obtain ⟨ht, f, hf⟩ := presents_ew a b c
  have := ht
  rw [ncard_cuffs_congr e]
  exact ncard_cuffs hf

omit [CompactSpace S] [T2Space S] in
/-- After capping, a part of the surface cut along an `O`-arc is simpler than the surface, unless
the other part is a closed disc. -/
theorem side_tri [ConnectedSpace S] (hS : IsSurface S) {W W' : Set Y} {X : Set Y} (hhne : W ≠ W')
  (hsc : spaceComponents Y = {W, W'}) (hX : (X ∩ W).Nonempty) (_hXb : IsOArc X) (hXbd : X ⊆ bd Y)
    (hYs : IsSurface Y) (hW : IsClopen W) (hWc : ConnectedSpace W)
    (hcase : CutIsSimpler Y S ∨ CutHasCopy Y S ClosedCylinder ∨ CutHasDisc Y)
    (hpaste : Nonempty (W' ≃ₜ ClosedUnitDisc) → ∀ a b c, Nonempty (W ≃ₜ SurfaceModel a b c) → 0 < c
      ∧ Nonempty (S ≃ₜ SurfaceModel a b (c - 1))) :
    Nonempty (W ≃ₜ ClosedUnitDisc) ∨ ∀ (V : Type) [TopologicalSpace V], CapDrops W' V
      → IsSimplerThan V S := by
  obtain ⟨ds⟩ := nonempty_disc_homeo
  obtain ⟨a', b', c', ⟨eS⟩⟩ := classification.{0} S hS ‹_›
  have hdrop_simple : ∀ (V : Type) [TopologicalSpace V], CapDrops W' V → IsSimplerThan W' S
    → IsSimplerThan V S := by
    rintro V _ hV ⟨a, b, c, a₁, b₁, c₁, h1, h2, h3, h4, h5⟩
    obtain ⟨c₂, h6, h7⟩ := hV a b c h1
    exact ⟨a, b, c₂, a₁, b₁, c₁, h7, h2, h3, h4, by omega⟩
  rcases hcase with ⟨-, h⟩ | ⟨C₁, C₂, hne, he, ⟨e₁⟩, ⟨e₂⟩⟩ | ⟨C₁, C₂, hne, he, hdisc⟩
  · exact .inr fun V _ hV => hdrop_simple V hV (h W' (hsc ▸ mem_insert_of_mem _ rfl))
  · rcases Set.pair_eq_pair_iff.mp (he.symm.trans hsc) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine .inr fun V _ hV => ?_
      obtain ⟨c₂, h6, h7⟩ := hV a' b' c' ⟨e₂.trans eS⟩
      exact ⟨a', b', c₂, a', b', c', h7, ⟨eS⟩, le_rfl, le_rfl, by omega⟩
    · by_cases hd : Nonempty (S ≃ₜ ClosedUnitDisc)
      · obtain ⟨d⟩ := hd
        exact .inl ⟨e₂.trans d⟩
      · refine .inr fun V _ hV => ?_
        obtain ⟨cy⟩ := nonempty_cyl_homeo
        obtain ⟨c₂, h6, h7⟩ := hV 0 0 2 ⟨e₁.trans cy.symm⟩
        have hc0 : c' ≠ 0 := by
          rintro rfl
          obtain ⟨y, hy, hyW⟩ := hX
          have hyb : (⟨y, hyW⟩ : C₂) ∈ bd C₂ := (mem_bd_sub hW.2).mpr (hXbd hy)
          have h2 := cuffs_model (e₂.trans eS)
          have h3 := (Set.ncard_pos (cuff_statement.{0} C₂ (isSurface_sub hYs hW)).2.1).mpr ⟨_, ⟨y,
            hyW⟩, hyb, rfl⟩
          omega
        have h1 : ¬ (a' = 0 ∧ b' = 0 ∧ c' = 1) := by
          rintro ⟨rfl, rfl, rfl⟩
          exact hd ⟨eS.trans ds⟩
        exact ⟨0, 0, c₂, a', b', c', h7, ⟨eS⟩, by omega, by omega, by omega⟩
  · rcases Set.pair_eq_pair_iff.mp (he.symm.trans hsc) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨d⟩ := hdisc
      exact .inl ⟨d.symm⟩
    · obtain ⟨d⟩ := hdisc
      by_cases h0 : a' = 0 ∧ b' = 0 ∧ c' = 0
      · obtain ⟨rfl, rfl, rfl⟩ := h0
        obtain ⟨a, b, c, ⟨e⟩⟩ := classification.{0} C₂ (isSurface_sub hYs hW) hWc
        obtain ⟨h1, ⟨e3⟩⟩ := hpaste ⟨d.symm⟩ a b c ⟨e⟩
        obtain ⟨h4, h5, -⟩ := modelCriterion.2 a b (c - 1) 0 0 0 |>.mp ⟨e3.symm.trans eS⟩
        have ha : a = 0 := by omega
        have hb : b = 0 := by omega
        have hc : c = 1 := by omega
        subst ha hb hc
        exact .inl ⟨e.trans ds⟩
      · refine .inr fun V _ hV => ?_
        obtain ⟨c₂, h6, h7⟩ := hV 0 0 1 ⟨d.symm.trans ds.symm⟩
        have h8 : c₂ = 0 := by omega
        subst h8
        exact ⟨0, 0, 0, a', b', c', h7, ⟨eS⟩, by omega, by omega, by omega⟩

/-- The conclusion of `CutNormalOArcPaintingStatement`. -/
def OArcConclusion (S : Type) [TopologicalSpace S] (Γ : Painting S) (F : Set S) : Prop :=
  (Γ.C.Nonempty ∧
      ∃ (S₀ : Type) (_ : TopologicalSpace S₀) (_ : CompactSpace S₀) (_ : T2Space S₀)
        (_ : ConnectedSpace S₀) (ι₀ : S → S₀) (Γ₀ : Painting S₀),
      IsSurface S₀ ∧ IsSimplerThan S₀ S ∧
      IsCutSidePainting S Γ ∅ Γ.C S₀ ι₀ Γ₀) ∨
    (∃ I₁ I₂ : Set (Set S),
      I₁ ⊆ Γ.C ∧ I₂ = Γ.C \ I₁ ∧
      (∀ c₁ ∈ I₁, ∀ c₂ ∈ I₂, tilde c₁ ∩ tilde c₂ = ∅) ∧
      ((∃ Δ : Set S, IsClosedDisc Δ ∧ discBd Δ = F ∧ {c ∈ Γ.C | c ⊆ Δ} = I₁) ∨
       (I₂.Nonempty →
         ∃ (S' : Type) (_ : TopologicalSpace S') (_ : CompactSpace S') (_ : T2Space S')
            (_ : ConnectedSpace S') (ι : S → S') (Γ' : Painting S'),
          IsSurface S' ∧ IsSimplerThan S' S ∧
          IsCutSidePainting S Γ ∅ I₂ S' ι Γ')) ∧
      ((∃ Δ : Set S, IsClosedDisc Δ ∧ discBd Δ = F ∧ {c ∈ Γ.C | c ⊆ Δ} = I₂) ∨
       (I₁.Nonempty →
         ∃ (S' : Type) (_ : TopologicalSpace S') (_ : CompactSpace S') (_ : T2Space S')
            (_ : ConnectedSpace S') (ι : S → S') (Γ' : Painting S'),
          IsSurface S' ∧ IsSimplerThan S' S ∧
          IsCutSidePainting S Γ ∅ I₁ S' ι Γ')))

/-- A side of the cut, capped, with its painting. -/
theorem side_package [CompactSpace Y] (hS : IsSurface S) {Γ : Painting S} {ψ : Y
  → S} {F : Set S} (hd : Disjoint F Γ.U) (hψ : IsCutting ψ F) (hY : IsSurface Y)
    (hFc : IsClosed F) {W : Set Y} (hW : IsClopen W) (hc : ConnectedSpace W)
    (hB : IsOArc ((ψ ∘ (Subtype.val : W → Y)) ⁻¹' F) ∨ ∃ P P', Disjoint P P' ∧ P ∪ P' = (ψ ∘
      (Subtype.val : W → Y)) ⁻¹' F ∧ IsOArc P ∧ IsOArc P') :
    ∃ (V : Type) (_ : TopologicalSpace V) (_ : CompactSpace V) (_ : T2Space V)
      (_ : ConnectedSpace V), IsSurface V ∧ CapDrops W V ∧
      ((keepCells Γ (ψ ∘ (Subtype.val : W → Y)) F).Nonempty → ∃ (ι : S → V)
        (Γ' : Painting V),
          IsCutSidePainting S Γ ∅ (keepCells Γ (ψ ∘ (Subtype.val : W → Y)) F) V ι Γ') := by
  have hmap := cutMap_sub hψ hFc hW
  have hsurf := isSurface_sub hY hW
  have hcW : CompactSpace W := hsurf.1
  have ht2W : T2Space W := hsurf.2.1
  obtain ⟨V, tV, j, hV, hcV, hj, hbd, hdrop⟩ := cap_lifts hsurf hmap.bdF hB
  have hP : ∃ P, IsOArc P ∧ P ⊆ (ψ ∘ (Subtype.val : W → Y)) ⁻¹' F := by
    rcases hB with h | ⟨P, P', -, hu, h, -⟩
    · exact ⟨_, h, subset_rfl⟩
    · exact ⟨P, h, hu ▸ subset_union_left⟩
  obtain ⟨P, hO, hs⟩ := hP
  obtain ⟨φ⟩ := id hO
  have hne : (φ 1).1 ≠ (φ (Circle.exp Real.pi)).1 := fun h => by
    have h5 := congrArg (fun z : Circle => (z : ℂ)) (φ.injective (Subtype.ext h))
    norm_num at h5
  obtain ⟨A, B, hA, -, hu, -⟩ := hO.lines (φ 1).2 (φ (Circle.exp Real.pi)).2 hne
  have hcV' : CompactSpace V := hV.1
  have ht2V : T2Space V := hV.2.1
  exact ⟨V, tV, hcV', ht2V, hcV, hV, hdrop, fun hne => side_cut hS hd hmap hj hbd hA (fun z hz
    => hs (hu.subset (.inl hz))) hne⟩

omit [CompactSpace S] in
/-- Pasting back a side that is a closed disc gives the surface. -/
theorem paste_side (hS : IsSurface S) {ψ : Y
  → S} {F : Set S} (hψ : IsCutting ψ F) (hY : IsSurface Y) {W W' X : Set Y} (hW : IsClopen W)
    (hu : W ∪ W' = univ) (hdW : Disjoint W W') (hXW : X ⊆ W) (hXb : IsOArc X) (hXe : BijOn ψ X F)
      (hbX : X ⊆ bd Y) (hinj : InjOn ψ W) {Δ : Set S} (hΔ : IsClosedDisc Δ)
    (hrΔ : Δ = ψ '' W') (hdΔ : discBd Δ = F) {a b c : ℕ} (e : W ≃ₜ SurfaceModel a b c) : 0 < c
      ∧ Nonempty (S ≃ₜ SurfaceModel a b (c - 1)) := by
  have hsurf := isSurface_sub hY hW
  have hcW : CompactSpace W := hsurf.1
  have hι : IsClosedEmbedding (ψ ∘ (Subtype.val : W → Y)) :=
    (hψ.1.comp continuous_subtype_val).isClosedEmbedding fun y y' he => Subtype.ext
      (hinj y.2 y'.2 he)
  have hC : IsCuff (Subtype.val ⁻¹' X : Set W) := oarc_cuff hsurf (isOArc_preimage hXb hXW) fun y
    hy => (mem_bd_sub hW.2).mpr (hbX hy)
  have him : (ψ ∘ (Subtype.val : W → Y)) '' (Subtype.val ⁻¹' X : Set W) = F := by
    rw [image_comp, Subtype.image_preimage_coe, inter_eq_right.mpr hXW, hXe.image_eq]
  have hFΔ : F ⊆ Δ := hdΔ ▸ discBd_subset Δ
  refine paste_model hsurf hC hS hι hΔ ?_ ?_ (by rw [him, hdΔ]) e
  · rw [eq_univ_iff_forall]
    intro x
    obtain ⟨y, rfl⟩ := hψ.2.1 x
    rcases (hu ▸ mem_univ y : y ∈ W ∪ W') with h | h
    · exact .inl ⟨⟨y, h⟩, rfl⟩
    · exact .inr (hrΔ ▸ mem_image_of_mem _ h)
  · rw [him]
    apply subset_antisymm
    · rintro _ ⟨⟨y, rfl⟩, h⟩
      rw [hrΔ] at h
      obtain ⟨y', hy', he⟩ := h
      by_contra hn
      have hyF : y' ∈ ψ ⁻¹' Fᶜ := by rwa [mem_preimage, he]
      have h1 : y' = y.1 := hψ.2.2.1 hyF hn he
      exact disjoint_left.mp hdW y.2 (h1 ▸ hy')
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := hXe.surjOn hx
      exact ⟨⟨⟨y, hXW hy⟩, rfl⟩, hFΔ hx⟩

/-- The case where the cut surface is connected. -/
theorem connected_case [CompactSpace Y]
    (hS : IsSurface S) {Γ : Painting S} {ψ : Y → S} {F : Set S}
    (hd : Disjoint F Γ.U) (hψ : IsCutting ψ F) (hY : IsSurface Y)
    (hFc : IsClosed F) (hYc : ConnectedSpace Y) (hcase : CutIsSimpler Y S
      ∨ CutHasCopy Y S ClosedCylinder ∨ CutHasDisc Y)
    (hB : IsOArc (ψ ⁻¹' F) ∨ ∃ P P', Disjoint P P' ∧ P ∪ P' = ψ ⁻¹' F ∧ IsOArc P ∧ IsOArc P')
      (hne : Γ.C.Nonempty) : OArcConclusion S Γ F := by
  have hone : ∀ C ∈ spaceComponents Y, C = univ := fun C hC => by
    rw [spaceComponents_eq] at hC
    obtain ⟨y, rfl⟩ := hC
    exact PreconnectedSpace.connectedComponent_eq_univ y
  obtain ⟨y₀⟩ : Nonempty Y := inferInstance
  have hunivc : univ ∈ spaceComponents Y := by
    rw [spaceComponents_eq]
    exact ⟨y₀, PreconnectedSpace.connectedComponent_eq_univ y₀⟩
  have hsimp : IsSimplerThan (univ : Set Y) S := by
    rcases hcase with h | ⟨C₁, C₂, hneC, heq, -, -⟩ | ⟨C₁, C₂, hneC, heq, -⟩
    · exact h.2 univ hunivc
    · exact absurd ((hone C₁ (heq ▸ mem_insert _ _)).trans (hone C₂ (heq ▸ mem_insert_of_mem _
      rfl)).symm) hneC
    · exact absurd ((hone C₁ (heq ▸ mem_insert _ _)).trans (hone C₂ (heq ▸ mem_insert_of_mem _
      rfl)).symm) hneC
  have hcu : ConnectedSpace ↥(univ : Set Y) := (Homeomorph.Set.univ
    Y).symm.surjective.connectedSpace (Homeomorph.Set.univ Y).symm.continuous
  have hB' : IsOArc ((ψ ∘ (Subtype.val : ↥(univ : Set Y) → Y)) ⁻¹' F) ∨ ∃ P P', Disjoint P P'
    ∧ P ∪ P' = (ψ ∘ (Subtype.val : ↥(univ : Set Y) → Y)) ⁻¹' F ∧ IsOArc P ∧ IsOArc P' := by
    rcases hB with h | ⟨P, P', hdj, hu, h1, h2⟩
    · exact .inl (isOArc_preimage h (subset_univ _))
    · refine .inr ⟨_, _, hdj.preimage Subtype.val, ?_, isOArc_preimage h1 (subset_univ _),
        isOArc_preimage h2 (subset_univ _)⟩
      rw [← preimage_union, hu, preimage_comp]
  obtain ⟨V, tV, hcV, ht2V, hconnV, hV, hdrop, hp⟩ := side_package hS hd hψ hY hFc isClopen_univ
    hcu hB'
  have hkeep : keepCells Γ (ψ ∘ (Subtype.val : ↥(univ : Set Y) → Y)) F = Γ.C := by
    ext c
    constructor
    · exact fun h => h.1
    · refine fun hc => ⟨hc, fun x hx => ⟨?_, fun hxF => disjoint_left.mp hd hxF
      (arcComponentsIn_subset hc hx).1⟩⟩
      obtain ⟨y, rfl⟩ := hψ.2.1 x
      exact ⟨⟨y, mem_univ _⟩, rfl⟩
  obtain ⟨ι, Γ', hpp⟩ := hp (hkeep ▸ hne)
  rw [hkeep] at hpp
  obtain ⟨a, b, c, a₁, b₁, c₁, h1, h2, h3, h4, h5⟩ := hsimp
  obtain ⟨c₂, h6, h7⟩ := hdrop a b c h1
  exact .inl ⟨hne, V, tV, hcV, ht2V, hconnV, ι, Γ', hV, ⟨a, b, c₂, a₁, b₁, c₁, h7, h2, h3, h4,
    by omega⟩, hpp⟩

/-- The case of `CutNormalOArcPaintingStatement` of a curve off the paint. -/
theorem cut_off_paint [ConnectedSpace S] (hS : IsSurface S) {Γ : Painting S} {F : Set S}
  (hO : IsOArc F) (hd : Disjoint F Γ.U) : OArcConclusion S Γ F := by
  have hdb : Disjoint F (bd S) := hd.mono_right Γ.bd_subset
  have hFc : IsClosed F := by
    obtain ⟨φ⟩ := id hO
    have hc : IsCompact F := by
      rw [isCompact_iff_compactSpace]
      exact φ.compactSpace
    exact hc.isClosed
  by_cases hne : Γ.C.Nonempty
  swap
  · have hC : Γ.C = ∅ := not_nonempty_iff_eq_empty.mp hne
    refine .inr ⟨∅, ∅, empty_subset _, by rw [hC, empty_sdiff], by simp,
      .inr fun h => absurd h (by simp), .inr fun h => absurd h (by simp)⟩
  obtain ⟨Y, tY, ψ, hY, hψ, hcase, hlift⟩ := cutOArc.{0} S F hS ‹_› hO hdb
  have ht2Y : T2Space Y := hY.2.1
  have hcY : CompactSpace Y := hY.1
  rcases hlift with ⟨X, X', hdX, hun, hOX, hOX', bX, bX'⟩ | hQ
  swap
  · obtain ⟨φ⟩ := id hQ
    have hp := hQ.isPreconnected
    rcases cut_comps hψ hY hp hp (union_self _) (φ 1).2 (φ 1).2 with hYc | ⟨W₁, W₂, -, -, h1, h2,
      -, -, -, hdW, -, -⟩
    · exact connected_case hS hd hψ hY hFc hYc hcase (.inl hQ) hne
    · exact absurd (h2 (φ 1).2) (disjoint_left.mp hdW (h1 (φ 1).2))
  obtain ⟨φ⟩ := id hOX
  obtain ⟨φ'⟩ := id hOX'
  rcases cut_comps hψ hY hOX.isPreconnected hOX'.isPreconnected hun (φ 1).2
    (φ' 1).2 with hYc | ⟨W₁, W₂, hne', hsc, hX₁, hX₂, hW₁, hW₂, hU, hdW, hc₁, hc₂⟩
  · exact connected_case hS hd hψ hY hFc hYc hcase (.inr ⟨X, X', hdX, hun, hOX, hOX'⟩) hne
  have hfib : ∀ {W₀ X₀ X₁ : Set Y}, Disjoint W₀ X₁ → X₀ ∪ X₁ = ψ ⁻¹' F → X₀ ⊆ W₀ → (ψ ∘
    (Subtype.val : W₀ → Y)) ⁻¹' F = Subtype.val ⁻¹' X₀ := by
    intro W₀ X₀ X₁ hd1 hu hs
    ext y
    change ψ y.1 ∈ F ↔ y.1 ∈ X₀
    constructor
    · intro h
      rcases (hu.symm.subset h : y.1 ∈ X₀ ∪ X₁) with h1 | h1
      · exact h1
      · exact absurd h1 (disjoint_left.mp hd1 y.2)
    · intro h
      exact hu.subset (Or.inl h)
  have hd₁ : Disjoint W₁ X' := hdW.mono_right hX₂
  have hd₂ : Disjoint W₂ X := hdW.symm.mono_right hX₁
  have hun' : X' ∪ X = ψ ⁻¹' F := by rw [union_comm]; exact hun
  have hB₁ := hfib hd₁ hun hX₁
  have hB₂ := hfib hd₂ hun' hX₂
  obtain ⟨V₁, tV₁, cV₁, tV₁', hV₁c, hV₁, hdrop₁, hp₁⟩ := side_package hS hd hψ hY hFc hW₁ hc₁ (.inl
    (hB₁ ▸ isOArc_preimage hOX hX₁))
  obtain ⟨V₂, tV₂, cV₂, tV₂', hV₂c, hV₂, hdrop₂, hp₂⟩ := side_package hS hd hψ hY hFc hW₂ hc₂ (.inl
    (hB₂ ▸ isOArc_preimage hOX' hX₂))
  have hm₁ := cutMap_sub hψ hFc hW₁
  have hm₂ := cutMap_sub hψ hFc hW₂
  let I₁ := keepCells Γ (ψ ∘ (Subtype.val : W₁ → Y)) F
  let I₂ := keepCells Γ (ψ ∘ (Subtype.val : W₂ → Y)) F
  let P₁ := range (ψ ∘ (Subtype.val : W₁ → Y)) \ F
  let P₂ := range (ψ ∘ (Subtype.val : W₂ → Y)) \ F
  have hPd : Disjoint P₁ P₂ := by
    rw [disjoint_left]
    rintro _ ⟨⟨y, rfl⟩, h1⟩ ⟨⟨y', he⟩, -⟩
    have he' : ψ y'.1 = ψ y.1 := he
    have hy'F : y'.1 ∈ ψ ⁻¹' Fᶜ := by rwa [mem_preimage, he']
    have h2 : y'.1 = y.1 := hψ.2.2.1 hy'F h1 he'
    exact disjoint_left.mp hdW y.2 (h2 ▸ y'.2)
  have hPc : Fᶜ ⊆ P₁ ∪ P₂ := fun x hx => by
    obtain ⟨y, rfl⟩ := hψ.2.1 x
    rcases (hU ▸ mem_univ y : y ∈ W₁ ∪ W₂) with h | h
    · exact .inl ⟨⟨⟨y, h⟩, rfl⟩, hx⟩
    · exact .inr ⟨⟨⟨y, h⟩, rfl⟩, hx⟩
  have hside : ∀ c ∈ Γ.C, c ⊆ P₁ ∨ c ⊆ P₂ := fun c hc => by
    have hs : c ⊆ Fᶜ := fun x hx hxF => disjoint_left.mp hd hxF (arcComponentsIn_subset hc hx).1
    exact (arcComponentsIn_isPathConnected hc).isConnected.isPreconnected.subset_or_subset
      hm₁.isOpen hm₂.isOpen hPd (hs.trans hPc)
  have hI₂ : I₂ = Γ.C \ I₁ := by
    ext c
    constructor
    · rintro ⟨hc, hs⟩
      refine ⟨hc, fun h => ?_⟩
      obtain ⟨x, hx⟩ := arcComponentsIn_nonempty hc
      exact disjoint_left.mp hPd (h.2 hx) (hs hx)
    · rintro ⟨hc, hn⟩
      exact ⟨hc, (hside c hc).resolve_left fun h => hn ⟨hc, h⟩⟩
  have hcl : ∀ {W₀ : Set Y}, IsClopen W₀ → ∀ c ∈ keepCells Γ (ψ ∘ (Subtype.val : W₀
    → Y)) F, closure c ⊆ range (ψ ∘ (Subtype.val : W₀ → Y)) \ F := by
    intro W₀ hW₀ c hc
    have hcW : CompactSpace W₀ := (isSurface_sub hY hW₀).1
    have hrc : IsClosed (range (ψ ∘ (Subtype.val : W₀ → Y))) := (isCompact_range
      (hψ.1.comp continuous_subtype_val)).isClosed
    refine fun x hx => ⟨closure_minimal (fun z hz => (hc.2 hz).1) hrc hx,
      fun hxF => disjoint_left.mp hd hxF ?_⟩
    exact closure_minimal (fun z hz => (arcComponentsIn_subset hc.1 hz).1) Γ.isClosed_U hx
  have hinj₁ : InjOn ψ W₁ := by
    intro y hy y' hy' he
    by_cases hF : ψ y ∈ F
    · have h1 : y ∈ X := by
        have := (hfib hd₁ hun hX₁).subset (show (⟨y, hy⟩ : W₁) ∈ _ from hF)
        exact this
      have h2 : y' ∈ X := by
        have hy'F : ψ y' ∈ F := he ▸ hF
        exact (hfib hd₁ hun hX₁).subset
          (show (⟨y', hy'⟩ : W₁) ∈ _ from hy'F)
      exact bX.injOn h1 h2 he
    · have hy'F : y' ∈ ψ ⁻¹' Fᶜ := by rwa [mem_preimage, ← he]
      exact hψ.2.2.1 hF hy'F he
  have hinj₂ : InjOn ψ W₂ := by
    intro y hy y' hy' he
    by_cases hF : ψ y ∈ F
    · have h1 : y ∈ X' := by
        have := (hfib hd₂ hun' hX₂).subset (show (⟨y, hy⟩ : W₂) ∈ _ from hF)
        exact this
      have h2 : y' ∈ X' := by
        have hy'F : ψ y' ∈ F := he ▸ hF
        exact (hfib hd₂ hun' hX₂).subset
          (show (⟨y', hy'⟩ : W₂) ∈ _ from hy'F)
      exact bX'.injOn h1 h2 he
    · have hy'F : y' ∈ ψ ⁻¹' Fᶜ := by rwa [mem_preimage, ← he]
      exact hψ.2.2.1 hF hy'F he
  have hbX : X ⊆ bd Y := fun y hy => hψ.2.2.2.2 (hun.subset (.inl hy))
  have hbX' : X' ⊆ bd Y := fun y hy => hψ.2.2.2.2 (hun.subset (.inr hy))
  have hnor : Γ.IsNormal F := fun x hx => absurd hx.2 (disjoint_left.mp hd hx.1)
  have hdisc₁ : Nonempty (W₁ ≃ₜ ClosedUnitDisc) → ∃ Δ : Set S, IsClosedDisc Δ ∧ discBd Δ = F
    ∧ {c ∈ Γ.C | c ⊆ Δ} = I₁ ∧ Δ = ψ '' W₁ := by
    rintro ⟨e⟩
    have : Nonempty W₁ := ⟨⟨_, hX₁ (φ 1).2⟩⟩
    obtain ⟨h1, h2, h3⟩ := side_disc_image hS hm₁ hO hnor hW₁.1 hinj₁ (fun x hx =>
      (bX.image_eq ▸ image_mono hX₁ : F ⊆ _) hx) e
    exact ⟨_, h1, h2, h3, by rw [range_comp, Subtype.range_val]⟩
  have hdisc₂ : Nonempty (W₂ ≃ₜ ClosedUnitDisc) → ∃ Δ : Set S, IsClosedDisc Δ ∧ discBd Δ = F
    ∧ {c ∈ Γ.C | c ⊆ Δ} = I₂ ∧ Δ = ψ '' W₂ := by
    rintro ⟨e⟩
    have : Nonempty W₂ := ⟨⟨_, hX₂ (φ' 1).2⟩⟩
    obtain ⟨h1, h2, h3⟩ := side_disc_image hS hm₂ hO hnor hW₂.1 hinj₂ (fun x hx =>
      (bX'.image_eq ▸ image_mono hX₂ : F ⊆ _) hx) e
    exact ⟨_, h1, h2, h3, by rw [range_comp, Subtype.range_val]⟩
  have hU' : W₂ ∪ W₁ = univ := by rw [union_comm]; exact hU
  have ht₁ := side_tri hS (W := W₁) (W' := W₂) (X := X) hne' hsc ⟨_, (φ 1).2, hX₁
    (φ 1).2⟩ hOX hbX hY hW₁ hc₁ hcase (fun hdd a b c ⟨e⟩ => by
    obtain ⟨Δ, h1, h2, -, h4⟩ := hdisc₂ hdd
    exact paste_side hS hψ hY hW₁ hU hdW hX₁ hOX bX hbX hinj₁ h1 h4 h2 e)
  have ht₂ := side_tri hS (W := W₂) (W' := W₁) (X := X') hne'.symm (by rw [hsc, pair_comm]) ⟨_,
    (φ' 1).2, hX₂ (φ' 1).2⟩ hOX' hbX' hY hW₂ hc₂ hcase (fun hdd a b c ⟨e⟩ => by
    obtain ⟨Δ, h1, h2, -, h4⟩ := hdisc₁ hdd
    exact paste_side hS hψ hY hW₂ hU' hdW.symm hX₂ hOX' bX' hbX' hinj₂ h1 h4 h2 e)
  refine .inr ⟨I₁, I₂, fun c hc => hc.1, hI₂, ?_, ?_, ?_⟩
  · intro c₁ hc₁' c₂ hc₂'
    rw [eq_empty_iff_forall_notMem]
    rintro x ⟨hx, hx'⟩
    exact disjoint_left.mp hPd (hcl hW₁ c₁ hc₁' hx.1) (hcl hW₂ c₂ hc₂' hx'.1)
  · rcases ht₁ with h | h
    · obtain ⟨Δ, h1, h2, h3, -⟩ := hdisc₁ h
      exact .inl ⟨Δ, h1, h2, h3⟩
    · refine .inr fun hne2 => ?_
      obtain ⟨ι, Γ', hpp⟩ := hp₂ hne2
      exact ⟨V₂, tV₂, cV₂, tV₂', hV₂c, ι, Γ', hV₂, h V₂ hdrop₂, hpp⟩
  · rcases ht₂ with h | h
    · obtain ⟨Δ, h1, h2, h3, -⟩ := hdisc₂ h
      exact .inl ⟨Δ, h1, h2, h3⟩
    · refine .inr fun hne2 => ?_
      obtain ⟨ι, Γ', hpp⟩ := hp₁ hne2
      exact ⟨V₁, tV₁, cV₁, tV₁', hV₁c, ι, Γ', hV₁, h V₁ hdrop₁, hpp⟩

end GraphMinor.GM17
