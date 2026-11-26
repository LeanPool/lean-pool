/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section5Side
import LeanPool.GraphMinor.Surface.HoleDisc
import LeanPool.GraphMinor.Surface.SurfacePull
import LeanPool.GraphMinor.Surface.AddCrosscap
import LeanPool.GraphMinor.GM11.PlaneFacts

/-!
# From the surface to the capped surface

Graph Minors XII, Section 5 (pages 254–255), works with a surface `Σ`, the part `Σ₁` of it, and the
surface `Σ̂₁` made by filling in discs. Here `capUp` moves a subset of `Σ` to `Σ̂₁` and `capDown`
moves
it back. We show that the closures of the filled-in discs are closed discs, and that the conditions
of (5.3) give the conditions `CapSetup` of `Section5Side.lean`.
-/

public section

namespace GraphMinor.GM12

open Set Topology Metric GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 Hypergraph

universe u

variable {S T : Type u} [TopologicalSpace S] [T2Space S] [TopologicalSpace T] [T2Space T]
  {n : ℕ} {C : Fin n → Set S} {P₁ P₂ : Set S} {ι : P₁ → T} {D : Fin n → Set T}

@[expose] public section

/-- The part of `X ⊆ Σ` in `Σ₁`, moved to `Σ̂₁`. -/
def capUp (ι : P₁ → T) (X : Set S) : Set T := ι '' ((↑) ⁻¹' X)

end

/-- The part of `Y ⊆ Σ̂₁` in `Σ₁`, moved back to `Σ`. -/
@[expose] def capDown (ι : P₁ → T) (Y : Set T) : Set S := (↑) '' (ι ⁻¹' Y)

omit [TopologicalSpace S] [T2Space S] [TopologicalSpace T] [T2Space T] in
theorem mem_capUp {X : Set S} {y : T} : y ∈ capUp ι X ↔ ∃ x : P₁, x.1 ∈ X ∧ ι x = y := Iff.rfl

omit [TopologicalSpace S] [T2Space S] [TopologicalSpace T] [T2Space T] in
theorem mem_capDown {Y : Set T} {x : S} : x ∈ capDown ι Y ↔ ∃ p : P₁, ι p ∈ Y ∧ p.1 = x := Iff.rfl

omit [TopologicalSpace S] [T2Space S] [TopologicalSpace T] [T2Space T] in
theorem capUp_mono {X X' : Set S} (h : X ⊆ X') : capUp ι X ⊆ capUp ι X' :=
  image_mono (preimage_mono h)

omit [TopologicalSpace S] [T2Space S] [TopologicalSpace T] [T2Space T] in
theorem capDown_subset (Y : Set T) : capDown ι Y ⊆ P₁ := by
  rintro _ ⟨p, -, rfl⟩
  exact p.2

omit [TopologicalSpace S] [T2Space S] [TopologicalSpace T] [T2Space T] in
theorem capUp_subset_range (X : Set S) : capUp ι X ⊆ range ι := image_subset_range _ _

omit [TopologicalSpace S] [T2Space S] [TopologicalSpace T] [T2Space T] in
theorem val_mem_capUp {X : Set S} {x : S} (hx₁ : x ∈ P₁) (hx : x ∈ X) : ι ⟨x, hx₁⟩ ∈ capUp ι X :=
  ⟨⟨x, hx₁⟩, hx, rfl⟩

section inj

variable (hι : Function.Injective ι)
include hι

omit [TopologicalSpace S] [T2Space S] [TopologicalSpace T] [T2Space T] in
theorem mem_capUp_val {X : Set S} {p : P₁} : ι p ∈ capUp ι X ↔ p.1 ∈ X := by
  constructor
  · rintro ⟨q, hq, he⟩
    rwa [← hι he]
  · exact fun h => ⟨p, h, rfl⟩

omit [TopologicalSpace S] [T2Space S] [TopologicalSpace T] [T2Space T] in
theorem capDown_capUp {X : Set S} (hX : X ⊆ P₁) : capDown ι (capUp ι X) = X := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (mem_capUp_val hι).mp hp
  · intro hx
    exact ⟨⟨x, hX hx⟩, (mem_capUp_val hι).mpr hx, rfl⟩

omit [TopologicalSpace S] [T2Space S] [TopologicalSpace T] [T2Space T] hι in
theorem capUp_capDown {Y : Set T} (hY : Y ⊆ range ι) : capUp ι (capDown ι Y) = Y := by
  ext y
  constructor
  · rintro ⟨p, ⟨q, hq, he⟩, rfl⟩
    rw [Subtype.ext he.symm]
    exact hq
  · intro hy
    obtain ⟨p, rfl⟩ := hY hy
    exact ⟨p, ⟨p, hy, rfl⟩, rfl⟩

omit [TopologicalSpace S] [T2Space S] [TopologicalSpace T] [T2Space T] in
theorem ncard_capUp {X : Set S} (hX : X ⊆ P₁) : (capUp ι X).ncard = X.ncard := by
  have h1 : (capUp ι X).ncard = ((↑) ⁻¹' X : Set P₁).ncard := ncard_image_of_injective _ hι
  have h2 : X = (↑) '' ((↑) ⁻¹' X : Set P₁) := by
    rw [Subtype.image_preimage_coe]
    exact (inter_eq_right.mpr hX).symm
  rw [h1]
  conv_rhs => rw [h2]
  exact (ncard_image_of_injective _ Subtype.val_injective).symm

end inj

omit [T2Space T] in
theorem IsCappedSplit.isClosed₁ (h : IsCappedSplit C P₁ P₂ ι D) : IsClosed P₁ := by
  have : CompactSpace P₁ := h.manifold₁.1
  exact isCompact_iff_compactSpace.mpr this |>.isClosed

omit [T2Space T] in
theorem IsCappedSplit.isClosed₂ (h : IsCappedSplit C P₁ P₂ ι D) : IsClosed P₂ := by
  have : CompactSpace P₂ := h.manifold₂.1
  exact isCompact_iff_compactSpace.mpr this |>.isClosed

omit [T2Space S] [T2Space T] in
theorem IsCappedSplit.C_sub₁ (h : IsCappedSplit C P₁ P₂ ι D) (k : Fin n) : C k ⊆ P₁ := fun _ hx =>
  (h.inter.symm ▸ mem_iUnion.mpr ⟨k, hx⟩ : _ ∈ P₁ ∩ P₂).1

omit [T2Space S] [T2Space T] in
theorem IsCappedSplit.C_sub₂ (h : IsCappedSplit C P₁ P₂ ι D) (k : Fin n) : C k ⊆ P₂ := fun _ hx =>
  (h.inter.symm ▸ mem_iUnion.mpr ⟨k, hx⟩ : _ ∈ P₁ ∩ P₂).2

omit [T2Space S] [T2Space T] in
theorem IsCappedSplit.D_off (h : IsCappedSplit C P₁ P₂ ι D) (k : Fin n) : Disjoint (D k) (range ι)
  := by
  refine Set.disjoint_left.mpr fun x hx hr => ?_
  have : x ∈ (range ι)ᶜ := h.compl ▸ mem_iUnion.mpr ⟨k, hx⟩
  exact this hr

omit [T2Space S] in
theorem IsCappedSplit.isClosed_range (h : IsCappedSplit C P₁ P₂ ι D) : IsClosed (range ι) := by
  have : CompactSpace P₁ := h.manifold₁.1
  exact (isCompact_range h.isEmbedding.continuous).isClosed

omit [T2Space S] [T2Space T] in
/-- The boundary of `D k`, as a subset of the closure. -/
theorem closure_diff_eq (h : IsCappedSplit C P₁ P₂ ι D) (k : Fin n) :
    closure (D k) \ D k = capUp ι (C k) := by
  have := h.bounds k
  change subBd (D k) = capUp ι (C k) at this
  rw [← this, subBd]
  have hop : IsClosed (univ \ D k) := by
    rw [← compl_eq_univ_sdiff]
    exact (h.isOpenDisc k).1.isClosed_compl
  rw [hop.closure_eq]
  ext x
  simp [mem_sdiff, mem_inter_iff]

omit [T2Space S] [T2Space T] in
theorem isOArc_capUp (h : IsCappedSplit C P₁ P₂ ι D) (k : Fin n) : IsOArc (capUp ι (C k)) := by
  have hpre : IsOArc ((↑) ⁻¹' C k : Set P₁) := by
    apply isOArc_of_image IsEmbedding.subtypeVal
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr (h.C_sub₁ k)]
    exact h.isOArc k
  exact isOArc_image h.isEmbedding hpre

omit [T2Space S] [T2Space T] in
/-- A point of a cap boundary is a limit of points of `Σ₁` off the cap boundaries. -/
theorem mem_closure_off (h : IsCappedSplit C P₁ P₂ ι D) (k : Fin n) {x : T} (hx : x ∈ capUp ι
  (C k)) :
    x ∈ closure (closure (D k))ᶜ := by
  obtain ⟨c, hc, rfl⟩ := hx
  have hm := mem_closure_compl_bd (h.manifold₁.2.2 c)
  have hcont := h.isEmbedding.continuous
  have h1 : ι c ∈ closure (ι '' (bd P₁)ᶜ) := image_closure_subset_closure_image hcont ⟨c, hm, rfl⟩
  refine closure_mono ?_ h1
  rintro _ ⟨p, hp, rfl⟩ hcl
  have hr : ι p ∈ closure (D k) \ D k :=
    ⟨hcl, fun hD => Set.disjoint_left.mp (h.D_off k) hD ⟨p, rfl⟩⟩
  rw [closure_diff_eq h] at hr
  have hpC : p.1 ∈ C k := (mem_capUp_val h.isEmbedding.injective).mp hr
  have hbd : p.1 ∈ (↑) '' bd P₁ := h.bd₁ ▸ mem_iUnion.mpr ⟨k, hpC⟩
  obtain ⟨q, hq, he⟩ := hbd
  rw [Subtype.ext he] at hq
  exact hp hq

variable [ConnectedSpace T]

omit [T2Space S] [T2Space T] in
/-- The closure of a filled-in disc is a closed disc, bounded by the matching `O`-arc. -/
theorem cap_closure (h : IsCappedSplit C P₁ P₂ ι D) (k : Fin n) :
    IsClosedDisc (closure (D k)) ∧ discBd (closure (D k)) = capUp ι (C k) ∧
      discInt (closure (D k)) = D k := by
  have hS := IsClosedSurface.isSurface h.surface_hat
  have hb : bd T = ∅ := eq_empty_of_forall_notMem fun x hx => hx (h.surface_hat.2.2 x)
  have hO : IsOArc (closure (D k) \ D k) := by
    rw [closure_diff_eq h]
    exact isOArc_capUp h k
  obtain ⟨h1, h2⟩ := closure_disc hS (h.isOpenDisc k) (by rw [hb]; exact disjoint_bot_right) hO
    (fun x hx => mem_closure_off h k (closure_diff_eq h k ▸ hx))
  refine ⟨h1, h2.trans (closure_diff_eq h k), ?_⟩
  rw [discInt, h2]
  ext x
  constructor
  · rintro ⟨hx, hn⟩
    by_contra hD
    exact hn ⟨hx, hD⟩
  · exact fun hx => ⟨subset_closure hx, fun hn => hn.2 hx⟩

omit [ConnectedSpace T] in
omit [T2Space T] in
/-- Moving a normal line back to `Σ`. -/
theorem line_capDown (h : IsCappedSplit C P₁ P₂ ι D) {L : Set T} (hL : IsLine L)
    (hoff : L ⊆ range ι) : IsLine (capDown ι L) := by
  obtain ⟨f⟩ := hL
  have hu : ∃ u v, IsLineWithEnds L u v := ⟨_, _, f, rfl, rfl⟩
  obtain ⟨u, v, hl⟩ := hu
  obtain ⟨u', v', -, -, hp⟩ := hl.pull h.isEmbedding hoff
  have hl' := hp.map_of_embedding (j := ((↑) : P₁ → S)) IsEmbedding.subtypeVal
  obtain ⟨g, -⟩ := hl'
  exact ⟨g⟩

omit [T2Space T] in
/-- The conditions of (5.3) give `CapSetup` for the closures of the filled-in discs. -/
theorem capSetup {Γ : Drawing S} {Γ₁ : Drawing T} {θ : ℕ}
    {𝒯 : Set (Hypergraph T (Set T) × Hypergraph T (Set T))}
    (h : IsCappedSplit C P₁ P₂ ι D) (hΓ : IsCappedDrawing ι Γ Γ₁)
    (hN : ∀ k, Γ.IsNormal (C k)) (hT : IsTangle Γ₁.toHypergraph θ 𝒯)
    (hR : (PaintingOrDrawing.drawing Γ₁).IsRespectful θ 𝒯)
    (hi : ∀ k l, k ≠ l → ∀ F : Set S, IsLine F → Γ.IsNormal F → F ⊆ P₁ →
      (F ∩ C k).Nonempty → (F ∩ C l).Nonempty → θ ≤ (F ∩ Γ.V).ncard)
    (hm : ∀ k, θ ≤ (Γ.V ∩ C k).ncard)
    (hf : ∀ k, ∀ X ⊆ capUp ι (Γ.V ∩ C k), X.ncard ≤ θ → IsFreeSet Γ₁.toHypergraph 𝒯 θ X) :
    CapSetup (fun k => closure (D k)) Γ₁ θ 𝒯 := by
  have hιi := h.isEmbedding.injective
  have hV : ∀ {X : Set S}, X ⊆ P₁ → capUp ι (X ∩ Γ.V) = capUp ι X ∩ Γ₁.V := by
    intro X _
    rw [hΓ.2]
    ext y
    constructor
    · rintro ⟨p, ⟨h1, h2⟩, rfl⟩
      exact ⟨⟨p, h1, rfl⟩, ⟨p, h2, rfl⟩⟩
    · rintro ⟨⟨p, h1, rfl⟩, h2⟩
      exact ⟨p, ⟨h1, (mem_capUp_val hιi).mp h2⟩, rfl⟩
  have hbdV : ∀ k, discBd (closure (D k)) ∩ Γ₁.V = capUp ι (Γ.V ∩ C k) := by
    intro k
    rw [(cap_closure h k).2.1, Set.inter_comm Γ.V, hV (h.C_sub₁ k)]
  refine ⟨fun k => (cap_closure h k).1, ?_, ?_, hT, hR, ?_, ?_, ?_⟩
  · intro k l hkl
    refine Set.disjoint_left.mpr fun x hk hl => ?_
    have hcase : ∀ m, x ∈ closure (D m) → x ∈ D m ∨ x ∈ capUp ι (C m) := fun m hm' => by
      by_cases hd : x ∈ D m
      · exact .inl hd
      · exact .inr (closure_diff_eq h m ▸ ⟨hm', hd⟩)
    rcases hcase k hk with h1 | h1 <;> rcases hcase l hl with h2 | h2
    · exact Set.disjoint_left.mp (h.disjoint_D k l hkl) h1 h2
    · exact Set.disjoint_left.mp (h.D_off k) h1 (capUp_subset_range _ h2)
    · exact Set.disjoint_left.mp (h.D_off l) h2 (capUp_subset_range _ h1)
    · obtain ⟨p, hp, rfl⟩ := h1
      exact Set.disjoint_left.mp (h.disjoint k l hkl) hp ((mem_capUp_val hιi).mp h2)
  · intro k x ⟨hxc, hxU⟩
    have hU : x ∈ capUp ι Γ.U := by
      have := hxU
      rw [hΓ.1] at this
      exact this
    have hxd : x ∉ D k := fun hd => Set.disjoint_left.mp (h.D_off k) hd (capUp_subset_range _ hU)
    have hxC : x ∈ capUp ι (C k) := closure_diff_eq h k ▸ ⟨hxc, hxd⟩
    refine ⟨(cap_closure h k).2.1 ▸ hxC, ?_⟩
    obtain ⟨p, hp, rfl⟩ := hxC
    have hpU : p.1 ∈ Γ.U := (mem_capUp_val hιi).mp hU
    rw [hΓ.2]
    exact ⟨p, hN k ⟨hp, hpU⟩, rfl⟩
  · intro k l hkl L hL hNL hoff hk hl
    have hLr : L ⊆ range ι := by
      intro x hx
      by_contra hn
      have : x ∈ ⋃ m, D m := h.compl ▸ hn
      obtain ⟨m, hm'⟩ := mem_iUnion.mp this
      exact Set.disjoint_left.mp (hoff m) hx ((cap_closure h m).2.2.symm ▸ hm')
    have hmeet : ∀ m, (L ∩ closure (D m)).Nonempty → (capDown ι L ∩ C m).Nonempty := by
      rintro m ⟨x, hxL, hxc⟩
      have hxC : x ∈ capUp ι (C m) := closure_diff_eq h m ▸
        ⟨hxc, fun hd => Set.disjoint_left.mp (h.D_off m) hd (hLr hxL)⟩
      obtain ⟨p, hp, rfl⟩ := hxC
      exact ⟨p.1, ⟨p, hxL, rfl⟩, hp⟩
    have hsubP := capDown_subset (ι := ι) L
    have hN' : Γ.IsNormal (capDown ι L) := by
      rintro _ ⟨⟨p, hp, rfl⟩, hpU⟩
      have : ι p ∈ L ∩ Γ₁.U := ⟨hp, by rw [hΓ.1]; exact ⟨p, hpU, rfl⟩⟩
      have hv := hNL this
      rw [hΓ.2] at hv
      exact (mem_capUp_val hιi).mp hv
    have := hi k l hkl _ (line_capDown h hL hLr) hN' hsubP (hmeet k hk) (hmeet l hl)
    have he : capUp ι (capDown ι L ∩ Γ.V) = L ∩ Γ₁.V := by
      rw [hV hsubP, capUp_capDown hLr]
    rw [← he, ncard_capUp hιi (inter_subset_left.trans hsubP)]
    exact this
  · intro k
    rw [hbdV, ncard_capUp hιi (inter_subset_right.trans (h.C_sub₁ k))]
    exact hm k
  · intro k X hX hc
    exact hf k X (hbdV k ▸ hX) hc

end GraphMinor.GM12
