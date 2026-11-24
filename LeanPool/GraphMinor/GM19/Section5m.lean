/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section5l

/-!
# Graph Minors XIX, proof of (5.4): the colour scheme of a fragment

The fragment `Σ₁` gets the colour scheme `χ'` of the proof of (5.4): the frame is `ψ⁻¹(Φ) ∩ Σ₁`, the
orders `Ω(2)`,
`Ω(3)` do not change, a side over a side `S` of `Φ` has the order `Ω_χ(S)`. A side over an edge of
`K` is short and
gets one colour. The paper colours that side by itself. Colour schemes here keep one fixed set of
colours, so we take
one colour `a₀` for all those sides, which does no harm since these sides have no order to respect.

Then a coloured linear inflation on each fragment glues to a coloured linear inflation on `Σ`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

universe w

variable {S S₁ : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace S₁] [T2Space S₁] {α :
  Type w}


/-- The order with one element. -/
def QuasiOrder.single (a : α) : QuasiOrder α where
  E := {a}
  le _ _ := True
  refl _ _ := trivial
  trans _ _ _ _ _ _ _ _ := trivial

theorem QuasiOrder.isWQO_single (a : α) : (QuasiOrder.single a).IsWQO :=
  fun _ _ ↦ ⟨0, 1, zero_lt_one, trivial⟩

variable {Γ : Painting S} {K : Drawing S} {ψ : S₁ → S}

open Classical in
/-- The order of a side of the fragment. -/
noncomputable def fragΩ (χ : ColourScheme S α) (a₀ : α) (ψ : S₁ → S) (R : Set S₁) : QuasiOrder α :=
  if h : ∃ s ∈ χ.Φ.sides, ψ '' R ⊆ s then χ.ΩS h.choose else QuasiOrder.single a₀

open Classical in
/-- The colour of a short side of the fragment. -/
noncomputable def fragShort (χ : ColourScheme S α) (a₀ : α) (ψ : S₁ → S) (R : Set S₁) : α :=
  if h : ∃ s ∈ χ.Φ.sides, ψ '' R ⊆ s then χ.shortElem h.choose else a₀

omit [T2Space S] [TopologicalSpace S₁] [T2Space S₁] in
theorem exists_choose_eq {χ : ColourScheme S α} {R : Set S₁} (h : ∃ s ∈ χ.Φ.sides, ψ '' R ⊆ s)
  (hne : R.Nonempty)
    {s : Set S} (hs : s ∈ χ.Φ.sides) (hsub : ψ '' R ⊆ s) : h.choose = s := by
  obtain ⟨x, hx⟩ := hne
  exact GM11.arcComponent_eq h.choose_spec.1 hs (h.choose_spec.2 (mem_image_of_mem ψ hx)) (hsub
    (mem_image_of_mem ψ hx))

/-- The colour scheme of the fragment. -/
noncomputable def fragScheme (χ : ColourScheme S α) (a₀ : α) {Γ : Painting S}
  (D : FrameData χ.Φ Γ K ψ)
    (hF : IsFeature χ.Φ K) (flip : Set S₁ → Bool) : ColourScheme S₁ α where
  isSurface := D.pull.frag.isSurface
  connected := D.pull.frag.connected
  Φ := D.frame hF flip
  Ω2 := χ.Ω2
  Ω3 := χ.Ω3
  ΩS := fragΩ χ a₀ ψ
  shortElem := fragShort χ a₀ ψ
  isWQO_2 := χ.isWQO_2
  isWQO_3 := χ.isWQO_3
  isWQO_S R _ := by
    by_cases h : ∃ s ∈ χ.Φ.sides, ψ '' R ⊆ s
    · rw [fragΩ, dite_eq_left_of_eq_true (eq_true h)]
      exact χ.isWQO_S _ h.choose_spec.1
    · rw [fragΩ, dite_eq_right_of_eq_false (eq_false h)]
      exact QuasiOrder.isWQO_single a₀
  short_singleton R hR := by
    by_cases h : ∃ s ∈ χ.Φ.sides, ψ '' R ⊆ s
    · rw [fragΩ, fragShort, dite_eq_left_of_eq_true (eq_true h), dite_eq_left_of_eq_true
      (eq_true h)]
      exact χ.short_singleton _ ⟨h.choose_spec.1, fun hl ↦ hR.2 ⟨_, ⟨h.choose_spec.1, hl⟩,
        h.choose_spec.2⟩⟩
    · rw [fragΩ, fragShort, dite_eq_right_of_eq_false (eq_false h),
        dite_eq_right_of_eq_false (eq_false h)]
      rfl

variable {χ : ColourScheme S α} {a₀ : α}

theorem fragScheme_ΩS {D : FrameData χ.Φ Γ K ψ} {hF : IsFeature χ.Φ K} {flip : Set S₁
  → Bool} {R : Set S₁}
    (hne : R.Nonempty) {s : Set S} (hs : s ∈ χ.Φ.sides) (hsub : ψ '' R ⊆ s) :
    (fragScheme χ a₀ D hF flip).ΩS R = χ.ΩS s := by
  have h : ∃ s ∈ χ.Φ.sides, ψ '' R ⊆ s := ⟨s, hs, hsub⟩
  change fragΩ χ a₀ ψ R = _
  rw [fragΩ, dite_eq_left_of_eq_true (eq_true h), exists_choose_eq h hne hs hsub]

open Classical in
/-- The colouring of the pull-back. -/
noncomputable def fragφ (P : ColouredPainting χ) (ψ : S₁ → S) (a₀ : α) (e₁ : Set S₁) : α :=
  if ψ '' e₁ ∈ P.Γ.E then P.φ (ψ '' e₁) else a₀

omit [T2Space S] [TopologicalSpace S₁] [T2Space S₁] in
theorem fragφ_eq {P : ColouredPainting χ} {e₁ : Set S₁} (h : ψ '' e₁ ∈ P.Γ.E) : fragφ P ψ a₀ e₁
  = P.φ (ψ '' e₁) :=
  ite_eq_left h

theorem fragScheme_Ω_neg {D : FrameData χ.Φ Γ K ψ} {hF : IsFeature χ.Φ K} {flip : Set S₁
  → Bool} {R : Set S₁}
    (h : ¬ ∃ s ∈ χ.Φ.sides, ψ '' R ⊆ s) : (fragScheme χ a₀ D hF flip).ΩS R = QuasiOrder.single a₀
      := by
  change fragΩ χ a₀ ψ R = _
  rw [fragΩ, dite_eq_right_of_eq_false (eq_false h)]

namespace FrameData

variable [Nonempty S₁] {Φ : Frame S} (D : FrameData Φ Γ K ψ) (flip : Set S₁ → Bool)
include D

/-- An internal edge of the pull-back is a lift of an edge of `Γ`. -/
theorem exists_lift_of_internal {e₁ : Set S₁} (he₁ : e₁ ∈ (D.paint flip).E)
  (hi : Painting.IsInternal e₁) :
    ∃ e ∈ Γ.E, ¬ Painting.IsBorder e ∧ (ψ ⁻¹' e).Nonempty ∧ e₁ = ψ ⁻¹' e := by
  rcases (D.mem_paint_E flip).mp he₁ with hp | ⟨e, he, hb, hne, rfl⟩
  · obtain ⟨x, hx⟩ := hp.1
    exact absurd (hp.2.1 hx).1 (disjoint_left.mp hi hx)
  · exact ⟨e, he, hb, hne, rfl⟩

/-- A border edge of the pull-back is an arc of the boundary. -/
theorem mem_arcs_of_border {e₁ : Set S₁} (he₁ : e₁ ∈ (D.paint flip).E) (hb : Painting.IsBorder e₁) :
    e₁ ∈ arcComponentsIn (bd S₁ \ pullV Γ K ψ) := by
  rcases (D.mem_paint_E flip).mp he₁ with hp | ⟨e, he, hb', hne, rfl⟩
  · exact hp
  · obtain ⟨x, hx, hxb⟩ := hb
    exact absurd hxb (D.pull.preimage_subset_int (D.pull.subset_R he hb' hne) hx)

omit [Nonempty S₁] in
omit [T2Space S] [T2Space S₁] in
/-- A side of the fragment over no side of `Φ` lies over an edge of `K`, so no edge of `Γ` has its
image there. -/
theorem image_notMem {R e₁ : Set S₁} (hR : R ∈ arcComponentsIn (bd S₁ \ pullFrameV Φ K ψ))
  (hsub : e₁ ⊆ R)
    (hne : e₁.Nonempty) (h : ¬ ∃ s ∈ Φ.sides, ψ '' R ⊆ s) : ψ '' e₁ ∉ Γ.E := by
  intro hE
  rcases D.image_side hR with h' | ⟨f, hf, hsub'⟩
  · exact h h'
  · obtain ⟨x, hx⟩ := hne
    have hxf := hf.2.1 (hsub' (mem_image_of_mem ψ (hsub hx)))
    have hxE := hE.2.1 (mem_image_of_mem ψ hx)
    exact hxf.2 (D.pull.inter ⟨hxE.1, hxf.1⟩).2

end FrameData

/-- The coloured pull-back of a coloured painting. -/
noncomputable def fragPainting {Γ₀ : Painting S} [Nonempty S₁] (D₀ : FrameData χ.Φ Γ₀ K ψ)
  (hF : IsFeature χ.Φ K)
    (flip : Set S₁ → Bool) (P : ColouredPainting χ) (D : FrameData χ.Φ P.Γ K ψ)
      (hA : IsAnchored P.Γ K) :
    ColouredPainting (fragScheme χ a₀ D₀ hF flip) where
  Γ := D.paint flip
  φ := fragφ P ψ a₀
  fits := by
    have := χ.connected
    exact D.theorem_5_3_proof hF hA flip
  internal_2_mem e₁ he₁ hi h2 := by
    obtain ⟨e, he, hb, hne, rfl⟩ := D.exists_lift_of_internal flip he₁ hi
    have hsub := D.pull.subset_R he hb hne
    have hsur : ψ '' (ψ ⁻¹' e) = e := image_preimage_eq_of_subset (hsub.trans
      (image_subset_range _ _))
    rw [fragφ_eq (hsur.symm ▸ he), hsur]
    refine P.internal_2_mem e he (disjoint_left.mpr fun x hx hxb ↦ hb ⟨x, hx, hxb⟩) ?_
    rw [← D.pull.ncard_tilde he hsub]
    exact h2
  internal_3_mem e₁ he₁ hi h2 := by
    obtain ⟨e, he, hb, hne, rfl⟩ := D.exists_lift_of_internal flip he₁ hi
    have hsub := D.pull.subset_R he hb hne
    have hsur : ψ '' (ψ ⁻¹' e) = e := image_preimage_eq_of_subset (hsub.trans
      (image_subset_range _ _))
    rw [fragφ_eq (hsur.symm ▸ he), hsur]
    refine P.internal_3_mem e he (disjoint_left.mpr fun x hx hxb ↦ hb ⟨x, hx, hxb⟩) ?_
    rw [← D.pull.ncard_tilde he hsub]
    exact h2
  border_mem e₁ he₁ R hR hbs := by
    have ha := D.mem_arcs_of_border flip he₁ hbs.1
    by_cases h : ∃ s ∈ χ.Φ.sides, ψ '' R ⊆ s
    · obtain ⟨s, hs, hsub⟩ := h
      obtain ⟨x, hx⟩ := ha.1
      have hxb : ψ x ∈ bd S := (hs.2.1 (hsub (mem_image_of_mem ψ (hbs.2 hx)))).1
      obtain ⟨hE, -⟩ := D.pull.image_border_edge ha hx hxb
      rw [fragScheme_ΩS ⟨x, hbs.2 hx⟩ hs hsub, fragφ_eq hE]
      exact P.border_mem _ hE s hs ⟨⟨ψ x, mem_image_of_mem ψ hx, hxb⟩,
        (image_mono hbs.2).trans hsub⟩
    · have hE := D.image_notMem hR hbs.2 ha.1 h
      rw [fragScheme_Ω_neg h]
      exact ite_eq_right hE

variable {Γ₀ : Painting S} [Nonempty S₁]

/-- A coloured linear inflation on the fragment is a `FragInflation`. -/
theorem fragInflation {D₀ : FrameData χ.Φ Γ₀ K ψ} {hF : IsFeature χ.Φ K} {flip : Set S₁ → Bool}
    {P₁ P₂ : ColouredPainting χ} {D₁ : FrameData χ.Φ P₁.Γ K ψ} {D₂ : FrameData χ.Φ P₂.Γ K ψ}
    {hA₁ : IsAnchored P₁.Γ K} {hA₂ : IsAnchored P₂.Γ K} {σv : S₁ → Set S₁} {σe : Set S₁ → Set S₁}
    (h : IsColouredLinearInflation (fragScheme χ a₀ D₀ hF flip) (fragPainting (a₀
      := a₀) D₀ hF flip P₁ D₁ hA₁)
      (fragPainting (a₀ := a₀) D₀ hF flip P₂ D₂ hA₂) σv σe)
    (hflip : IsPaperFlip χ.Φ K ψ D₁.pull.frag.isSurface flip) (hV : ∀ v ∈ K.V, v ∈ P₁.Γ.V ↔ v ∈
      P₂.Γ.V) :
    FragInflation D₁ D₂ hF flip σv σe where
  inflation := h.isLinear
  respects := h.respects
  flip_spec := hflip
  fits := (fragPainting (a₀ := a₀) D₀ hF flip P₁ D₁ hA₁).fits
  fits' := (fragPainting (a₀ := a₀) D₀ hF flip P₂ D₂ hA₂).fits
  same_V := hV

variable {ι : Type} {Y : ι → Type} [∀ t, TopologicalSpace (Y t)] [∀ t, T2Space
  (Y t)] [∀ t, Nonempty (Y t)]
  {ψ : ∀ t, Y t → S}

/-- **Gluing coloured inflations.** Coloured linear inflations of the fragments give a coloured
linear inflation of
`(Γ₁, φ₁)` in `(Γ₂, φ₂)`. -/
theorem glue_coloured {Γ₀ : ι → Painting S} {D₀ : ∀ t, FrameData χ.Φ (Γ₀ t) K
  (ψ t)} {hF : IsFeature χ.Φ K}
    {flip : ∀ t, Set (Y t) → Bool} {P₁ P₂ : ColouredPainting χ} {D₁ : ∀ t, FrameData χ.Φ P₁.Γ K
      (ψ t)}
    {D₂ : ∀ t, FrameData χ.Φ P₂.Γ K (ψ t)} {hA₁ : IsAnchored P₁.Γ K} {hA₂ : IsAnchored P₂.Γ K}
    {σv : ∀ t, Y t → Set (Y t)} {σe : ∀ t, Set (Y t) → Set (Y t)}
    (h : ∀ t, IsColouredLinearInflation (fragScheme χ a₀ (D₀ t) hF (flip t))
      (fragPainting (a₀ := a₀) (D₀ t) hF (flip t) P₁ (D₁ t) hA₁)
      (fragPainting (a₀ := a₀) (D₀ t) hF (flip t) P₂ (D₂ t) hA₂) (σv t) (σe t))
    (hflip : ∀ t, IsPaperFlip χ.Φ K (ψ t) (D₁ t).pull.frag.isSurface (flip t))
    (hV : ∀ v ∈ K.V, v ∈ P₁.Γ.V ↔ v ∈ P₂.Γ.V) (hC : IsCover K ψ) :
    IsColouredLinearInflation χ P₁ P₂ (glueV ψ σv) (glueE ψ σe) := by
  have G : ∀ t, FragInflation (D₁ t) (D₂ t) hF (flip t) (σv t) (σe t) := fun t ↦ fragInflation
    (h t) (hflip t) hV
  have hL := glue_linear G hC
  have hint : ∀ e ∈ P₁.Γ.E, Painting.IsInternal e → ∀ t, (ψ t ⁻¹' e).Nonempty →
      ψ t ⁻¹' e ∈ ((D₁ t).paint (flip t)).E ∧ Painting.IsInternal (ψ t ⁻¹' e) ∧
      (tilde (ψ t ⁻¹' e)).ncard = (tilde e).ncard := by
    intro e he hi t hne
    have hb : ¬ Painting.IsBorder e := fun ⟨x, hx, hxb⟩ ↦ disjoint_left.mp hi hx hxb
    have hsub := (D₁ t).pull.subset_R he hb hne
    exact ⟨((D₁ t).mem_paint_E (flip t)).mpr (Or.inr ⟨e, he, hb, hne, rfl⟩),
      disjoint_left.mpr fun x hx hxb ↦ (D₁ t).pull.preimage_subset_int hsub hx hxb,
        (D₁ t).pull.ncard_tilde he hsub⟩
  refine ⟨⟨hL.toIsInflation, glue_respects G hC, ?_, ?_, ?_⟩, hL⟩
  · intro e he hi h2
    obtain ⟨t, hne⟩ := exists_lift hC he
    obtain ⟨hE₁, hi₁, hn⟩ := hint e he hi t hne
    obtain ⟨hsur, -, hE', -⟩ := (G t).edge_main he hne
    have := (h t).le_internal_2 _ hE₁ hi₁ (hn.trans h2)
    change χ.Ω2.le (fragφ P₁ (ψ t) a₀ (ψ t ⁻¹' e)) (fragφ P₂ (ψ t) a₀ (σe t (ψ t ⁻¹' e))) at this
    rwa [fragφ_eq (hsur.symm ▸ he), fragφ_eq hE', hsur, ← glueE_eq G hC.off he hne] at this
  · intro e he hi h2
    obtain ⟨t, hne⟩ := exists_lift hC he
    obtain ⟨hE₁, hi₁, hn⟩ := hint e he hi t hne
    obtain ⟨hsur, -, hE', -⟩ := (G t).edge_main he hne
    have := (h t).le_internal_3 _ hE₁ hi₁ (hn.trans h2)
    change χ.Ω3.le (fragφ P₁ (ψ t) a₀ (ψ t ⁻¹' e)) (fragφ P₂ (ψ t) a₀ (σe t (ψ t ⁻¹' e))) at this
    rwa [fragφ_eq (hsur.symm ▸ he), fragφ_eq hE', hsur, ← glueE_eq G hC.off he hne] at this
  · intro e he s hs hbs
    obtain ⟨t, hne⟩ := exists_lift hC he
    obtain ⟨hsur, hE₁, hE', -⟩ := (G t).edge_main he hne
    have hbe := (P₁.Γ.border_edge e he hbs.1).2
    obtain ⟨x, hx⟩ := id hne
    obtain ⟨he₁, -⟩ := (D₁ t).pull.preimage_border_edge he hbe hx
    obtain ⟨R, hR, hes⟩ := exists_arcComp_superset he₁.2.2.1 (F := bd (Y t) \ pullFrameV χ.Φ K
      (ψ t))
      (fun x hx ↦ ⟨(he₁.2.1 hx).1, fun h ↦ (he₁.2.1 hx).2 ((D₁ t).pullFrameV_subset h)⟩)
    obtain ⟨s', hs', hRs⟩ := (D₁ t).exists_side_of_bd hR (hes hx) (hbe hx)
    obtain rfl : s' = s := GM11.arcComponent_eq hs' hs (hRs (mem_image_of_mem _ (hes hx)))
      (hbs.2 hx)
    have hbb : Painting.IsBorder (ψ t ⁻¹' e) := ⟨x, hx, (he₁.2.1 hx).1⟩
    have := (h t).le_border _ hE₁ R hR ⟨hbb, hes⟩
    rw [fragScheme_ΩS ⟨x, hes hx⟩ hs hRs] at this
    change (χ.ΩS s').le (fragφ P₁ (ψ t) a₀ (ψ t ⁻¹' e)) (fragφ P₂ (ψ t) a₀ (σe t
      (ψ t ⁻¹' e))) at this
    rwa [fragφ_eq (hsur.symm ▸ he), fragφ_eq hE', hsur, ← glueE_eq G hC.off he hne] at this

end GraphMinor.GM19
