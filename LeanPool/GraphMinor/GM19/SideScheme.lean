/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FreeFrame

import LeanPool.GraphMinor.GM19.FragmentOrient

/-!
# The colour scheme of the proof of (11.1)

For the pieces `X₁, …, X_t` of the long side `S` the proof of (11.1) takes smaller ideals `{x : x ≱
ω'ᵢ}`. Here `lab` says which element each side leaves out, and
`ColourScheme.restrictSides` is the colour scheme with these ideals. It has the same frame and order
as the scheme it comes from, so an inflation for it is one for that scheme
(`IsColouredLinearInflation.of_restrictSides`). The result used later is `wellBehaved_side`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe w

variable {S S₁ : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace S₁] [T2Space S₁] {β :
  Type w}

/-- The ideal of the elements that are not above `w`. -/
def QuasiOrder.withoutAbove (Ω : QuasiOrder β) (w : β) : QuasiOrder β where
  E := {x ∈ Ω.E | ¬ Ω.le w x}
  le := Ω.le
  refl x hx := Ω.refl x hx.1
  trans x hx y hy z hz := Ω.trans x hx.1 y hy.1 z hz.1

theorem QuasiOrder.isWQO_withoutAbove {Ω : QuasiOrder β} (h : Ω.IsWQO) (w : β) :
  (Ω.withoutAbove w).IsWQO := fun f hf ↦ h f fun i ↦ (hf i).1

theorem QuasiOrder.isStrictSubIdeal_withoutAbove {Ω : QuasiOrder β} {w : β} (hw : w ∈ Ω.E) :
  (Ω.withoutAbove w).IsStrictSubIdeal Ω := by
  refine ⟨⟨fun _ h ↦ h.1, fun x' hx' x hx hle ↦ ⟨hx, fun hl ↦ hx'.2 (Ω.trans w hw x hx x' hx'.1 hl
    hle)⟩, fun _ _ _ _ ↦ Iff.rfl⟩, fun he ↦ ?_⟩
  have : w ∈ (Ω.withoutAbove w).E := he ▸ hw
  exact this.2 (Ω.refl w hw)

/-- The order of a side, with the elements above `lab R` left out. -/
def restrictΩ (χ' : ColourScheme S₁ β) (lab : Set S₁ → Option β) (R : Set S₁) : QuasiOrder β :=
  match lab R with
  | some w => (χ'.ΩS R).withoutAbove w
  | none => χ'.ΩS R

omit [T2Space S₁] in
theorem restrictΩ_none {χ' : ColourScheme S₁ β} {lab : Set S₁ → Option β} {R : Set S₁} (h : lab R
  = none) : restrictΩ χ' lab R = χ'.ΩS R := by
  simp [restrictΩ, h]

omit [T2Space S₁] in
theorem restrictΩ_some {χ' : ColourScheme S₁ β} {lab : Set S₁ → Option β} {R : Set S₁} {w : β}
  (h : lab R = some w) : restrictΩ χ' lab R = (χ'.ΩS R).withoutAbove w := by
  simp [restrictΩ, h]

/-- The colour scheme with the smaller orders. -/
def ColourScheme.restrictSides (χ' : ColourScheme S₁ β) (lab : Set S₁ → Option β)
  (hlab : ∀ R ∈ χ'.Φ.shortSides, lab R = none) : ColourScheme S₁ β where
  isSurface := χ'.isSurface
  connected := χ'.connected
  Φ := χ'.Φ
  Ω2 := χ'.Ω2
  Ω3 := χ'.Ω3
  ΩS := restrictΩ χ' lab
  shortElem := χ'.shortElem
  isWQO_2 := χ'.isWQO_2
  isWQO_3 := χ'.isWQO_3
  isWQO_S R hR := by
    cases h : lab R with
    | none => rw [restrictΩ_none h]; exact χ'.isWQO_S R hR
    | some w => rw [restrictΩ_some h]; exact QuasiOrder.isWQO_withoutAbove (χ'.isWQO_S R hR) w
  short_singleton R hR := by
    rw [restrictΩ_none (hlab R hR)]
    exact χ'.short_singleton R hR

/-- A coloured painting whose colours avoid what `lab` leaves out, as a painting of the smaller
scheme. -/
def ColouredPainting.restrictSides {χ' : ColourScheme S₁ β} (P : ColouredPainting χ') (lab : Set S₁
  → Option β) (hlab : ∀ R ∈ χ'.Φ.shortSides, lab R = none)
    (hc : ∀ e ∈ P.Γ.E, ∀ R ∈ χ'.Φ.sides, BordersSide e R → ∀ w, lab R = some w → ¬ (χ'.ΩS R).le w
      (P.φ e)) : ColouredPainting (χ'.restrictSides lab hlab) where
  Γ := P.Γ
  φ := P.φ
  fits := P.fits
  internal_2_mem := P.internal_2_mem
  internal_3_mem := P.internal_3_mem
  border_mem e he R hR hb := by
    change P.φ e ∈ (restrictΩ χ' lab R).E
    cases h : lab R with
    | none => rw [restrictΩ_none h]; exact P.border_mem e he R hR hb
    | some w => rw [restrictΩ_some h]; exact ⟨P.border_mem e he R hR hb, hc e he R hR hb w h⟩

omit [T2Space S₁] in
theorem IsColouredLinearInflation.of_restrictSides {χ' : ColourScheme S₁ β} {P Q : ColouredPainting
  χ'} {lab : Set S₁ → Option β} {hlab : ∀ R ∈ χ'.Φ.shortSides, lab R = none}
    {hP : ∀ e ∈ P.Γ.E, ∀ R ∈ χ'.Φ.sides, BordersSide e R → ∀ w, lab R = some w → ¬ (χ'.ΩS R).le w
      (P.φ e)}
    {hQ : ∀ e ∈ Q.Γ.E, ∀ R ∈ χ'.Φ.sides, BordersSide e R → ∀ w, lab R = some w → ¬ (χ'.ΩS R).le w
      (Q.φ e)} {σv : S₁ → Set S₁} {σe : Set S₁ → Set S₁}
    (h : IsColouredLinearInflation (χ'.restrictSides lab hlab) (P.restrictSides lab hlab hP)
      (Q.restrictSides lab hlab hQ) σv σe) : IsColouredLinearInflation χ' P Q σv σe := by
  refine ⟨⟨h.isInflation, h.respects, h.le_internal_2, h.le_internal_3, fun e he R hR hb ↦ ?_⟩,
    h.isLinear⟩
  have := h.le_border e he R hR hb
  change (restrictΩ χ' lab R).le _ _ at this
  cases hl : lab R with
  | none => rwa [restrictΩ_none hl] at this
  | some w => rwa [restrictΩ_some hl] at this


variable [Nonempty S₁] {χ : ColourScheme S β} {K : Drawing S} {ψ : S₁ → S} {Γ : Painting S}

omit [Nonempty S₁] in
/-- A label is missing on each short side, if labels sit only over `side`. -/
theorem lab_short (D : FrameData χ.Φ Γ K ψ) (hF : IsFeature χ.Φ K) (flip : Set S₁ → Bool)
  (a₀ : β) {side : Set S} (hside : side ∈ χ.Φ.longSides) {lab : Set S₁ → Option β}
    (hnone : ∀ R, ¬ ψ '' R ⊆ side → lab R = none) : ∀ R ∈ (fragScheme χ a₀ D hF flip).Φ.shortSides,
      lab R = none := fun R hR ↦ by
  refine hnone R fun hsub ↦ hR.2 ⟨side, hside, hsub⟩

open Classical in
omit [Nonempty S₁] in
/-- **The colour scheme of (11.1) is a refinement of `χ`.** -/
theorem restrictSides_isRefinement (D : FrameData χ.Φ Γ K ψ) (hF : IsFeature χ.Φ K) (flip : Set S₁
  → Bool) (a₀ : β) (hhom : Nonempty (S₁ ≃ₜ S)) (hinj : Function.Injective ψ) {side : Set S}
    (hside : side ∈ χ.Φ.longSides) {lab : Set S₁ → Option β} (hnone : ∀ R, ¬ ψ '' R ⊆ side → lab R
      = none)
    (hsome : ∀ R ∈ arcComponentsIn (bd S₁ \ pullFrameV χ.Φ K ψ), ψ '' R ⊆ side → ∃ w ∈
      (χ.ΩS side).E, lab R = some w)
    (hkeep : ∀ s ∈ χ.Φ.longSides, s ≠ side → (s ∩ range ψ) \ K.U = ∅ ∨ IsPathConnected
      ((s ∩ range ψ) \ K.U)) :
    ((fragScheme χ a₀ D hF flip).restrictSides lab (lab_short D hF flip a₀ hside
      hnone)).IsRefinement χ := by
  set χ₁ := fragScheme χ a₀ D hF flip with hχ₁
  have hlongs : ∀ R, R ∈ χ₁.Φ.longSides ↔ R ∈ arcComponentsIn (bd S₁ \ pullFrameV χ.Φ K ψ)
    ∧ ∃ s ∈ χ.Φ.longSides, ψ '' R ⊆ s := fun R ↦ Iff.rfl
  let f : Set S₁ → Set S := fun R ↦ if h : ∃ s ∈ χ.Φ.longSides, ψ '' R ⊆ s then h.choose else ∅
  have hf : ∀ {R}, (∃ s ∈ χ.Φ.longSides, ψ '' R ⊆ s) → f R ∈ χ.Φ.longSides ∧ ψ '' R ⊆ f R
    := fun {R} h ↦ by
    simp only [f, dite_eq_left h]
    exact h.choose_spec
  have hoffK : ∀ {R s}, R ∈ arcComponentsIn (bd S₁ \ pullFrameV χ.Φ K ψ) → s ∈ χ.Φ.longSides
    → ψ '' R ⊆ s → ψ '' R ⊆ (s ∩ range ψ) \ K.U := by
    rintro R s hR hs hsub _ ⟨x, hx, rfl⟩
    refine ⟨⟨hsub (mem_image_of_mem _ hx), mem_range_self x⟩, fun hk ↦ ?_⟩
    have hb : ψ x ∈ bd S := (hs.1.2.1 (hsub (mem_image_of_mem _ hx))).1
    exact (hR.2.1 hx).2 (Or.inr (D.K_bd ⟨hk, hb⟩))
  have hfside : ∀ {R}, R ∈ χ₁.Φ.longSides → f R = side → ψ '' R ⊆ side := fun {R} hR he ↦ by
    have := (hf ((hlongs R).1 hR).2).2
    rwa [he] at this
  have hΩ : ∀ {R}, R ∈ χ₁.Φ.longSides → χ₁.ΩS R = χ.ΩS (f R) := fun {R} hR ↦ by
    obtain ⟨hRs, hl⟩ := (hlongs R).1 hR
    obtain ⟨m, sub⟩ := hf hl
    exact fragScheme_ΩS hRs.1 m.1 sub
  have hstrict : ∀ {R}, R ∈ χ₁.Φ.longSides → f R = side → (restrictΩ χ₁ lab R).IsStrictSubIdeal
    (χ.ΩS (f R)) := fun {R} hR he ↦ by
    obtain ⟨w, hw, hl⟩ := hsome R ((hlongs R).1 hR).1 (hfside hR he)
    rw [restrictΩ_some hl, hΩ hR, he]
    exact QuasiOrder.isStrictSubIdeal_withoutAbove hw
  have huniq : ∀ {R₁ R₂}, R₁ ∈ χ₁.Φ.longSides → R₂ ∈ χ₁.Φ.longSides → f R₁ = f R₂ → f R₁ ≠ side
    → R₁ = R₂ := by
    intro R₁ R₂ h₁ h₂ he hne
    obtain ⟨h₁s, h₁l⟩ := (hlongs R₁).1 h₁
    obtain ⟨h₂s, h₂l⟩ := (hlongs R₂).1 h₂
    obtain ⟨m₁, s₁⟩ := hf h₁l
    obtain ⟨m₂, s₂⟩ := hf h₂l
    rw [← he] at m₂ s₂
    have b₁ := hoffK h₁s m₁ s₁
    have b₂' := hoffK h₂s m₁ s₂
    obtain ⟨x, hx⟩ := h₁s.1
    have hne' : ((f R₁ ∩ range ψ) \ K.U).Nonempty := ⟨_, b₁ (mem_image_of_mem _ hx)⟩
    rcases hkeep _ m₁ hne with h₀ | hp
    · exact absurd hne' (by rw [h₀]; exact not_nonempty_empty)
    · refine D.side_eq_of_isPathConnected hinj hp (fun z hz ↦ hz.1.2) (fun z hz ↦
        (m₁.1.2.1 hz.1.1).1) ?_ h₁s h₂s b₁ b₂'
      refine disjoint_left.2 fun z hz hv ↦ ?_
      rcases hv with hv | hv
      · exact (m₁.1.2.1 hz.1.1).2 hv
      · exact hz.2 (K.V_subset_U hv)
  refine ⟨hhom, rfl, rfl, f, fun R hR ↦ (hf ((hlongs R).1 hR).2).1, fun R hR ↦ ?_,
    fun R₁ h₁ R₂ h₂ hne he ↦ ?_, fun hall ↦ ?_⟩
  · by_cases he : f R = side
    · exact (hstrict hR he).1
    · have hl : lab R = none := hnone R fun hsub ↦ by
        obtain ⟨hRs, hl⟩ := (hlongs R).1 hR
        obtain ⟨m, sub⟩ := hf hl
        obtain ⟨x, hx⟩ := hRs.1
        exact he (GM11.arcComponent_eq m.1 hside.1 (sub (mem_image_of_mem _ hx)) (hsub
          (mem_image_of_mem _ hx)))
      change (restrictΩ χ₁ lab R).IsSubIdeal _
      rw [restrictΩ_none hl, hΩ hR]
      exact QuasiOrder.isSubIdeal_refl _
  · by_cases hs : f R₁ = side
    · exact hstrict h₁ hs
    · exact absurd (huniq h₁ h₂ he hs) hne
  · exfalso
    obtain ⟨R, hR, hfR, hE⟩ := hall side hside
    have hs := hstrict (R := R) hR hfR
    rw [hfR] at hs
    exact hs.2 hE

variable {𝒮 : Set (ColouredPainting χ)}

/-- **The places with colours off the labels are well-behaved by `S₄`.** -/
theorem wellBehaved_side (hS : IsSurface S) (hF : IsFeature χ.Φ K) (hcl : IsPaintingClass χ 𝒮)
    (hlines : ∀ e ∈ arcComponentsIn (K.U \ K.V), ∃ u v, u ≠ v ∧ closure e ∩ K.V = {u, v}
      ∧ IsLineWithEnds (closure e) u v)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] {ψ : Y → S} (hY : IsSurface Y)
      (hψ : IsCutMap ψ K.U) (hsheet : HasSheets ψ K)
    (y : Y) (l : List S) (m : ℕ) (a₀ : β) (hS4 : ConditionS4 χ) (hhom : Nonempty
      (connectedComponent y ≃ₜ S)) (hinj : InjOn ψ (connectedComponent y))
    (hO : IsOrientableSurface (connectedComponent y) → IsOrientableSurface S) {side : Set S}
      (hside : side ∈ χ.Φ.longSides) {lab : Set (connectedComponent y) → Option β}
    (hnone : ∀ R, ¬ (fun x : connectedComponent y ↦ ψ x.1) '' R ⊆ side → lab R = none)
    (hsome : ∀ R ∈ arcComponentsIn (bd (connectedComponent y) \ pullFrameV χ.Φ K
      (fun x : connectedComponent y ↦ ψ x.1)), (fun x : connectedComponent y ↦ ψ x.1) '' R ⊆ side →
      ∃ w ∈ (χ.ΩS side).E, lab R = some w)
    (hkeep : ∀ s ∈ χ.Φ.longSides, s ≠ side → (s ∩ (ψ '' connectedComponent y)) \ K.U = ∅
      ∨ IsPathConnected ((s ∩ (ψ '' connectedComponent y)) \ K.U)) :
    IsWellBehavedPlaces {X | IsCutPlace χ K (fun x : connectedComponent y ↦ ψ x.1) l m X ∧ X.P ∈ 𝒮 ∧
      ∀ R w, lab R = some w → ∀ e ∈ X.P.Γ.E, e ⊆ (fun x : connectedComponent y ↦ ψ x.1) '' R → ¬
        (χ.ΩS side).le w (X.P.φ e)} := by
  have : Nonempty (connectedComponent y) := ⟨⟨y, mem_connectedComponent⟩⟩
  have hr : range (fun x : connectedComponent y ↦ ψ x.1) = ψ '' connectedComponent y := by
    ext z
    simp
  apply wellBehaved_of_fragment (fun x : connectedComponent y ↦ ψ x.1) hF l m a₀
    (fun a b hab hoff ↦ Subtype.ext (hψ.2.2.1 hoff (fun h ↦ hoff (hab ▸ h)) hab))
    (fun X hX ↦ frameData_of_cut hS X.P.fits hX.inter hlines hY hψ hsheet y)
  intro seq hq h flip hflip
  set D := fun i ↦ frameData_of_cut hS (seq i).P.fits (h i).inter hlines hY hψ hsheet y with hDdef
  set χ₁ := fragScheme χ a₀ (D 0) hF flip with hχ₁
  have hl := lab_short (D 0) hF flip a₀ hside hnone
  have hc : ∀ i, ∀ e ∈ ((fragPainting (a₀ := a₀) (D 0) hF flip (seq i).P (D i)
    (h i).anchored).Γ).E, ∀ R ∈ χ₁.Φ.sides, BordersSide e R → ∀ w, lab R = some w →
      ¬ (χ₁.ΩS R).le w ((fragPainting (a₀ := a₀) (D 0) hF flip (seq i).P (D i) (h i).anchored).φ e)
        := by
    intro i e₁ he₁ R hR hbs w hw
    have hRs : (fun x : connectedComponent y ↦ ψ x.1) '' R ⊆ side := by
      by_contra hn
      rw [hnone R hn] at hw
      exact absurd hw (by simp)
    have ha := (D i).mem_arcs_of_border flip he₁ hbs.1
    obtain ⟨x, hx⟩ := ha.1
    have hxb : ψ x.1 ∈ bd S := (hside.1.2.1 (hRs (mem_image_of_mem _ (hbs.2 hx)))).1
    obtain ⟨hE, -⟩ := (D i).pull.image_border_edge ha hx hxb
    have hΩ : χ₁.ΩS R = χ.ΩS side := fragScheme_ΩS ⟨x, hbs.2 hx⟩ hside.1 hRs
    rw [hΩ]
    change ¬ (χ.ΩS side).le w (fragφ (seq i).P (fun x : connectedComponent y ↦ ψ x.1) a₀ e₁)
    rw [fragφ_eq hE]
    exact (hq i).2 R w hw _ hE (image_mono hbs.2)
  have hnb := hS4 _ (χ₁.restrictSides lab hl) (restrictSides_isRefinement (D 0) hF flip a₀ hhom
    (fun a b hab ↦ Subtype.ext (hinj a.2 b.2 hab)) hside hnone hsome
    (fun s hs hne ↦ by rw [hr]; exact hkeep s hs hne))
  have hsim := frag_similarly hcl hS hF a₀ (D 0) (fun i ↦ (seq i).P) (fun i ↦ (hq i).1) D (fun i ↦
    (h i).anchored) flip hO
  by_contra hno
  push Not at hno
  exact hnb ⟨fun i ↦ (fragPainting (a₀ := a₀) (D 0) hF flip (seq i).P (D i)
    (h i).anchored).restrictSides lab hl (hc i), fun i j hij ⟨σv, σe, hσ⟩ ↦
    hno i j hij σv σe hσ.of_restrictSides, hsim⟩

end GraphMinor.GM19
