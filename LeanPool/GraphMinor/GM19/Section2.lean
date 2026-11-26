/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.CapExists
public import LeanPool.GraphMinor.GM19.Section4c
public import LeanPool.GraphMinor.GM20.Cited
public import LeanPool.GraphMinor.Surface.MoveCuff

/-!
# Graph Minors XIX, (2.1) from (3.1)

This is the proof of (2.1) on pages 330–331 of the paper. The topology of that proof, which is
making
the frame and the thin paintings, is the named statement `Theorem21TopologyStatement`. Everything
else
is here: colouring the new paintings, passing to a subsequence for the short sides, and turning a
linear inflation of the new paintings back into one of the old paintings.
The deductions that use later proofs are in `Section2Proved`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Function Topology GraphMinor.Surface

universe u w

variable {S : Type u} [TopologicalSpace S]

/-- `Γ'` is the painting that the proof of Graph Minors XIX, (2.1) (pages 330–331), makes from `Γ`.
It is the image of `Γ` under the homeomorphism `h`, with each edge of size 3 replaced by the three
arcs of its boundary and a thin disc `s(e)` inside it. The directions of the border edges are those
of the frame. -/
structure IsThinning (Φ : Frame S) (Γ : Painting S) (h : S ≃ₜ S) (Γ' : Painting S)
    (s : Set S → Set S) : Prop where
  null : HasNullSignature h
  null_symm : HasNullSignature h.symm
  V_eq : Γ'.V = h '' Γ.V
  fits : Γ'.Fits Φ
  three : ∀ e ∈ Γ.E, (tilde e).ncard = 3 →
    s e ∈ Γ'.E ∧ tilde (s e) = h '' tilde e ∧ Γ'.γ (s e) = (Γ.γ e).map h
  three_inj : InjOn s {e ∈ Γ.E | (tilde e).ncard = 3}
  three_surj : ∀ e' ∈ Γ'.E, (tilde e').ncard = 3 → ∃ e ∈ Γ.E, (tilde e).ncard = 3 ∧ s e = e'
  two : ∀ e ∈ Γ.E, (tilde e).ncard = 2 → h '' e ∈ Γ'.E
  internal_γ : ∀ e ∈ Γ.E, (tilde e).ncard = 2 → Painting.IsInternal e →
    Γ'.γ (h '' e) = (Γ.γ e).map h
  border_γ : ∀ e ∈ Γ.E, Painting.IsBorder e →
    Γ'.γ (h '' e) = (Γ.γ e).map h ∨ Γ'.γ (h '' e) = ((Γ.γ e).map h).reverse
  rest : ∀ e' ∈ Γ'.E, (tilde e').ncard = 2 → (∃ e ∈ Γ.E, (tilde e).ncard = 2 ∧ h '' e = e') ∨
    (Painting.IsInternal e' ∧ ∃ c ∈ Γ.E, (tilde c).ncard = 3 ∧ tilde e' ⊆ h '' tilde c)
  short : ∀ t ∈ Φ.shortSides, ∃ e ∈ Γ.E, h '' e = t

/-- The topology in the proof of Graph Minors XIX, (2.1) (pages 330–331): there is a frame with one
long and one short side on each cuff, and each internally 3-connected painting has, after a
homeomorphism that keeps each cuff and its orientation, a thinning that fits this frame. The rest of
that proof is `GM19.theorem_2_1_proof`. -/
def Theorem21TopologyStatement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S], IsSurface S → ConnectedSpace S →
    ∃ Φ : Frame S, ∀ Γ : Painting S, Γ.IsInternallyThreeConnected →
      ∃ (h : S ≃ₜ S) (Γ' : Painting S) (s : Set S → Set S), IsThinning Φ Γ h Γ' s

/-! ### Orders -/

namespace QuasiOrder

/-- The quasi-order `Ω × R` of the paper. The sixth label is for short sides. -/
def labelOrder (Ω : Type w) [Preorder Ω] : QuasiOrder (Ω × Fin 6) where
  E := univ
  le x y := x.1 ≤ y.1 ∧ x.2 = y.2
  refl _ _ := ⟨le_rfl, rfl⟩
  trans _ _ _ _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

theorem labelOrder_isWQO (Ω : Type w) [Preorder Ω] [WellQuasiOrderedLE Ω] :
    (labelOrder Ω).IsWQO := fun f _ ↦
  ((wellQuasiOrdered_le (α := Ω)).prod (Finite.wellQuasiOrdered (Eq : Fin 6 → Fin 6 → Prop))) f

/-- The quasi-order with one element. -/
def pointOrder {α : Type w} (x : α) : QuasiOrder α where
  E := {x}
  le := Eq
  refl _ _ := rfl
  trans _ _ _ _ _ _ h₁ h₂ := h₁.trans h₂

theorem pointOrder_isWQO {α : Type w} (x : α) : (pointOrder x).IsWQO := fun _f hf ↦
  ⟨0, 1, Nat.zero_lt_one, (hf 0).trans (hf 1).symm⟩

end QuasiOrder

/-! ### Order on a cuff -/

theorem continuous_cuffPoint {Θ : Set S} (f : Circle ≃ₜ Θ) : Continuous (cuffPoint f) :=
  continuous_subtype_val.comp (f.continuous.comp Circle.exp.continuous)

/-- The other orientation of `Θ`. -/
noncomputable def revParam {Θ : Set S} (f : Circle ≃ₜ Θ) : Circle ≃ₜ Θ :=
  (Homeomorph.inv Circle).trans f

theorem cuffPoint_revParam {Θ : Set S} (f : Circle ≃ₜ Θ) (t : ℝ) :
    cuffPoint (revParam f) t = cuffPoint f (-t) := by
  simp [cuffPoint, revParam, Circle.exp_neg]

theorem revParam_revParam {Θ : Set S} (f : Circle ≃ₜ Θ) : revParam (revParam f) = f := by
  ext x
  simp [revParam]

theorem cuffPoint_add {Θ : Set S} (f : Circle ≃ₜ Θ) (t : ℝ) :
    cuffPoint f (t + 2 * Real.pi) = cuffPoint f t := by
  simp [cuffPoint, Circle.exp_add, Circle.exp_two_pi]

/-- A homeomorphism with null signature keeps the order on each cuff. -/
theorem ImmediatelyPrecedes.null {α : S ≃ₜ S} (hα : HasNullSignature α) {Θ : Set S}
    (hΘ : Θ ∈ cuffs S) {f : Circle ≃ₜ Θ} {n : S} {A : Set S} (h : ImmediatelyPrecedes f n A) :
    ImmediatelyPrecedes f (α n) (α '' A) := by
  obtain ⟨g, ⟨l, hlc, hlm, hl⟩, hg⟩ := hα Θ f hΘ
  obtain ⟨t₀, t₁, h01, h02, hn, rfl⟩ := h
  have hcp : ∀ t, α (cuffPoint f t) = cuffPoint f (l t) := fun t ↦ by
    simp only [cuffPoint]
    rw [hg, hl]
  have hIoo : l '' Ioo t₀ t₁ = Ioo (l t₀) (l t₁) := by
    apply Subset.antisymm
    · rintro _ ⟨t, ht, rfl⟩
      exact ⟨hlm ht.1, hlm ht.2⟩
    · exact intermediate_value_Ioo h01.le hlc.continuousOn
  refine ⟨l t₀, l t₁, hlm h01, ?_, by rw [← hcp, hn], ?_⟩
  · have := hlm.monotone h02
    rwa [lift_period hlc hlm hl] at this
  · rw [← hIoo, image_image, image_image]
    exact image_congr fun t _ ↦ hcp t

/-- Turning the orientation around: the other end of `A` immediately precedes `A`. -/
theorem ImmediatelyPrecedes.reverse [T2Space S] {Θ : Set S} {f : Circle ≃ₜ Θ} {n m : S} {A : Set S}
    (h : ImmediatelyPrecedes f n A) (hm : m ∈ tilde A) (hne : m ≠ n) :
    ImmediatelyPrecedes (revParam f) m A := by
  obtain ⟨t₀, t₁, h01, h02, rfl, rfl⟩ := h
  have hc := continuous_cuffPoint f
  have hcl : closure (cuffPoint f '' Ioo t₀ t₁) ⊆ cuffPoint f '' Icc t₀ t₁ :=
    closure_minimal (image_mono Ioo_subset_Icc_self) (isCompact_Icc.image hc).isClosed
  obtain ⟨t, ht, rfl⟩ := hcl hm.1
  have ht0 : t ≠ t₀ := fun h ↦ hne (by rw [h])
  have ht1 : t = t₁ := by
    by_contra hn'
    refine hm.2 (mem_image_of_mem _ ⟨lt_of_le_of_ne ht.1 ht0.symm, lt_of_le_of_ne ht.2 hn'⟩)
  subst ht1
  refine ⟨-t, -t₀, neg_lt_neg h01, by linarith, ?_, ?_⟩
  · rw [cuffPoint_revParam, neg_neg]
  · ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨-u, ⟨by linarith [hu.2], by linarith [hu.1]⟩, by rw [cuffPoint_revParam, neg_neg]⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨-u, ⟨by linarith [hu.2], by linarith [hu.1]⟩, by rw [cuffPoint_revParam]⟩

theorem null_mem {α : S ≃ₜ S} (hα : HasNullSignature α) {Θ : Set S} (hΘ : Θ ∈ cuffs S)
    (hO : IsOArc Θ) {a : S} (ha : a ∈ Θ) : α a ∈ Θ := by
  obtain ⟨f⟩ := hO
  obtain ⟨g, -, hg⟩ := hα Θ f hΘ
  have := hg (f.symm ⟨a, ha⟩)
  simp only [Homeomorph.apply_symm_apply] at this
  rw [this]
  exact (f _).2

/-! ### Paintings -/

theorem tilde_image_homeo (h : S ≃ₜ S) (e : Set S) : tilde (h '' e) = h '' tilde e := by
  rw [tilde, tilde, ← h.image_closure, image_sdiff h.injective]

theorem ncard_tilde_image (h : S ≃ₜ S) (e : Set S) :
    (tilde (h '' e)).ncard = (tilde e).ncard := by
  rw [tilde_image_homeo, ncard_image_of_injective _ h.injective]

theorem isBorder_image (h : S ≃ₜ S) {e : Set S} :
    Painting.IsBorder (h '' e) ↔ Painting.IsBorder e := by
  have hset : h '' e ∩ bd S = h '' (e ∩ bd S) := by
    conv_lhs => rw [← image_bd h]
    exact (image_inter h.injective).symm
  simp only [Painting.IsBorder]
  rw [hset, image_nonempty]

theorem isInternal_iff_not_border {e : Set S} : Painting.IsInternal e ↔ ¬ Painting.IsBorder e := by
  rw [Painting.IsInternal, Painting.IsBorder, not_nonempty_iff_eq_empty,
    disjoint_iff_inter_eq_empty]

theorem size_two_of_border (Γ : Painting S) {e : Set S} (he : e ∈ Γ.E)
    (hb : Painting.IsBorder e) : (tilde e).ncard = 2 :=
  (Γ.border_edge e he hb).1

theorem internal_of_three (Γ : Painting S) {e : Set S} (he : e ∈ Γ.E) (h3 : (tilde e).ncard = 3) :
    Painting.IsInternal e := by
  rw [isInternal_iff_not_border]
  intro hb
  have := size_two_of_border Γ he hb
  omega

namespace IsThinning

variable {Φ : Frame S} {Γ Γ' : Painting S} {h : S ≃ₜ S} {s : Set S → Set S}

theorem size_s (T : IsThinning Φ Γ h Γ' s) {e : Set S} (he : e ∈ Γ.E) (h3 : (tilde e).ncard = 3) :
    (tilde (s e)).ncard = 3 := by
  rw [(T.three e he h3).2.1, ncard_image_of_injective _ h.injective, h3]

/-- The new edge of an old edge. -/
noncomputable def edge (_Γ : Painting S) (h : S ≃ₜ S) (s : Set S → Set S) (e : Set S) : Set S :=
  open Classical in if (tilde e).ncard = 3 then s e else h '' e

theorem edge_three {e : Set S} (h3 : (tilde e).ncard = 3) : edge Γ h s e = s e := ite_eq_left h3

theorem edge_two {e : Set S} (h2 : (tilde e).ncard = 2) : edge Γ h s e = h '' e :=
  ite_eq_right (by omega)

theorem edge_mem (T : IsThinning Φ Γ h Γ' s) {e : Set S} (he : e ∈ Γ.E) :
    edge Γ h s e ∈ Γ'.E := by
  rcases Γ.size_cases he with h2 | h3
  · rw [edge_two h2]
    exact T.two e he h2
  · rw [edge_three h3]
    exact (T.three e he h3).1

theorem edge_size (T : IsThinning Φ Γ h Γ' s) {e : Set S} (he : e ∈ Γ.E) :
    (tilde (edge Γ h s e)).ncard = (tilde e).ncard := by
  rcases Γ.size_cases he with h2 | h3
  · rw [edge_two h2, ncard_tilde_image]
  · rw [edge_three h3, T.size_s he h3, h3]

theorem edge_inj (T : IsThinning Φ Γ h Γ' s) {e₁ e₂ : Set S} (h₁ : e₁ ∈ Γ.E) (h₂ : e₂ ∈ Γ.E)
    (he : edge Γ h s e₁ = edge Γ h s e₂) : e₁ = e₂ := by
  have hsz : (tilde e₁).ncard = (tilde e₂).ncard := by
    rw [← T.edge_size h₁, ← T.edge_size h₂, he]
  rcases Γ.size_cases h₁ with h2 | h3
  · rw [edge_two h2, edge_two (hsz ▸ h2)] at he
    exact image_injective.2 h.injective he
  · rw [edge_three h3, edge_three (hsz ▸ h3)] at he
    exact T.three_inj ⟨h₁, h3⟩ ⟨h₂, hsz ▸ h3⟩ he

/-- Adjacent vertices of the new skeleton come from adjacent vertices of the old one. -/
theorem skAdj_symm (T : IsThinning Φ Γ h Γ' s) {a b : S} (hab : Γ'.skAdj.Adj a b) :
    Γ.skAdj.Adj (h.symm a) (h.symm b) := by
  obtain ⟨hne, ha, hb, e', he', hae, hbe⟩ := hab
  have hV : ∀ {x}, x ∈ Γ'.V → h.symm x ∈ Γ.V := fun {x} hx ↦ by
    rw [T.V_eq] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  have hsym : ∀ {X : Set S} {x}, x ∈ h '' X → h.symm x ∈ X := fun {X x} hx ↦ by
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  refine ⟨fun he ↦ hne (h.symm.injective he), hV ha, hV hb, ?_⟩
  rcases Γ'.size_cases he' with h2 | h3
  · rcases T.rest e' he' h2 with ⟨e, he, -, rfl⟩ | ⟨-, c, hc, -, hsub⟩
    · rw [tilde_image_homeo] at hae hbe
      exact ⟨e, he, hsym hae, hsym hbe⟩
    · exact ⟨c, hc, hsym (hsub hae), hsym (hsub hbe)⟩
  · obtain ⟨e, he, h3', rfl⟩ := T.three_surj e' he' h3
    rw [(T.three e he h3').2.1] at hae hbe
    exact ⟨e, he, hsym hae, hsym hbe⟩

theorem side_of_border (T : IsThinning Φ Γ h Γ' s) {y : Set S} (hy : y ∈ Γ'.E)
    (hb : Painting.IsBorder y) : ∃ t ∈ Φ.sides, y ⊆ t := by
  have hsub : y ⊆ bd S \ Φ.V := fun x hx ↦
    ⟨(Γ'.border_edge y hy hb).2 hx, fun hV ↦ (hy.2.1 hx).2 (T.fits.V_subset hV)⟩
  obtain ⟨t, ht, hyt⟩ := exists_arcComp_superset hy.2.2.1 hsub
  exact ⟨t, ht, hyt⟩

end IsThinning

/-! ### The colouring -/

variable {Ω : Type w} [Preorder Ω]

open Classical in
/-- The colouring `φ'` of the paper, with labels `-1, 0, 1, 2, 3` written `0, 1, 2, 3, 4`. -/
noncomputable def thinColour (Φ : Frame S) (Γ Γ' : Painting S) (h : S ≃ₜ S) (s : Set S → Set S)
    (φ : Set S → Ω) (x₀ : Ω) (e' : Set S) : Ω × Fin 6 :=
  if h₃ : ∃ e ∈ Γ.E, (tilde e).ncard = 3 ∧ s e = e' then (φ h₃.choose, 4)
  else if e' ∈ Φ.shortSides then (x₀, 5)
  else if h₂ : ∃ e ∈ Γ.E, (tilde e).ncard = 2 ∧ h '' e = e' then
    (φ h₂.choose, if Painting.IsInternal e' then 3
      else if Γ'.γ e' = (Γ.γ h₂.choose).map h then 2 else 0)
  else (x₀, 1)

section Colour

variable {Φ : Frame S} {Γ Γ' : Painting S} {h : S ≃ₜ S} {s : Set S → Set S}
  {φ : Set S → Ω} {x₀ : Ω}

omit [Preorder Ω] in
theorem thinColour_three (T : IsThinning Φ Γ h Γ' s) {e : Set S} (he : e ∈ Γ.E)
    (h3 : (tilde e).ncard = 3) : thinColour Φ Γ Γ' h s φ x₀ (s e) = (φ e, 4) := by
  have hex : ∃ c ∈ Γ.E, (tilde c).ncard = 3 ∧ s c = s e := ⟨e, he, h3, rfl⟩
  rw [thinColour, dite_eq_left hex]
  have hc := hex.choose_spec
  rw [T.three_inj ⟨hc.1, hc.2.1⟩ ⟨he, h3⟩ hc.2.2]

theorem no_three_of_size (T : IsThinning Φ Γ h Γ' s) {e' : Set S} (h2 : (tilde e').ncard = 2) :
    ¬ ∃ e ∈ Γ.E, (tilde e).ncard = 3 ∧ s e = e' := by
  rintro ⟨e, he, h3, rfl⟩
  have := T.size_s he h3
  omega

omit [Preorder Ω] in
theorem thinColour_short (T : IsThinning Φ Γ h Γ' s) {t : Set S} (ht : t ∈ Φ.shortSides) :
    thinColour Φ Γ Γ' h s φ x₀ t = (x₀, 5) := by
  rw [thinColour, dite_eq_right (no_three_of_size T (Φ.side_shape t ht.1).1), ite_eq_left ht]

open Classical in
omit [Preorder Ω] in
theorem thinColour_two (T : IsThinning Φ Γ h Γ' s) {e : Set S} (he : e ∈ Γ.E)
    (h2 : (tilde e).ncard = 2) (hs : h '' e ∉ Φ.shortSides) :
    thinColour Φ Γ Γ' h s φ x₀ (h '' e) = (φ e, if Painting.IsInternal (h '' e) then 3
      else if Γ'.γ (h '' e) = (Γ.γ e).map h then 2 else 0) := by
  classical
  have hex : ∃ c ∈ Γ.E, (tilde c).ncard = 2 ∧ h '' c = h '' e := ⟨e, he, h2, rfl⟩
  rw [thinColour, dite_eq_right (no_three_of_size T (by rw [ncard_tilde_image, h2])), ite_eq_right
    hs, dite_eq_left hex]
  have hc : hex.choose = e := image_injective.2 h.injective hex.choose_spec.2.2
  rw [hc]

omit [Preorder Ω] in
/-- The label of an edge of size 2 of the new painting. -/
theorem thinColour_cases (T : IsThinning Φ Γ h Γ' s) {e' : Set S} (he' : e' ∈ Γ'.E)
    (h2 : (tilde e').ncard = 2) :
    e' ∈ Φ.shortSides ∨
    (∃ e ∈ Γ.E, (tilde e).ncard = 2 ∧ h '' e = e' ∧ e' ∉ Φ.shortSides) ∨
    (thinColour Φ Γ Γ' h s φ x₀ e').2 = 1 := by
  classical
  by_cases hs : e' ∈ Φ.shortSides
  · exact Or.inl hs
  by_cases hex : ∃ e ∈ Γ.E, (tilde e).ncard = 2 ∧ h '' e = e'
  · obtain ⟨e, he, h2', rfl⟩ := hex
    exact Or.inr (Or.inl ⟨e, he, h2', rfl, hs⟩)
  · refine Or.inr (Or.inr ?_)
    rw [thinColour, dite_eq_right (no_three_of_size T h2), ite_eq_right hs, dite_eq_right hex]

theorem nonempty_edge (Γ' : Painting S) {e : Set S} (he : e ∈ Γ'.E) : e.Nonempty := he.1

/-- A border edge of a painting that is inside a short side is this side. -/
theorem eq_of_subset_short (T : IsThinning Φ Γ h Γ' s) {y t : Set S} (hy : y ∈ Γ'.E)
    (ht : t ∈ Φ.shortSides) (hsub : y ⊆ t) : y = t := by
  obtain ⟨x, hx⟩ := hy.1
  exact arcComp_eq_of_mem hy (T.fits.short_sides ht) hx (hsub hx)

end Colour

/-- The colour scheme `χ` of the paper. -/
noncomputable def thinScheme [WellQuasiOrderedLE Ω] (hS : IsSurface S) (hc : ConnectedSpace S)
    (Φ : Frame S) (x₀ : Ω) : ColourScheme S (Ω × Fin 6) :=
  open Classical in
  { isSurface := hS
    connected := hc
    Φ := Φ
    Ω2 := QuasiOrder.labelOrder Ω
    Ω3 := QuasiOrder.labelOrder Ω
    ΩS := fun t ↦ if t ∈ Φ.shortSides then QuasiOrder.pointOrder (x₀, 5)
      else QuasiOrder.labelOrder Ω
    shortElem := fun _ ↦ (x₀, 5)
    isWQO_2 := QuasiOrder.labelOrder_isWQO Ω
    isWQO_3 := QuasiOrder.labelOrder_isWQO Ω
    isWQO_S := fun t _ ↦ by
      split_ifs
      · exact QuasiOrder.pointOrder_isWQO _
      · exact QuasiOrder.labelOrder_isWQO Ω
    short_singleton := fun t ht ↦ by
      rw [ite_eq_left ht]
      rfl }

/-- The `χ`-coloured painting `(Γ', φ')` of the paper. -/
noncomputable def thinPainting [WellQuasiOrderedLE Ω] {Φ : Frame S} {Γ Γ' : Painting S}
    {h : S ≃ₜ S} {s : Set S → Set S} (T : IsThinning Φ Γ h Γ' s) (hS : IsSurface S)
    (hc : ConnectedSpace S) (φ : Set S → Ω) (x₀ : Ω) : ColouredPainting
      (thinScheme hS hc Φ x₀) where
  Γ := Γ'
  φ := thinColour Φ Γ Γ' h s φ x₀
  fits := T.fits
  internal_2_mem _ _ _ _ := mem_univ _
  internal_3_mem _ _ _ _ := mem_univ _
  border_mem e he t ht hb := by
    classical
    by_cases hs : t ∈ Φ.shortSides
    · have heq := eq_of_subset_short T he hs hb.2
      change _ ∈ (if t ∈ Φ.shortSides then QuasiOrder.pointOrder (x₀, 5)
        else QuasiOrder.labelOrder Ω).E
      rw [ite_eq_left hs, heq, thinColour_short T hs]
      rfl
    · change _ ∈ (if t ∈ Φ.shortSides then QuasiOrder.pointOrder (x₀, 5)
        else QuasiOrder.labelOrder Ω).E
      rw [ite_eq_right hs]
      exact mem_univ _

/-! ### Turning an inflation back -/

section Pull

variable [WellQuasiOrderedLE Ω] {Φ : Frame S} {Γ₁ Γ₁' Γ₂ Γ₂' : Painting S} {h₁ h₂ : S ≃ₜ S}
  {s₁ s₂ : Set S → Set S} {φ₁ φ₂ : Set S → Ω} {x₀ : Ω}

/-- The direction of the new edge against the old one, for a pair of matched edges. -/
def SameDir (Γ₁ Γ₁' Γ₂ Γ₂' : Painting S) (h₁ h₂ : S ≃ₜ S) (e f y z : Set S) : Prop :=
  (Γ₁'.γ y = (Γ₁.γ e).map h₁ ∧ Γ₂'.γ z = (Γ₂.γ f).map h₂) ∨
  (Γ₁'.γ y = ((Γ₁.γ e).map h₁).reverse ∧ Γ₂'.γ z = ((Γ₂.γ f).map h₂).reverse ∧
    Painting.IsBorder e)

/-- Each old edge has its partner `f`. This is the text from "We construct `σ`" to the end of (2) in
the paper. -/
theorem exists_partner (hS : IsSurface S) (hc : ConnectedSpace S)
    (T₁ : IsThinning Φ Γ₁ h₁ Γ₁' s₁) (T₂ : IsThinning Φ Γ₂ h₂ Γ₂' s₂)
    (hshort : ∀ t ∈ Φ.shortSides, ∀ e₁ ∈ Γ₁.E, ∀ e₂ ∈ Γ₂.E, h₁ '' e₁ = t → h₂ '' e₂ = t →
      φ₁ e₁ ≤ φ₂ e₂ ∧ (Γ₁'.γ t = (Γ₁.γ e₁).map h₁ ↔ Γ₂'.γ t = (Γ₂.γ e₂).map h₂))
    {σv : S → Set S} {σe : Set S → Set S}
    (hσ : IsColouredLinearInflation (thinScheme hS hc Φ x₀) (thinPainting T₁ hS hc φ₁ x₀)
      (thinPainting T₂ hS hc φ₂ x₀) σv σe)
    {e : Set S} (he : e ∈ Γ₁.E) :
    ∃ f ∈ Γ₂.E, (tilde f).ncard = (tilde e).ncard ∧ φ₁ e ≤ φ₂ f ∧
      σe (IsThinning.edge Γ₁ h₁ s₁ e) = IsThinning.edge Γ₂ h₂ s₂ f ∧
      SameDir Γ₁ Γ₁' Γ₂ Γ₂' h₁ h₂ e f (IsThinning.edge Γ₁ h₁ s₁ e) (IsThinning.edge Γ₂ h₂ s₂ f)
        := by
  classical
  have hmem : ∀ {y}, y ∈ Γ₁'.E → σe y ∈ Γ₂'.E := fun {y} hy ↦ hσ.isInflation.edge_mem y hy
  have hsz : ∀ {y}, y ∈ Γ₁'.E → (tilde (σe y)).ncard = (tilde y).ncard := fun {y} hy ↦
    hσ.isInflation.edge_size y hy
  rcases Γ₁.size_cases he with h2 | h3
  · have hy₁ : h₁ '' e ∈ Γ₁'.E := T₁.two e he h2
    have hy2 : (tilde (h₁ '' e)).ncard = 2 := by rw [ncard_tilde_image, h2]
    have hz2 : (tilde (σe (h₁ '' e))).ncard = 2 := by rw [hsz hy₁, hy2]
    have hedge : IsThinning.edge Γ₁ h₁ s₁ e = h₁ '' e := IsThinning.edge_two h2
    rw [hedge]
    have partner : ∀ c : Fin 6, c ≠ 1 → c ≠ 5 →
        (thinColour Φ Γ₂ Γ₂' h₂ s₂ φ₂ x₀ (σe (h₁ '' e))).2 = c →
        ∃ f ∈ Γ₂.E, (tilde f).ncard = 2 ∧ h₂ '' f = σe (h₁ '' e) ∧ σe (h₁ '' e) ∉ Φ.shortSides := by
      intro c hc1 hc5 hlab
      rcases thinColour_cases (φ := φ₂) (x₀ := x₀) T₂ (hmem hy₁) hz2 with hs | hf | h1
      · rw [thinColour_short T₂ hs] at hlab
        exact absurd hlab.symm hc5
      · exact hf
      · exact absurd (hlab.symm.trans h1) hc1
    by_cases hb : Painting.IsBorder e
    · have hyb : Painting.IsBorder (h₁ '' e) := (isBorder_image h₁).2 hb
      by_cases hsh : h₁ '' e ∈ Φ.shortSides
      · obtain ⟨hzb, hzs⟩ := hσ.respects _ hy₁ hyb
        have hzsub : σe (h₁ '' e) ⊆ h₁ '' e := (hzs _ hsh.1).1 Subset.rfl
        have hz : σe (h₁ '' e) = h₁ '' e := eq_of_subset_short T₂ (hmem hy₁) hsh hzsub
        obtain ⟨f, hf, hft⟩ := T₂.short _ hsh
        have hf2 : (tilde f).ncard = 2 := by
          rw [← ncard_tilde_image h₂, hft, hy2]
        obtain ⟨hle, hiff⟩ := hshort _ hsh e he f hf rfl hft
        have hedgef : IsThinning.edge Γ₂ h₂ s₂ f = h₁ '' e := by
          rw [IsThinning.edge_two hf2, hft]
        refine ⟨f, hf, hf2.trans h2.symm, hle, by rw [hz, hedgef], ?_⟩
        rw [hedgef]
        have hf' : Painting.IsBorder f := by
          rw [← isBorder_image h₂, hft]
          exact hyb
        have hfγ := T₂.border_γ f hf hf'
        rw [hft] at hfγ
        rcases T₁.border_γ e he hb with hg | hg
        · exact Or.inl ⟨hg, hiff.1 hg⟩
        · by_cases hg' : Γ₁'.γ (h₁ '' e) = (Γ₁.γ e).map h₁
          · exact Or.inl ⟨hg', hiff.1 hg'⟩
          · exact Or.inr ⟨hg, hfγ.resolve_left fun h ↦ hg' (hiff.2 h), hb⟩
      · obtain ⟨t, ht, hyt⟩ := T₁.side_of_border hy₁ hyb
        have htshort : t ∉ Φ.shortSides := fun hts ↦
          hsh ((eq_of_subset_short T₁ hy₁ hts hyt).symm ▸ hts)
        have hle := hσ.le_border _ hy₁ t ht ⟨hyb, hyt⟩
        have hle' : (thinColour Φ Γ₁ Γ₁' h₁ s₁ φ₁ x₀ (h₁ '' e)).1 ≤
            (thinColour Φ Γ₂ Γ₂' h₂ s₂ φ₂ x₀ (σe (h₁ '' e))).1 ∧
            (thinColour Φ Γ₁ Γ₁' h₁ s₁ φ₁ x₀ (h₁ '' e)).2 =
            (thinColour Φ Γ₂ Γ₂' h₂ s₂ φ₂ x₀ (σe (h₁ '' e))).2 := by
          change (if t ∈ Φ.shortSides then QuasiOrder.pointOrder ((x₀, 5) : Ω × Fin 6)
            else QuasiOrder.labelOrder Ω).le _ _ at hle
          rw [ite_eq_right htshort] at hle
          exact hle
        have hyint : ¬ Painting.IsInternal (h₁ '' e) := fun hi ↦
          (isInternal_iff_not_border.1 hi) hyb
        rw [thinColour_two T₁ he h2 hsh, ite_eq_right hyint] at hle'
        by_cases hdir : Γ₁'.γ (h₁ '' e) = (Γ₁.γ e).map h₁
        · rw [ite_eq_left hdir] at hle'
          obtain ⟨f, hf, hf2, hfz, hzs⟩ := partner 2 (by decide) (by decide) hle'.2.symm
          have hedgef : IsThinning.edge Γ₂ h₂ s₂ f = σe (h₁ '' e) := by
            rw [IsThinning.edge_two hf2, hfz]
          rw [← hfz, thinColour_two T₂ hf hf2 (hfz ▸ hzs)] at hle'
          refine ⟨f, hf, hf2.trans h2.symm, hle'.1, hedgef.symm, ?_⟩
          rw [hedgef]
          refine Or.inl ⟨hdir, ?_⟩
          have hl := hle'.2
          rw [← hfz]
          by_contra hn
          simp only [hn, ite_false] at hl
          split_ifs at hl <;> simp at hl
        · rw [ite_eq_right hdir] at hle'
          obtain ⟨f, hf, hf2, hfz, hzs⟩ := partner 0 (by decide) (by decide) hle'.2.symm
          have hedgef : IsThinning.edge Γ₂ h₂ s₂ f = σe (h₁ '' e) := by
            rw [IsThinning.edge_two hf2, hfz]
          rw [← hfz, thinColour_two T₂ hf hf2 (hfz ▸ hzs)] at hle'
          refine ⟨f, hf, hf2.trans h2.symm, hle'.1, hedgef.symm, ?_⟩
          rw [hedgef]
          have hl := hle'.2
          have hni : ¬ Painting.IsInternal (h₂ '' f) := fun hi ↦ by
            simp only [hi, ite_true] at hl
            simp at hl
          have hnd : Γ₂'.γ (h₂ '' f) ≠ (Γ₂.γ f).map h₂ := fun hd ↦ by
            simp only [hni, hd, ite_false, ite_true] at hl
            simp at hl
          have hf' : Painting.IsBorder f := by
            rw [← isBorder_image h₂]
            by_contra hn
            exact hni (isInternal_iff_not_border.2 hn)
          refine Or.inr ⟨(T₁.border_γ e he hb).resolve_left hdir, ?_, hb⟩
          rw [← hfz]
          exact (T₂.border_γ f hf hf').resolve_left hnd
    · have hint : Painting.IsInternal e := isInternal_iff_not_border.2 hb
      have hyint : Painting.IsInternal (h₁ '' e) := isInternal_iff_not_border.2 fun h' ↦
        hb ((isBorder_image h₁).1 h')
      have hsh : h₁ '' e ∉ Φ.shortSides := fun hts ↦ by
        obtain ⟨x, hx⟩ := hy₁.1
        have hxb : x ∈ bd S := (hts.1.2.1 hx).1
        exact disjoint_left.1 hyint hx hxb
      have hle : (thinColour Φ Γ₁ Γ₁' h₁ s₁ φ₁ x₀ (h₁ '' e)).1 ≤
          (thinColour Φ Γ₂ Γ₂' h₂ s₂ φ₂ x₀ (σe (h₁ '' e))).1 ∧
          (thinColour Φ Γ₁ Γ₁' h₁ s₁ φ₁ x₀ (h₁ '' e)).2 =
          (thinColour Φ Γ₂ Γ₂' h₂ s₂ φ₂ x₀ (σe (h₁ '' e))).2 :=
        hσ.le_internal_2 _ hy₁ hyint hy2
      rw [thinColour_two T₁ he h2 hsh, ite_eq_left hyint] at hle
      obtain ⟨f, hf, hf2, hfz, hzs⟩ := partner 3 (by decide) (by decide) hle.2.symm
      have hedgef : IsThinning.edge Γ₂ h₂ s₂ f = σe (h₁ '' e) := by
        rw [IsThinning.edge_two hf2, hfz]
      rw [← hfz, thinColour_two T₂ hf hf2 (hfz ▸ hzs)] at hle
      refine ⟨f, hf, hf2.trans h2.symm, hle.1, hedgef.symm, ?_⟩
      rw [hedgef, ← hfz]
      have hl := hle.2
      have hi : Painting.IsInternal (h₂ '' f) := by
        by_contra hn
        simp only [hn, ite_false] at hl
        split_ifs at hl <;> simp at hl
      have hi' : Painting.IsInternal f := isInternal_iff_not_border.2 fun h' ↦
        (isInternal_iff_not_border.1 hi) ((isBorder_image h₂).2 h')
      exact Or.inl ⟨T₁.internal_γ e he h2 hint, T₂.internal_γ f hf hf2 hi'⟩
  · have hy₁ := (T₁.three e he h3).1
    have hedge : IsThinning.edge Γ₁ h₁ s₁ e = s₁ e := IsThinning.edge_three h3
    rw [hedge]
    have hy3 := T₁.size_s he h3
    have hint : Painting.IsInternal (s₁ e) := internal_of_three Γ₁' hy₁ hy3
    have hz3 : (tilde (σe (s₁ e))).ncard = 3 := by rw [hsz hy₁, hy3]
    obtain ⟨f, hf, hf3, hfz⟩ := T₂.three_surj _ (hmem hy₁) hz3
    have hle : (thinColour Φ Γ₁ Γ₁' h₁ s₁ φ₁ x₀ (s₁ e)).1 ≤
        (thinColour Φ Γ₂ Γ₂' h₂ s₂ φ₂ x₀ (σe (s₁ e))).1 ∧
        (thinColour Φ Γ₁ Γ₁' h₁ s₁ φ₁ x₀ (s₁ e)).2 =
        (thinColour Φ Γ₂ Γ₂' h₂ s₂ φ₂ x₀ (σe (s₁ e))).2 :=
      hσ.le_internal_3 _ hy₁ hint hy3
    rw [thinColour_three T₁ he h3, ← hfz, thinColour_three T₂ hf hf3] at hle
    refine ⟨f, hf, hf3.trans h3.symm, hle.1, ?_, ?_⟩
    · rw [IsThinning.edge_three hf3, hfz]
    · rw [IsThinning.edge_three hf3]
      exact Or.inl ⟨(T₁.three e he h3).2.2, (T₂.three f hf hf3).2.2⟩

theorem ends_getElem? {Γ Γ' : Painting S} {σv : S → Set S} {σe : Set S → Set S}
    (hσ : IsInflation Γ Γ' σv σe) {e : Set S} (he : e ∈ Γ.E) {i : ℕ} {a b : S}
    (ha : (Γ.γ e)[i]? = some a) (hb : (Γ'.γ (σe e))[i]? = some b) : b ∈ σv a := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 ha
  obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.1 hb
  exact hσ.ends e he i hi hi'

private theorem homeomorph_preserves_cuff_meets {Θ E : Set S} {α : S ≃ₜ S}
    (hΘ : Θ ∈ cuffs S) (hΘO : IsOArc Θ) (hα : HasNullSignature α)
    (hα' : HasNullSignature α.symm) :
    (E ∩ Θ).Nonempty ↔ (α '' E ∩ Θ).Nonempty := by
  constructor
  · rintro ⟨x, hx, hxΘ⟩
    exact ⟨α x, mem_image_of_mem _ hx, null_mem hα hΘ hΘO hxΘ⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, hxΘ⟩
    have h := null_mem hα' hΘ hΘO hxΘ
    exact ⟨x, hx, by simpa only [Homeomorph.symm_apply_apply] using h⟩

/-- The inflation `σ` of the paper. -/
theorem exists_pull (hS : IsSurface S) (hc : ConnectedSpace S)
    (T₁ : IsThinning Φ Γ₁ h₁ Γ₁' s₁) (T₂ : IsThinning Φ Γ₂ h₂ Γ₂' s₂)
    (hshort : ∀ t ∈ Φ.shortSides, ∀ e₁ ∈ Γ₁.E, ∀ e₂ ∈ Γ₂.E, h₁ '' e₁ = t → h₂ '' e₂ = t →
      φ₁ e₁ ≤ φ₂ e₂ ∧ (Γ₁'.γ t = (Γ₁.γ e₁).map h₁ ↔ Γ₂'.γ t = (Γ₂.γ e₂).map h₂))
    {σv' : S → Set S} {σe' : Set S → Set S}
    (hσ : IsColouredLinearInflation (thinScheme hS hc Φ x₀) (thinPainting T₁ hS hc φ₁ x₀)
      (thinPainting T₂ hS hc φ₂ x₀) σv' σe') :
    ∃ (σv : S → Set S) (σe : Set S → Set S), IsLinearInflation Γ₁ Γ₂ σv σe ∧
      ∀ e ∈ Γ₁.E, φ₁ e ≤ φ₂ (σe e) := by
  classical
  have : T2Space S := hS.2.1
  have hcuffO : ∀ Θ ∈ cuffs S, IsOArc Θ := (cuff_statement.{u} S hS).2.2
  have hinf : IsInflation Γ₁' Γ₂' σv' σe' := hσ.isInflation
  have hlin : IsLinearInflation Γ₁' Γ₂' σv' σe' := hσ.isLinear
  have hp : ∀ e, ∃ f, e ∈ Γ₁.E → f ∈ Γ₂.E ∧ (tilde f).ncard = (tilde e).ncard ∧ φ₁ e ≤ φ₂ f ∧
      σe' (IsThinning.edge Γ₁ h₁ s₁ e) = IsThinning.edge Γ₂ h₂ s₂ f ∧
      SameDir Γ₁ Γ₁' Γ₂ Γ₂' h₁ h₂ e f (IsThinning.edge Γ₁ h₁ s₁ e) (IsThinning.edge Γ₂ h₂ s₂ f)
        := by
    intro e
    by_cases he : e ∈ Γ₁.E
    · obtain ⟨f, hf⟩ := exists_partner hS hc T₁ T₂ hshort hσ he
      exact ⟨f, fun _ ↦ hf⟩
    · exact ⟨e, fun h ↦ absurd h he⟩
  choose σe hσe using hp
  let σv : S → Set S := fun v ↦ h₂.symm '' σv' (h₁ v)
  have hV₁ : ∀ {v}, v ∈ Γ₁.V → h₁ v ∈ Γ₁'.V := fun hv ↦ T₁.V_eq ▸ mem_image_of_mem _ hv
  have hsym : ∀ {X : Set S} {x}, h₂ x ∈ X → x ∈ h₂.symm '' X := fun {X x} hx ↦
    ⟨h₂ x, hx, by simp⟩
  have hbd₁ : ∀ {e}, e ∈ Γ₁.E → Painting.IsBorder e → IsThinning.edge Γ₁ h₁ s₁ e = h₁ '' e :=
    fun he hb ↦ IsThinning.edge_two (size_two_of_border Γ₁ he hb)
  have hlen : ∀ e ∈ Γ₁.E, (Γ₂.γ (σe e)).length = (Γ₁.γ e).length := fun e he ↦ by
    rw [Γ₂.length_γ (hσe e he).1, Γ₁.length_γ he, (hσe e he).2.1]
  have hends : ∀ e ∈ Γ₁.E, ∀ (i : ℕ) (hi : i < (Γ₁.γ e).length)
      (hi' : i < (Γ₂.γ (σe e)).length), (Γ₂.γ (σe e))[i] ∈ σv (Γ₁.γ e)[i] := by
    intro e he i hi hi'
    obtain ⟨hf, -, -, hz, hdir⟩ := hσe e he
    have hmemy := T₁.edge_mem he
    have key := fun (j : ℕ) (a b : S) ↦ ends_getElem? (i := j) (a := a) (b := b) hinf hmemy
    rw [hz] at key
    rcases hdir with ⟨h₁', h₂'⟩ | ⟨h₁', h₂', -⟩
    · rw [h₁', h₂'] at key
      exact hsym (key i _ _ (by simp [List.getElem?_eq_getElem hi])
        (by simp [List.getElem?_eq_getElem hi']))
    · rw [h₁', h₂'] at key
      have hl := hlen e he
      have hj : (Γ₁.γ e).length - 1 - i < (Γ₁.γ e).length := by omega
      have hindex : (Γ₁.γ e).length - 1 - ((Γ₁.γ e).length - 1 - i) = i := by omega
      refine hsym (key ((Γ₁.γ e).length - 1 - i) _ _ ?_ ?_)
      · rw [List.getElem?_reverse (by simpa using hj), List.length_map, hindex]
        simp [List.getElem?_eq_getElem hi]
      · rw [List.getElem?_reverse (by simpa [hl] using hj), List.length_map, hl, hindex]
        simp [List.getElem?_eq_getElem hi']
  have hinfl : IsInflation Γ₁ Γ₂ σv σe :=
    { edge_mem := fun e he ↦ (hσe e he).1
      edge_size := fun e he ↦ (hσe e he).2.1
      edge_injOn := fun e₁ h₁e e₂ h₂e heq ↦ by
        have hz₁ := (hσe e₁ h₁e).2.2.2.1
        have hz₂ := (hσe e₂ h₂e).2.2.2.1
        rw [heq, ← hz₂] at hz₁
        exact T₁.edge_inj h₁e h₂e (hinf.edge_injOn (T₁.edge_mem h₁e) (T₁.edge_mem h₂e) hz₁)
      vertex_nonempty := fun v hv ↦ (hinf.vertex_nonempty _ (hV₁ hv)).image _
      vertex_subset := fun v hv ↦ by
        rintro _ ⟨x, hx, rfl⟩
        have hx' := hinf.vertex_subset _ (hV₁ hv) hx
        rw [T₂.V_eq] at hx'
        obtain ⟨y, hy, rfl⟩ := hx'
        simpa using hy
      vertex_connected := fun v hv ↦ by
        have hpre := hinf.vertex_connected _ (hV₁ hv)
        let ψ : (Γ₂'.skAdj.induce (σv' (h₁ v))) →g (Γ₂.skAdj.induce (σv v)) :=
          { toFun := fun a ↦ ⟨h₂.symm a.1, mem_image_of_mem _ a.2⟩
            map_rel' := fun {a b} hab ↦ T₂.skAdj_symm hab }
        have hsurj : Surjective ψ := by
          rintro ⟨_, a, ha, rfl⟩
          exact ⟨⟨a, ha⟩, rfl⟩
        exact hpre.map ψ hsurj
      vertex_disjoint := fun v₁ hv₁ v₂ hv₂ hne ↦ by
        have := hinf.vertex_disjoint _ (hV₁ hv₁) _ (hV₁ hv₂) (h₁.injective.ne hne)
        exact (disjoint_image_iff h₂.symm.injective).2 this
      ends := hends }
  refine ⟨σv, σe, ⟨hinfl, ?_, ?_, ?_⟩, fun e he ↦ (hσe e he).2.2.1⟩
  · intro e he Θ hΘ
    have hbdΘ : Θ ⊆ bd S := by
      obtain ⟨z, -, rfl⟩ := hΘ
      exact connectedComponentIn_subset _ _
    have hborder : ∀ {E : Set S}, (E ∩ Θ).Nonempty → Painting.IsBorder E := fun ⟨x, hx, hxΘ⟩ ↦
      ⟨x, hx, hbdΘ hxΘ⟩
    rcases Γ₁.size_cases he with h2 | h3
    · have hf := hσe e he
      have hf2 : (tilde (σe e)).ncard = 2 := hf.2.1.trans h2
      have hz := hf.2.2.2.1
      rw [IsThinning.edge_two h2, IsThinning.edge_two hf2] at hz
      have hiff := hlin.borders_iff _ (T₁.two e he h2) Θ hΘ
      rw [hz] at hiff
      have himg := fun {α : S ≃ₜ S} {E : Set S} hα hα' =>
        homeomorph_preserves_cuff_meets (α := α) (E := E) hΘ (hcuffO Θ hΘ) hα hα'
      rw [himg T₁.null T₁.null_symm, himg (E := σe e) T₂.null T₂.null_symm]
      exact hiff
    · have h1 : ¬ (e ∩ Θ).Nonempty := fun hn ↦ by
        have := size_two_of_border Γ₁ he (hborder hn)
        omega
      have hf3 : (tilde (σe e)).ncard = 3 := (hσe e he).2.1.trans h3
      have h2' : ¬ (σe e ∩ Θ).Nonempty := fun hn ↦ by
        have := size_two_of_border Γ₂ (hσe e he).1 (hborder hn)
        omega
      exact iff_of_false h1 h2'
  · intro e' he' hb hne
    have h2 := size_two_of_border Γ₂ he' hb
    have hy' := T₂.two e' he' h2
    have hyb : Painting.IsBorder (h₂ '' e') := (isBorder_image h₂).2 hb
    have hnot : h₂ '' e' ∉ σe' '' Γ₁'.E := by
      rintro ⟨c, hc, hcz⟩
      have hcsize : (tilde c).ncard = 2 := by
        rw [← hinf.edge_size c hc, hcz, ncard_tilde_image, h2]
      rcases thinColour_cases (φ := φ₁) (x₀ := x₀) T₁ hc hcsize with hs | ⟨e, he, he2, rfl, -⟩ |
        hlab
      · obtain ⟨e, he, rfl⟩ := T₁.short c hs
        have he2 : (tilde e).ncard = 2 := by rw [← ncard_tilde_image h₁, hcsize]
        refine hne ⟨e, he, ?_⟩
        have hz := (hσe e he).2.2.2.1
        have hf2 : (tilde (σe e)).ncard = 2 := (hσe e he).2.1.trans he2
        rw [IsThinning.edge_two he2, IsThinning.edge_two hf2, hcz] at hz
        exact (image_injective.2 h₂.injective hz).symm
      · refine hne ⟨e, he, ?_⟩
        have hz := (hσe e he).2.2.2.1
        have hf2 : (tilde (σe e)).ncard = 2 := (hσe e he).2.1.trans he2
        rw [IsThinning.edge_two he2, IsThinning.edge_two hf2, hcz] at hz
        exact (image_injective.2 h₂.injective hz).symm
      · have hcint : Painting.IsInternal c := by
          rcases T₁.rest c hc hcsize with ⟨e, he, he2, rfl⟩ | ⟨hi, -⟩
          · exfalso
            by_cases hs : h₁ '' e ∈ Φ.shortSides
            · rw [thinColour_short T₁ hs] at hlab
              simp at hlab
            · rw [thinColour_two T₁ he he2 hs] at hlab
              simp only at hlab
              split_ifs at hlab <;> simp at hlab
          · exact hi
        have hle : (thinColour Φ Γ₁ Γ₁' h₁ s₁ φ₁ x₀ c).1 ≤
            (thinColour Φ Γ₂ Γ₂' h₂ s₂ φ₂ x₀ (σe' c)).1 ∧
            (thinColour Φ Γ₁ Γ₁' h₁ s₁ φ₁ x₀ c).2 =
            (thinColour Φ Γ₂ Γ₂' h₂ s₂ φ₂ x₀ (σe' c)).2 :=
          hσ.le_internal_2 c hc hcint hcsize
        have hl := hle.2
        rw [hlab, hcz] at hl
        by_cases hs : h₂ '' e' ∈ Φ.shortSides
        · rw [thinColour_short T₂ hs] at hl
          simp at hl
        · rw [thinColour_two T₂ he' h2 hs] at hl
          have hni : ¬ Painting.IsInternal (h₂ '' e') := fun hi ↦
            (isInternal_iff_not_border.1 hi) hyb
          simp only [hni, ite_false] at hl
          split_ifs at hl <;> simp at hl
    obtain ⟨v', hv', hsub⟩ := hlin.border_edge _ hy' hyb hnot
    rw [T₁.V_eq] at hv'
    obtain ⟨v, hv, rfl⟩ := hv'
    refine ⟨v, hv, fun x hx ↦ ?_⟩
    exact hsym (hsub (by rw [tilde_image_homeo]; exact mem_image_of_mem _ hx))
  · intro e he Θ hΘ hne f n n' hn hn' hip
    have hbdΘ : Θ ⊆ bd S := by
      obtain ⟨z, -, rfl⟩ := hΘ
      exact connectedComponentIn_subset _ _
    obtain ⟨x, hxe, hxΘ⟩ := hne
    have hb : Painting.IsBorder e := ⟨x, hxe, hbdΘ hxΘ⟩
    have h2 := size_two_of_border Γ₁ he hb
    obtain ⟨hf, hf2', -, hz, hdir⟩ := hσe e he
    have hf2 : (tilde (σe e)).ncard = 2 := hf2'.trans h2
    rw [IsThinning.edge_two h2, IsThinning.edge_two hf2] at hz
    rw [IsThinning.edge_two h2, IsThinning.edge_two hf2] at hdir
    have hyΘ : (h₁ '' e ∩ Θ).Nonempty :=
      ⟨h₁ x, mem_image_of_mem _ hxe, null_mem T₁.null hΘ (hcuffO Θ hΘ) hxΘ⟩
    have hback : ∀ {g : Circle ≃ₜ Θ} {m : S}, ImmediatelyPrecedes g (h₂ m) (h₂ '' σe e) →
        ImmediatelyPrecedes g m (σe e) := fun {g m} hi ↦ by
      have := ImmediatelyPrecedes.null T₂.null_symm hΘ hi
      simpa [image_image] using this
    rcases hdir with ⟨h₁', h₂'⟩ | ⟨h₁', h₂', -⟩
    · refine hback (hz ▸ hlin.orientation _ (T₁.two e he h2) Θ hΘ hyΘ f (h₁ n) (h₂ n') ?_ ?_
        (ImmediatelyPrecedes.null T₁.null hΘ hip))
      · rw [h₁', List.head?_map, hn]
        rfl
      · rw [hz, h₂', List.head?_map, hn']
        rfl
    · have hlen₁ : (Γ₁.γ e).length = 2 := by rw [Γ₁.length_γ he, h2]
      have hlen₂ : (Γ₂.γ (σe e)).length = 2 := by rw [Γ₂.length_γ hf, hf2]
      obtain ⟨a, m, hl₁⟩ := List.length_eq_two.1 hlen₁
      obtain ⟨a', m', hl₂⟩ := List.length_eq_two.1 hlen₂
      rw [hl₁] at hn h₁'
      rw [hl₂] at hn' h₂'
      simp only [List.head?_cons, Option.some.injEq] at hn hn'
      subst hn hn'
      have hnd₁ := Γ₁.γ_nodup e he
      have hnd₂ := Γ₂.γ_nodup _ hf
      rw [hl₁] at hnd₁
      rw [hl₂] at hnd₂
      have hmt : m ∈ tilde e := by
        rw [← Γ₁.γ_set e he, hl₁]
        simp
      have hat : a' ∈ tilde (σe e) := by
        rw [← Γ₂.γ_set _ hf, hl₂]
        simp
      have hne₁ : m ≠ a := fun h ↦ by simp [h] at hnd₁
      have hne₂ : a' ≠ m' := fun h ↦ by simp [h] at hnd₂
      have step₁ := ImmediatelyPrecedes.null T₁.null hΘ (hip.reverse hmt hne₁)
      have step₂ := hlin.orientation _ (T₁.two e he h2) Θ hΘ hyΘ (revParam f) (h₁ m) (h₂ m')
        (by rw [h₁']; simp) (by rw [hz, h₂']; simp) step₁
      rw [hz] at step₂
      have step₃ := (hback step₂).reverse hat hne₂
      rwa [revParam_revParam] at step₃

end Pull

end GraphMinor.GM19
