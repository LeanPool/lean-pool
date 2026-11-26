/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.JordanDomain
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Cutting a Jordan domain along a cross-cut

For an `O`-arc `F` in the complex plane, `inner F` is the bounded component of the complement and
`outer F` the unbounded one. `theta_cut` is the theta curve lemma: if `F = A₁ ∪ A₂`, and `c` is an
arc with its open part in `inner F` and with the same ends as `A₁` and `A₂`, then `inner F` minus
`c` is the disjoint union of `inner (A₁ ∪ c)` and `inner (A₂ ∪ c)`. The proof uses the frontier
property of the Jordan curve theorem and Janiszewski's theorem.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

/-- The bounded part of the complement of `F`. -/
def inner (F : Set ℂ) : Set ℂ := {z | z ∉ F ∧ Bornology.IsBounded (connectedComponentIn Fᶜ z)}

/-- The unbounded part of the complement of `F`. -/
def outer (F : Set ℂ) : Set ℂ := {z | z ∉ F ∧ ¬ Bornology.IsBounded (connectedComponentIn Fᶜ z)}

/-- The facts of the Jordan curve theorem in terms of `inner` and `outer`, gathered for use in this
file. `isJordanParts` proves them for every `O`-arc. -/
structure IsJordanParts (F : Set ℂ) : Prop where
  isOpen_inner : IsOpen (inner F)
  isOpen_outer : IsOpen (outer F)
  isConnected_inner : IsConnected (inner F)
  isConnected_outer : IsConnected (outer F)
  isBounded_inner : Bornology.IsBounded (inner F)
  not_isBounded_outer : ¬ Bornology.IsBounded (outer F)
  disjoint : Disjoint (inner F) (outer F)
  union_eq : inner F ∪ outer F = Fᶜ
  frontier_inner : frontier (inner F) = F
  frontier_outer : frontier (outer F) = F
  isCompact : IsCompact F

/-- The Jordan curve theorem in terms of `inner` and `outer`. -/
theorem isJordanParts {F : Set ℂ} (φ : Circle ≃ₜ F) : IsJordanParts F := by
  obtain ⟨A, B, ⟨hne, hcomp, hAf, hBf⟩, hAb, hBb⟩ := jordan_complex φ
  rw [← compl_eq_univ_sdiff] at hcomp
  have hFc := isCompact_of_oArc φ
  have hAmem : A ∈ componentsIn Fᶜ := by rw [hcomp]; simp
  have hBmem : B ∈ componentsIn Fᶜ := by rw [hcomp]; simp
  obtain ⟨a, ha, rfl⟩ := hAmem
  obtain ⟨b, hb, rfl⟩ := hBmem
  have hsplit : ∀ z, z ∉ F → connectedComponentIn Fᶜ z = connectedComponentIn Fᶜ a ∨
      connectedComponentIn Fᶜ z = connectedComponentIn Fᶜ b := by
    intro z hz
    have : connectedComponentIn Fᶜ z ∈ componentsIn Fᶜ := mem_image_of_mem _ hz
    rw [hcomp] at this
    exact this
  have hinner : inner F = connectedComponentIn Fᶜ a := by
    ext z
    constructor
    · rintro ⟨hz, hzb⟩
      rcases hsplit z hz with h | h
      · exact h ▸ mem_connectedComponentIn hz
      · exact absurd (h ▸ hzb) hBb
    · intro hz
      have hzF : z ∉ F := connectedComponentIn_subset _ _ hz
      exact ⟨hzF, by rw [← connectedComponentIn_eq hz]; exact hAb⟩
  have houter : outer F = connectedComponentIn Fᶜ b := by
    ext z
    constructor
    · rintro ⟨hz, hzb⟩
      rcases hsplit z hz with h | h
      · exact absurd (h ▸ hAb) hzb
      · exact h ▸ mem_connectedComponentIn hz
    · intro hz
      have hzF : z ∉ F := connectedComponentIn_subset _ _ hz
      exact ⟨hzF, by rw [← connectedComponentIn_eq hz]; exact hBb⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hFc⟩
  · rw [hinner]; exact isOpen_component hFc.isClosed a
  · rw [houter]; exact isOpen_component hFc.isClosed b
  · rw [hinner]; exact isConnected_connectedComponentIn_iff.mpr ha
  · rw [houter]; exact isConnected_connectedComponentIn_iff.mpr hb
  · rw [hinner]; exact hAb
  · rw [houter]; exact hBb
  · exact Set.disjoint_left.mpr fun z h1 h2 => h2.2 h1.2
  · ext z
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hz
      by_cases hb' : Bornology.IsBounded (connectedComponentIn Fᶜ z)
      · exact Or.inl ⟨hz, hb'⟩
      · exact Or.inr ⟨hz, hb'⟩
  · rw [hinner]; exact hAf
  · rw [houter]; exact hBf

namespace IsJordanParts

variable {F : Set ℂ}

theorem inner_subset_compl (_h : IsJordanParts F) : inner F ⊆ Fᶜ := fun _ hz => hz.1

theorem outer_subset_compl (_h : IsJordanParts F) : outer F ⊆ Fᶜ := fun _ hz => hz.1

theorem closure_inner (h : IsJordanParts F) : closure (inner F) = inner F ∪ F := by
  rw [closure_eq_self_union_frontier, h.frontier_inner]

theorem closure_outer (h : IsJordanParts F) : closure (outer F) = outer F ∪ F := by
  rw [closure_eq_self_union_frontier, h.frontier_outer]

theorem isCompact_closure_inner (h : IsJordanParts F) : IsCompact (inner F ∪ F) :=
  h.closure_inner ▸ h.isBounded_inner.isCompact_closure

/-- A preconnected set that misses `F` and meets `outer F` lies in `outer F`. -/
theorem subset_outer (h : IsJordanParts F) {C : Set ℂ} (hC : IsPreconnected C) (hF : Disjoint C F)
    (hne : (C ∩ outer F).Nonempty) : C ⊆ outer F := by
  have hsub : C ⊆ inner F ∪ outer F := by
    rw [h.union_eq]
    exact fun z hz hzF => Set.disjoint_left.mp hF hz hzF
  have := hC.subset_right_of_subset_union h.isOpen_inner h.isOpen_outer h.disjoint hsub hne
  exact this

/-- A preconnected set that misses `F` and meets `inner F` lies in `inner F`. -/
theorem subset_inner (h : IsJordanParts F) {C : Set ℂ} (hC : IsPreconnected C) (hF : Disjoint C F)
    (hne : (C ∩ inner F).Nonempty) : C ⊆ inner F := by
  have hsub : C ⊆ inner F ∪ outer F := by
    rw [h.union_eq]
    exact fun z hz hzF => Set.disjoint_left.mp hF hz hzF
  exact hC.subset_left_of_subset_union h.isOpen_inner h.isOpen_outer h.disjoint hsub hne

/-- A point of `F'` that is no point of `F`, and a limit of `outer F`, lies in `outer F`. -/
theorem mem_outer_of_mem_closure (h : IsJordanParts F) {z : ℂ} (hz : z ∈ closure (outer F))
    (hzF : z ∉ F) : z ∈ outer F := by
  rw [h.closure_outer] at hz
  exact hz.resolve_right hzF

end IsJordanParts

/-- The data of a theta curve: three arcs with common ends `p, q`, the arc `c` inside `F`. -/
structure IsTheta (F F₁ F₂ A₁ A₂ c : Set ℂ) (p q : ℂ) : Prop where
  parts : IsJordanParts F
  parts₁ : IsJordanParts F₁
  parts₂ : IsJordanParts F₂
  eq : F = A₁ ∪ A₂
  eq₁ : F₁ = A₁ ∪ c
  eq₂ : F₂ = A₂ ∪ c
  meet : A₁ ∩ A₂ ⊆ {p, q}
  ends : p ∈ c ∧ q ∈ c
  inside : c \ {p, q} ⊆ inner F
  ends₁ : p ∈ F ∧ q ∈ F
  conn : IsPreconnected c
  ne₁ : (A₁ \ {p, q}).Nonempty
  ne₂ : (A₂ \ {p, q}).Nonempty

namespace IsTheta

variable {F F₁ F₂ A₁ A₂ c : Set ℂ} {p q : ℂ}

/-- The theta curve with the two sides exchanged. -/
theorem symm (h : IsTheta F F₁ F₂ A₁ A₂ c p q) : IsTheta F F₂ F₁ A₂ A₁ c p q where
  parts := h.parts
  parts₁ := h.parts₂
  parts₂ := h.parts₁
  eq := by rw [h.eq, union_comm]
  eq₁ := h.eq₂
  eq₂ := h.eq₁
  meet := by rw [inter_comm]; exact h.meet
  ends := h.ends
  inside := h.inside
  ends₁ := h.ends₁
  conn := h.conn
  ne₁ := h.ne₂
  ne₂ := h.ne₁

theorem c_disjoint_outer (h : IsTheta F F₁ F₂ A₁ A₂ c p q) : Disjoint c (outer F) := by
  refine Set.disjoint_left.mpr fun z hz hzo => ?_
  by_cases hpq : z ∈ ({p, q} : Set ℂ)
  · rcases hpq with rfl | hpq
    · exact hzo.1 h.ends₁.1
    · rw [mem_singleton_iff.mp hpq] at hzo
      exact hzo.1 h.ends₁.2
  · exact Set.disjoint_left.mp h.parts.disjoint (h.inside ⟨hz, hpq⟩) hzo

theorem outer_subset₁ (h : IsTheta F F₁ F₂ A₁ A₂ c p q) : outer F ⊆ outer F₁ := by
  have hdisj : Disjoint (outer F) F₁ := by
    rw [h.eq₁, Set.disjoint_union_right]
    refine ⟨Set.disjoint_left.mpr fun z hz hzA => hz.1 ?_, h.c_disjoint_outer.symm⟩
    rw [h.eq]
    exact Or.inl hzA
  have hsub : outer F ⊆ inner F₁ ∪ outer F₁ := by
    rw [h.parts₁.union_eq]
    exact fun z hz hzF => Set.disjoint_left.mp hdisj hz hzF
  by_contra hcon
  have hin : outer F ⊆ inner F₁ := by
    refine h.parts.isConnected_outer.isPreconnected.subset_left_of_subset_union
      h.parts₁.isOpen_inner h.parts₁.isOpen_outer h.parts₁.disjoint hsub ?_
    obtain ⟨z, hz, hzn⟩ := not_subset.mp hcon
    exact ⟨z, hz, (hsub hz).resolve_right hzn⟩
  exact h.parts.not_isBounded_outer (h.parts₁.isBounded_inner.subset hin)

/-- The open arc on the other side lies outside `F₁`. -/
theorem open_arc_subset_outer (h : IsTheta F F₁ F₂ A₁ A₂ c p q) : A₂ \ {p, q} ⊆ outer F₁ := by
  rintro z ⟨hzA, hz⟩
  have hzF : z ∈ F := by rw [h.eq]; exact Or.inr hzA
  have hcl : z ∈ closure (outer F) := h.parts.frontier_outer.symm ▸ hzF |> frontier_subset_closure
  refine h.parts₁.mem_outer_of_mem_closure (closure_mono h.outer_subset₁ hcl) ?_
  rw [h.eq₁]
  rintro (h1 | h1)
  · exact hz (h.meet ⟨h1, hzA⟩)
  · exact (Set.disjoint_left.mp h.parts.disjoint (h.inside ⟨h1, hz⟩)) (by
      exact absurd hzF ((h.inside ⟨h1, hz⟩).1))

theorem inner_disjoint_F (h : IsTheta F F₁ F₂ A₁ A₂ c p q) : Disjoint (inner F₁) F := by
  refine Set.disjoint_left.mpr fun z hz hzF => ?_
  rw [h.eq] at hzF
  have hzF₁ : z ∉ F₁ := hz.1
  rcases hzF with hzA | hzA
  · exact hzF₁ (h.eq₁ ▸ Or.inl hzA)
  · by_cases hpq : z ∈ ({p, q} : Set ℂ)
    · rcases hpq with rfl | hpq
      · exact hzF₁ (h.eq₁ ▸ Or.inr h.ends.1)
      · rw [mem_singleton_iff.mp hpq] at hzF₁
        exact hzF₁ (h.eq₁ ▸ Or.inr h.ends.2)
    · exact Set.disjoint_left.mp h.parts₁.disjoint hz (h.open_arc_subset_outer ⟨hzA, hpq⟩)

/-- Each part lies in `inner F`. -/
theorem inner_subset₁ (h : IsTheta F F₁ F₂ A₁ A₂ c p q) : inner F₁ ⊆ inner F := by
  intro z hz
  have hzF : z ∉ F := fun hzF => Set.disjoint_left.mp h.inner_disjoint_F hz hzF
  have hzU : z ∈ inner F ∪ outer F := by rw [h.parts.union_eq]; exact hzF
  refine hzU.resolve_right fun hzo => ?_
  exact Set.disjoint_left.mp h.parts₁.disjoint hz (h.outer_subset₁ hzo)

/-- The two parts are disjoint. -/
theorem disjoint_inner (h : IsTheta F F₁ F₂ A₁ A₂ c p q) : Disjoint (inner F₁) (inner F₂) := by
  have hsub : inner F₁ ⊆ outer F₂ := by
    obtain ⟨a, ha⟩ := h.ne₁
    have haA : a ∈ A₁ := ha.1
    have hao : a ∈ outer F₂ := h.symm.open_arc_subset_outer ha
    have hfr : a ∈ frontier (inner F₁) := by
      rw [h.parts₁.frontier_inner, h.eq₁]
      exact Or.inl haA
    have hcl : a ∈ closure (inner F₁) := frontier_subset_closure hfr
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp hcl _ h.parts₂.isOpen_outer hao
    refine h.parts₂.subset_outer h.parts₁.isConnected_inner.isPreconnected ?_ ⟨z, hz2, hz1⟩
    refine Set.disjoint_left.mpr fun w hw hwF => ?_
    rw [h.eq₂] at hwF
    rcases hwF with hwA | hwc
    · exact Set.disjoint_left.mp h.inner_disjoint_F hw (h.eq ▸ Or.inr hwA)
    · exact hw.1 (h.eq₁ ▸ Or.inr hwc)
  exact Set.disjoint_left.mpr fun z h1 h2 =>
    Set.disjoint_left.mp h.parts₂.disjoint h2 (hsub h1)

theorem inter_eq (h : IsTheta F F₁ F₂ A₁ A₂ c p q) : F₁ ∩ F₂ = c := by
  ext z
  constructor
  · rintro ⟨h1, h2⟩
    rw [h.eq₁] at h1
    rw [h.eq₂] at h2
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · rcases h.meet ⟨h1, h2⟩ with rfl | h3
        · exact h.ends.1
        · rw [mem_singleton_iff.mp h3]
          exact h.ends.2
      · exact h2
    · exact h1
  · intro hz
    exact ⟨h.eq₁ ▸ Or.inr hz, h.eq₂ ▸ Or.inr hz⟩

/-- **Theta curve lemma.** `inner F` minus the cross-cut is the union of the two parts. -/
theorem inner_sdiff (h : IsTheta F F₁ F₂ A₁ A₂ c p q) : inner F \ c = inner F₁ ∪ inner F₂ := by
  ext z
  constructor
  · rintro ⟨hz, hzc⟩
    have hzF : z ∉ F := hz.1
    have hz1 : z ∉ F₁ := by
      rw [h.eq₁]
      rintro (h1 | h1)
      · exact hzF (h.eq ▸ Or.inl h1)
      · exact hzc h1
    have hz2 : z ∉ F₂ := by
      rw [h.eq₂]
      rintro (h1 | h1)
      · exact hzF (h.eq ▸ Or.inr h1)
      · exact hzc h1
    by_contra hcon
    rw [mem_union, not_or] at hcon
    have hzo1 : z ∈ outer F₁ :=
      (show z ∈ inner F₁ ∪ outer F₁ by rw [h.parts₁.union_eq]; exact hz1).resolve_left hcon.1
    have hzo2 : z ∈ outer F₂ :=
      (show z ∈ inner F₂ ∪ outer F₂ by rw [h.parts₂.union_eq]; exact hz2).resolve_left hcon.2
    obtain ⟨w, hw⟩ := h.parts.isConnected_outer.nonempty
    have hw1 := h.outer_subset₁ hw
    have hw2 := h.symm.outer_subset₁ hw
    have hcomp : ∀ {G : Set ℂ}, IsJordanParts G → z ∈ outer G → w ∈ outer G →
        w ∈ connectedComponentIn Gᶜ z := fun hG hz' hw' =>
      hG.isConnected_outer.isPreconnected.subset_connectedComponentIn hz' hG.outer_subset_compl hw'
    have hK : IsPreconnected (F₁ ∩ F₂) := by rw [h.inter_eq]; exact h.conn
    have hunion : F ⊆ F₁ ∪ F₂ := by
      rw [h.eq, h.eq₁, h.eq₂]
      exact union_subset_union subset_union_left subset_union_left
    have hmain := janiszewski h.parts₁.isCompact h.parts₂.isCompact hK
      (fun hh => hh.elim hz1 hz2) (fun hh => hh.elim hw1.1 hw2.1)
      (hcomp h.parts₁ hzo1 hw1) (hcomp h.parts₂ hzo2 hw2)
    have hC : IsPreconnected (connectedComponentIn (F₁ ∪ F₂)ᶜ z) :=
      isPreconnected_connectedComponentIn
    have hdisj : Disjoint (connectedComponentIn (F₁ ∪ F₂)ᶜ z) F :=
      Set.disjoint_left.mpr fun y hy hyF => connectedComponentIn_subset _ _ hy (hunion hyF)
    have hout := h.parts.subset_outer hC hdisj ⟨w, hmain, hw⟩
    exact Set.disjoint_left.mp h.parts.disjoint hz
      (hout (mem_connectedComponentIn fun hh => hh.elim hz1 hz2))
  · rintro (hz | hz)
    · exact ⟨h.inner_subset₁ hz, fun hc => hz.1 (h.eq₁ ▸ Or.inr hc)⟩
    · exact ⟨h.symm.inner_subset₁ hz, fun hc => hz.1 (h.eq₂ ▸ Or.inr hc)⟩

end IsTheta

local notation "𝕀" => unitInterval

/-- `e` is an injective path. -/
def IsArcMap {X : Type*} [TopologicalSpace X] (e : 𝕀 → X) : Prop :=
  Continuous e ∧ Function.Injective e

/-- The range of an injective path `a` and the range of an injective path `b` with the same ends,
meeting only in the ends, form an `O`-arc. The upper half of the circle goes to `a` and the lower
half to `b`, with the parameter read off the real part. -/
theorem oArc_of_two_arcs {X : Type*} [TopologicalSpace X] [T2Space X] {a b : 𝕀 → X}
    (ha : IsArcMap a) (hb : IsArcMap b) (h0 : a 0 = b 0) (h1 : a 1 = b 1)
    (h01 : ∀ s t, a s = b t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) :
    Nonempty (Circle ≃ₜ (range a ∪ range b : Set X)) := by
  classical
  have hbd : ∀ w : Circle, |(w : ℂ).re| ≤ 1 := fun w => by
    have := Complex.abs_re_le_norm (w : ℂ)
    rwa [Circle.norm_coe] at this
  let τ : Circle → 𝕀 := fun w => ⟨(1 - (w : ℂ).re) / 2, by
    have := abs_le.mp (hbd w)
    constructor <;> linarith [this.1, this.2]⟩
  have hτ : Continuous τ := by
    refine Continuous.subtype_mk ?_ _
    have : Continuous fun w : Circle => (w : ℂ) := continuous_subtype_val
    exact ((continuous_const.sub (Complex.continuous_re.comp this)).div_const 2)
  let g : Circle → X := fun w => if 0 ≤ (w : ℂ).im then a (τ w) else b (τ w)
  have him : Continuous fun w : Circle => (w : ℂ).im :=
    Complex.continuous_im.comp continuous_subtype_val
  have hsq : ∀ w : Circle, (w : ℂ).re * (w : ℂ).re + (w : ℂ).im * (w : ℂ).im = 1 := fun w => by
    have h := Complex.sq_norm (w : ℂ)
    rw [Circle.norm_coe, Complex.normSq_apply] at h
    linarith
  have hτ0 : ∀ w : Circle, (w : ℂ).im = 0 → τ w = 0 ∨ τ w = 1 := by
    intro w hw
    have h := hsq w
    rw [hw] at h
    have hfac : ((w : ℂ).re - 1) * ((w : ℂ).re + 1) = 0 := by linarith
    rcases mul_eq_zero.mp hfac with h1 | h1
    · left
      refine Subtype.ext ?_
      change (1 - (w : ℂ).re) / 2 = 0
      rw [sub_eq_zero.mp h1]
      norm_num
    · right
      refine Subtype.ext ?_
      change (1 - (w : ℂ).re) / 2 = 1
      rw [eq_neg_of_add_eq_zero_left h1]
      norm_num
  have hg : Continuous g := by
    refine Continuous.if_le (ha.1.comp hτ) (hb.1.comp hτ) continuous_const him ?_
    intro w hw
    rcases hτ0 w hw.symm with h | h
    · simp only [h, h0]
    · simp only [h, h1]
  have hre : ∀ {w w' : Circle}, τ w = τ w' → (w : ℂ).re = (w' : ℂ).re := fun {w w'} h => by
    have : (1 - (w : ℂ).re) / 2 = (1 - (w' : ℂ).re) / 2 := congrArg Subtype.val h
    linarith
  have hsame : ∀ {w w' : Circle}, τ w = τ w' → 0 ≤ (w : ℂ).im → 0 ≤ (w' : ℂ).im → w = w' := by
    intro w w' h h1 h2
    have h3 := hre h
    have h4 := hsq w
    have h5 := hsq w'
    rw [h3] at h4
    have h6 : (w : ℂ).im = (w' : ℂ).im := by nlinarith [mul_self_nonneg ((w : ℂ).im - (w' : ℂ).im)]
    exact Circle.ext (Complex.ext h3 h6)
  have hsameneg : ∀ {w w' : Circle}, τ w = τ w' → (w : ℂ).im < 0 → (w' : ℂ).im < 0 → w = w' := by
    intro w w' h h1 h2
    have h3 := hre h
    have h4 := hsq w
    have h5 := hsq w'
    rw [h3] at h4
    have h6 : (w : ℂ).im = (w' : ℂ).im := by nlinarith [mul_self_nonneg ((w : ℂ).im - (w' : ℂ).im)]
    exact Circle.ext (Complex.ext h3 h6)
  -- The two points with parameter `0` and `1` lie on the real axis.
  have him0 : ∀ {w : Circle}, τ w = 0 ∨ τ w = 1 → (w : ℂ).im = 0 := by
    intro w h
    have h4 := hsq w
    have hre1 : (w : ℂ).re = 1 ∨ (w : ℂ).re = -1 := by
      rcases h with h | h
      · left
        have : (1 - (w : ℂ).re) / 2 = 0 := congrArg Subtype.val h
        linarith
      · right
        have : (1 - (w : ℂ).re) / 2 = 1 := congrArg Subtype.val h
        linarith
    rcases hre1 with h1 | h1 <;> rw [h1] at h4 <;> nlinarith [mul_self_nonneg (w : ℂ).im]
  have hmixed : ∀ {w w' : Circle}, 0 ≤ (w : ℂ).im → (w' : ℂ).im < 0 → a (τ w) = b (τ w') → False
    := by
    intro w w' h1 h2 h
    rcases h01 _ _ h with ⟨_, h3⟩ | ⟨_, h3⟩
    · exact absurd (him0 (Or.inl h3)) h2.ne
    · exact absurd (him0 (Or.inr h3)) h2.ne
  have hgi : Function.Injective g := by
    intro w w' h
    simp only [g] at h
    by_cases h1 : 0 ≤ (w : ℂ).im <;> by_cases h2 : 0 ≤ (w' : ℂ).im
    · simp only [h1, h2, ite_true] at h
      exact hsame (ha.2 h) h1 h2
    · simp only [h1, h2, ite_true, ite_false] at h
      exact (hmixed h1 (not_le.mp h2) h).elim
    · simp only [h1, h2, ite_true, ite_false] at h
      exact (hmixed h2 (not_le.mp h1) h.symm).elim
    · simp only [h1, h2, ite_false] at h
      exact hsameneg (hb.2 h) (not_le.mp h1) (not_le.mp h2)
  have hrange : range g = range a ∪ range b := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      by_cases h1 : 0 ≤ (w : ℂ).im
      · left
        simp only [g, h1, ite_true]
        exact ⟨_, rfl⟩
      · right
        simp only [g, h1, ite_false]
        exact ⟨_, rfl⟩
    · have hpt : ∀ t : 𝕀, ∃ w : Circle, τ w = t ∧ 0 ≤ (w : ℂ).im ∧
          ∃ w' : Circle, τ w' = t ∧ (w' : ℂ).im ≤ 0 := by
        intro t
        have ht0 := t.2.1
        have ht1 := t.2.2
        set x : ℝ := 1 - 2 * t with hx
        have hx2 : 0 ≤ 1 - x * x := by rw [hx]; nlinarith
        set y := Real.sqrt (1 - x * x) with hy
        have hy2 : y * y = 1 - x * x := Real.mul_self_sqrt hx2
        have hnorm : ∀ s : ℝ, s * s = y * y → ‖(⟨x, s⟩ : ℂ)‖ = 1 := by
          intro s hs
          have h := Complex.sq_norm (⟨x, s⟩ : ℂ)
          rw [Complex.normSq_mk, hs, hy2] at h
          have h3 : ‖(⟨x, s⟩ : ℂ)‖ ^ 2 = 1 ^ 2 := by rw [h]; ring
          exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp h3
        have hτt : ∀ (s : ℝ) (hs : ‖(⟨x, s⟩ : ℂ)‖ = 1),
            τ ⟨⟨x, s⟩, mem_sphere_zero_iff_norm.mpr hs⟩ = t := by
          intro s hs
          refine Subtype.ext ?_
          change (1 - x) / 2 = t
          rw [hx]
          ring
        refine ⟨⟨⟨x, y⟩, mem_sphere_zero_iff_norm.mpr (hnorm y rfl)⟩, hτt y (hnorm y rfl),
          Real.sqrt_nonneg _, ⟨⟨x, -y⟩, mem_sphere_zero_iff_norm.mpr (hnorm (-y) (by ring))⟩,
          hτt (-y) (hnorm (-y) (by ring)), ?_⟩
        change -y ≤ 0
        linarith [Real.sqrt_nonneg (1 - x * x)]
      rintro (⟨t, rfl⟩ | ⟨t, rfl⟩)
      · obtain ⟨w, hw, h1, -⟩ := hpt t
        exact ⟨w, by simp only [g, h1, ite_true, hw]⟩
      · obtain ⟨-, -, -, w, hw, hle⟩ := hpt t
        rcases eq_or_lt_of_le hle with h2 | h2
        · refine ⟨w, ?_⟩
          simp only [g, h2, le_refl, ite_true, hw]
          rcases hτ0 w h2 with h3 | h3
          · rw [← hw, h3, h0]
          · rw [← hw, h3, h1]
        · exact ⟨w, by simp only [g, not_le.mpr h2, ite_false, hw]⟩
  have hemb := (hg.isClosedEmbedding hgi).isEmbedding
  exact ⟨hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)⟩

/-- Two different points of an `O`-arc cut it into two arcs that meet only in the ends. -/
theorem exists_two_arcs {F : Set ℂ} (φ : Circle ≃ₜ F) {p q : ℂ} (hp : p ∈ F) (hq : q ∈ F)
    (hpq : p ≠ q) : ∃ a b : 𝕀 → ℂ, IsArcMap a ∧ IsArcMap b ∧ a 0 = p ∧ a 1 = q ∧ b 0 = p ∧ b 1 = q ∧
      range a ∪ range b = F ∧ (∀ s t, a s = b t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) := by
  have hpi := Real.pi_pos
  let t : Circle := φ.symm ⟨p, hp⟩
  let P : ℝ → ℂ := fun r => arcPoint φ t r
  have hPc : Continuous P := (continuous_arcPoint φ).comp (continuous_const.prodMk continuous_id)
  have hP0 : P 0 = p := by simp [P, arcPoint, t]
  have hP2 : P (2 * Real.pi) = p := by simp [P, arcPoint, t, Circle.exp_two_pi]
  have hexp : ∀ z (hz : z ∈ F), ∃ r, 0 ≤ r ∧ r ≤ 2 * Real.pi ∧ P r = z := by
    intro z hz
    obtain ⟨r, h1, h2, h3⟩ := exists_angle_near t (φ.symm ⟨z, hz⟩) 0 le_rfl hpi.le
    refine ⟨r, by simpa using h1, by simpa using h2, ?_⟩
    simp [P, arcPoint, ← h3]
  have hPinj : ∀ r r', 0 ≤ r → r ≤ 2 * Real.pi → 0 ≤ r' → r' ≤ 2 * Real.pi → P r = P r' →
      r = r' ∨ (r = 0 ∧ r' = 2 * Real.pi) ∨ (r = 2 * Real.pi ∧ r' = 0) := by
    intro r r' h1 h2 h3 h4 h
    have h5 : t * Circle.exp r = t * Circle.exp r' := φ.injective (Subtype.ext h)
    have h6 := mul_left_cancel h5
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h6
    have hle : (m : ℝ) * (2 * Real.pi) = r - r' := by linarith
    have hm1 : (m : ℝ) ≤ 1 := by
      by_contra hc
      rw [not_le] at hc
      nlinarith
    have hm2 : (-1 : ℝ) ≤ m := by
      by_contra hc
      rw [not_le] at hc
      nlinarith
    have hm3 : m ≤ 1 := by exact_mod_cast hm1
    have hm4 : -1 ≤ m := by exact_mod_cast hm2
    have hcases : m = -1 ∨ m = 0 ∨ m = 1 := by omega
    rcases hcases with rfl | rfl | rfl
    · right; left
      push_cast at hle
      constructor <;> nlinarith
    · left
      push_cast at hle
      linarith
    · right; right
      push_cast at hle
      constructor <;> nlinarith
  obtain ⟨θ, hθ0, hθ1, hθ⟩ := hexp q hq
  have hθpos : 0 < θ := lt_of_le_of_ne hθ0 fun h => hpq (by rw [← hP0, h, hθ])
  have hθlt : θ < 2 * Real.pi := lt_of_le_of_ne hθ1 fun h => hpq (by rw [← hP2, ← h, hθ])
  have hgap : 0 < 2 * Real.pi - θ := by linarith
  let a : 𝕀 → ℂ := fun s => P (θ * s)
  let b : 𝕀 → ℂ := fun s => P (2 * Real.pi - (2 * Real.pi - θ) * s)
  have hs0 : ∀ s : 𝕀, 0 ≤ (s : ℝ) ∧ (s : ℝ) ≤ 1 := fun s => ⟨s.2.1, s.2.2⟩
  have hab : ∀ s : 𝕀, 0 ≤ θ * s ∧ θ * s ≤ θ := fun s =>
    ⟨mul_nonneg hθ0 (hs0 s).1, by nlinarith [(hs0 s).2]⟩
  have hbb : ∀ s : 𝕀, θ ≤ 2 * Real.pi - (2 * Real.pi - θ) * s ∧
      2 * Real.pi - (2 * Real.pi - θ) * s ≤ 2 * Real.pi := fun s => by
    constructor <;> nlinarith [(hs0 s).1, (hs0 s).2]
  have hac : IsArcMap a := by
    refine ⟨hPc.comp (continuous_const.mul continuous_subtype_val), fun s s' h => ?_⟩
    rcases hPinj _ _ (hab s).1 (by linarith [(hab s).2]) (hab s').1 (by linarith [(hab s').2]) h
      with
      h1 | ⟨-, h1⟩ | ⟨h1, -⟩
    · exact Subtype.ext (mul_left_cancel₀ hθpos.ne' h1)
    · linarith [(hab s').2]
    · linarith [(hab s).2]
  have hbc : IsArcMap b := by
    refine ⟨hPc.comp (continuous_const.sub (continuous_const.mul continuous_subtype_val)),
      fun s s' h => ?_⟩
    rcases hPinj _ _ (by linarith [(hbb s).1]) (hbb s).2 (by linarith [(hbb s').1])
      (hbb s').2 h with
      h1 | ⟨h1, -⟩ | ⟨-, h1⟩
    · refine Subtype.ext (mul_left_cancel₀ hgap.ne' ?_)
      linarith
    · linarith [(hbb s).1]
    · linarith [(hbb s').1]
  refine ⟨a, b, hac, hbc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [a, Icc.coe_zero, mul_zero, hP0]
  · simp only [a, Icc.coe_one, mul_one, hθ]
  · simp only [b, Icc.coe_zero, mul_zero, sub_zero, hP2]
  · simp only [b, Icc.coe_one, mul_one, sub_sub_cancel, hθ]
  · ext z
    constructor
    · rintro (⟨s, rfl⟩ | ⟨s, rfl⟩) <;> exact (φ _).2
    · intro hz
      obtain ⟨r, h1, h2, rfl⟩ := hexp z hz
      by_cases hr : r ≤ θ
      · left
        refine ⟨⟨r / θ, div_nonneg h1 hθ0, (div_le_one hθpos).mpr hr⟩, ?_⟩
        simp only [a]
        rw [mul_div_cancel₀ _ hθpos.ne']
      · right
        rw [not_le] at hr
        refine ⟨⟨(2 * Real.pi - r) / (2 * Real.pi - θ), div_nonneg (by linarith) hgap.le,
          (div_le_one hgap).mpr (by linarith)⟩, ?_⟩
        simp only [b]
        rw [mul_div_cancel₀ _ hgap.ne']
        congr 1
        ring
  · intro s s' h
    rcases hPinj _ _ (hab s).1 (by linarith [(hab s).2]) (by linarith [(hbb s').1])
      (hbb s').2 h with
      h1 | ⟨h1, h2⟩ | ⟨h1, -⟩
    · right
      have h2 := (hab s).2
      have h3 := (hbb s').1
      have h4 : θ * s = θ := by linarith
      have h5 : (2 * Real.pi - θ) * s' = 2 * Real.pi - θ := by linarith
      refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
      · exact mul_left_cancel₀ hθpos.ne' (h4.trans (mul_one θ).symm)
      · exact mul_left_cancel₀ hgap.ne' (h5.trans (mul_one _).symm)
    · left
      refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
      · exact mul_left_cancel₀ hθpos.ne' (h1.trans (mul_zero θ).symm)
      · refine mul_left_cancel₀ hgap.ne' ?_
        change (2 * Real.pi - θ) * (s' : ℝ) = (2 * Real.pi - θ) * 0
        linarith
    · linarith [(hab s).2]

end GraphMinor.Surface
