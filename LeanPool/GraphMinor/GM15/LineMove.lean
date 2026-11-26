/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscArcs
public import LeanPool.GraphMinor.GM12.Section3DiscBoundaryExtension
import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.Surface.InvarianceOfDomain

/-!
# Moving one line across a closed disc

Graph Minors XV, (3.4), page 122, takes any drawing $H' = H \cup P_1 \cup \dots \cup P_{k-1}$
with the paths drawn in the closed disc $\bar\Lambda$. To use a chart of $\bar\Lambda$ in which
the paths are straight chords, we move the paths onto chords by a homeomorphism of the disc
that fixes its boundary.

This file gives the step for one line. Let $L, L'$ be two lines in a closed disc $D$ with the
same ends $a, b$, each meeting the boundary only in its ends. Cutting $D$ along $L$ and along
$L'$ gives two pairs of closed discs, and the discs of each pair have the same part of the
boundary of $D$. On the boundary of each piece we map $L$ onto $L'$ and fix the rest, extend
this to the pieces, and glue (`exists_homeo_moving_line`).
-/

public section

namespace GraphMinor.GM15

open Set Topology Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-- The boundary of a closed disc is closed. -/
theorem isClosed_discBd [T2Space S] {D : Set S} (hD : IsClosedDisc D) : IsClosed (discBd D) := by
  obtain ⟨φ⟩ := hD.isOArc_discBd
  have h : discBd D = range (fun w => (φ w).1) := by
    ext x
    exact ⟨fun hx => ⟨φ.symm ⟨x, hx⟩, by simp⟩, fun ⟨w, hw⟩ => hw ▸ (φ w).2⟩
  rw [h]
  exact (isCompact_range (continuous_subtype_val.comp φ.continuous)).isClosed

/-- A line is closed. -/
theorem isClosed_of_isLineWithEnds [T2Space S] {L : Set S} {a b : S} (hL : IsLineWithEnds L a b) :
    IsClosed L := by
  obtain ⟨f, -, -⟩ := hL
  have h : L = range (fun t => (f t).1) := by
    ext x
    exact ⟨fun hx => ⟨f.symm ⟨x, hx⟩, by simp⟩, fun ⟨t, ht⟩ => ht ▸ (f t).2⟩
  rw [h]
  exact (isCompact_range (continuous_subtype_val.comp f.continuous)).isClosed

section LineSwap

variable {L L' : Set S} (f : unitInterval ≃ₜ L) (f' : unitInterval ≃ₜ L')

open Classical in
/-- The map that sends the line `L` onto `L'`, following their parametrizations `f` and `f'`,
and fixes every other point. -/
noncomputable def lineSwap (x : S) : S :=
  if hx : x ∈ L then (f' (f.symm ⟨x, hx⟩)).1 else x

variable {f f'}

theorem lineSwap_of_mem {x : S} (hx : x ∈ L) : lineSwap f f' x = (f' (f.symm ⟨x, hx⟩)).1 := by
  simp [lineSwap, hx]

theorem lineSwap_of_notMem {x : S} (hx : x ∉ L) : lineSwap f f' x = x := by
  simp [lineSwap, hx]

theorem lineSwap_mem {x : S} (hx : x ∈ L) : lineSwap f f' x ∈ L' := by
  rw [lineSwap_of_mem hx]
  exact (f' _).2

theorem lineSwap_lineSwap {x : S} (hx : x ∈ L) : lineSwap f' f (lineSwap f f' x) = x := by
  have key : ∀ t, lineSwap f' f (f' t).1 = (f t).1 := fun t => by
    rw [lineSwap_of_mem (f' t).2]
    simp
  rw [lineSwap_of_mem hx, key]
  simp

/-- `lineSwap` fixes the common first end of the two lines. -/
theorem lineSwap_zero {a : S} (hf : (f 0).1 = a) (hf' : (f' 0).1 = a) :
    lineSwap f f' a = a := by
  have ha : a ∈ L := hf ▸ (f 0).2
  rw [lineSwap_of_mem ha]
  have : (⟨a, ha⟩ : L) = f 0 := Subtype.ext hf.symm
  rw [this, Homeomorph.symm_apply_apply, hf']

/-- `lineSwap` fixes the common last end of the two lines. -/
theorem lineSwap_one {b : S} (hf : (f 1).1 = b) (hf' : (f' 1).1 = b) :
    lineSwap f f' b = b := by
  have hb : b ∈ L := hf ▸ (f 1).2
  rw [lineSwap_of_mem hb]
  have : (⟨b, hb⟩ : L) = f 1 := Subtype.ext hf.symm
  rw [this, Homeomorph.symm_apply_apply, hf']

/-- `lineSwap` fixes every point that is not an inner point of `L`. -/
theorem lineSwap_eq_self {a b x : S} (hfa : (f 0).1 = a) (hfa' : (f' 0).1 = a)
    (hfb : (f 1).1 = b) (hfb' : (f' 1).1 = b) (hx : x ∈ L → x = a ∨ x = b) :
    lineSwap f f' x = x := by
  by_cases hxL : x ∈ L
  · rcases hx hxL with rfl | rfl
    · exact lineSwap_zero hfa hfa'
    · exact lineSwap_one hfb hfb'
  · exact lineSwap_of_notMem hxL

theorem continuousOn_lineSwap_line : ContinuousOn (lineSwap f f') L := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : L.domRestrict (lineSwap f f') = fun x : L => (f' (f.symm x)).1 := by
    funext x
    simp only [domRestrict_apply, lineSwap_of_mem x.2]
  rw [this]
  exact continuous_subtype_val.comp (f'.continuous.comp f.symm.continuous)

/-- `lineSwap` is continuous on `K ∪ L` when `K` is closed and meets `L` only in its ends. -/
theorem continuousOn_lineSwap [T2Space S] {a b : S} {K : Set S} (hK : IsClosed K)
    (hfa : (f 0).1 = a) (hfa' : (f' 0).1 = a) (hfb : (f 1).1 = b) (hfb' : (f' 1).1 = b)
    (hKL : K ∩ L ⊆ {a, b}) : ContinuousOn (lineSwap f f') (K ∪ L) := by
  have hL : IsLineWithEnds L a b := ⟨f, hfa, hfb⟩
  refine ContinuousOn.union_of_isClosed ?_ continuousOn_lineSwap_line hK
    (isClosed_of_isLineWithEnds hL)
  refine continuousOn_id.congr fun x hx => ?_
  exact lineSwap_eq_self hfa hfa' hfb hfb' fun hxL => hKL ⟨hx, hxL⟩

end LineSwap

/-- One side of `exists_homeo_moving_line`. Let `Δ, Δ'` be closed discs with boundaries `A ∪ L`
and `A ∪ L'`, where `L, L'` are lines with ends `a, b` and `A` misses both lines and has closure
meeting them only in `a, b`. Then there is a homeomorphism `Δ → Δ'` that is `lineSwap` on the
boundary. -/
theorem exists_half_homeo [T2Space S] {Δ Δ' A L L' : Set S} {a b : S}
    (hΔ : IsClosedDisc Δ) (hΔ' : IsClosedDisc Δ') (f : unitInterval ≃ₜ L) (f' : unitInterval ≃ₜ L')
    (hfa : (f 0).1 = a) (hfa' : (f' 0).1 = a) (hfb : (f 1).1 = b) (hfb' : (f' 1).1 = b)
    (hbd : discBd Δ = A ∪ L) (hbd' : discBd Δ' = A ∪ L')
    (hAL : Disjoint A L) (hAL' : Disjoint A L')
    (hcl : closure A ∩ L ⊆ {a, b}) (hcl' : closure A ∩ L' ⊆ {a, b}) :
    ∃ F F' : S → S, MapsTo F Δ Δ' ∧ MapsTo F' Δ' Δ ∧ ContinuousOn F Δ ∧ ContinuousOn F' Δ' ∧
      LeftInvOn F' F Δ ∧ LeftInvOn F F' Δ' ∧ (∀ x ∈ discBd Δ, F x = lineSwap f f' x) ∧
      (∀ y ∈ discBd Δ', F' y = lineSwap f' f y) := by
  classical
  -- `lineSwap` maps `A ∪ L` onto `A ∪ L'`, with inverse `lineSwap f' f`.
  have hmaps : ∀ x ∈ A ∪ L, lineSwap f f' x ∈ A ∪ L' := by
    rintro x (hx | hx)
    · rw [lineSwap_of_notMem (disjoint_left.mp hAL hx)]
      exact Or.inl hx
    · exact Or.inr (lineSwap_mem hx)
  have hmaps' : ∀ y ∈ A ∪ L', lineSwap f' f y ∈ A ∪ L := by
    rintro y (hy | hy)
    · rw [lineSwap_of_notMem (disjoint_left.mp hAL' hy)]
      exact Or.inl hy
    · exact Or.inr (lineSwap_mem hy)
  have hinv : ∀ x ∈ A ∪ L, lineSwap f' f (lineSwap f f' x) = x := by
    rintro x (hx | hx)
    · rw [lineSwap_of_notMem (disjoint_left.mp hAL hx),
        lineSwap_of_notMem (disjoint_left.mp hAL' hx)]
    · exact lineSwap_lineSwap hx
  have hinv' : ∀ y ∈ A ∪ L', lineSwap f f' (lineSwap f' f y) = y := by
    rintro y (hy | hy)
    · rw [lineSwap_of_notMem (disjoint_left.mp hAL' hy),
        lineSwap_of_notMem (disjoint_left.mp hAL hy)]
    · exact lineSwap_lineSwap hy
  have hc : ContinuousOn (lineSwap f f') (A ∪ L) :=
    (continuousOn_lineSwap isClosed_closure hfa hfa' hfb hfb' hcl).mono
      (union_subset_union_left _ subset_closure)
  have hc' : ContinuousOn (lineSwap f' f) (A ∪ L') :=
    (continuousOn_lineSwap isClosed_closure hfa' hfa hfb' hfb hcl').mono
      (union_subset_union_left _ subset_closure)
  let e : discBd Δ ≃ₜ discBd Δ' :=
    { toFun := fun x => ⟨lineSwap f f' x.1, hbd' ▸ hmaps x.1 (hbd ▸ x.2)⟩
      invFun := fun y => ⟨lineSwap f' f y.1, hbd ▸ hmaps' y.1 (hbd' ▸ y.2)⟩
      left_inv := fun x => Subtype.ext (hinv x.1 (hbd ▸ x.2))
      right_inv := fun y => Subtype.ext (hinv' y.1 (hbd' ▸ y.2))
      continuous_toFun := Continuous.subtype_mk
        (hc.comp_continuous continuous_subtype_val fun x => hbd ▸ x.2) _
      continuous_invFun := Continuous.subtype_mk
        (hc'.comp_continuous continuous_subtype_val fun y => hbd' ▸ y.2) _ }
  obtain ⟨Φ, hΦ⟩ := GM12.exists_disc_homeomorph_extending_boundary hΔ hΔ' e
  let F : S → S := fun x => if hx : x ∈ Δ then (Φ ⟨x, hx⟩).1 else x
  let F' : S → S := fun y => if hy : y ∈ Δ' then (Φ.symm ⟨y, hy⟩).1 else y
  have hF : ∀ x (hx : x ∈ Δ), F x = (Φ ⟨x, hx⟩).1 := fun x hx => by simp [F, hx]
  have hF' : ∀ y (hy : y ∈ Δ'), F' y = (Φ.symm ⟨y, hy⟩).1 := fun y hy => by simp [F', hy]
  have hFbd : ∀ x ∈ discBd Δ, F x = lineSwap f f' x := fun x hx => by
    rw [hF x (discBd_subset Δ hx)]
    exact hΦ ⟨x, hx⟩
  refine ⟨F, F', fun x hx => ?_, fun y hy => ?_, ?_, ?_, fun x hx => ?_, fun y hy => ?_,
    hFbd, fun y hy => ?_⟩
  · rw [hF x hx]
    exact (Φ _).2
  · rw [hF' y hy]
    exact (Φ.symm _).2
  · rw [continuousOn_iff_continuous_domRestrict]
    have : Δ.domRestrict F = fun x : Δ => (Φ x).1 := by
      funext x
      exact hF x.1 x.2
    rw [this]
    exact continuous_subtype_val.comp Φ.continuous
  · rw [continuousOn_iff_continuous_domRestrict]
    have : Δ'.domRestrict F' = fun y : Δ' => (Φ.symm y).1 := by
      funext y
      exact hF' y.1 y.2
    rw [this]
    exact continuous_subtype_val.comp Φ.symm.continuous
  · rw [hF x hx, hF' _ (Φ _).2]
    simp
  · rw [hF' y hy, hF _ (Φ.symm _).2]
    simp
  · -- `y = F x` for the boundary point `x = lineSwap f' f y`.
    have hx : lineSwap f' f y ∈ discBd Δ := hbd ▸ hmaps' y (hbd' ▸ hy)
    have hFx : F (lineSwap f' f y) = y := by
      rw [hFbd _ hx, hinv' y (hbd' ▸ hy)]
    have hxΔ := discBd_subset Δ hx
    calc F' y = F' (F (lineSwap f' f y)) := by rw [hFx]
      _ = lineSwap f' f y := by
        rw [hF _ hxΔ, hF' _ (Φ _).2]
        simp

/-- **Moving one line across a closed disc.** Let `L, L'` be lines in a closed disc `D` with the
same ends `a ≠ b`, each meeting the boundary of `D` only in `a, b`. Then there is a homeomorphism
of `D` onto itself that fixes the boundary of `D` pointwise and maps `L` onto `L'`. -/
theorem exists_homeo_moving_line [T2Space S] {D L L' : Set S} {a b : S} (hD : IsClosedDisc D)
    (hab : a ≠ b) (hL : IsLineWithEnds L a b) (hL' : IsLineWithEnds L' a b) (hLD : L ⊆ D)
    (hL'D : L' ⊆ D) (hLbd : L ∩ discBd D = {a, b}) (hL'bd : L' ∩ discBd D = {a, b}) :
    ∃ Ψ Ψ' : S → S, MapsTo Ψ D D ∧ MapsTo Ψ' D D ∧ ContinuousOn Ψ D ∧ ContinuousOn Ψ' D ∧
      LeftInvOn Ψ' Ψ D ∧ LeftInvOn Ψ Ψ' D ∧ (∀ x ∈ discBd D, Ψ x = x) ∧ Ψ '' L = L' := by
  classical
  obtain ⟨f, hfa, hfb⟩ := hL
  obtain ⟨f', hfa', hfb'⟩ := hL'
  -- Cut `D` along `L` and along `L'`.
  obtain ⟨A₁, A₂, Δ₁, Δ₂, hA₁₂, hcomp, hΔ₁, hΔ₂, hU, hI, hb₁, hb₂, -⟩ :=
    disc_iArc D L a b hD hLD hab ⟨f, hfa, hfb⟩ hLbd
  obtain ⟨B₁, B₂, E₁', E₂', hB₁₂, hcomp', hE₁', hE₂', hU', hI', hc₁', hc₂', -⟩ :=
    disc_iArc D L' a b hD hL'D hab ⟨f', hfa', hfb'⟩ hL'bd
  -- Name the pieces of the cut along `L'` so that they have the boundary parts `A₁, A₂`.
  obtain ⟨E₁, E₂, hE₁, hE₂, hUE, hIE, hd₁, hd₂⟩ : ∃ E₁ E₂ : Set S, IsClosedDisc E₁ ∧
      IsClosedDisc E₂ ∧ E₁ ∪ E₂ = D ∧ E₁ ∩ E₂ = L' ∧ discBd E₁ = A₁ ∪ L' ∧
      discBd E₂ = A₂ ∪ L' := by
    have hB₁ : B₁ ∈ ({A₁, A₂} : Set (Set S)) := hcomp ▸ hcomp' ▸ Or.inl rfl
    have hB₂ : B₂ ∈ ({A₁, A₂} : Set (Set S)) := hcomp ▸ hcomp' ▸ Or.inr rfl
    rcases hB₁ with rfl | rfl
    · rcases hB₂ with rfl | rfl
      · exact absurd rfl hB₁₂
      · exact ⟨E₁', E₂', hE₁', hE₂', hU', hI', hc₁', hc₂'⟩
    · rcases hB₂ with rfl | rfl
      · exact ⟨E₂', E₁', hE₂', hE₁', union_comm E₁' E₂' ▸ hU', inter_comm E₁' E₂' ▸ hI', hc₂',
          hc₁'⟩
      · exact absurd rfl hB₁₂
  -- Facts about the boundary parts `A₁, A₂`.
  have hAsub : ∀ A ∈ componentsIn (discBd D \ {a, b}), A ⊆ discBd D \ {a, b} := by
    rintro _ ⟨x, -, rfl⟩
    exact connectedComponentIn_subset _ _
  have hA₁ : A₁ ⊆ discBd D \ {a, b} := hAsub A₁ (hcomp ▸ Or.inl rfl)
  have hA₂ : A₂ ⊆ discBd D \ {a, b} := hAsub A₂ (hcomp ▸ Or.inr rfl)
  have hcover : discBd D \ {a, b} ⊆ A₁ ∪ A₂ := fun x hx => by
    have hmem : connectedComponentIn (discBd D \ {a, b}) x ∈ ({A₁, A₂} : Set (Set S)) :=
      hcomp ▸ ⟨x, hx, rfl⟩
    have hx' := mem_connectedComponentIn hx
    rcases hmem with h | h
    · exact Or.inl (h ▸ hx')
    · exact Or.inr (h ▸ hx')
  have hdisj : ∀ {A M : Set S}, A ⊆ discBd D \ {a, b} → M ∩ discBd D = {a, b} → Disjoint A M :=
    fun {A M} hA hM => disjoint_left.mpr fun x hxA hxM => by
      have : x ∈ M ∩ discBd D := ⟨hxM, (hA hxA).1⟩
      rw [hM] at this
      exact (hA hxA).2 this
  have hclos : ∀ {A M : Set S}, A ⊆ discBd D \ {a, b} → M ∩ discBd D = {a, b} →
      closure A ∩ M ⊆ {a, b} := fun {A M} hA hM x hx => by
    have hxbd : x ∈ discBd D :=
      (isClosed_discBd hD).closure_subset_iff.mpr (hA.trans sdiff_subset) hx.1
    rw [← hM]
    exact ⟨hx.2, hxbd⟩
  -- The two halves.
  obtain ⟨F₁, F₁', hm₁, hm₁', hc₁, hc₁'', hl₁, hr₁, hbd₁, hbd₁'⟩ :=
    exists_half_homeo hΔ₁ hE₁ f f' hfa hfa' hfb hfb' hb₁ hd₁ (hdisj hA₁ hLbd) (hdisj hA₁ hL'bd)
      (hclos hA₁ hLbd) (hclos hA₁ hL'bd)
  obtain ⟨F₂, F₂', hm₂, hm₂', hc₂, hc₂'', hl₂, hr₂, hbd₂, hbd₂'⟩ :=
    exists_half_homeo hΔ₂ hE₂ f f' hfa hfa' hfb hfb' hb₂ hd₂ (hdisj hA₂ hLbd) (hdisj hA₂ hL'bd)
      (hclos hA₂ hLbd) (hclos hA₂ hL'bd)
  have hLb₁ : L ⊆ discBd Δ₁ := hb₁ ▸ subset_union_right
  have hLb₂ : L ⊆ discBd Δ₂ := hb₂ ▸ subset_union_right
  have hL'b₁ : L' ⊆ discBd E₁ := hd₁ ▸ subset_union_right
  have hL'b₂ : L' ⊆ discBd E₂ := hd₂ ▸ subset_union_right
  -- The halves agree on the cut lines.
  have hagree : ∀ x ∈ L, F₁ x = F₂ x := fun x hx => by
    rw [hbd₁ x (hLb₁ hx), hbd₂ x (hLb₂ hx)]
  have hagree' : ∀ y ∈ L', F₁' y = F₂' y := fun y hy => by
    rw [hbd₁' y (hL'b₁ hy), hbd₂' y (hL'b₂ hy)]
  let Ψ : S → S := fun x => if x ∈ Δ₁ then F₁ x else F₂ x
  let Ψ' : S → S := fun y => if y ∈ E₁ then F₁' y else F₂' y
  have hΨ₁ : ∀ x ∈ Δ₁, Ψ x = F₁ x := fun x hx => by simp [Ψ, hx]
  have hΨ₂ : ∀ x ∈ Δ₂, Ψ x = F₂ x := fun x hx => by
    by_cases h : x ∈ Δ₁
    · rw [hΨ₁ x h]
      exact hagree x (hI ▸ ⟨h, hx⟩)
    · simp [Ψ, h]
  have hΨ'₁ : ∀ y ∈ E₁, Ψ' y = F₁' y := fun y hy => by simp [Ψ', hy]
  have hΨ'₂ : ∀ y ∈ E₂, Ψ' y = F₂' y := fun y hy => by
    by_cases h : y ∈ E₁
    · rw [hΨ'₁ y h]
      exact hagree' y (hIE ▸ ⟨h, hy⟩)
    · simp [Ψ', h]
  have hD₁ : ∀ x ∈ D, x ∈ Δ₁ ∨ x ∈ Δ₂ := fun x hx => by rw [← hU] at hx; exact hx
  have hE₁₂ : ∀ y ∈ D, y ∈ E₁ ∨ y ∈ E₂ := fun y hy => by rw [← hUE] at hy; exact hy
  have hsub₁ : E₁ ⊆ D := hUE ▸ subset_union_left
  have hsub₂ : E₂ ⊆ D := hUE ▸ subset_union_right
  have hsubΔ₁ : Δ₁ ⊆ D := hU ▸ subset_union_left
  have hsubΔ₂ : Δ₂ ⊆ D := hU ▸ subset_union_right
  refine ⟨Ψ, Ψ', fun x hx => ?_, fun y hy => ?_, ?_, ?_, fun x hx => ?_, fun y hy => ?_,
    fun x hx => ?_, ?_⟩
  · rcases hD₁ x hx with h | h
    · rw [hΨ₁ x h]
      exact hsub₁ (hm₁ h)
    · rw [hΨ₂ x h]
      exact hsub₂ (hm₂ h)
  · rcases hE₁₂ y hy with h | h
    · rw [hΨ'₁ y h]
      exact hsubΔ₁ (hm₁' h)
    · rw [hΨ'₂ y h]
      exact hsubΔ₂ (hm₂' h)
  · rw [← hU]
    exact ContinuousOn.union_of_isClosed (hc₁.congr hΨ₁) (hc₂.congr hΨ₂) hΔ₁.isClosed
      hΔ₂.isClosed
  · rw [← hUE]
    exact ContinuousOn.union_of_isClosed (hc₁''.congr hΨ'₁) (hc₂''.congr hΨ'₂) hE₁.isClosed
      hE₂.isClosed
  · rcases hD₁ x hx with h | h
    · rw [hΨ₁ x h, hΨ'₁ _ (hm₁ h), hl₁ h]
    · rw [hΨ₂ x h, hΨ'₂ _ (hm₂ h), hl₂ h]
  · rcases hE₁₂ y hy with h | h
    · rw [hΨ'₁ y h, hΨ₁ _ (hm₁' h), hr₁ h]
    · rw [hΨ'₂ y h, hΨ₂ _ (hm₂' h), hr₂ h]
  · -- A boundary point of `D` lies in `A₁`, in `A₂` or in `{a, b} ⊆ L`, and `lineSwap` fixes it.
    have hfix : lineSwap f f' x = x := lineSwap_eq_self hfa hfa' hfb hfb' fun hxL => by
      have : x ∈ L ∩ discBd D := ⟨hxL, hx⟩
      rw [hLbd] at this
      exact this
    by_cases hxab : x ∈ ({a, b} : Set S)
    · have hxL : x ∈ L := (hLbd ▸ hxab : x ∈ L ∩ discBd D).1
      rw [hΨ₁ x (hLb₁.trans (discBd_subset _) hxL), hbd₁ x (hLb₁ hxL), hfix]
    · rcases hcover ⟨hx, hxab⟩ with h | h
      · have hx₁ : x ∈ discBd Δ₁ := hb₁ ▸ Or.inl h
        rw [hΨ₁ x (discBd_subset _ hx₁), hbd₁ x hx₁, hfix]
      · have hx₂ : x ∈ discBd Δ₂ := hb₂ ▸ Or.inl h
        rw [hΨ₂ x (discBd_subset _ hx₂), hbd₂ x hx₂, hfix]
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hΨ₁ x (hLb₁.trans (discBd_subset _) hx), hbd₁ x (hLb₁ hx)]
      exact lineSwap_mem hx
    · intro hy
      refine ⟨lineSwap f' f y, lineSwap_mem hy, ?_⟩
      have hx := lineSwap_mem (f := f') (f' := f) hy
      rw [hΨ₁ _ (hLb₁.trans (discBd_subset _) hx), hbd₁ _ (hLb₁ hx), lineSwap_lineSwap hy]

end GraphMinor.GM15
