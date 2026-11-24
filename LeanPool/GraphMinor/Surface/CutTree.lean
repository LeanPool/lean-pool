/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CrossCut

/-!
# Cuts and trees of cuts

`IsCut F a b e` says that `e` is a cross-cut of the `O`-arc `F` and that `a` and `b` are the two
arcs
of `F` between its ends. A `CutTree P F` is a finite binary tree of cuts that starts at `F` and has
leaves whose inner domains satisfy `P`.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

local notation "𝕀" => unitInterval

/-- The closed domain of `F`. -/
def closedInner (F : Set ℂ) : Set ℂ := inner F ∪ F

/-- `e` is a cross-cut of `F` with ends the ends of the two arcs `a` and `b` of `F`. -/
structure IsCut (F : Set ℂ) (a b e : 𝕀 → ℂ) : Prop where
  arc_a : IsArcMap a
  arc_b : IsArcMap b
  arc_e : IsArcMap e
  a_zero : a 0 = e 0
  a_one : a 1 = e 1
  b_zero : b 0 = e 0
  b_one : b 1 = e 1
  ne : e 0 ≠ e 1
  union : range a ∪ range b = F
  meet : ∀ s t, a s = b t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)
  inside : ∀ t, t ≠ 0 → t ≠ 1 → e t ∈ inner F

/-- The `O`-arc formed by the arc `a` and the cross-cut `e`. -/
def side (a e : 𝕀 → ℂ) : Set ℂ := range a ∪ range e

namespace IsCut

variable {F : Set ℂ} {a b e : 𝕀 → ℂ}

/-- The cut with its two sides exchanged. -/
theorem symm (h : IsCut F a b e) : IsCut F b a e where
  arc_a := h.arc_b
  arc_b := h.arc_a
  arc_e := h.arc_e
  a_zero := h.b_zero
  a_one := h.b_one
  b_zero := h.a_zero
  b_one := h.a_one
  ne := h.ne
  union := by rw [union_comm]; exact h.union
  meet := fun s t hst => (h.meet t s hst.symm).imp And.symm And.symm
  inside := h.inside

theorem e_notMem (h : IsCut F a b e) {t : 𝕀} (h0 : t ≠ 0) (h1 : t ≠ 1) : e t ∉ F :=
  (h.inside t h0 h1).1

theorem a_mem (h : IsCut F a b e) (s : 𝕀) : a s ∈ F := h.union ▸ Or.inl ⟨s, rfl⟩

theorem b_mem (h : IsCut F a b e) (s : 𝕀) : b s ∈ F := h.union ▸ Or.inr ⟨s, rfl⟩

/-- The arc `a` meets the cross-cut only in their ends. -/
theorem a_eq_e (h : IsCut F a b e) (s t : 𝕀) (hst : a s = e t) :
    (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
  by_cases h0 : t = 0
  · left
    refine ⟨h.arc_a.2 ?_, h0⟩
    rw [hst, h0, h.a_zero]
  · by_cases h1 : t = 1
    · right
      refine ⟨h.arc_a.2 ?_, h1⟩
      rw [hst, h1, h.a_one]
    · exact absurd (hst ▸ h.a_mem s) (h.e_notMem h0 h1)

/-- The side of a cut is an `O`-arc. -/
theorem oArc_side (h : IsCut F a b e) : Nonempty (Circle ≃ₜ side a e) :=
  oArc_of_two_arcs h.arc_a h.arc_e h.a_zero h.a_one h.a_eq_e

/-- A cut is a theta curve. -/
theorem isTheta (h : IsCut F a b e) (hF : IsJordanParts F) :
    IsTheta F (side a e) (side b e) (range a) (range b) (range e) (e 0) (e 1) := by
  obtain ⟨φ₁⟩ := h.oArc_side
  obtain ⟨φ₂⟩ := h.symm.oArc_side
  have hmid : (⟨1 / 2, by norm_num, by norm_num⟩ : 𝕀) ≠ 0 ∧
      (⟨1 / 2, by norm_num, by norm_num⟩ : 𝕀) ≠ 1 := by
    constructor <;> intro hh <;> have := congrArg Subtype.val hh <;> norm_num at this
  have hcase : ∀ {c : 𝕀 → ℂ}, IsArcMap c → c 0 = e 0 → c 1 = e 1 → (range c \ {e 0, e 1}).Nonempty
    := by
    intro c hc h0 h1
    refine ⟨c ⟨1 / 2, by norm_num, by norm_num⟩, ⟨_, rfl⟩, ?_⟩
    rintro (hh | hh)
    · exact hmid.1 (hc.2 (hh.trans h0.symm))
    · exact hmid.2 (hc.2 (mem_singleton_iff.mp hh |>.trans h1.symm))
  refine ⟨hF, isJordanParts φ₁, isJordanParts φ₂, h.union.symm, rfl, rfl, ?_, ⟨⟨0, rfl⟩, ⟨1, rfl⟩⟩,
    ?_,
    ⟨h.a_zero ▸ h.a_mem 0, h.a_one ▸ h.a_mem 1⟩, ?_, hcase h.arc_a h.a_zero h.a_one,
    hcase h.arc_b h.b_zero h.b_one⟩
  · rintro _ ⟨⟨s, rfl⟩, ⟨t, ht⟩⟩
    rcases h.meet s t ht.symm with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl h.a_zero
    · exact Or.inr h.a_one
  · rintro _ ⟨⟨t, rfl⟩, hn⟩
    refine h.inside t (fun h0 => hn (Or.inl (by rw [h0]))) fun h1 => hn (Or.inr (by rw [h1]; rfl))
  · exact isPreconnected_range h.arc_e.1

end IsCut

/-- A cross-cut of `F` gives a cut. -/
theorem exists_isCut {F : Set ℂ} (φ : Circle ≃ₜ F) {e : 𝕀 → ℂ} (he : IsArcMap e) (hne : e 0 ≠ e 1)
    (h0 : e 0 ∈ F) (h1 : e 1 ∈ F) (hin : ∀ t, t ≠ 0 → t ≠ 1 → e t ∈ inner F) :
    ∃ a b, IsCut F a b e := by
  obtain ⟨a, b, ha, hb, ha0, ha1, hb0, hb1, hu, hm⟩ := exists_two_arcs φ h0 h1 hne
  exact ⟨a, b, ha, hb, he, ha0, ha1, hb0, hb1, hne, hu, hm, hin⟩

/-- A finite binary tree of cuts from `F`, with leaves satisfying `P`. -/
inductive CutTree (P : Set ℂ → Prop) : Set ℂ → Prop
  | leaf {F : Set ℂ} : P (inner F) → CutTree P F
  | node {F : Set ℂ} {a b e : 𝕀 → ℂ} : IsCut F a b e → CutTree P (side a e) →
      CutTree P (side b e) → CutTree P F

/-- The inner domains of a tree lie in the inner domain of the root. -/
theorem IsCut.inner_side_subset {F : Set ℂ} {a b e : 𝕀 → ℂ} (h : IsCut F a b e)
    (hF : IsJordanParts F) : inner (side a e) ⊆ inner F ∧ inner (side b e) ⊆ inner F :=
  ⟨(h.isTheta hF).inner_subset₁, (h.isTheta hF).symm.inner_subset₁⟩

/-- An antitone property of the root can be added to the leaves of a tree. -/
theorem CutTree.strengthen {P Q : Set ℂ → Prop} (hQ : ∀ {U V}, U ⊆ V → Q V → Q U) {F : Set ℂ}
    (ht : CutTree P F) (hF : Nonempty (Circle ≃ₜ F)) (hq : Q (inner F)) :
    CutTree (fun U => Q U ∧ P U) F := by
  induction ht with
  | leaf h => exact .leaf ⟨hq, h⟩
  | @node F a b e hc _ _ ih₁ ih₂ =>
    obtain ⟨φ⟩ := hF
    have hsub := hc.inner_side_subset (isJordanParts φ)
    exact .node hc (ih₁ hc.oArc_side (hQ hsub.1 hq)) (ih₂ hc.symm.oArc_side (hQ hsub.2 hq))

/-- Trees compose: from each leaf of a tree for `Q` grow a tree for `P`, and keep `Q` if it is
antitone. -/
theorem CutTree.bind {P Q : Set ℂ → Prop} (hQ : ∀ {U V}, U ⊆ V → Q V → Q U) {F : Set ℂ}
    (ht : CutTree Q F) (hF : Nonempty (Circle ≃ₜ F))
    (hnext : ∀ G : Set ℂ, Nonempty (Circle ≃ₜ G) → CutTree P G) :
    CutTree (fun U => Q U ∧ P U) F := by
  induction ht with
  | leaf h => exact (hnext _ hF).strengthen hQ hF h
  | @node F a b e hc _ _ ih₁ ih₂ =>
    exact .node hc (ih₁ hc.oArc_side) (ih₂ hc.symm.oArc_side)

/-- The leaves of a tree may be weakened. -/
theorem CutTree.map {P Q : Set ℂ → Prop} {F : Set ℂ} (ht : CutTree P F)
    (hF : Nonempty (Circle ≃ₜ F))
    (h : ∀ G : Set ℂ, Nonempty (Circle ≃ₜ G) → P (inner G) → Q (inner G)) : CutTree Q F := by
  induction ht with
  | leaf hp => exact .leaf (h _ hF hp)
  | @node F a b e hc _ _ ih₁ ih₂ =>
    exact .node hc (ih₁ hc.oArc_side) (ih₂ hc.symm.oArc_side)

end GraphMinor.Surface
