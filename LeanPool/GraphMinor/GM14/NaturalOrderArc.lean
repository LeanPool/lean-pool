/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Two consecutive vertices of a natural order

Let `Ω` be a natural order from an `O`-arc `F`, and let `L ⊆ F` be connected, with `a, b` as its
only
vertices of `ΩBar`. Then `a` and `b` are consecutive: one of the two intervals of `Ω` between them
is
empty (`interval_empty_of_arc`). We use this for an edge of the circuit `C₁` in (8.4). If a path of
a
crooked transaction were such an edge, it would be peripheral.
-/


@[expose] public section

namespace GraphMinor.GM14

open Set Topology GraphMinor GraphMinor.GM09 GraphMinor.Surface Real

universe u w

/-- Two points cut the circle into two open arcs. -/
theorem circle_separates {L : Set Circle} (hL : IsPreconnected L) {p q x y : ℝ} (h₁ : p < x)
    (h₂ : x < q) (h₃ : q < y) (h₄ : y < p + 2 * π) (hx : Circle.exp x ∈ L) (hy : Circle.exp y ∈ L)
    (hp : Circle.exp p ∉ L) (hq : Circle.exp q ∉ L) : False := by
  have hopen := isLocalHomeomorph_circleExp.isOpenMap
  have hP : IsOpen (Circle.exp '' Ioo p q) := hopen _ isOpen_Ioo
  have hQ : IsOpen (Circle.exp '' Ioo q (p + 2 * π)) := hopen _ isOpen_Ioo
  have hpi : 0 < 2 * π := by positivity
  have hdis : Disjoint (Circle.exp '' Ioo p q) (Circle.exp '' Ioo q (p + 2 * π)) := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨r, ⟨hr₁, hr₂⟩, rfl⟩ ⟨s, ⟨hs₁, hs₂⟩, hs⟩
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hs
    have hgt : (0 : ℝ) < (m : ℝ) * (2 * π) := by linarith
    have hlt : (m : ℝ) * (2 * π) < 1 * (2 * π) := by linarith
    have h₅ : (0 : ℝ) < m := (mul_pos_iff_of_pos_right hpi).mp hgt
    have h₆ : (m : ℝ) < 1 := lt_of_mul_lt_mul_right hlt hpi.le
    have h₇ : 0 < m := by exact_mod_cast h₅
    have h₈ : m < 1 := by exact_mod_cast h₆
    omega
  have hcover : L ⊆ Circle.exp '' Ioo p q ∪ Circle.exp '' Ioo q (p + 2 * π) := by
    intro z hz
    obtain ⟨θ, rfl⟩ : ∃ θ : ℝ, Circle.exp θ = z := ⟨Complex.arg z, Circle.exp_arg z⟩
    let t : ℝ := toIcoMod Real.two_pi_pos p θ
    have ht : Circle.exp t = Circle.exp θ := by
      refine Circle.exp_eq_exp.mpr ⟨-toIcoDiv Real.two_pi_pos p θ, ?_⟩
      have := self_sub_toIcoDiv_zsmul Real.two_pi_pos p θ
      simp only [zsmul_eq_mul] at this
      simp only [t, Int.cast_neg, neg_mul, ← this]
      ring
    obtain ⟨ht₁, ht₂⟩ : t ∈ Ico p (p + 2 * π) := toIcoMod_mem_Ico Real.two_pi_pos p θ
    rw [← ht] at hz ⊢
    have hne₁ : t ≠ p := fun h => hp (h ▸ hz)
    have hne₂ : t ≠ q := fun h => hq (h ▸ hz)
    rcases lt_or_gt_of_ne hne₂ with h | h
    · exact Or.inl ⟨t, ⟨lt_of_le_of_ne ht₁ hne₁.symm, h⟩, rfl⟩
    · exact Or.inr ⟨t, ⟨h, ht₂⟩, rfl⟩
  rcases hL.subset_or_subset hP hQ hdis hcover with h | h
  · obtain ⟨s, ⟨hs₁, hs₂⟩, hs⟩ := h hy
    exact disjoint_left.mp hdis ⟨s, ⟨hs₁, hs₂⟩, hs⟩ ⟨y, ⟨h₃, h₄⟩, rfl⟩
  · obtain ⟨s, ⟨hs₁, hs₂⟩, hs⟩ := h hx
    exact disjoint_left.mp hdis ⟨x, ⟨h₁, h₂⟩, rfl⟩ ⟨s, ⟨hs₁, hs₂⟩, hs⟩

variable {α : Type u} {S : Type w} [TopologicalSpace S]

/-- See the module docstring. -/
theorem interval_empty_of_arc {ν : α → S} {Ω : CyclicPerm α} {F L : Set S}
    (hnat : IsNaturalOrderFrom ν Ω F) (hLF : L ⊆ F) (hL : IsPreconnected L) {a b : α}
    (ha : ν a ∈ L) (hb : ν b ∈ L) (hoff : ∀ v ∈ Ω.bar, ν v ∈ L → v = a ∨ v = b) :
    Ω.interval a b = ∅ ∨ Ω.interval b a = ∅ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨c, hcb, hc⟩, ⟨d, hdb, hd⟩⟩ := hcon
  obtain ⟨-, φ, hm, hord⟩ := hnat
  obtain ⟨t₁, t₂, t₃, h₁₂, h₂₃, h₃₁, e₁, e₂, e₃⟩ := hord a c b hc
  obtain ⟨s₁, s₂, s₃, k₁₂, k₂₃, k₃₁, f₁, f₂, f₃⟩ := hord b d a hd
  -- The set `L`, on the circle.
  let K : Set F := Subtype.val ⁻¹' L
  have hK : IsPreconnected K := by
    rw [← IsInducing.subtypeVal.isPreconnected_image]
    rwa [Subtype.image_preimage_coe, inter_eq_right.mpr hLF]
  let T : Set Circle := φ.symm '' K
  have hT : IsPreconnected T := hK.image _ φ.symm.continuous.continuousOn
  have hmem : ∀ r : ℝ, Circle.exp r ∈ T ↔ (φ (Circle.exp r)).1 ∈ L := by
    intro r
    constructor
    · rintro ⟨y, hy, hyr⟩
      rw [← hyr, φ.apply_symm_apply]
      exact hy
    · intro h
      exact ⟨φ (Circle.exp r), h, φ.symm_apply_apply _⟩
  have hinj : ∀ {x y : ℝ}, (φ (Circle.exp x)).1 = (φ (Circle.exp y)).1 →
      ∃ m : ℤ, x = y + m * (2 * π) := fun h =>
    Circle.exp_eq_exp.mp (φ.injective (Subtype.ext h))
  obtain ⟨m, hm₁⟩ := hinj (f₁.trans e₃.symm)
  obtain ⟨n, hn₁⟩ := hinj (f₃.trans e₁.symm)
  have hpi : 0 < 2 * π := by positivity
  -- The point of `d`, in the same period as the rest.
  set u : ℝ := s₂ - m * (2 * π) with hu
  have hexp : Circle.exp u = Circle.exp s₂ := Circle.exp_eq_exp.mpr ⟨-m, by
    rw [hu]
    push_cast
    ring⟩
  have hk : ((n - m : ℤ) : ℝ) = 1 := by
    push_cast
    have h₅ : (t₃ : ℝ) < t₁ + (n - m) * (2 * π) := by nlinarith
    have h₆ : t₁ + ((n : ℝ) - m) * (2 * π) < t₃ + 2 * π := by nlinarith
    have h₇ : (0 : ℝ) < ((n : ℝ) - m) * (2 * π) := by nlinarith
    have h₈ : ((n : ℝ) - m) * (2 * π) < 2 * (2 * π) := by nlinarith
    have h₉ : (0 : ℝ) < (n : ℝ) - m := (mul_pos_iff_of_pos_right hpi).mp h₇
    have h₁₀ : (n : ℝ) - m < 2 := lt_of_mul_lt_mul_right h₈ hpi.le
    have i₁ : (0 : ℤ) < n - m := by exact_mod_cast h₉
    have i₂ : n - m < (2 : ℤ) := by exact_mod_cast h₁₀
    have i₃ : n - m = (1 : ℤ) := by omega
    exact_mod_cast i₃
  have hk' : (n : ℝ) - m = 1 := by
    push_cast at hk
    exact hk
  have hu₁ : t₃ < u := by
    rw [hu]
    nlinarith
  have hu₂ : u < t₁ + 2 * π := by
    rw [hu]
    have : s₃ - m * (2 * π) = t₁ + ((n : ℝ) - m) * (2 * π) := by
      rw [hn₁]
      ring
    rw [hk'] at this
    linarith
  have hcL : Circle.exp t₂ ∉ T := by
    rw [hmem, e₂]
    intro h
    rcases hoff c hcb.1 h with rfl | rfl
    · exact hcb.2 (Or.inl rfl)
    · exact hcb.2 (Or.inr rfl)
  have hdL : Circle.exp u ∉ T := by
    rw [hexp, hmem, f₂]
    intro h
    rcases hoff d hdb.1 h with rfl | rfl
    · exact hdb.2 (Or.inr rfl)
    · exact hdb.2 (Or.inl rfl)
  have hbL : Circle.exp t₃ ∈ T := by
    rw [hmem, e₃]
    exact hb
  have haL : Circle.exp (t₁ + 2 * π) ∈ T := by
    rw [Circle.exp_add_two_pi, hmem, e₁]
    exact ha
  exact circle_separates hT h₂₃ hu₁ hu₂ (by linarith) hbL haL hcL hdL

end GraphMinor.GM14
