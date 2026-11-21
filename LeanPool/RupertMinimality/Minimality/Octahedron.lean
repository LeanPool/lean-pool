/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.Unimodal

/-! # Octahedron -/

@[expose] public section

namespace RupertMinimality

/-!
# Corollary 7.8: octahedra with Condition A

At a view along the axis `d = a - a'` the two poles project to one point, and
for each equator edge `uv` the two facets `auv` (front) and `a'uv` (back)
combine into a `d`-invariant affine function vanishing on `u, v` and negative
at the poles and the other two equator points (`edge_normal_of_facets`).  So
the projected equator is a strictly convex quadrilateral (in one of the two
orientations, `quad_orient`) with the poles strictly inside.  Condition A is
the open condition `Overlap4` on the equator depths, which makes any 4-cycle
with distinct depths unimodal (`isCyclicUnimodal_four`).  Theorem 7.5 in its
open-condition form (`isRupert_of_open_unimodal`) finishes.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### 4-cycles -/

/-- The 4-cycle `p₀ p₁ p₂ p₃`. -/
def quad {α : Type*} (p₀ p₁ p₂ p₃ : α) : ZMod 4 → α := ![p₀, p₁, p₂, p₃]

theorem zmod4_table (i : ZMod 4) :
    (i = 0 ∧ i + 1 = 1 ∧ i + 2 = 2 ∧ i + 3 = 3) ∨ (i = 1 ∧ i + 1 = 2 ∧ i + 2 = 3 ∧ i + 3 = 0) ∨
    (i = 2 ∧ i + 1 = 3 ∧ i + 2 = 0 ∧ i + 3 = 1) ∨ (i = 3 ∧ i + 1 = 0 ∧ i + 2 = 1 ∧ i + 3 = 2) := by
  revert i; decide

/-- Strict overlap of the ranges of the diagonals `{z₀, z₂}` and `{z₁, z₃}` of
a 4-cycle, in expanded form. -/
def Overlap4 (z₀ z₁ z₂ z₃ : ℝ) : Prop :=
  (z₀ < z₁ ∨ z₀ < z₃ ∨ z₂ < z₁ ∨ z₂ < z₃) ∧ (z₁ < z₀ ∨ z₃ < z₀ ∨ z₁ < z₂ ∨ z₃ < z₂) ∧
    z₀ ≠ z₂ ∧ z₁ ≠ z₃

theorem overlap4_of_minmax {z₀ z₁ z₂ z₃ : ℝ}
    (h : max (min z₀ z₂) (min z₁ z₃) < min (max z₀ z₂) (max z₁ z₃)) : Overlap4 z₀ z₁ z₂ z₃ := by
  rw [max_lt_iff, lt_min_iff, lt_min_iff] at h
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  have n02 : z₀ ≠ z₂ := fun e => by rw [e, min_self, max_self] at h1; exact lt_irrefl _ h1
  have n13 : z₁ ≠ z₃ := fun e => by rw [e, min_self, max_self] at h4; exact lt_irrefl _ h4
  simp only [min_lt_iff, lt_max_iff] at h2 h3
  exact ⟨by tauto, by tauto, n02, n13⟩

theorem Overlap4.symm {z₀ z₁ z₂ z₃ : ℝ} (h : Overlap4 z₀ z₁ z₂ z₃) : Overlap4 z₀ z₃ z₂ z₁ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by tauto, by tauto, h3, Ne.symm h4⟩

theorem Overlap4.mul {z₀ z₁ z₂ z₃ : ℝ} (h : Overlap4 z₀ z₁ z₂ z₃) {t : ℝ} (ht : t ≠ 0) :
    Overlap4 (t * z₀) (t * z₁) (t * z₂) (t * z₃) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hne : ∀ {x y : ℝ}, x ≠ y → t * x ≠ t * y := fun hxy e => hxy (mul_left_cancel₀ ht e)
  rcases lt_or_gt_of_ne ht with ht | ht
  · have key : ∀ {x y : ℝ}, x < y → t * y < t * x := fun hxy => by nlinarith
    exact ⟨by rcases h2 with h | h | h | h <;> [exact Or.inl (key h); exact Or.inr (Or.inl (key h));
        exact Or.inr (Or.inr (Or.inl (key h))); exact Or.inr (Or.inr (Or.inr (key h)))],
      by rcases h1 with h | h | h | h <;> [exact Or.inl (key h); exact Or.inr (Or.inl (key h));
        exact Or.inr (Or.inr (Or.inl (key h))); exact Or.inr (Or.inr (Or.inr (key h)))],
      hne h3, hne h4⟩
  · have key : ∀ {x y : ℝ}, x < y → t * x < t * y := fun hxy => by nlinarith
    exact ⟨by rcases h1 with h | h | h | h <;> [exact Or.inl (key h); exact Or.inr (Or.inl (key h));
        exact Or.inr (Or.inr (Or.inl (key h))); exact Or.inr (Or.inr (Or.inr (key h)))],
      by rcases h2 with h | h | h | h <;> [exact Or.inl (key h); exact Or.inr (Or.inl (key h));
        exact Or.inr (Or.inr (Or.inl (key h))); exact Or.inr (Or.inr (Or.inr (key h)))],
      hne h3, hne h4⟩

theorem isOpen_overlap4 : IsOpen {z : ZMod 4 → ℝ | Overlap4 (z 0) (z 1) (z 2) (z 3)} := by
  have hlt : ∀ i j : ZMod 4, IsOpen {z : ZMod 4 → ℝ | z i < z j} := fun i j =>
    isOpen_lt (continuous_apply i) (continuous_apply j)
  have hne : ∀ i j : ZMod 4, IsOpen {z : ZMod 4 → ℝ | z i ≠ z j} := fun i j =>
    isOpen_ne_fun (continuous_apply i) (continuous_apply j)
  simp only [Overlap4, Set.ofPred_and, Set.ofPred_or]
  exact (((hlt 0 1).union ((hlt 0 3).union ((hlt 2 1).union (hlt 2 3)))).inter
    (((hlt 1 0).union ((hlt 3 0).union ((hlt 1 2).union (hlt 3 2)))).inter
      ((hne 0 2).inter (hne 1 3))))

theorem Overlap4.not_saddle {z : ZMod 4 → ℝ} (h : Overlap4 (z 0) (z 1) (z 2) (z 3)) (i : ZMod 4)
    (h1 : z (i + 1) < z i) (h2 : z (i + 3) < z i) (h3 : z (i + 1) < z (i + 2))
    (h4 : z (i + 3) < z (i + 2)) : False := by
  obtain ⟨hA, hB, -, -⟩ := h
  rcases zmod4_table i with ⟨rfl, e1, e2, e3⟩ | ⟨rfl, e1, e2, e3⟩ | ⟨rfl, e1, e2, e3⟩ |
    ⟨rfl, e1, e2, e3⟩ <;> simp only [e1, e2, e3] at h1 h2 h3 h4 <;>
    rcases hA with hA | hA | hA | hA <;> rcases hB with hB | hB | hB | hB <;> linarith

/-- A 4-cycle of distinct depths whose diagonals' ranges overlap is unimodal. -/
theorem isCyclicUnimodal_four {z : ZMod 4 → ℝ} (hinj : Function.Injective z)
    (h : Overlap4 (z 0) (z 1) (z 2) (z 3)) : IsCyclicUnimodal z := by
  refine ⟨hinj, le_antisymm ?_ ?_⟩
  · rw [Finset.card_le_one]
    intro i hi j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    by_contra hne
    have hsub : ∀ m : ZMod 4, m - 1 = m + 3 := by decide
    rw [hsub] at hi hj
    have hcase : ∀ i j : ZMod 4, j ≠ i → j = i + 1 ∨ j = i + 2 ∨ j = i + 3 := by decide
    have a1 : ∀ m : ZMod 4, m + 1 + 3 = m := by decide
    have a2 : ∀ m : ZMod 4, m + 2 + 3 = m + 1 := by decide
    have a3 : ∀ m : ZMod 4, m + 2 + 1 = m + 3 := by decide
    have a4 : ∀ m : ZMod 4, m + 3 + 1 = m := by decide
    rcases hcase i j (Ne.symm hne) with rfl | rfl | rfl
    · rw [a1] at hj; linarith [hi.2, hj.1]
    · rw [a2, a3] at hj
      exact h.not_saddle i hi.2 hi.1 hj.1 hj.2
    · rw [a4] at hj; linarith [hi.1, hj.2]
  · obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ z ⟨0, Finset.mem_univ _⟩
    have b1 : ∀ m : ZMod 4, m - 1 ≠ m := by decide
    have b2 : ∀ m : ZMod 4, m + 1 ≠ m := by decide
    refine Finset.card_pos.mpr ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩⟩
    · exact lt_of_le_of_ne (hm _ (Finset.mem_univ _)) (hinj.ne (b1 m))
    · exact lt_of_le_of_ne (hm _ (Finset.mem_univ _)) (hinj.ne (b2 m))

/-! ### Convex quadrilaterals -/

/-- `q₀ q₁ q₂ q₃` is a strictly convex counterclockwise quadrilateral and `o`
is strictly left of each of its edges. -/
def QuadLeft (q₀ q₁ q₂ q₃ o : ℝ²) : Prop :=
  0 < cross2 (q₁ - q₀) (q₂ - q₀) ∧ 0 < cross2 (q₁ - q₀) (q₃ - q₀) ∧ 0 < cross2 (q₁ - q₀) (o - q₀) ∧
  0 < cross2 (q₂ - q₁) (q₃ - q₁) ∧ 0 < cross2 (q₂ - q₁) (q₀ - q₁) ∧ 0 < cross2 (q₂ - q₁) (o - q₁) ∧
  0 < cross2 (q₃ - q₂) (q₀ - q₂) ∧ 0 < cross2 (q₃ - q₂) (q₁ - q₂) ∧ 0 < cross2 (q₃ - q₂) (o - q₂) ∧
  0 < cross2 (q₀ - q₃) (q₁ - q₃) ∧ 0 < cross2 (q₀ - q₃) (q₂ - q₃) ∧ 0 < cross2 (q₀ - q₃) (o - q₃)

theorem QuadLeft.isCcwPolygon {q₀ q₁ q₂ q₃ o : ℝ²} (h : QuadLeft q₀ q₁ q₂ q₃ o) :
    IsCcwPolygon (quad q₀ q₁ q₂ q₃) := by
  refine ⟨le_refl _ |>.trans' (by norm_num), fun i j h1 h2 => ?_⟩
  have hcase : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 0) ∨
      (i = 2 ∧ j = 0) ∨ (i = 2 ∧ j = 1) ∨ (i = 3 ∧ j = 1) ∨ (i = 3 ∧ j = 2) := by decide
  obtain ⟨h01, h02, -, h11, h12, -, h21, h22, -, h31, h32, -⟩ := h
  rcases hcase i j h1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [h01, h02, h11, h12, h21, h22, h31, h32]

theorem QuadLeft.left {q₀ q₁ q₂ q₃ o : ℝ²} (h : QuadLeft q₀ q₁ q₂ q₃ o) (i : ZMod 4) :
    0 < cross2 (quad q₀ q₁ q₂ q₃ (i + 1) - quad q₀ q₁ q₂ q₃ i) (o - quad q₀ q₁ q₂ q₃ i) := by
  obtain ⟨-, -, h0, -, -, h1, -, -, h2, -, -, h3⟩ := h
  have hcase : ∀ i : ZMod 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
  rcases hcase i with rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3]

theorem cross2_rev (u v X : ℝ²) : cross2 (u - v) (X - v) = -cross2 (v - u) (X - u) := by
  simp [cross2]; ring

/-- With `⟪N, e⟫ = 0`, `⟪N, ·⟫` is a multiple of `cross2 e ·`. -/
theorem inner_mul_eq_cross2_mul (N e X : ℝ²) (h : ⟪N, e⟫ = 0) :
    (e 0 ^ 2 + e 1 ^ 2) * ⟪N, X⟫ = cross2 e X * ⟪N, rot90 e⟫ := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial] at h ⊢
  simp only [cross2, rot90]
  simp
  linear_combination (e 0 * X 0 + e 1 * X 1) * h

theorem edge_sign {N u v X : ℝ²} (h0 : ⟪N, v - u⟫ = 0) (hX : ⟪N, X - u⟫ < 0) (huv : u ≠ v) :
    cross2 (v - u) (X - u) * ⟪N, rot90 (v - u)⟫ < 0 := by
  have hE : 0 < (v - u) 0 ^ 2 + (v - u) 1 ^ 2 := by
    by_contra hc
    push Not at hc
    have e0 : (v - u) 0 = 0 := by nlinarith [sq_nonneg ((v - u) 0), sq_nonneg ((v - u) 1)]
    have e1 : (v - u) 1 = 0 := by nlinarith [sq_nonneg ((v - u) 0), sq_nonneg ((v - u) 1)]
    apply huv
    have : v - u = 0 := by ext i; fin_cases i <;> simp [e0, e1]
    exact (sub_eq_zero.mp this).symm
  rw [← inner_mul_eq_cross2_mul N (v - u) (X - u) h0]
  exact mul_neg_of_pos_of_neg hE hX

theorem sign_aux {a b c : ℝ} (h1 : b * a < 0) (h2 : b * c < 0) : 0 < a * c := by
  nlinarith [sq_nonneg b, mul_pos_of_neg_of_neg h1 h2]

theorem pos_of_mul_neg_neg {a b : ℝ} (h : a * b < 0) (hb : b < 0) : 0 < a := by nlinarith

theorem neg_of_mul_neg_pos {a b : ℝ} (h : a * b < 0) (hb : 0 < b) : a < 0 := by nlinarith

theorem neg_of_mul_pos_neg {a b : ℝ} (h : 0 < a * b) (ha : a < 0) : b < 0 := by nlinarith

theorem pos_of_mul_pos_pos {a b : ℝ} (h : 0 < a * b) (ha : 0 < a) : 0 < b := by nlinarith

/-- Edge data for the four edges of a quadrilateral (a normal vanishing on the
edge and negative at the other points) make it strictly convex in one of the
two orientations, with `o` inside. -/
theorem quad_orient {q₀ q₁ q₂ q₃ o : ℝ²}
    (E₀ : ∃ N : ℝ², ⟪N, q₁ - q₀⟫ = 0 ∧ ⟪N, q₂ - q₀⟫ < 0 ∧ ⟪N, q₃ - q₀⟫ < 0 ∧ ⟪N, o - q₀⟫ < 0)
    (E₁ : ∃ N : ℝ², ⟪N, q₂ - q₁⟫ = 0 ∧ ⟪N, q₃ - q₁⟫ < 0 ∧ ⟪N, q₀ - q₁⟫ < 0 ∧ ⟪N, o - q₁⟫ < 0)
    (E₂ : ∃ N : ℝ², ⟪N, q₃ - q₂⟫ = 0 ∧ ⟪N, q₀ - q₂⟫ < 0 ∧ ⟪N, q₁ - q₂⟫ < 0 ∧ ⟪N, o - q₂⟫ < 0)
    (E₃ : ∃ N : ℝ², ⟪N, q₀ - q₃⟫ = 0 ∧ ⟪N, q₁ - q₃⟫ < 0 ∧ ⟪N, q₂ - q₃⟫ < 0 ∧ ⟪N, o - q₃⟫ < 0) :
    QuadLeft q₀ q₁ q₂ q₃ o ∨ QuadLeft q₀ q₃ q₂ q₁ o := by
  obtain ⟨N₀, z₀, a₀, b₀, o₀⟩ := E₀
  obtain ⟨N₁, z₁, a₁, b₁, o₁⟩ := E₁
  obtain ⟨N₂, z₂, a₂, b₂, o₂⟩ := E₂
  obtain ⟨N₃, z₃, a₃, b₃, o₃⟩ := E₃
  have n01 : q₀ ≠ q₁ := fun e => by rw [e, sub_self, inner_zero_right] at b₁; exact lt_irrefl _ b₁
  have n12 : q₁ ≠ q₂ := fun e => by rw [e, sub_self, inner_zero_right] at b₂; exact lt_irrefl _ b₂
  have n23 : q₂ ≠ q₃ := fun e => by rw [e, sub_self, inner_zero_right] at b₃; exact lt_irrefl _ b₃
  have n30 : q₃ ≠ q₀ := fun e => by rw [e, sub_self, inner_zero_right] at b₀; exact lt_irrefl _ b₀
  have A₀ := edge_sign z₀ a₀ n01
  have B₀ := edge_sign z₀ b₀ n01
  have O₀ := edge_sign z₀ o₀ n01
  have A₁ := edge_sign z₁ a₁ n12
  have B₁ := edge_sign z₁ b₁ n12
  have O₁ := edge_sign z₁ o₁ n12
  have A₂ := edge_sign z₂ a₂ n23
  have B₂ := edge_sign z₂ b₂ n23
  have O₂ := edge_sign z₂ o₂ n23
  have A₃ := edge_sign z₃ a₃ n30
  have B₃ := edge_sign z₃ b₃ n30
  have O₃ := edge_sign z₃ o₃ n30
  set s₀ := ⟪N₀, rot90 (q₁ - q₀)⟫
  set s₁ := ⟪N₁, rot90 (q₂ - q₁)⟫
  set s₂ := ⟪N₂, rot90 (q₃ - q₂)⟫
  set s₃ := ⟪N₃, rot90 (q₀ - q₃)⟫
  -- cyclic area identities link consecutive edges
  have c01 : cross2 (q₂ - q₁) (q₀ - q₁) = cross2 (q₁ - q₀) (q₂ - q₀) := by simp [cross2]; ring
  have c12 : cross2 (q₃ - q₂) (q₁ - q₂) = cross2 (q₂ - q₁) (q₃ - q₁) := by simp [cross2]; ring
  have c23 : cross2 (q₀ - q₃) (q₂ - q₃) = cross2 (q₃ - q₂) (q₀ - q₂) := by simp [cross2]; ring
  have s01 : 0 < s₀ * s₁ := sign_aux A₀ (by rw [← c01]; exact B₁)
  have s12 : 0 < s₁ * s₂ := sign_aux A₁ (by rw [← c12]; exact B₂)
  have s23 : 0 < s₂ * s₃ := sign_aux A₂ (by rw [← c23]; exact B₃)
  have hs0 : s₀ ≠ 0 := fun e => by rw [e, mul_zero] at A₀; exact lt_irrefl _ A₀
  rcases lt_or_gt_of_ne hs0 with h0 | h0
  · have h1 : s₁ < 0 := neg_of_mul_pos_neg s01 h0
    have h2 : s₂ < 0 := neg_of_mul_pos_neg s12 h1
    have h3 : s₃ < 0 := neg_of_mul_pos_neg s23 h2
    left
    exact ⟨pos_of_mul_neg_neg A₀ h0, pos_of_mul_neg_neg B₀ h0, pos_of_mul_neg_neg O₀ h0,
      pos_of_mul_neg_neg A₁ h1, pos_of_mul_neg_neg B₁ h1, pos_of_mul_neg_neg O₁ h1,
      pos_of_mul_neg_neg A₂ h2, pos_of_mul_neg_neg B₂ h2, pos_of_mul_neg_neg O₂ h2,
      pos_of_mul_neg_neg A₃ h3, pos_of_mul_neg_neg B₃ h3, pos_of_mul_neg_neg O₃ h3⟩
  · have h1 : 0 < s₁ := pos_of_mul_pos_pos s01 h0
    have h2 : 0 < s₂ := pos_of_mul_pos_pos s12 h1
    have h3 : 0 < s₃ := pos_of_mul_pos_pos s23 h2
    right
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [cross2_rev, neg_pos]
    exacts [neg_of_mul_neg_pos B₃ h3, neg_of_mul_neg_pos A₃ h3, neg_of_mul_neg_pos O₃ h3,
      neg_of_mul_neg_pos B₂ h2, neg_of_mul_neg_pos A₂ h2, neg_of_mul_neg_pos O₂ h2,
      neg_of_mul_neg_pos B₁ h1, neg_of_mul_neg_pos A₁ h1, neg_of_mul_neg_pos O₁ h1,
      neg_of_mul_neg_pos B₀ h0, neg_of_mul_neg_pos A₀ h0, neg_of_mul_neg_pos O₀ h0]

theorem quad_injective {α : Type*} {p₀ p₁ p₂ p₃ : α} (h01 : p₀ ≠ p₁) (h02 : p₀ ≠ p₂)
    (h03 : p₀ ≠ p₃) (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃) :
    Function.Injective (quad p₀ p₁ p₂ p₃) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | exact absurd hij h01
    | exact absurd hij h02
    | exact absurd hij h03
    | exact absurd hij h12
    | exact absurd hij h13
    | exact absurd hij h23
    | exact absurd hij.symm h01
    | exact absurd hij.symm h02
    | exact absurd hij.symm h03
    | exact absurd hij.symm h12
    | exact absurd hij.symm h13
    | exact absurd hij.symm h23

/-! ### From facets to the projected equator -/

theorem exists_normal_of_affine (f : ℝ³ →ᵃ[ℝ] ℝ) : ∃ N : ℝ³, ∀ y z, f y - f z = ⟪N, y - z⟫ := by
  refine ⟨(InnerProductSpace.toDual ℝ ℝ³).symm (LinearMap.toContinuousLinearMap f.linear),
    fun y z => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply, LinearMap.coe_toContinuousLinearMap']
  rw [← vsub_eq_sub y z, f.linear_apply_vsub]; rfl

/-- At a view along `d = a - a'`, a front facet `auv` and a back facet `a'uv`
combine into a normal of the projected edge `uv`, negative at the projected
poles and at any point below both facets. -/
theorem edge_normal_of_facets {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3)
    {a a' u v w₁ w₂ : ℝ³} {ρ : ℝ} (hρ : ρ ≠ 0) (hRd : R.toEuclideanLin (a - a') = ρ • ez)
    {f₁ f₂ : ℝ³ →ᵃ[ℝ] ℝ} (h1a : f₁ a = 0) (h1u : f₁ u = 0) (h1v : f₁ v = 0) (h1a' : f₁ a' < 0)
    (h1w₁ : f₁ w₁ < 0) (h1w₂ : f₁ w₂ < 0) (h2a' : f₂ a' = 0) (h2u : f₂ u = 0) (h2v : f₂ v = 0)
    (h2a : f₂ a < 0) (h2w₁ : f₂ w₁ < 0) (h2w₂ : f₂ w₂ < 0) :
    ∃ N : ℝ², ⟪N, projXy (R.toEuclideanLin v) - projXy (R.toEuclideanLin u)⟫ = 0 ∧
      ⟪N, projXy (R.toEuclideanLin w₁) - projXy (R.toEuclideanLin u)⟫ < 0 ∧
      ⟪N, projXy (R.toEuclideanLin w₂) - projXy (R.toEuclideanLin u)⟫ < 0 ∧
      ⟪N, projXy (R.toEuclideanLin a) - projXy (R.toEuclideanLin u)⟫ < 0 := by
  obtain ⟨N₁, hN₁⟩ := exists_normal_of_affine f₁
  obtain ⟨N₂, hN₂⟩ := exists_normal_of_affine f₂
  have hν : 0 < ⟪N₁, a - a'⟫ := by rw [← hN₁]; linarith
  have hμ : 0 < -⟪N₂, a - a'⟫ := by rw [← hN₂]; linarith
  set μ := -⟪N₂, a - a'⟫
  set ν := ⟪N₁, a - a'⟫
  set N₃ := μ • N₁ + ν • N₂ with hN₃
  have hN₃d : ⟪N₃, a - a'⟫ = 0 := by
    rw [hN₃, inner_add_left, real_inner_smul_left, real_inner_smul_left]; ring
  have hg : ∀ w, ⟪N₃, w - u⟫ = μ * f₁ w + ν * f₂ w := by
    intro w
    rw [hN₃, inner_add_left, real_inner_smul_left, real_inner_smul_left, ← hN₁, ← hN₂, h1u, h2u,
      sub_zero, sub_zero]
  have hhor : (R.toEuclideanLin N₃) 2 = 0 := by
    have : ρ * (R.toEuclideanLin N₃) 2 = ⟪R.toEuclideanLin N₃, R.toEuclideanLin (a - a')⟫ := by
      rw [hRd, real_inner_smul_right, inner_ez]
    rw [inner_toEuclideanLin_SO3 hR, hN₃d] at this
    exact (mul_eq_zero.mp this).resolve_left hρ
  have key : ∀ w, ⟪projXy (R.toEuclideanLin N₃),
      projXy (R.toEuclideanLin w) - projXy (R.toEuclideanLin u)⟫ = μ * f₁ w + ν * f₂ w := by
    intro w
    rw [← proj_xy_sub', inner_proj_xy_of_horizontal hhor, ← map_sub, inner_toEuclideanLin_SO3 hR,
      hg]
  refine ⟨projXy (R.toEuclideanLin N₃), ?_, ?_, ?_, ?_⟩ <;> rw [key]
  · rw [h1v, h2v]; ring
  · nlinarith [mul_neg_of_pos_of_neg hμ h1w₁, mul_neg_of_pos_of_neg hν h2w₁]
  · nlinarith [mul_neg_of_pos_of_neg hμ h1w₂, mul_neg_of_pos_of_neg hν h2w₂]
  · rw [h1a, mul_zero, zero_add]; exact mul_neg_of_pos_of_neg hν h2a

/-- An octahedron with opposite vertex pairs `(a, a')`, `(b, b')`, `(c, c')`:
the eight triangles with one vertex from each pair are facets. -/
structure IsOctahedron (a a' b b' c c' : ℝ³) : Prop where
  nodup : [a, a', b, b', c, c'].Nodup
  facet_abc : IsFacetTriangle {a, a', b, b', c, c'} a b c
  facet_abc' : IsFacetTriangle {a, a', b, b', c, c'} a b c'
  facet_ab'c : IsFacetTriangle {a, a', b, b', c, c'} a b' c
  facet_ab'c' : IsFacetTriangle {a, a', b, b', c, c'} a b' c'
  facet_a'bc : IsFacetTriangle {a, a', b, b', c, c'} a' b c
  facet_a'bc' : IsFacetTriangle {a, a', b, b', c, c'} a' b c'
  facet_a'b'c : IsFacetTriangle {a, a', b, b', c, c'} a' b' c
  facet_a'b'c' : IsFacetTriangle {a, a', b, b', c, c'} a' b' c'

/-- **Corollary 7.8 (Condition A).**  With `d = a - a'`, if the projections of
the diagonals `bb'` and `cc'` onto the axis `aa'` overlap in more than a point,
the octahedron is Rupert. -/
theorem isRupert_octahedron_conditionA {a a' b b' c c' : ℝ³} (h : IsOctahedron a a' b b' c c')
    (hA : max (min ⟪a - a', b⟫ ⟪a - a', b'⟫) (min ⟪a - a', c⟫ ⟪a - a', c'⟫) <
      min (max ⟪a - a', b⟫ ⟪a - a', b'⟫) (max ⟪a - a', c⟫ ⟪a - a', c'⟫)) :
    IsRupert {a, a', b, b', c, c'} := by
  classical
  have hnd := h.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  set V : Finset ℝ³ := {a, a', b, b', c, c'} with hV
  have haV : a ∈ V := Finset.mem_insert_self ..
  have ha'V : a' ∈ V := by simp [hV]
  have hbV : b ∈ V := by simp [hV]
  have hb'V : b' ∈ V := by simp [hV]
  have hcV : c ∈ V := by simp [hV]
  have hc'V : c' ∈ V := by simp [hV]
  obtain ⟨R, hR, r, hr, hRd⟩ := exists_rotation_to_ez (a - a') (sub_ne_zero.mpr haa')
  -- the eight facets
  obtain ⟨F₁, F₁a, F₁b, F₁c, F₁n⟩ := h.facet_abc
  obtain ⟨F₂, F₂a, F₂b, F₂c, F₂n⟩ := h.facet_abc'
  obtain ⟨F₃, F₃a, F₃b, F₃c, F₃n⟩ := h.facet_ab'c
  obtain ⟨F₄, F₄a, F₄b, F₄c, F₄n⟩ := h.facet_ab'c'
  obtain ⟨G₁, G₁a, G₁b, G₁c, G₁n⟩ := h.facet_a'bc
  obtain ⟨G₂, G₂a, G₂b, G₂c, G₂n⟩ := h.facet_a'bc'
  obtain ⟨G₃, G₃a, G₃b, G₃c, G₃n⟩ := h.facet_a'b'c
  obtain ⟨G₄, G₄a, G₄b, G₄c, G₄n⟩ := h.facet_a'b'c'
  have E₀ := edge_normal_of_facets (u := b) (v := c) (w₁ := b') (w₂ := c') hR hr hRd F₁a F₁b F₁c
    (F₁n a' ha'V (Ne.symm haa') ha'b ha'c)
    (F₁n b' hb'V (Ne.symm hab') (Ne.symm hbb') hb'c)
    (F₁n c' hc'V (Ne.symm hac') (Ne.symm hbc') (Ne.symm hcc'))
    G₁a G₁b G₁c (G₁n a haV haa' hab hac)
    (G₁n b' hb'V (Ne.symm ha'b') (Ne.symm hbb') hb'c)
    (G₁n c' hc'V (Ne.symm ha'c') (Ne.symm hbc') (Ne.symm hcc'))
  have E₁ := edge_normal_of_facets (u := c) (v := b') (w₁ := c') (w₂ := b) hR hr hRd F₃a F₃c F₃b
    (F₃n a' ha'V (Ne.symm haa') ha'b' ha'c)
    (F₃n c' hc'V (Ne.symm hac') (Ne.symm hb'c') (Ne.symm hcc'))
    (F₃n b hbV (Ne.symm hab) hbb' hbc)
    G₃a G₃c G₃b (G₃n a haV haa' hab' hac)
    (G₃n c' hc'V (Ne.symm ha'c') (Ne.symm hb'c') (Ne.symm hcc'))
    (G₃n b hbV (Ne.symm ha'b) hbb' hbc)
  have E₂ := edge_normal_of_facets (u := b') (v := c') (w₁ := b) (w₂ := c) hR hr hRd F₄a F₄b F₄c
    (F₄n a' ha'V (Ne.symm haa') ha'b' ha'c')
    (F₄n b hbV (Ne.symm hab) hbb' hbc')
    (F₄n c hcV (Ne.symm hac) (Ne.symm hb'c) hcc')
    G₄a G₄b G₄c (G₄n a haV haa' hab' hac')
    (G₄n b hbV (Ne.symm ha'b) hbb' hbc')
    (G₄n c hcV (Ne.symm ha'c) (Ne.symm hb'c) hcc')
  have E₃ := edge_normal_of_facets (u := c') (v := b) (w₁ := c) (w₂ := b') hR hr hRd F₂a F₂c F₂b
    (F₂n a' ha'V (Ne.symm haa') ha'b ha'c')
    (F₂n c hcV (Ne.symm hac) (Ne.symm hbc) hcc')
    (F₂n b' hb'V (Ne.symm hab') (Ne.symm hbb') hb'c')
    G₂a G₂c G₂b (G₂n a haV haa' hab hac')
    (G₂n c hcV (Ne.symm ha'c) (Ne.symm hbc) hcc')
    (G₂n b' hb'V (Ne.symm ha'b') (Ne.symm hbb') hb'c')
  have hPa' : projXy (R.toEuclideanLin a') = projXy (R.toEuclideanLin a) := by
    have : projXy (R.toEuclideanLin a) - projXy (R.toEuclideanLin a') = 0 := by
      rw [← proj_xy_sub', ← map_sub, hRd, proj_xy_smul']
      simp [projXy, ez]
    exact (sub_eq_zero.mp this).symm
  have hdepth : ∀ y, (R.toEuclideanLin y) 2 = r⁻¹ * ⟪a - a', y⟫ := by
    intro y
    have : r * (R.toEuclideanLin y) 2 = ⟪a - a', y⟫ := by
      rw [← inner_ez, ← real_inner_smul_right, ← hRd, inner_toEuclideanLin_SO3 hR,
        real_inner_comm]
    rw [← this]; field_simp
  have fin : ∀ u₁ u₃ : ℝ³, ((u₁ = c ∧ u₃ = c') ∨ (u₁ = c' ∧ u₃ = c)) →
      Overlap4 ⟪a - a', b⟫ ⟪a - a', u₁⟫ ⟪a - a', b'⟫ ⟪a - a', u₃⟫ →
      QuadLeft (projXy (R.toEuclideanLin b)) (projXy (R.toEuclideanLin u₁))
        (projXy (R.toEuclideanLin b')) (projXy (R.toEuclideanLin u₃))
        (projXy (R.toEuclideanLin a)) → IsRupert V := by
    intro u₁ u₃ hu hO hL
    have hx : ∀ i, quad b u₁ b' u₃ i ∈ V := by
      intro i
      rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> fin_cases i <;>
        first | exact hbV | exact hcV | exact hb'V | exact hc'V
    have hinj : Function.Injective (quad b u₁ b' u₃) := by
      rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact quad_injective hbc hbb' hbc' (Ne.symm hb'c) hcc' hb'c'
      · exact quad_injective hbc' hbb' hbc (Ne.symm hb'c') (Ne.symm hcc') hb'c
    have hPx : (fun i => projXy (R.toEuclideanLin (quad b u₁ b' u₃ i))) =
        quad (projXy (R.toEuclideanLin b)) (projXy (R.toEuclideanLin u₁))
          (projXy (R.toEuclideanLin b')) (projXy (R.toEuclideanLin u₃)) := by
      funext i; fin_cases i <;> rfl
    refine isRupert_of_open_unimodal V hR (quad b u₁ b' u₃) hx hinj ?_ ?_
      (fun z => Overlap4 (z 0) (z 1) (z 2) (z 3)) isOpen_overlap4 ?_
      (fun z hz hQ => isCyclicUnimodal_four hz hQ)
    · rw [hPx]; exact hL.isCcwPolygon
    · intro v hv hvx i
      have hPi : ∀ j, projXy (R.toEuclideanLin (quad b u₁ b' u₃ j)) =
          quad (projXy (R.toEuclideanLin b)) (projXy (R.toEuclideanLin u₁))
            (projXy (R.toEuclideanLin b')) (projXy (R.toEuclideanLin u₃)) j :=
        fun j => congrFun hPx j
      rw [hPi, hPi]
      have hva : v = a ∨ v = a' := by
        simp only [hV, mem_insert, mem_singleton] at hv
        have h0 := hvx 0; have h1 := hvx 1; have h2 := hvx 2; have h3 := hvx 3
        change v ≠ b at h0; change v ≠ u₁ at h1; change v ≠ b' at h2; change v ≠ u₃ at h3
        rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          clear * - hv h0 h1 h2 h3 <;> tauto
      rcases hva with rfl | rfl
      · exact hL.left i
      · rw [hPa']; exact hL.left i
    · change Overlap4 ((R.toEuclideanLin b) 2) ((R.toEuclideanLin u₁) 2)
        ((R.toEuclideanLin b') 2) ((R.toEuclideanLin u₃) 2)
      rw [hdepth, hdepth, hdepth, hdepth]
      exact hO.mul (inv_ne_zero hr)
  have hO := overlap4_of_minmax hA
  rcases quad_orient E₀ E₁ E₂ E₃ with hL | hL
  · exact fin c c' (Or.inl ⟨rfl, rfl⟩) hO hL
  · exact fin c' c (Or.inr ⟨rfl, rfl⟩) hO.symm hL

end Minimality

end RupertMinimality
