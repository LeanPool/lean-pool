/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.L8Shapes

/-! # L8 T3 -/

@[expose] public section

namespace RupertMinimality

/-!
# Theorem 8.4: every T3 is Rupert
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- **T3 (tetragonal antiwedge), combinatorial form**: the
quadrilateral facets `A C C' A'` and `B C C' B'`, and the triangles `ABC`,
`A'B'C'`, `ABB'`, `AB'A'` (the bent quad `ABB'A'` with diagonal `AB'`). -/
structure IsT3 (A B C A' B' C' : ℝ³) : Prop where
  nodup : [A, B, C, A', B', C'].Nodup
  affineIndependent : AffineIndependent ℝ ![A, B, C, C']
  quad₁ : IsFacet {A, B, C, A', B', C'} {A, C, C', A'}
  quad₂ : IsFacet {A, B, C, A', B', C'} {B, C, C', B'}
  facet_ABC : IsFacetTriangle {A, B, C, A', B', C'} A B C
  facet_A'B'C' : IsFacetTriangle {A, B, C, A', B', C'} A' B' C'
  facet_ABB' : IsFacetTriangle {A, B, C, A', B', C'} A B B'
  facet_AB'A' : IsFacetTriangle {A, B, C, A', B', C'} A B' A'

/-! ### Tools: 3- and 5-cycles -/

theorem isCyclicUnimodal_of_atMostOne {k : ℕ} [NeZero k] (hk : 2 ≤ k) {z : ZMod k → ℝ}
    (hinj : Function.Injective z)
    (h : ∀ i j, z (i - 1) < z i ∧ z (i + 1) < z i → z (j - 1) < z j ∧ z (j + 1) < z j → i = j) :
    IsCyclicUnimodal z := by
  refine ⟨hinj, le_antisymm ?_ ?_⟩
  · rw [Finset.card_le_one]
    intro i hi j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    exact h i j hi hj
  · obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ z ⟨0, Finset.mem_univ _⟩
    have c1 : m - 1 ≠ m := by
      intro e; have := zmod_ne_add_one hk (m - 1); rw [sub_add_cancel] at this; exact this e
    have c2 : m + 1 ≠ m := (zmod_ne_add_one hk m).symm
    refine Finset.card_pos.mpr ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩⟩
    · exact lt_of_le_of_ne (hm _ (Finset.mem_univ _)) (hinj.ne c1)
    · exact lt_of_le_of_ne (hm _ (Finset.mem_univ _)) (hinj.ne c2)

theorem isCyclicUnimodal_three {z : ZMod 3 → ℝ} (hinj : Function.Injective z) :
    IsCyclicUnimodal z := by
  refine isCyclicUnimodal_of_atMostOne (by norm_num) hinj fun i j hi hj => ?_
  by_contra hne
  have hc : ∀ i j : ZMod 3, i ≠ j → j = i + 1 ∨ i = j + 1 := by decide
  have hs : ∀ i : ZMod 3, i + 1 - 1 = i := fun i => by ring
  rcases hc i j hne with rfl | rfl
  · rw [hs] at hj; linarith [hi.2, hj.1]
  · rw [hs] at hi; linarith [hi.1, hj.2]

theorem zmod3_add_one : (0 : ZMod 3) + 1 = 1 ∧ (1 : ZMod 3) + 1 = 2 ∧ (2 : ZMod 3) + 1 = 0 := by
  decide

theorem zmod3_pairs : ∀ i j : ZMod 3, j ≠ i → j ≠ i + 1 →
    (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 1) := by decide

theorem zmod3_cases (i : ZMod 3) : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide

section tri
variable {α : Type*} (p₀ p₁ p₂ : α)
theorem tri_0 : tri p₀ p₁ p₂ 0 = p₀ := rfl
theorem tri_1 : tri p₀ p₁ p₂ 1 = p₁ := rfl
theorem tri_2 : tri p₀ p₁ p₂ 2 = p₂ := rfl
end tri

/-- Corollary 8.0′ for a triangular silhouette (any distinct depths are
unimodal). -/
theorem isRupert_of_tilted_three (V : Finset ℝ³) (u₀ v : ℝ³) (hu₀ : u₀ ≠ 0)
    (x : ZMod 3 → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → TiltSign (x (i + 1) - x i) (x j - x i) u₀ v)
    (hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i, TiltSign (x (i + 1) - x i) (y - x i) u₀ v) :
    IsRupert V :=
  isRupert_of_tilted_unimodal V u₀ v hu₀ (le_refl _) x hxV hcyc hrest (fun _ => True)
    (by simp) (fun _ _ _ _ => trivial) trivial (fun z hz _ => isCyclicUnimodal_three hz)

theorem zmod5_pairs : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
    (i = 0 ∧ (j = 2 ∨ j = 3 ∨ j = 4)) ∨ (i = 1 ∧ (j = 3 ∨ j = 4 ∨ j = 0)) ∨
    (i = 2 ∧ (j = 4 ∨ j = 0 ∨ j = 1)) ∨ (i = 3 ∧ (j = 0 ∨ j = 1 ∨ j = 2)) ∨
    (i = 4 ∧ (j = 1 ∨ j = 2 ∨ j = 3)) := by decide

/-- The robust condition of the 5-cycle `(A, B, B', C', A')` (case `BB' ∥ CC'`). -/
def Q5a (z : ZMod 5 → ℝ) : Prop := z 1 < z 0 ∧ z 1 < z 2 ∧ z 0 < z 4 ∧ z 2 < z 3

/-- The robust condition of the 5-cycle `(A, A', B', B, C)` (case `AA' ∥ CC'`). -/
def Q5b (z : ZMod 5 → ℝ) : Prop := z 0 < z 1 ∧ z 2 < z 1 ∧ z 4 < z 0 ∧ (z 3 < z 2 ∨ z 3 < z 4)

theorem unimodal5_tac {z : ZMod 5 → ℝ} (hinj : Function.Injective z)
    (h : ∀ i j : ZMod 5, z (i - 1) < z i ∧ z (i + 1) < z i →
      z (j - 1) < z j ∧ z (j + 1) < z j → i = j) : IsCyclicUnimodal z :=
  isCyclicUnimodal_of_atMostOne (by norm_num) hinj h

theorem isCyclicUnimodal_Q5a {z : ZMod 5 → ℝ} (hinj : Function.Injective z)
    (h : Q5a z ∨ Q5a fun i => -z i) : IsCyclicUnimodal z := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_sub_one
  refine unimodal5_tac hinj fun i j hi hj => ?_
  simp only [Q5a] at h
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [a0, a1, a2, a3, a4, b0, b1, b2, b3, b4] at hi hj <;>
    first | rfl | (exfalso; rcases h with h | h <;> linarith [hi.1, hi.2, hj.1, hj.2, h.1,
      h.2.1, h.2.2.1, h.2.2.2])

theorem isCyclicUnimodal_Q5b {z : ZMod 5 → ℝ} (hinj : Function.Injective z)
    (h : Q5b z ∨ Q5b fun i => -z i) : IsCyclicUnimodal z := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_sub_one
  refine unimodal5_tac hinj fun i j hi hj => ?_
  simp only [Q5b] at h
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [a0, a1, a2, a3, a4, b0, b1, b2, b3, b4] at hi hj <;>
    first | rfl | (exfalso; rcases h with ⟨h1, h2, h3, h4 | h4⟩ | ⟨h1, h2, h3, h4 | h4⟩ <;>
      linarith [hi.1, hi.2, hj.1, hj.2])

theorem isOpen_Q5a : IsOpen {z : ZMod 5 → ℝ | Q5a z ∨ Q5a fun i => -z i} := by
  have hlt : ∀ i j : ZMod 5, IsOpen {z : ZMod 5 → ℝ | z i < z j} := fun i j =>
    isOpen_lt (continuous_apply i) (continuous_apply j)
  have hlt' : ∀ i j : ZMod 5, IsOpen {z : ZMod 5 → ℝ | -z i < -z j} := fun i j =>
    isOpen_lt (continuous_apply i).neg (continuous_apply j).neg
  simp only [Q5a, Set.ofPred_and, Set.ofPred_or]
  exact ((hlt 1 0).inter ((hlt 1 2).inter ((hlt 0 4).inter (hlt 2 3)))).union
    ((hlt' 1 0).inter ((hlt' 1 2).inter ((hlt' 0 4).inter (hlt' 2 3))))

theorem isOpen_Q5b : IsOpen {z : ZMod 5 → ℝ | Q5b z ∨ Q5b fun i => -z i} := by
  have hlt : ∀ i j : ZMod 5, IsOpen {z : ZMod 5 → ℝ | z i < z j} := fun i j =>
    isOpen_lt (continuous_apply i) (continuous_apply j)
  have hlt' : ∀ i j : ZMod 5, IsOpen {z : ZMod 5 → ℝ | -z i < -z j} := fun i j =>
    isOpen_lt (continuous_apply i).neg (continuous_apply j).neg
  simp only [Q5b, Set.ofPred_and, Set.ofPred_or]
  exact ((hlt 0 1).inter ((hlt 2 1).inter ((hlt 4 0).inter ((hlt 3 2).union (hlt 3 4))))).union
    ((hlt' 0 1).inter ((hlt' 2 1).inter ((hlt' 4 0).inter ((hlt' 3 2).union (hlt' 3 4)))))

theorem Q5a_scale {z : ZMod 5 → ℝ} {c : ℝ} (hc : 0 < c) (h : Q5a z ∨ Q5a fun i => -z i) :
    Q5a (fun i => c * z i) ∨ Q5a fun i => -(c * z i) := by
  simp only [Q5a] at h ⊢
  have k : ∀ {x y : ℝ}, x < y → c * x < c * y := fun hxy => by nlinarith
  have k' : ∀ {x y : ℝ}, -x < -y → -(c * x) < -(c * y) := fun hxy => by nlinarith
  rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · exact Or.inl ⟨k h1, k h2, k h3, k h4⟩
  · exact Or.inr ⟨k' h1, k' h2, k' h3, k' h4⟩

theorem Q5b_scale {z : ZMod 5 → ℝ} {c : ℝ} (hc : 0 < c) (h : Q5b z ∨ Q5b fun i => -z i) :
    Q5b (fun i => c * z i) ∨ Q5b fun i => -(c * z i) := by
  simp only [Q5b] at h ⊢
  have k : ∀ {x y : ℝ}, x < y → c * x < c * y := fun hxy => by nlinarith
  have k' : ∀ {x y : ℝ}, -x < -y → -(c * x) < -(c * y) := fun hxy => by nlinarith
  rcases h with ⟨h1, h2, h3, h4 | h4⟩ | ⟨h1, h2, h3, h4 | h4⟩
  · exact Or.inl ⟨k h1, k h2, k h3, Or.inl (k h4)⟩
  · exact Or.inl ⟨k h1, k h2, k h3, Or.inr (k h4)⟩
  · exact Or.inr ⟨k' h1, k' h2, k' h3, Or.inl (k' h4)⟩
  · exact Or.inr ⟨k' h1, k' h2, k' h3, Or.inr (k' h4)⟩

theorem Q5a_affine {g : ZMod 5 → ℝ} (h : Q5a g) (c σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    Q5a (fun i => c + σ * g i) ∨ Q5a fun i => -(c + σ * g i) := by
  simp only [Q5a] at h ⊢
  rcases hσ with rfl | rfl
  · left; obtain ⟨h1, h2, h3, h4⟩ := h; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · right; obtain ⟨h1, h2, h3, h4⟩ := h; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem Q5b_affine {g : ZMod 5 → ℝ} (h : Q5b g) (c σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    Q5b (fun i => c + σ * g i) ∨ Q5b fun i => -(c + σ * g i) := by
  simp only [Q5b] at h ⊢
  rcases hσ with rfl | rfl
  · left; obtain ⟨h1, h2, h3, h4 | h4⟩ := h
    · exact ⟨by linarith, by linarith, by linarith, Or.inl (by linarith)⟩
    · exact ⟨by linarith, by linarith, by linarith, Or.inr (by linarith)⟩
  · right; obtain ⟨h1, h2, h3, h4 | h4⟩ := h
    · exact ⟨by linarith, by linarith, by linarith, Or.inl (by linarith)⟩
    · exact ⟨by linarith, by linarith, by linarith, Or.inr (by linarith)⟩

/-! ### Depth case analyses -/

theorem t3_nws_iii {a b c c' a' b' : ℝ} (hcc : c < c') (hA : a < a' ∨ c' < a')
    (hB : b < c ∨ b < b') :
    NWS4 (quad a b' c' c) ∨ NWS4 (quad a b' c' a') ∨ NWS4 (quad a b' b c) := by
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  simp only [NWS4, quad_0, quad_1, quad_2, quad_3, not_and_or, not_or, not_lt] at h1 h2 h3
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    rcases hA with hA | hA <;> rcases hB with hB | hB <;>
    linarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2,
      h3.1, h3.2.1, h3.2.2.1, h3.2.2.2]

theorem t3_nws_b1 {a b c c' a' b' : ℝ} (hcc : c < c') (hA : a < a' ∨ c' < a') (hbb : b < b') :
    NWS4 (quad a b' b c) ∨ NWS4 (quad a b' c' c) ∨ Q5a (quint a b b' c' a') := by
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  simp only [NWS4, quad_0, quad_1, quad_2, quad_3, not_and_or, not_or, not_lt] at h1 h2
  apply h3
  simp only [Q5a, quint_0, quint_1, quint_2, quint_3, quint_4]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    rcases hA with hA | hA <;>
    first
    | (exfalso; linarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2])
    | exact ⟨by linarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2],
        by linarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2],
        by linarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2],
        by linarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2]⟩

theorem t3_nws_a1 {a b c c' a' b' : ℝ} (hcc : c < c') (haa : a < a') (hB : b < c ∨ b < b') :
    NWS4 (quad a b' c' c) ∨ NWS4 (quad a b' c' a') ∨ Q5b (quint a a' b' b c) := by
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  simp only [NWS4, quad_0, quad_1, quad_2, quad_3, not_and_or, not_or, not_lt] at h1 h2
  apply h3
  simp only [Q5b, quint_0, quint_1, quint_2, quint_3, quint_4]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    first
    | (exfalso; linarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2])
    | (refine ⟨by linarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2],
        by linarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2],
        by linarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2], ?_⟩
       rcases hB with hB | hB
       · right; linarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2]
       · left; linarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2])

/-- The facet conditions put a T3 in normal form, in the frame
`(A - C, B - C, C' - C)`: `A' = (α, 0, α')`, `B' = (0, β, β')` with the convex
quads (`α + α' > 1`, `β + β' > 1`) and the bent quad `ABB'A'` with diagonal
`AB'` (`α' (1 - β) < β' (1 - α)`). -/
theorem IsT3.exists_normalForm {A B C A' B' C' : ℝ³} (h : IsT3 A B C A' B' C') :
    ∃ α α' β β' : ℝ, 0 < α ∧ 0 < α' ∧ 0 < β ∧ 0 < β' ∧ 1 < α + α' ∧ 1 < β + β' ∧
      α' * (1 - β) < β' * (1 - α) ∧
      A' = C + cmb (A - C) (B - C) (C' - C) α 0 α' ∧
      B' = C + cmb (A - C) (B - C) (C' - C) 0 β β' := by
  have hnd := h.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hAB, hAC, hAA', hAB', hAC'⟩, ⟨hBC, hBA', hBB', hBC'⟩, ⟨hCA', hCB', hCC'⟩,
    ⟨hA'B', hA'C'⟩, hB'C', -⟩ := hnd
  obtain ⟨lA, lB, lC, lC', hs1, hA'⟩ := exists_bary h.affineIndependent A'
  obtain ⟨mA, mB, mC, mC', hs2, hB'⟩ := exists_bary h.affineIndependent B'
  have ev1 := fun f : ℝ³ →ᵃ[ℝ] ℝ => (hA' ▸ affine_apply_comb4 f hs1 :
    f A' = lA * f A + lB * f B + lC * f C + lC' * f C')
  have ev2 := fun f : ℝ³ →ᵃ[ℝ] ℝ => (hB' ▸ affine_apply_comb4 f hs2 :
    f B' = mA * f A + mB * f B + mC * f C + mC' * f C')
  -- the quads
  obtain ⟨q₁, hq₁0, hq₁⟩ := h.quad₁
  have q₁A := hq₁0 A (by simp)
  have q₁C := hq₁0 C (by simp)
  have q₁C' := hq₁0 C' (by simp)
  have q₁A' := hq₁0 A' (by simp)
  have q₁B := hq₁ B (by simp) (by simp [Ne.symm hAB, hBC, hBC', hBA'])
  have q₁B' := hq₁ B' (by simp) (by simp [Ne.symm hAB', Ne.symm hCB', hB'C', Ne.symm hA'B'])
  obtain ⟨q₂, hq₂0, hq₂⟩ := h.quad₂
  have q₂B := hq₂0 B (by simp)
  have q₂C := hq₂0 C (by simp)
  have q₂C' := hq₂0 C' (by simp)
  have q₂B' := hq₂0 B' (by simp)
  have q₂A := hq₂ A (by simp) (by simp [hAB, hAC, hAC', hAB'])
  have q₂A' := hq₂ A' (by simp) (by simp [Ne.symm hBA', Ne.symm hCA', hA'C', hA'B'])
  have e1 := ev1 q₁
  rw [q₁A', q₁A, q₁C, q₁C'] at e1
  have hlB : lB = 0 := by
    have : lB * q₁ B = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right q₁B.ne
  have e2 := ev2 q₂
  rw [q₂B', q₂B, q₂C, q₂C'] at e2
  have hmA : mA = 0 := by
    have : mA * q₂ A = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right q₂A.ne
  have e3 := ev1 q₂
  rw [q₂B, q₂C, q₂C'] at e3
  have hα : 0 < lA := by
    by_contra hc; push Not at hc
    linarith only [e3, q₂A', mul_nonneg_of_nonpos_of_nonpos hc q₂A.le]
  have e4 := ev2 q₁
  rw [q₁A, q₁C, q₁C'] at e4
  have hβ : 0 < mB := by
    by_contra hc; push Not at hc
    linarith only [e4, q₁B', mul_nonneg_of_nonpos_of_nonpos hc q₁B.le]
  -- the triangle `ABC`
  obtain ⟨g, gA, gB, gC, hg⟩ := h.facet_ABC
  have gC' := hg C' (by simp) (Ne.symm hAC') (Ne.symm hBC') (Ne.symm hCC')
  have gA' := hg A' (by simp) (Ne.symm hAA') (Ne.symm hBA') (Ne.symm hCA')
  have gB' := hg B' (by simp) (Ne.symm hAB') (Ne.symm hBB') (Ne.symm hCB')
  rw [ev1, gA, gB, gC] at gA'
  rw [ev2, gA, gB, gC] at gB'
  have hα' : 0 < lC' := by
    by_contra hc; push Not at hc
    linarith only [gA', mul_nonneg_of_nonpos_of_nonpos hc gC'.le]
  have hβ' : 0 < mC' := by
    by_contra hc; push Not at hc
    linarith only [gB', mul_nonneg_of_nonpos_of_nonpos hc gC'.le]
  -- the bent quad `ABB'A'`
  obtain ⟨k, kA, kB, kB', hk⟩ := h.facet_ABB'
  have kC := hk C (by simp) (Ne.symm hAC) (Ne.symm hBC) hCB'
  have kC' := hk C' (by simp) (Ne.symm hAC') (Ne.symm hBC') (Ne.symm hB'C')
  have kA' := hk A' (by simp) (Ne.symm hAA') (Ne.symm hBA') hA'B'
  rw [ev2, kA, kB] at kB'
  rw [ev1, kA, kB] at kA'
  obtain ⟨n, nA, nB', nA', hn⟩ := h.facet_AB'A'
  have nC := hn C (by simp) (Ne.symm hAC) hCB' hCA'
  have nC' := hn C' (by simp) (Ne.symm hAC') (Ne.symm hB'C') (Ne.symm hA'C')
  rw [ev1, nA] at nA'
  have hmC : mC = 1 - mB - mC' := by linarith
  have hlC : lC = 1 - lA - lC' := by linarith
  have hB0 : mC * k C + mC' * k C' = 0 := by linarith
  have hA0 : lC * k C + lC' * k C' < 0 := by linarith
  have hN0 : lC * n C + lC' * n C' = 0 := by rw [hlB] at nA'; linarith
  have hbb : 1 < mB + mC' := by
    have h1 : mC' * k C' < 0 := mul_neg_of_pos_of_neg hβ' kC'
    have h2 : 0 < mC * k C := by linarith
    have h3 : mC < 0 := by
      by_contra hc; push Not at hc
      linarith [mul_nonpos_of_nonneg_of_nonpos hc kC.le]
    linarith
  have haa : 1 < lA + lC' := by
    have h1 : lC' * n C' < 0 := mul_neg_of_pos_of_neg hα' nC'
    have h2 : 0 < lC * n C := by linarith
    have h3 : lC < 0 := by
      by_contra hc; push Not at hc
      linarith [mul_nonpos_of_nonneg_of_nonpos hc nC.le]
    linarith
  have hbent : lC' * (1 - mB) < mC' * (1 - lA) := by
    have h1 : mC' * (lC * k C + lC' * k C') < 0 := mul_neg_of_pos_of_neg hβ' hA0
    have h2 : k C * (mC' * lC - lC' * mC) < 0 := by linear_combination h1 - lC' * hB0
    have h3 : 0 < mC' * lC - lC' * mC := by
      by_contra hc; push Not at hc
      linarith [mul_nonneg_of_nonpos_of_nonpos kC.le hc]
    rw [hmC, hlC] at h3; linarith
  refine ⟨lA, lC', mB, mC', hα, hα', hβ, hβ', haa, hbb, hbent, ?_, ?_⟩
  · rw [hA', hlB, hlC]; simp only [cmb]; module
  · rw [hB', hmA, hmC]; simp only [cmb]; module

/-- **T3, case `(X, Y) = (A, B)`**: the silhouette is the face `ABC`. -/
theorem isRupert_T3_i {A B C C' : ℝ³} (hΔ : det3 (A - C) (B - C) (C' - C) ≠ 0)
    {α α' β β' : ℝ} (hα : 0 < α) (hα' : 0 < α') (hβ : 0 < β) (hβ' : 0 < β')
    (h1α : α < 1) (h1β : β < 1) :
    IsRupert {A, B, C, C + cmb (A - C) (B - C) (C' - C) α 0 α',
      C + cmb (A - C) (B - C) (C' - C) 0 β β', C'} := by
  classical
  set f₁ := A - C
  set f₂ := B - C
  set f₃ := C' - C
  obtain ⟨σ, hσ, hD⟩ := det3_pos_or_neg hΔ
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  set P := fun a b c : ℝ => C + cmb f₁ f₂ f₃ a b c with hP
  have eA' : C + cmb f₁ f₂ f₃ α 0 α' = P α 0 α' := rfl
  have eB' : C + cmb f₁ f₂ f₃ 0 β β' = P 0 β β' := rfl
  have eA : A = P 1 0 0 := by simp [hP, cmb, f₁]
  have eB : B = P 0 1 0 := by simp [hP, cmb, f₂]
  have eC : C = P 0 0 0 := by simp [hP, cmb]
  have eC' : C' = P 0 0 1 := by simp [hP, cmb, f₃]
  rw [eA', eB', eA, eB, eC, eC']
  set V : Finset ℝ³ := {P 1 0 0, P 0 1 0, P 0 0 0, P α 0 α', P 0 β β', P 0 0 1} with hV
  have hmemV : ∀ z ∈ V, z = P 1 0 0 ∨ z = P 0 1 0 ∨ z = P 0 0 0 ∨ z = P α 0 α' ∨
      z = P 0 β β' ∨ z = P 0 0 1 := by
    intro z hz; simpa [hV] using hz
  set u₀ := σ • cmb f₁ f₂ f₃ 0 0 1 with hu₀
  have hd : cmb f₁ f₂ f₃ 0 0 1 = f₃ := by simp [cmb]
  have hf₃ : f₃ ≠ 0 := by
    intro h0
    have := (cmb_eq_zero hΔ (hd.trans h0)).2.2
    norm_num at this
  have hu₀0 : u₀ ≠ 0 := by rw [hu₀, hd]; exact smul_ne_zero hσ0 hf₃
  have hs0 : 0 < ⟪f₃, f₃⟫ := real_inner_self_pos.mpr hf₃
  have hdepth : ∀ a b c, ⟪P a b c, u₀⟫ =
      ⟪C, u₀⟫ + σ * (a * ⟪f₁, f₃⟫ + b * ⟪f₂, f₃⟫ + c * ⟪f₃, f₃⟫) := by
    intro a b c
    rw [hP]; simp only [inner_add_cmb, hu₀, hd, real_inner_smul_right]; ring
  obtain ⟨a0, a1, a2⟩ := zmod3_add_one
  replace h1α := sub_pos.mpr h1α
  replace h1β := sub_pos.mpr h1β
  have Pαβ := mul_pos hα' hβ
  refine isRupert_of_tilted_three V u₀ (σ • cmb f₁ f₂ f₃ (-1 / 2) (-β / 2) (-β' / 2)) hu₀0
    (tri (P 1 0 0) (P 0 1 0) (P 0 0 0)) ?_ ?_ ?_
  · intro i; rcases zmod3_cases i with rfl | rfl | rfl <;>
      simp [hV, tri_0, tri_1, tri_2]
  · intro i j hi hj
    rcases zmod3_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [a0, a1, a2, tri_0, tri_1, tri_2, hP, add_cmb_sub, hu₀] <;>
    exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
      (by simp only [detc]; clear * - hα hα' hβ hβ' h1α h1β Pαβ; linarith)
  · intro z hz hzx i
    have hx0 := hzx 0; have hx1 := hzx 1; have hx2 := hzx 2
    simp only [tri_0, tri_1, tri_2] at hx0 hx1 hx2
    rcases hmemV z hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
      try (first | exact absurd rfl hx0 | exact absurd rfl hx1 | exact absurd rfl hx2)
    all_goals
      rcases zmod3_cases i with rfl | rfl | rfl <;>
      simp only [a0, a1, a2, tri_0, tri_1, tri_2, hP, add_cmb_sub, hu₀] <;>
      first
        | exact tiltSign_zero hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _) (by simp only [detc]; ring1)
            (by simp only [detc]; clear * - hα hα' hβ hβ' h1α h1β Pαβ; linarith)
        | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (by simp only [detc]; clear * - hα hα' hβ hβ' h1α h1β Pαβ; linarith)

/-- **T3, case `(X, Y) = (A', B')`**: the silhouette is the face `A'B'C'`. -/
theorem isRupert_T3_ii {A B C C' : ℝ³} (hΔ : det3 (A - C) (B - C) (C' - C) ≠ 0)
    {α α' β β' : ℝ} (hα : 0 < α) (_ : 0 < α') (hβ : 0 < β) (_ : 0 < β')
    (h1α : 1 < α) (h1β : 1 < β) (haa : 1 < α + α') (hbb : 1 < β + β') :
    IsRupert {A, B, C, C + cmb (A - C) (B - C) (C' - C) α 0 α',
      C + cmb (A - C) (B - C) (C' - C) 0 β β', C'} := by
  classical
  set f₁ := A - C
  set f₂ := B - C
  set f₃ := C' - C
  obtain ⟨σ, hσ, hD⟩ := det3_pos_or_neg hΔ
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  set P := fun a b c : ℝ => C + cmb f₁ f₂ f₃ a b c with hP
  have eA' : C + cmb f₁ f₂ f₃ α 0 α' = P α 0 α' := rfl
  have eB' : C + cmb f₁ f₂ f₃ 0 β β' = P 0 β β' := rfl
  have eA : A = P 1 0 0 := by simp [hP, cmb, f₁]
  have eB : B = P 0 1 0 := by simp [hP, cmb, f₂]
  have eC : C = P 0 0 0 := by simp [hP, cmb]
  have eC' : C' = P 0 0 1 := by simp [hP, cmb, f₃]
  rw [eA', eB', eA, eB, eC, eC']
  set V : Finset ℝ³ := {P 1 0 0, P 0 1 0, P 0 0 0, P α 0 α', P 0 β β', P 0 0 1} with hV
  have hmemV : ∀ z ∈ V, z = P 1 0 0 ∨ z = P 0 1 0 ∨ z = P 0 0 0 ∨ z = P α 0 α' ∨
      z = P 0 β β' ∨ z = P 0 0 1 := by
    intro z hz; simpa [hV] using hz
  set u₀ := σ • cmb f₁ f₂ f₃ 0 0 1 with hu₀
  have hd : cmb f₁ f₂ f₃ 0 0 1 = f₃ := by simp [cmb]
  have hf₃ : f₃ ≠ 0 := by
    intro h0
    have := (cmb_eq_zero hΔ (hd.trans h0)).2.2
    norm_num at this
  have hu₀0 : u₀ ≠ 0 := by rw [hu₀, hd]; exact smul_ne_zero hσ0 hf₃
  have hs0 : 0 < ⟪f₃, f₃⟫ := real_inner_self_pos.mpr hf₃
  have hdepth : ∀ a b c, ⟪P a b c, u₀⟫ =
      ⟪C, u₀⟫ + σ * (a * ⟪f₁, f₃⟫ + b * ⟪f₂, f₃⟫ + c * ⟪f₃, f₃⟫) := by
    intro a b c
    rw [hP]; simp only [inner_add_cmb, hu₀, hd, real_inner_smul_right]; ring
  obtain ⟨a0, a1, a2⟩ := zmod3_add_one
  have Q1 := mul_pos hβ (sub_pos.mpr h1α)
  have Q2 := mul_pos hα (sub_pos.mpr h1β)
  have Q3 := mul_pos hα hβ
  have Q4 := mul_pos hβ (sub_pos.mpr haa)
  replace hbb := sub_pos.mpr hbb
  refine isRupert_of_tilted_three V u₀ (σ • cmb f₁ f₂ f₃ (1 / 2) (β / 2) (β' / 2)) hu₀0
    (tri (P α 0 α') (P 0 β β') (P 0 0 1)) ?_ ?_ ?_
  · intro i; rcases zmod3_cases i with rfl | rfl | rfl <;>
      simp [hV, tri_0, tri_1, tri_2]
  · intro i j hi hj
    rcases zmod3_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [a0, a1, a2, tri_0, tri_1, tri_2, hP, add_cmb_sub, hu₀] <;>
    first
      | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
          (by simp only [detc]; clear * - hα hβ Q1 Q2 Q3 hbb Q4; linarith)
  · intro z hz hzx i
    have hx0 := hzx 0; have hx1 := hzx 1; have hx2 := hzx 2
    simp only [tri_0, tri_1, tri_2] at hx0 hx1 hx2
    rcases hmemV z hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
      try (first | exact absurd rfl hx0 | exact absurd rfl hx1 | exact absurd rfl hx2)
    all_goals
      rcases zmod3_cases i with rfl | rfl | rfl <;>
      simp only [a0, a1, a2, tri_0, tri_1, tri_2, hP, add_cmb_sub, hu₀] <;>
      first
        | exact tiltSign_zero hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _) (by simp only [detc]; ring1)
            (by simp only [detc]; clear * - hα hβ Q1 Q2 Q3 hbb Q4; linarith)
        | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (by simp only [detc]; clear * - hα hβ Q1 Q2 Q3 hbb Q4; linarith)

private theorem depth_below_affine_combination {a b x y : ℝ} (ha : 0 < a)
    (ha₁ : 0 < 1 - a) (hab : 0 < a + b - 1) (hy : 0 < y) :
    x < a * x + b * y ∨ y < a * x + b * y := by
  have hbalance := mul_pos hab hy
  rcases le_or_gt x y with hxy | hyx
  · exact Or.inl (by linarith only [hbalance, mul_le_mul_of_nonneg_left hxy ha₁.le])
  · exact Or.inr (by linarith only [hbalance, mul_lt_mul_of_pos_left hyx ha])

private theorem depth_below_positive_combination {a b x y : ℝ} (ha : 0 < a - 1)
    (hb : 0 < b) (hy : 0 < y) : x < 0 ∨ x < a * x + b * y := by
  rcases lt_or_ge x 0 with hx | hx
  · exact Or.inl hx
  · exact Or.inr (by linarith only [mul_pos hb hy, mul_nonneg ha.le hx])

/-- **T3, case `(X, Y) = (A, B')`**: one of `LU`, `UU`, `LL` is robustly unimodal. -/
theorem isRupert_T3_iii {A B C C' : ℝ³} (hΔ : det3 (A - C) (B - C) (C' - C) ≠ 0)
    {α α' β β' : ℝ} (hα : 0 < α) (hα' : 0 < α') (hβ : 0 < β) (hβ' : 0 < β')
    (h1α : α < 1) (h1β : 1 < β) (haa : 1 < α + α') (hbb : 1 < β + β') :
    IsRupert {A, B, C, C + cmb (A - C) (B - C) (C' - C) α 0 α',
      C + cmb (A - C) (B - C) (C' - C) 0 β β', C'} := by
  classical
  set f₁ := A - C
  set f₂ := B - C
  set f₃ := C' - C
  obtain ⟨σ, hσ, hD⟩ := det3_pos_or_neg hΔ
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  set P := fun a b c : ℝ => C + cmb f₁ f₂ f₃ a b c with hP
  have eA' : C + cmb f₁ f₂ f₃ α 0 α' = P α 0 α' := rfl
  have eB' : C + cmb f₁ f₂ f₃ 0 β β' = P 0 β β' := rfl
  have eA : A = P 1 0 0 := by simp [hP, cmb, f₁]
  have eB : B = P 0 1 0 := by simp [hP, cmb, f₂]
  have eC : C = P 0 0 0 := by simp [hP, cmb]
  have eC' : C' = P 0 0 1 := by simp [hP, cmb, f₃]
  rw [eA', eB', eA, eB, eC, eC']
  set V : Finset ℝ³ := {P 1 0 0, P 0 1 0, P 0 0 0, P α 0 α', P 0 β β', P 0 0 1} with hV
  have hmemV : ∀ z ∈ V, z = P 1 0 0 ∨ z = P 0 1 0 ∨ z = P 0 0 0 ∨ z = P α 0 α' ∨
      z = P 0 β β' ∨ z = P 0 0 1 := by
    intro z hz; simpa [hV] using hz
  set u₀ := σ • cmb f₁ f₂ f₃ 0 0 1 with hu₀
  have hd : cmb f₁ f₂ f₃ 0 0 1 = f₃ := by simp [cmb]
  have hf₃ : f₃ ≠ 0 := by
    intro h0
    have := (cmb_eq_zero hΔ (hd.trans h0)).2.2
    norm_num at this
  have hu₀0 : u₀ ≠ 0 := by rw [hu₀, hd]; exact smul_ne_zero hσ0 hf₃
  have hs0 : 0 < ⟪f₃, f₃⟫ := real_inner_self_pos.mpr hf₃
  have hdepth : ∀ a b c, ⟪P a b c, u₀⟫ =
      ⟪C, u₀⟫ + σ * (a * ⟪f₁, f₃⟫ + b * ⟪f₂, f₃⟫ + c * ⟪f₃, f₃⟫) := by
    intro a b c
    rw [hP]; simp only [inner_add_cmb, hu₀, hd, real_inner_smul_right]; ring
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  replace h1α := sub_pos.mpr h1α
  replace h1β := sub_pos.mpr h1β
  have Q1 := mul_pos hβ h1α
  have Q2 := mul_pos hα h1β
  have Q3 := mul_pos hα hβ
  have Q4 := mul_pos hβ (sub_pos.mpr haa)
  have Q5 := mul_pos hα' hβ
  replace hbb := sub_pos.mpr hbb
  have hA : ⟪f₁, f₃⟫ < α * ⟪f₁, f₃⟫ + α' * ⟪f₃, f₃⟫ ∨
      ⟪f₃, f₃⟫ < α * ⟪f₁, f₃⟫ + α' * ⟪f₃, f₃⟫ :=
    depth_below_affine_combination hα h1α (sub_pos.mpr haa) hs0
  have hB : ⟪f₂, f₃⟫ < 0 ∨ ⟪f₂, f₃⟫ < β * ⟪f₂, f₃⟫ + β' * ⟪f₃, f₃⟫ :=
    depth_below_positive_combination h1β hβ' hs0
  rcases t3_nws_iii hs0 hA hB with h | h | h
  · -- LU = (A, B', C', C)
    have hQ : NWS4 fun i => ⟪quad (P 1 0 0) (P 0 β β') (P 0 0 1) (P 0 0 0) i, u₀⟫ := by
      have := h.affine ⟪C, u₀⟫ hσ0
      convert this using 2 with i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, hdepth] <;> ring
    refine isRupert_of_tilted_NWS4 V u₀ (σ • cmb f₁ f₂ f₃ 1 (-β / 2) (-β' / 2)) hu₀0 (quad (P 1 0
      0) (P 0 β β') (P 0 0 1) (P 0 0 0)) ?_ ?_ ?_ hQ
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp [hV, quad_0, quad_1, quad_2, quad_3]
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, hP, add_cmb_sub, hu₀] <;>
      first
        | exact tiltSign_zero hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _) (by simp only [detc]; ring1)
            (by simp only [detc]; clear * - hα hα' hβ hβ' h1α h1β Q1 Q2 Q3 Q4 Q5 hbb; linarith)
        | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (by simp only [detc]; clear * - hα hα' hβ hβ' h1α h1β Q1 Q2 Q3 Q4 Q5 hbb; linarith)
    · intro z hz hzx i
      have hx0 := hzx 0; have hx1 := hzx 1; have hx2 := hzx 2; have hx3 := hzx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at hx0 hx1 hx2 hx3
      rcases hmemV z hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
        try (first | exact absurd rfl hx0 | exact absurd rfl hx1 | exact absurd rfl hx2 |
          exact absurd rfl hx3)
      all_goals
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, hP, add_cmb_sub, hu₀] <;>
        first
          | exact tiltSign_zero hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
              (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _) (by simp only [detc]; ring1)
              (by simp only [detc]; clear * - hα hα' hβ hβ' h1α h1β Q1 Q2 Q3 Q4 Q5 hbb; linarith)
          | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
              (by simp only [detc]; clear * - hα hα' hβ hβ' h1α h1β Q1 Q2 Q3 Q4 Q5 hbb; linarith)
  · -- UU = (A, B', C', A')
    have hQ : NWS4 fun i => ⟪quad (P 1 0 0) (P 0 β β') (P 0 0 1) (P α 0 α') i, u₀⟫ := by
      have := h.affine ⟪C, u₀⟫ hσ0
      convert this using 2 with i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, hdepth] <;> ring
    refine isRupert_of_tilted_NWS4 V u₀ (σ • cmb f₁ f₂ f₃ (1 / 2) (β / 2) (β' / 2)) hu₀0 (quad (P
      1 0 0) (P 0 β β') (P 0 0 1) (P α 0 α')) ?_ ?_ ?_ hQ
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp [hV, quad_0, quad_1, quad_2, quad_3]
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, hP, add_cmb_sub, hu₀] <;>
      first
        | exact tiltSign_zero hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _) (by simp only [detc]; ring1)
            (by simp only [detc]; clear * - hα hα' hβ hβ' h1α h1β Q1 Q2 Q3 Q4 Q5 hbb; linarith)
        | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (by simp only [detc]; clear * - hα hα' hβ hβ' h1α h1β Q1 Q2 Q3 Q4 Q5 hbb; linarith)
    · intro z hz hzx i
      have hx0 := hzx 0; have hx1 := hzx 1; have hx2 := hzx 2; have hx3 := hzx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at hx0 hx1 hx2 hx3
      rcases hmemV z hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
        try (first | exact absurd rfl hx0 | exact absurd rfl hx1 | exact absurd rfl hx2 |
          exact absurd rfl hx3)
      all_goals
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, hP, add_cmb_sub, hu₀] <;>
        first
          | exact tiltSign_zero hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
              (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _) (by simp only [detc]; ring1)
              (by simp only [detc]; clear * - hα hα' hβ hβ' h1α h1β Q1 Q2 Q3 Q4 Q5 hbb; linarith)
          | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
              (by simp only [detc]; clear * - hα hα' hβ hβ' h1α h1β Q1 Q2 Q3 Q4 Q5 hbb; linarith)
  · -- LL = (A, B', B, C)
    have hQ : NWS4 fun i => ⟪quad (P 1 0 0) (P 0 β β') (P 0 1 0) (P 0 0 0) i, u₀⟫ := by
      have := h.affine ⟪C, u₀⟫ hσ0
      convert this using 2 with i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, hdepth] <;> ring
    refine isRupert_of_tilted_NWS4 V u₀ (σ • cmb f₁ f₂ f₃ (-1 / 2) (-β / 2) (-β' / 2)) hu₀0 (quad
      (P 1 0 0) (P 0 β β') (P 0 1 0) (P 0 0 0)) ?_ ?_ ?_ hQ
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp [hV, quad_0, quad_1, quad_2, quad_3]
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, hP, add_cmb_sub, hu₀] <;>
      first
        | exact tiltSign_zero hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _) (by simp only [detc]; ring1)
            (by simp only [detc]; clear * - hα hα' hβ hβ' h1α h1β Q1 Q2 Q3 Q4 Q5 hbb; linarith)
        | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (by simp only [detc]; clear * - hα hα' hβ hβ' h1α h1β Q1 Q2 Q3 Q4 Q5 hbb; linarith)
    · intro z hz hzx i
      have hx0 := hzx 0; have hx1 := hzx 1; have hx2 := hzx 2; have hx3 := hzx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at hx0 hx1 hx2 hx3
      rcases hmemV z hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
        try (first | exact absurd rfl hx0 | exact absurd rfl hx1 | exact absurd rfl hx2 |
          exact absurd rfl hx3)
      all_goals
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, hP, add_cmb_sub, hu₀] <;>
        first
          | exact tiltSign_zero hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
              (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _) (by simp only [detc]; ring1)
              (by simp only [detc]; clear * - hα hα' hβ hβ' h1α h1β Q1 Q2 Q3 Q4 Q5 hbb; linarith)
          | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
              (by simp only [detc]; clear * - hα hα' hβ hβ' h1α h1β Q1 Q2 Q3 Q4 Q5 hbb; linarith)

/-- **T3, degenerate case `BB' ∥ CC'`**: `LL`, `LU`, or the 5-cycle `(A, B, B', C', A')`. -/
theorem isRupert_T3_b1 {A B C C' : ℝ³} (hΔ : det3 (A - C) (B - C) (C' - C) ≠ 0)
    {α α' β' : ℝ} (hα : 0 < α) (hα' : 0 < α') (hβ' : 0 < β')
    (h1α : α < 1) (haa : 1 < α + α') :
    IsRupert {A, B, C, C + cmb (A - C) (B - C) (C' - C) α 0 α',
      C + cmb (A - C) (B - C) (C' - C) 0 1 β', C'} := by
  classical
  set f₁ := A - C
  set f₂ := B - C
  set f₃ := C' - C
  obtain ⟨σ, hσ, hD⟩ := det3_pos_or_neg hΔ
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  set P := fun a b c : ℝ => C + cmb f₁ f₂ f₃ a b c with hP
  have eA' : C + cmb f₁ f₂ f₃ α 0 α' = P α 0 α' := rfl
  have eB' : C + cmb f₁ f₂ f₃ 0 1 β' = P 0 1 β' := rfl
  have eA : A = P 1 0 0 := by simp [hP, cmb, f₁]
  have eB : B = P 0 1 0 := by simp [hP, cmb, f₂]
  have eC : C = P 0 0 0 := by simp [hP, cmb]
  have eC' : C' = P 0 0 1 := by simp [hP, cmb, f₃]
  rw [eA', eB', eA, eB, eC, eC']
  set V : Finset ℝ³ := {P 1 0 0, P 0 1 0, P 0 0 0, P α 0 α', P 0 1 β', P 0 0 1} with hV
  have hmemV : ∀ z ∈ V, z = P 1 0 0 ∨ z = P 0 1 0 ∨ z = P 0 0 0 ∨ z = P α 0 α' ∨
      z = P 0 1 β' ∨ z = P 0 0 1 := by
    intro z hz; simpa [hV] using hz
  set u₀ := σ • cmb f₁ f₂ f₃ 0 0 1 with hu₀
  have hd : cmb f₁ f₂ f₃ 0 0 1 = f₃ := by simp [cmb]
  have hf₃ : f₃ ≠ 0 := by
    intro h0
    have := (cmb_eq_zero hΔ (hd.trans h0)).2.2
    norm_num at this
  have hu₀0 : u₀ ≠ 0 := by rw [hu₀, hd]; exact smul_ne_zero hσ0 hf₃
  have hs0 : 0 < ⟪f₃, f₃⟫ := real_inner_self_pos.mpr hf₃
  have hdepth : ∀ a b c, ⟪P a b c, u₀⟫ =
      ⟪C, u₀⟫ + σ * (a * ⟪f₁, f₃⟫ + b * ⟪f₂, f₃⟫ + c * ⟪f₃, f₃⟫) := by
    intro a b c
    rw [hP]; simp only [inner_add_cmb, hu₀, hd, real_inner_smul_right]; ring
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  replace h1α := sub_pos.mpr h1α
  replace haa := sub_pos.mpr haa
  have Q1 := mul_pos hα hβ'
  have Q2 := mul_pos hα' hβ'
  have hA : ⟪f₁, f₃⟫ < α * ⟪f₁, f₃⟫ + α' * ⟪f₃, f₃⟫ ∨
      ⟪f₃, f₃⟫ < α * ⟪f₁, f₃⟫ + α' * ⟪f₃, f₃⟫ :=
    depth_below_affine_combination hα h1α haa hs0
  have hbb : ⟪f₂, f₃⟫ < ⟪f₂, f₃⟫ + β' * ⟪f₃, f₃⟫ := by
    linarith only [mul_pos hβ' hs0]
  rcases t3_nws_b1 hs0 hA hbb with h | h | h
  · -- LL = (A, B', B, C)
    have hQ : NWS4 fun i => ⟪quad (P 1 0 0) (P 0 1 β') (P 0 1 0) (P 0 0 0) i, u₀⟫ := by
      have := h.affine ⟪C, u₀⟫ hσ0
      convert this using 2 with i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, hdepth] <;> ring
    refine isRupert_of_tilted_NWS4 V u₀ (σ • cmb f₁ f₂ f₃ (-1 / 2) (-1 / 2) (-β' / 2)) hu₀0 (quad
      (P 1 0 0) (P 0 1 β') (P 0 1 0) (P 0 0 0)) ?_ ?_ ?_ hQ
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp [hV, quad_0, quad_1, quad_2, quad_3]
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, hP, add_cmb_sub, hu₀] <;>
      first
        | exact tiltSign_zero hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _) (by simp only [detc]; ring1)
            (by simp only [detc]; clear * - hα hα' hβ' h1α haa Q1 Q2; linarith)
        | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (by simp only [detc]; clear * - hα hα' hβ' h1α haa Q1 Q2; linarith)
    · intro z hz hzx i
      have hx0 := hzx 0; have hx1 := hzx 1; have hx2 := hzx 2; have hx3 := hzx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at hx0 hx1 hx2 hx3
      rcases hmemV z hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
        try (first | exact absurd rfl hx0 | exact absurd rfl hx1 | exact absurd rfl hx2 |
          exact absurd rfl hx3)
      all_goals
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, hP, add_cmb_sub, hu₀] <;>
        first
          | exact tiltSign_zero hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
              (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _) (by simp only [detc]; ring1)
              (by simp only [detc]; clear * - hα hα' hβ' h1α haa Q1 Q2; linarith)
          | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
              (by simp only [detc]; clear * - hα hα' hβ' h1α haa Q1 Q2; linarith)
  · -- LU = (A, B', C', C)
    have hQ : NWS4 fun i => ⟪quad (P 1 0 0) (P 0 1 β') (P 0 0 1) (P 0 0 0) i, u₀⟫ := by
      have := h.affine ⟪C, u₀⟫ hσ0
      convert this using 2 with i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, hdepth] <;> ring
    refine isRupert_of_tilted_NWS4 V u₀ (σ • cmb f₁ f₂ f₃ (1 / 2) (-1) (-β')) hu₀0 (quad (P 1 0
      0) (P 0 1 β') (P 0 0 1) (P 0 0 0)) ?_ ?_ ?_ hQ
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp [hV, quad_0, quad_1, quad_2, quad_3]
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, hP, add_cmb_sub, hu₀] <;>
      first
        | exact tiltSign_zero hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _) (by simp only [detc]; ring1)
            (by simp only [detc]; clear * - hα hα' hβ' h1α haa Q1 Q2; linarith)
        | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (by simp only [detc]; clear * - hα hα' hβ' h1α haa Q1 Q2; linarith)
    · intro z hz hzx i
      have hx0 := hzx 0; have hx1 := hzx 1; have hx2 := hzx 2; have hx3 := hzx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at hx0 hx1 hx2 hx3
      rcases hmemV z hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
        try (first | exact absurd rfl hx0 | exact absurd rfl hx1 | exact absurd rfl hx2 |
          exact absurd rfl hx3)
      all_goals
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, hP, add_cmb_sub, hu₀] <;>
        first
          | exact tiltSign_zero hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
              (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _) (by simp only [detc]; ring1)
              (by simp only [detc]; clear * - hα hα' hβ' h1α haa Q1 Q2; linarith)
          | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
              (by simp only [detc]; clear * - hα hα' hβ' h1α haa Q1 Q2; linarith)
  · -- the 5-cycle (A, B, B', C', A')
    have hQ : Q5a (fun i => ⟪quint (P 1 0 0) (P 0 1 0) (P 0 1 β') (P 0 0 1) (P α 0 α') i, u₀⟫) ∨
      Q5a fun i => -⟪quint (P 1 0 0) (P 0 1 0) (P 0 1 β') (P 0 0 1) (P α 0 α') i, u₀⟫ := by
      have := Q5a_affine h ⟪C, u₀⟫ σ hσ
      convert this using 3 <;> rename_i i <;>
        rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        simp only [quint_0, quint_1, quint_2, quint_3, quint_4, hdepth] <;> ring
    refine isRupert_of_tilted_unimodal V u₀ (σ • cmb f₁ f₂ f₃ (1 / 2) (1 / 2) (β' / 2)) hu₀0 (by
      norm_num)
      (quint (P 1 0 0) (P 0 1 0) (P 0 1 β') (P 0 0 1) (P α 0 α')) ?_ ?_ ?_
      (fun z => Q5a z ∨ Q5a fun i => -z i) isOpen_Q5a (fun z c hc hz => Q5a_scale hc hz) hQ
      (fun z hz hQ => isCyclicUnimodal_Q5a hz hQ)
    · intro i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        simp [hV, quint_0, quint_1, quint_2, quint_3, quint_4]
    · intro i j hi hj
      rcases zmod5_pairs i j hi hj with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ |
        ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ <;>
      simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, hP, add_cmb_sub,
        hu₀] <;>
      first
        | exact tiltSign_zero hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _) (by simp only [detc]; ring1)
            (by simp only [detc]; clear * - hα hα' hβ' h1α haa Q1 Q2; linarith)
        | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (by simp only [detc]; clear * - hα hα' hβ' h1α haa Q1 Q2; linarith)
    · intro z hz hzx i
      have hx0 := hzx 0; have hx1 := hzx 1; have hx2 := hzx 2; have hx3 := hzx 3; have hx4 := hzx 4
      simp only [quint_0, quint_1, quint_2, quint_3, quint_4] at hx0 hx1 hx2 hx3 hx4
      rcases hmemV z hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
        try (first | exact absurd rfl hx0 | exact absurd rfl hx1 | exact absurd rfl hx2 |
          exact absurd rfl hx3 | exact absurd rfl hx4)
      all_goals
        rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, hP,
          add_cmb_sub, hu₀] <;>
        first
          | exact tiltSign_zero hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
              (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _) (by simp only [detc]; ring1)
              (by simp only [detc]; clear * - hα hα' hβ' h1α haa Q1 Q2; linarith)
          | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
              (by simp only [detc]; clear * - hα hα' hβ' h1α haa Q1 Q2; linarith)

/-- **T3, degenerate case `AA' ∥ CC'`**: `LU`, `UU`, or the 5-cycle `(A, A', B', B, C)`. -/
theorem isRupert_T3_a1 {A B C C' : ℝ³} (hΔ : det3 (A - C) (B - C) (C' - C) ≠ 0)
    {α' β β' : ℝ} (hα' : 0 < α') (hβ : 0 < β) (hβ' : 0 < β')
    (h1β : 1 < β) (hbb : 1 < β + β') :
    IsRupert {A, B, C, C + cmb (A - C) (B - C) (C' - C) 1 0 α',
      C + cmb (A - C) (B - C) (C' - C) 0 β β', C'} := by
  classical
  set f₁ := A - C
  set f₂ := B - C
  set f₃ := C' - C
  obtain ⟨σ, hσ, hD⟩ := det3_pos_or_neg hΔ
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  set P := fun a b c : ℝ => C + cmb f₁ f₂ f₃ a b c with hP
  have eA' : C + cmb f₁ f₂ f₃ 1 0 α' = P 1 0 α' := rfl
  have eB' : C + cmb f₁ f₂ f₃ 0 β β' = P 0 β β' := rfl
  have eA : A = P 1 0 0 := by simp [hP, cmb, f₁]
  have eB : B = P 0 1 0 := by simp [hP, cmb, f₂]
  have eC : C = P 0 0 0 := by simp [hP, cmb]
  have eC' : C' = P 0 0 1 := by simp [hP, cmb, f₃]
  rw [eA', eB', eA, eB, eC, eC']
  set V : Finset ℝ³ := {P 1 0 0, P 0 1 0, P 0 0 0, P 1 0 α', P 0 β β', P 0 0 1} with hV
  have hmemV : ∀ z ∈ V, z = P 1 0 0 ∨ z = P 0 1 0 ∨ z = P 0 0 0 ∨ z = P 1 0 α' ∨
      z = P 0 β β' ∨ z = P 0 0 1 := by
    intro z hz; simpa [hV] using hz
  set u₀ := σ • cmb f₁ f₂ f₃ 0 0 1 with hu₀
  have hd : cmb f₁ f₂ f₃ 0 0 1 = f₃ := by simp [cmb]
  have hf₃ : f₃ ≠ 0 := by
    intro h0
    have := (cmb_eq_zero hΔ (hd.trans h0)).2.2
    norm_num at this
  have hu₀0 : u₀ ≠ 0 := by rw [hu₀, hd]; exact smul_ne_zero hσ0 hf₃
  have hs0 : 0 < ⟪f₃, f₃⟫ := real_inner_self_pos.mpr hf₃
  have hdepth : ∀ a b c, ⟪P a b c, u₀⟫ =
      ⟪C, u₀⟫ + σ * (a * ⟪f₁, f₃⟫ + b * ⟪f₂, f₃⟫ + c * ⟪f₃, f₃⟫) := by
    intro a b c
    rw [hP]; simp only [inner_add_cmb, hu₀, hd, real_inner_smul_right]; ring
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  replace h1β := sub_pos.mpr h1β
  replace hbb := sub_pos.mpr hbb
  have R1 := mul_pos hβ hα'
  have R2 := mul_pos hβ hβ'
  have R3 := mul_pos hβ h1β
  have haa : ⟪f₁, f₃⟫ < 1 * ⟪f₁, f₃⟫ + α' * ⟪f₃, f₃⟫ := by
    linarith only [mul_pos hα' hs0]
  have hB : ⟪f₂, f₃⟫ < 0 ∨ ⟪f₂, f₃⟫ < β * ⟪f₂, f₃⟫ + β' * ⟪f₃, f₃⟫ :=
    depth_below_positive_combination h1β hβ' hs0
  rcases t3_nws_a1 hs0 haa hB with h | h | h
  · -- LU = (A, B', C', C)
    have hQ : NWS4 fun i => ⟪quad (P 1 0 0) (P 0 β β') (P 0 0 1) (P 0 0 0) i, u₀⟫ := by
      have := h.affine ⟪C, u₀⟫ hσ0
      convert this using 2 with i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, hdepth] <;> ring
    refine isRupert_of_tilted_NWS4 V u₀ (σ • cmb f₁ f₂ f₃ 1 (-β / 2) (-β' / 2)) hu₀0 (quad (P 1 0
      0) (P 0 β β') (P 0 0 1) (P 0 0 0)) ?_ ?_ ?_ hQ
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp [hV, quad_0, quad_1, quad_2, quad_3]
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, hP, add_cmb_sub, hu₀] <;>
      first
        | exact tiltSign_zero hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _) (by simp only [detc]; ring1)
            (by simp only [detc]; clear * - hα' hβ hβ' h1β hbb R1 R2 R3; linarith)
        | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (by simp only [detc]; clear * - hα' hβ hβ' h1β hbb R1 R2 R3; linarith)
    · intro z hz hzx i
      have hx0 := hzx 0; have hx1 := hzx 1; have hx2 := hzx 2; have hx3 := hzx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at hx0 hx1 hx2 hx3
      rcases hmemV z hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
        try (first | exact absurd rfl hx0 | exact absurd rfl hx1 | exact absurd rfl hx2 |
          exact absurd rfl hx3)
      all_goals
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, hP, add_cmb_sub, hu₀] <;>
        first
          | exact tiltSign_zero hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
              (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _) (by simp only [detc]; ring1)
              (by simp only [detc]; clear * - hα' hβ hβ' h1β hbb R1 R2 R3; linarith)
          | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
              (by simp only [detc]; clear * - hα' hβ hβ' h1β hbb R1 R2 R3; linarith)
  · -- UU = (A, B', C', A')
    have hQ : NWS4 fun i => ⟪quad (P 1 0 0) (P 0 β β') (P 0 0 1) (P 1 0 α') i, u₀⟫ := by
      have := h.affine ⟪C, u₀⟫ hσ0
      convert this using 2 with i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, hdepth] <;> ring
    refine isRupert_of_tilted_NWS4 V u₀ (σ • cmb f₁ f₂ f₃ (1 / 2) (β / 2) (β' / 2)) hu₀0 (quad (P
      1 0 0) (P 0 β β') (P 0 0 1) (P 1 0 α')) ?_ ?_ ?_ hQ
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp [hV, quad_0, quad_1, quad_2, quad_3]
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, hP, add_cmb_sub, hu₀] <;>
      first
        | exact tiltSign_zero hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _) (by simp only [detc]; ring1)
            (by simp only [detc]; clear * - hα' hβ hβ' h1β hbb R1 R2 R3; linarith)
        | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (by simp only [detc]; clear * - hα' hβ hβ' h1β hbb R1 R2 R3; linarith)
    · intro z hz hzx i
      have hx0 := hzx 0; have hx1 := hzx 1; have hx2 := hzx 2; have hx3 := hzx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at hx0 hx1 hx2 hx3
      rcases hmemV z hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
        try (first | exact absurd rfl hx0 | exact absurd rfl hx1 | exact absurd rfl hx2 |
          exact absurd rfl hx3)
      all_goals
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, hP, add_cmb_sub, hu₀] <;>
        first
          | exact tiltSign_zero hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
              (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _) (by simp only [detc]; ring1)
              (by simp only [detc]; clear * - hα' hβ hβ' h1β hbb R1 R2 R3; linarith)
          | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
              (by simp only [detc]; clear * - hα' hβ hβ' h1β hbb R1 R2 R3; linarith)
  · -- the 5-cycle (A, A', B', B, C)
    have hQ : Q5b (fun i => ⟪quint (P 1 0 0) (P 1 0 α') (P 0 β β') (P 0 1 0) (P 0 0 0) i, u₀⟫) ∨
      Q5b fun i => -⟪quint (P 1 0 0) (P 1 0 α') (P 0 β β') (P 0 1 0) (P 0 0 0) i, u₀⟫ := by
      have := Q5b_affine h ⟪C, u₀⟫ σ hσ
      convert this using 3 <;> rename_i i <;>
        rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        simp only [quint_0, quint_1, quint_2, quint_3, quint_4, hdepth] <;> ring
    refine isRupert_of_tilted_unimodal V u₀ (σ • cmb f₁ f₂ f₃ (-1 / 2) (-β / 2) (-β' / 2)) hu₀0
      (by norm_num)
      (quint (P 1 0 0) (P 1 0 α') (P 0 β β') (P 0 1 0) (P 0 0 0)) ?_ ?_ ?_
      (fun z => Q5b z ∨ Q5b fun i => -z i) isOpen_Q5b (fun z c hc hz => Q5b_scale hc hz) hQ
      (fun z hz hQ => isCyclicUnimodal_Q5b hz hQ)
    · intro i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        simp [hV, quint_0, quint_1, quint_2, quint_3, quint_4]
    · intro i j hi hj
      rcases zmod5_pairs i j hi hj with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ |
        ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ <;>
      simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, hP, add_cmb_sub,
        hu₀] <;>
      first
        | exact tiltSign_zero hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _) (by simp only [detc]; ring1)
            (by simp only [detc]; clear * - hα' hβ hβ' h1β hbb R1 R2 R3; linarith)
        | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
            (by simp only [detc]; clear * - hα' hβ hβ' h1β hbb R1 R2 R3; linarith)
    · intro z hz hzx i
      have hx0 := hzx 0; have hx1 := hzx 1; have hx2 := hzx 2; have hx3 := hzx 3; have hx4 := hzx 4
      simp only [quint_0, quint_1, quint_2, quint_3, quint_4] at hx0 hx1 hx2 hx3 hx4
      rcases hmemV z hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
        try (first | exact absurd rfl hx0 | exact absurd rfl hx1 | exact absurd rfl hx2 |
          exact absurd rfl hx3 | exact absurd rfl hx4)
      all_goals
        rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, hP,
          add_cmb_sub, hu₀] <;>
        first
          | exact tiltSign_zero hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
              (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _) (by simp only [detc]; ring1)
              (by simp only [detc]; clear * - hα' hβ hβ' h1β hbb R1 R2 R3; linarith)
          | exact tiltSign_pos hD (det3_cmb _ _ _ _ _ _ _ _ _ _ _ _ _)
              (by simp only [detc]; clear * - hα' hβ hβ' h1β hbb R1 R2 R3; linarith)

/-- **Theorem 8.4.**  Every T3 is Rupert. -/
theorem isRupert_T3 {A B C A' B' C' : ℝ³} (h : IsT3 A B C A' B' C') :
    IsRupert {A, B, C, A', B', C'} := by
  obtain ⟨α, α', β, β', hα, hα', hβ, hβ', haa, hbb, hbent, hA', hB'⟩ := h.exists_normalForm
  have hΔ : det3 (A - C) (B - C) (C' - C) ≠ 0 := by
    intro h0
    apply not_coplanar_of_affineIndependent h.affineIndependent
    have hc := coplanar_of_det4_eq_zero (a := C) (b := A) (c := B) (d := C') h0
    convert hc using 1
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [hA', hB']
  rcases lt_trichotomy α 1 with h1 | h1 | h1
  · rcases lt_trichotomy β 1 with h2 | h2 | h2
    · exact isRupert_T3_i hΔ hα hα' hβ hβ' h1 h2
    · subst h2; exact isRupert_T3_b1 hΔ hα hα' hβ' h1 haa
    · exact isRupert_T3_iii hΔ hα hα' hβ hβ' h1 h2 haa hbb
  · subst h1
    have h2 : 1 < β := by
      by_contra hc; push Not at hc
      nlinarith [mul_nonneg hα'.le (sub_nonneg.mpr hc)]
    exact isRupert_T3_a1 hΔ hα' hβ hβ' h2 hbb
  · have h2 : 1 < β := by
      by_contra hc; push Not at hc
      nlinarith [mul_nonneg hα'.le (sub_nonneg.mpr hc), mul_pos hβ' (sub_pos.mpr h1)]
    exact isRupert_T3_ii hΔ hα hα' hβ hβ' h1 h2 haa hbb

end Minimality

end RupertMinimality
