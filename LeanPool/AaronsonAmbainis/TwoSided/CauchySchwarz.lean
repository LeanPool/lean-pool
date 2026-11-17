/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Cauchy–Schwarz and the choice of weights

The lemma that removes the weights (Lemma 5.3 of the paper, Section 5.2), for two finite
families of non-negative vectors (no cube). The steps of its proof: the Cauchy–Schwarz inequality
over the pairs (Step 1, `pair_cs`), the choice of the weights `w j = 1 / (√(X j * Y j) + ε)` with
`ε → 0` (Step 2, `weight_choice`), the Cauchy–Schwarz inequality over the coordinates (Step 3, in
`cs_core`), and the conclusion (`le_of_sq_le_mul`).

`abstract_cs` (Lemma 5.3): if the sums `∑_{j ∈ D x y} w j * a x j * b y j` are positive and
`∑_{x ∈ O} ∑_{y ∈ N} (∑_{j ∈ D x y} w j * a x j * b y j)⁻¹ ≤ C * ∑ j, (w j)⁻¹`
for every positive weight vector `w`, then
`(∑_{x ∈ O} (∑ j, a x j)⁻¹) * (∑_{y ∈ N} (∑ j, b y j)⁻¹) ≤ C`.

The lemma `abstract_cs` is used twice: for the two-sided inequality (`RemoveWeights.lean`) and
for the third-moment inequality (`Level/ThirdMoment.lean`).
-/

@[expose] public section

namespace AaronsonAmbainis

open Finset

/-- `s⁻¹ ^ 2 * s = s⁻¹` for every real `s` (also for `s = 0`). -/
lemma inv_sq_mul_self (s : ℝ) : s⁻¹ ^ 2 * s = s⁻¹ := by
  by_cases hs : s = 0
  · simp [hs]
  · rw [pow_two, mul_assoc, inv_mul_cancel₀ hs, mul_one]

/-- Expanding a weighted sum of products of two combinations of rows. -/
lemma sum_mul_rows {α β ι : Type*} [Fintype ι] (O : Finset α) (N : Finset β)
    (w : ι → ℝ) (u : α → ℝ) (v : β → ℝ) (f : α → ι → ℝ) (h : β → ι → ℝ) :
    ∑ j, w j * (∑ x ∈ O, u x * f x j) * (∑ y ∈ N, v y * h y j)
      = ∑ x ∈ O, ∑ y ∈ N, (u x * v y) * ∑ j, w j * f x j * h y j := by
  have h1 : ∀ j, w j * (∑ x ∈ O, u x * f x j) * (∑ y ∈ N, v y * h y j)
      = ∑ x ∈ O, ∑ y ∈ N, (u x * v y) * (w j * f x j * h y j) := by
    intro j
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  exact (Finset.mul_sum _ _ _).symm

/-- Cauchy–Schwarz over pairs. -/
lemma pair_cs {α β : Type*} (O : Finset α) (N : Finset β) (c s : α → β → ℝ)
    (hs : ∀ x ∈ O, ∀ y ∈ N, 0 < s x y) :
    (∑ x ∈ O, ∑ y ∈ N, c x y) ^ 2
      ≤ (∑ x ∈ O, ∑ y ∈ N, c x y ^ 2 * s x y) * (∑ x ∈ O, ∑ y ∈ N, (s x y)⁻¹) := by
  rw [← Finset.sum_product' O N (fun x y => c x y),
    ← Finset.sum_product' O N (fun x y => c x y ^ 2 * s x y),
    ← Finset.sum_product' O N (fun x y => (s x y)⁻¹)]
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (O ×ˢ N) ?_ ?_ ?_
  · intro p hp
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    exact mul_nonneg (sq_nonneg _) (hs p.1 hx p.2 hy).le
  · intro p hp
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    exact (inv_pos.mpr (hs p.1 hx p.2 hy)).le
  · intro p hp
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    have h := hs p.1 hx p.2 hy
    have he : c p.1 p.2 ^ 2 * s p.1 p.2 * (s p.1 p.2)⁻¹ = c p.1 p.2 ^ 2 := by
      rw [mul_assoc, mul_inv_cancel₀ h.ne', mul_one]
    exact he.ge

/-- If `Q ≤ S * (C * (S + c * ε))` for every `ε > 0`, then `Q ≤ C * S ^ 2`. -/
lemma le_of_forall_eps {Q S C c : ℝ} (hS : 0 ≤ S) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (h : ∀ ε : ℝ, 0 < ε → Q ≤ S * (C * (S + c * ε))) : Q ≤ C * S ^ 2 := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hK : 0 ≤ C * S * c := mul_nonneg (mul_nonneg hC hS) hc
  have hK1 : 0 < C * S * c + 1 := by linarith
  have h2 := h (δ / (C * S * c + 1)) (div_pos hδ hK1)
  have h3 : C * S * c * (δ / (C * S * c + 1)) ≤ δ := by
    rw [← mul_div_assoc, div_le_iff₀ hK1]
    nlinarith
  calc Q ≤ S * (C * (S + c * (δ / (C * S * c + 1)))) := h2
    _ = C * S ^ 2 + C * S * c * (δ / (C * S * c + 1)) := by ring
    _ ≤ C * S ^ 2 + δ := by linarith

/-- The choice of the weights `w j = 1 / (√(X j * Y j) + ε)`, `ε → 0`
(Step 2 of the proof of Lemma 5.3 of the paper). -/
lemma weight_choice {ι : Type*} [Fintype ι] (X Y : ι → ℝ) (hX : ∀ j, 0 ≤ X j)
    (hY : ∀ j, 0 ≤ Y j) (C Q : ℝ) (hC : 0 ≤ C)
    (h : ∀ w : ι → ℝ, (∀ j, 0 < w j) →
      Q ≤ (∑ j, w j * X j * Y j) * (C * ∑ j, (w j)⁻¹)) :
    Q ≤ C * (∑ j, Real.sqrt (X j * Y j)) ^ 2 := by
  have hr : ∀ j, 0 ≤ Real.sqrt (X j * Y j) := fun j => Real.sqrt_nonneg _
  have hS : 0 ≤ ∑ j, Real.sqrt (X j * Y j) := Finset.sum_nonneg fun j _ => hr j
  have hcard : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  refine le_of_forall_eps hS hC hcard ?_
  intro ε hε
  have hw : ∀ j, 0 < (Real.sqrt (X j * Y j) + ε)⁻¹ := fun j =>
    inv_pos.mpr (add_pos_of_nonneg_of_pos (hr j) hε)
  have h1 := h (fun j => (Real.sqrt (X j * Y j) + ε)⁻¹) hw
  have hA : ∑ j, (Real.sqrt (X j * Y j) + ε)⁻¹ * X j * Y j
      ≤ ∑ j, Real.sqrt (X j * Y j) := by
    apply Finset.sum_le_sum
    intro j _
    have hpos : 0 < Real.sqrt (X j * Y j) + ε := add_pos_of_nonneg_of_pos (hr j) hε
    have hsq : Real.sqrt (X j * Y j) * Real.sqrt (X j * Y j) = X j * Y j :=
      Real.mul_self_sqrt (mul_nonneg (hX j) (hY j))
    rw [mul_assoc, inv_mul_le_iff₀ hpos]
    nlinarith [mul_nonneg (hr j) hε.le]
  have hB : ∑ j, ((Real.sqrt (X j * Y j) + ε)⁻¹)⁻¹
      = ∑ j, Real.sqrt (X j * Y j) + (Fintype.card ι : ℝ) * ε := by
    simp only [inv_inv]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hD : 0 ≤ C * (∑ j, Real.sqrt (X j * Y j) + (Fintype.card ι : ℝ) * ε) :=
    mul_nonneg hC (add_nonneg hS (mul_nonneg hcard hε.le))
  calc Q ≤ (∑ j, (Real.sqrt (X j * Y j) + ε)⁻¹ * X j * Y j)
        * (C * ∑ j, ((Real.sqrt (X j * Y j) + ε)⁻¹)⁻¹) := h1
    _ = (∑ j, (Real.sqrt (X j * Y j) + ε)⁻¹ * X j * Y j)
        * (C * (∑ j, Real.sqrt (X j * Y j) + (Fintype.card ι : ℝ) * ε)) := by rw [hB]
    _ ≤ (∑ j, Real.sqrt (X j * Y j))
        * (C * (∑ j, Real.sqrt (X j * Y j) + (Fintype.card ι : ℝ) * ε)) :=
        mul_le_mul_of_nonneg_right hA hD

/-- `P ^ 2 ≤ C * P` and `0 ≤ C` give `P ≤ C`. -/
lemma le_of_sq_le_mul {P C : ℝ} (hC : 0 ≤ C) (h : P ^ 2 ≤ C * P) : P ≤ C := by
  by_contra hcon
  have hlt : C < P := not_le.mp hcon
  have hPpos : 0 < P := lt_of_le_of_lt hC hlt
  nlinarith [mul_pos (sub_pos.mpr hlt) hPpos]

/-- The Cauchy–Schwarz argument with general coefficients `u`, `v` satisfying
`u x ^ 2 * ∑ j, a x j = u x` and `v y ^ 2 * ∑ j, b y j = v y`. -/
lemma cs_core {α β ι : Type*} [Fintype ι] (O : Finset α) (N : Finset β)
    (a : α → ι → ℝ) (b : β → ι → ℝ) (ha : ∀ x j, 0 ≤ a x j) (hb : ∀ y j, 0 ≤ b y j)
    (u : α → ℝ) (v : β → ℝ)
    (hua : ∀ x, u x ^ 2 * ∑ j, a x j = u x) (hvb : ∀ y, v y ^ 2 * ∑ j, b y j = v y)
    (D : α → β → Finset ι) (C : ℝ) (hC : 0 ≤ C)
    (hpos : ∀ x ∈ O, ∀ y ∈ N, ∀ w : ι → ℝ, (∀ j, 0 < w j) →
      0 < ∑ j ∈ D x y, w j * a x j * b y j)
    (hpairs : ∀ w : ι → ℝ, (∀ j, 0 < w j) →
      ∑ x ∈ O, ∑ y ∈ N, (∑ j ∈ D x y, w j * a x j * b y j)⁻¹ ≤ C * ∑ j, (w j)⁻¹) :
    (∑ x ∈ O, u x) * (∑ y ∈ N, v y) ≤ C := by
  have hX : ∀ j, 0 ≤ ∑ x ∈ O, u x ^ 2 * a x j := fun j =>
    Finset.sum_nonneg fun x _ => mul_nonneg (sq_nonneg _) (ha x j)
  have hY : ∀ j, 0 ≤ ∑ y ∈ N, v y ^ 2 * b y j := fun j =>
    Finset.sum_nonneg fun y _ => mul_nonneg (sq_nonneg _) (hb y j)
  have hXsum : ∑ j, ∑ x ∈ O, u x ^ 2 * a x j = ∑ x ∈ O, u x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Finset.mul_sum, hua x]
  have hYsum : ∑ j, ∑ y ∈ N, v y ^ 2 * b y j = ∑ y ∈ N, v y := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [← Finset.mul_sum, hvb y]
  -- Cauchy–Schwarz over pairs, for every weight vector
  have hB : ∀ w : ι → ℝ, (∀ j, 0 < w j) →
      ((∑ x ∈ O, u x) * (∑ y ∈ N, v y)) ^ 2
        ≤ (∑ j, w j * (∑ x ∈ O, u x ^ 2 * a x j) * (∑ y ∈ N, v y ^ 2 * b y j))
          * (C * ∑ j, (w j)⁻¹) := by
    intro w hw
    have h1 := pair_cs O N (fun x y => u x * v y)
      (fun x y => ∑ j ∈ D x y, w j * a x j * b y j) (fun x hx y hy => hpos x hx y hy w hw)
    have h2 : ∑ x ∈ O, ∑ y ∈ N, (u x * v y) ^ 2 * ∑ j ∈ D x y, w j * a x j * b y j
        ≤ ∑ j, w j * (∑ x ∈ O, u x ^ 2 * a x j) * (∑ y ∈ N, v y ^ 2 * b y j) := by
      rw [sum_mul_rows O N w (fun x => u x ^ 2) (fun y => v y ^ 2) a b]
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => mul_nonneg (mul_nonneg (hw j).le (ha x j)) (hb y j)))
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    have h3 : 0 ≤ ∑ x ∈ O, ∑ y ∈ N, (∑ j ∈ D x y, w j * a x j * b y j)⁻¹ :=
      Finset.sum_nonneg fun x hx => Finset.sum_nonneg fun y hy =>
        (inv_pos.mpr (hpos x hx y hy w hw)).le
    have h4 : 0 ≤ ∑ j, w j * (∑ x ∈ O, u x ^ 2 * a x j) * (∑ y ∈ N, v y ^ 2 * b y j) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (hw j).le (hX j)) (hY j)
    calc ((∑ x ∈ O, u x) * (∑ y ∈ N, v y)) ^ 2
        = (∑ x ∈ O, ∑ y ∈ N, u x * v y) ^ 2 := by rw [Finset.sum_mul_sum]
      _ ≤ (∑ x ∈ O, ∑ y ∈ N, (u x * v y) ^ 2 * ∑ j ∈ D x y, w j * a x j * b y j)
          * (∑ x ∈ O, ∑ y ∈ N, (∑ j ∈ D x y, w j * a x j * b y j)⁻¹) := h1
      _ ≤ (∑ j, w j * (∑ x ∈ O, u x ^ 2 * a x j) * (∑ y ∈ N, v y ^ 2 * b y j))
          * (C * ∑ j, (w j)⁻¹) := mul_le_mul h2 (hpairs w hw) h3 h4
  -- the choice of the weights
  have hW := weight_choice (fun j => ∑ x ∈ O, u x ^ 2 * a x j)
    (fun j => ∑ y ∈ N, v y ^ 2 * b y j) hX hY C
    (((∑ x ∈ O, u x) * (∑ y ∈ N, v y)) ^ 2) hC hB
  -- Cauchy–Schwarz over the coordinates
  have hCS : (∑ j, Real.sqrt ((∑ x ∈ O, u x ^ 2 * a x j) * (∑ y ∈ N, v y ^ 2 * b y j))) ^ 2
      ≤ (∑ j, ∑ x ∈ O, u x ^ 2 * a x j) * (∑ j, ∑ y ∈ N, v y ^ 2 * b y j) :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ (fun j _ => hX j) (fun j _ => hY j)
      (fun j _ => (Real.sq_sqrt (mul_nonneg (hX j) (hY j))).le)
  rw [hXsum, hYsum] at hCS
  exact le_of_sq_le_mul hC (le_trans hW (mul_le_mul_of_nonneg_left hCS hC))

/-- The lemma that removes the weights (Lemma 5.3 of the paper): Steps 1–3 and the conclusion of
its proof. The reciprocals are `⁻¹`, with `0⁻¹ = 0` in Lean, and the sets `O` and `N` may be
empty; so the first assertion of Lemma 5.3, that the sums `∑ j, a x j` and `∑ j, b y j` are
positive, is not part of this statement. -/
lemma abstract_cs {α β ι : Type*} [Fintype ι] (O : Finset α) (N : Finset β)
    (a : α → ι → ℝ) (b : β → ι → ℝ) (ha : ∀ x j, 0 ≤ a x j) (hb : ∀ y j, 0 ≤ b y j)
    (D : α → β → Finset ι) (C : ℝ) (hC : 0 ≤ C)
    (hpos : ∀ x ∈ O, ∀ y ∈ N, ∀ w : ι → ℝ, (∀ j, 0 < w j) →
      0 < ∑ j ∈ D x y, w j * a x j * b y j)
    (hpairs : ∀ w : ι → ℝ, (∀ j, 0 < w j) →
      ∑ x ∈ O, ∑ y ∈ N, (∑ j ∈ D x y, w j * a x j * b y j)⁻¹ ≤ C * ∑ j, (w j)⁻¹) :
    (∑ x ∈ O, (∑ j, a x j)⁻¹) * (∑ y ∈ N, (∑ j, b y j)⁻¹) ≤ C :=
  cs_core O N a b ha hb (fun x => (∑ j, a x j)⁻¹) (fun y => (∑ j, b y j)⁻¹)
    (fun x => inv_sq_mul_self (∑ j, a x j)) (fun y => inv_sq_mul_self (∑ j, b y j))
    D C hC hpos hpairs

end AaronsonAmbainis
