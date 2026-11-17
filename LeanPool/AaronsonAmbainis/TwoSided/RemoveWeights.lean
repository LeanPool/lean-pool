/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.TwoSided.Overlap
public import LeanPool.AaronsonAmbainis.TwoSided.CauchySchwarz

/-!
# The two-sided inequality from the all-pairs inequality (`twoSided_of_allPairs`)

Section 5.2 of the paper (the proof of Theorem 5.4).

From the all-pairs inequality and `bdry g j = 2 ^ n * infl g j / 2 ≤ 2 ^ n * τ / 2`:

  `∑_{x ∈ O} ∑_{y ∈ N} (∑_{j ∈ Δ(x,y)} w j * lam x j * lam y j)⁻¹ ≤ (4 ^ n * τ / 4) * ∑ j, (w j)⁻¹`

for every positive weight vector `w` (`O = {g = true}`, `N = {g = false}`).  The lemma that
removes the weights (Lemma 5.3, `abstract_cs` in the file `CauchySchwarz.lean`) gives
`(∑_{x ∈ O} ‖lam x‖₁⁻¹) * (∑_{y ∈ N} ‖lam y‖₁⁻¹) ≤ 4 ^ n * τ / 4`; the overlap lemma
(file `Overlap.lean`) supplies the positivity of the denominators.
-/

@[expose] public section

namespace AaronsonAmbainis

open Finset

/-- The final arithmetic: `VO * VN ≤ T * T * τ / 4` gives `4 * (VO / T) * (VN / T) ≤ τ`. -/
lemma final_arith {VO VN T τ : ℝ} (hT : 0 < T) (h : VO * VN ≤ T * T * τ / 4) :
    4 * (VO / T) * (VN / T) ≤ τ := by
  have h1 : 4 * (VO / T) * (VN / T) = 4 * (VO * VN) / (T * T) := by ring
  rw [h1, div_le_iff₀ (mul_pos hT hT)]
  linarith

/-- The two-sided inequality (the inequality of Theorem 5.4 of the paper) from the all-pairs
inequality (Proposition 5.2). -/
theorem twoSided_of_allPairs : AllPairsInequality → TwoSidedInequality := by
  intro hAllPairs ι _ _ g lam hlam τ hτ hinfl
  have h2n : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have hC : 0 ≤ (2 : ℝ) ^ Fintype.card ι * 2 ^ Fintype.card ι * τ / 4 :=
    div_nonneg (mul_nonneg (mul_nonneg h2n.le h2n.le) hτ) (by norm_num)
  -- every boundary is at most `2 ^ n * τ / 2`
  have hb : ∀ j, (bdry g j : ℝ) ≤ 2 ^ Fintype.card ι * τ / 2 := by
    intro j
    have h1 := two_mul_bdry g j
    have h2 := mul_le_mul_of_nonneg_left (hinfl j) h2n.le
    linarith
  -- the all-pairs inequality with the influence bound
  have hpairs : ∀ w : ι → ℝ, (∀ j, 0 < w j) →
      ∑ x ∈ univ.filter (fun x : Cube ι => g x = true),
        ∑ y ∈ univ.filter (fun y : Cube ι => g y = false),
          (∑ j ∈ diffSet x y, w j * lam x j * lam y j)⁻¹
        ≤ (2 : ℝ) ^ Fintype.card ι * 2 ^ Fintype.card ι * τ / 4 * ∑ j, (w j)⁻¹ := by
    intro w hw
    have h1 := hAllPairs ι g w hw lam hlam
    have h3 : ∑ j, (bdry g j : ℝ) / w j ≤ 2 ^ Fintype.card ι * τ / 2 * ∑ j, (w j)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hb j) (inv_pos.mpr (hw j)).le
    have h4 : (2 : ℝ) ^ Fintype.card ι * ∑ j, (bdry g j : ℝ) / w j
        ≤ 2 ^ Fintype.card ι * (2 ^ Fintype.card ι * τ / 2 * ∑ j, (w j)⁻¹) :=
      mul_le_mul_of_nonneg_left h3 h2n.le
    have h5 : (2 : ℝ) ^ Fintype.card ι * (2 ^ Fintype.card ι * τ / 2 * ∑ j, (w j)⁻¹)
        = 2 * ((2 : ℝ) ^ Fintype.card ι * 2 ^ Fintype.card ι * τ / 4 * ∑ j, (w j)⁻¹) := by
      ring
    linarith
  -- positivity of the denominators: the overlap lemma
  have hpos : ∀ x ∈ univ.filter (fun x : Cube ι => g x = true),
      ∀ y ∈ univ.filter (fun y : Cube ι => g y = false),
      ∀ w : ι → ℝ, (∀ j, 0 < w j) → 0 < ∑ j ∈ diffSet x y, w j * lam x j * lam y j := by
    intro x hx y hy w hw
    have hgx : g x = true := (Finset.mem_filter.mp hx).2
    have hgy : g y = false := (Finset.mem_filter.mp hy).2
    have hne : g x ≠ g y := by
      intro h
      rw [hgx, hgy] at h
      exact Bool.noConfusion h
    exact overlap_pos hne (hlam x) (hlam y) hw
  have key := abstract_cs (univ.filter fun x : Cube ι => g x = true)
    (univ.filter fun y : Cube ι => g y = false) lam lam
    (fun x j => (hlam x).1 j) (fun y j => (hlam y).1 j) diffSet
    ((2 : ℝ) ^ Fintype.card ι * 2 ^ Fintype.card ι * τ / 4) hC hpos hpairs
  exact final_arith h2n key

end AaronsonAmbainis
