/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.Level.Basic
public import LeanPool.AaronsonAmbainis.Level.AllPairs
public import LeanPool.AaronsonAmbainis.TwoSided.CauchySchwarz

/-!
# The third-moment inequality

Let `f` be a real function on the cube with rows of cost at most `K` at every point, and let
`M ≥ 0` bound all the mean absolute increments `L_j = meanAbsIncr f j`. Then, for every real `s`,

`E[((f - s)⁺)^3] · Pr[f ≤ s] ≤ (3/2) K² M`

(Theorem 7.6 of the paper; `thirdMoment_of_integratedAllPairs :
IntegratedAllPairsInequality → ThirdMomentInequality`; the unnormalised form is
`Level.thirdMoment_core`).

Proof: in the integrated all-pairs inequality (Proposition 7.4) keep the pairs `(x, y)` with
`f y ≤ s < f x`, where `(f x - f y)^3 ≥ (f x - s)^3`. Dividing the row at `x` by `(f x - s)^3`
turns the inequality into the hypothesis of the lemma that removes the weights (Lemma 5.3 of the
paper; `abstract_cs` in `TwoSided/CauchySchwarz.lean`), whose conclusion is the claim.

Two consequences of the third-moment inequality:

* `Level.thirdMoment_lower` — the inequality on the other side,
  `E[((s - f)⁺)^3] · Pr[f ≥ s] ≤ (3/2) K² M` (the second inequality of Theorem 7.6);
* `Level.separated_sets` — if `f ≥ s + θ` on `A` and `f ≤ s` on `B`, then
  `2 θ^3 μ(A) μ(B) ≤ 3 K² M` (Corollary 7.7).
-/

@[expose] public section

namespace AaronsonAmbainis

open Finset

namespace Level

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The integrated all-pairs inequality multiplied by `4`, so that `4^n` appears in place of
`4^(n-1)` (for `n = 0` both sides are `0`). -/
lemma four_mul_integrated (hInt : IntegratedAllPairsInequality) (f : Cube ι → ℝ)
    (a : Cube ι → ι → ℝ) (ha : ∀ x j, 0 ≤ a x j)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) (w : ι → ℝ) (hw : ∀ j, 0 < w j) :
    4 * ∑ x, ∑ y ∈ univ.filter (fun y : Cube ι => f y < f x),
        (f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)
      ≤ 4 ^ Fintype.card ι * ∑ j, meanAbsIncr f j / w j := by
  have h := hInt ι f a ha hrow w hw
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [Finset.univ_eq_empty (α := ι), Finset.sum_empty, mul_zero] at h ⊢
    linarith
  · rw [four_pow_card, mul_assoc]
    linarith

/-- The third-moment inequality, unnormalised:
`(∑_x ((f x - s)⁺)^3) · #{y : f y ≤ s} ≤ (3/2) 4^n M K²`. -/
theorem thirdMoment_core (hInt : IntegratedAllPairsInequality) (f : Cube ι → ℝ)
    (a : Cube ι → ι → ℝ) (ha : ∀ x j, 0 ≤ a x j) {K : ℝ} (hsum : ∀ x, ∑ j, a x j ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j, meanAbsIncr f j ≤ M) (s : ℝ) :
    (∑ x, max (f x - s) 0 ^ 3) * ((univ.filter (fun y : Cube ι => f y ≤ s)).card : ℝ)
      ≤ 3 / 2 * 4 ^ Fintype.card ι * M * K ^ 2 := by
  have hC : 0 ≤ 3 / 2 * (4 : ℝ) ^ Fintype.card ι * M := by positivity
  have hRHS : 0 ≤ 3 / 2 * (4 : ℝ) ^ Fintype.card ι * M * K ^ 2 := by positivity
  -- the two sets
  obtain ⟨A, hA⟩ : ∃ A : Finset (Cube ι), A = univ.filter (fun x : Cube ι => s < f x) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Finset (Cube ι), B = univ.filter (fun y : Cube ι => f y ≤ s) := ⟨_, rfl⟩
  have hmemA : ∀ x, x ∈ A ↔ s < f x := by
    intro x
    rw [hA]
    simp
  have hmemB : ∀ y, y ∈ B ↔ f y ≤ s := by
    intro y
    rw [hB]
    simp
  -- the third moment as a sum over `A`
  have hsumA : ∑ x, max (f x - s) 0 ^ 3 = ∑ x ∈ A, (f x - s) ^ 3 := by
    rw [hA, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : s < f x
    · rw [ite_eq_left hx, max_eq_left (by linarith : 0 ≤ f x - s)]
    · rw [ite_eq_right hx, max_eq_right (by linarith [not_lt.mp hx] : f x - s ≤ 0)]
      norm_num
  rw [← hB, hsumA]
  -- the trivial cases
  rcases A.eq_empty_or_nonempty with hAe | ⟨x0, hx0⟩
  · rw [hAe, Finset.sum_empty, zero_mul]
    exact hRHS
  rcases B.eq_empty_or_nonempty with hBe | ⟨y0, hy0⟩
  · rw [hBe, Finset.card_empty, Nat.cast_zero, mul_zero]
    exact hRHS
  have hx0' := (hmemA x0).mp hx0
  have hy0' := (hmemB y0).mp hy0
  -- positivity of the costs
  have hposA : ∀ x ∈ A, 0 < ∑ j, a x j := fun x hx =>
    rowSum_pos ha hrow (ne_of_gt (lt_of_le_of_lt hy0' ((hmemA x).mp hx)))
  have hposB : ∀ y ∈ B, 0 < ∑ j, a y j := fun y hy =>
    rowSum_pos ha hrow (ne_of_lt (lt_of_le_of_lt ((hmemB y).mp hy) hx0'))
  have hK : 0 < K := lt_of_lt_of_le (hposA x0 hx0) (hsum x0)
  -- the rows on `A`, divided by `(f x - s)^3`
  have hscal : ∀ x ∈ A, ∀ (y : Cube ι) (w : ι → ℝ),
      ∑ j ∈ diffSet x y, w j * (a x j / max (f x - s) 0 ^ 3) * a y j
        = (∑ j ∈ diffSet x y, w j * a x j * a y j) / (f x - s) ^ 3 := by
    intro x hx y w
    have hxs : 0 < f x - s := sub_pos.mpr ((hmemA x).mp hx)
    rw [max_eq_left hxs.le, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have key := abstract_cs A B (fun x j => a x j / max (f x - s) 0 ^ 3) a
    (fun x j => div_nonneg (ha x j) (pow_nonneg (le_max_right _ _) 3)) ha diffSet
    (3 / 2 * 4 ^ Fintype.card ι * M) hC ?_ ?_
  · -- the conclusion of the Cauchy–Schwarz lemma
    have h1 : ∑ x ∈ A, (f x - s) ^ 3 / K
        ≤ ∑ x ∈ A, (∑ j, a x j / max (f x - s) 0 ^ 3)⁻¹ := by
      apply Finset.sum_le_sum
      intro x hx
      have hxs : 0 < f x - s := sub_pos.mpr ((hmemA x).mp hx)
      rw [max_eq_left hxs.le, ← Finset.sum_div, inv_div]
      exact div_le_div_of_nonneg_left (pow_pos hxs 3).le (hposA x hx) (hsum x)
    have h2 : (B.card : ℝ) / K ≤ ∑ y ∈ B, (∑ j, a y j)⁻¹ := by
      have h := Finset.sum_le_sum (s := B) (f := fun _ => K⁻¹) (g := fun y => (∑ j, a y j)⁻¹)
        (fun y hy => inv_anti₀ (hposB y hy) (hsum y))
      rw [Finset.sum_const, nsmul_eq_mul] at h
      rw [div_eq_mul_inv]
      exact h
    have h3 : 0 ≤ ∑ x ∈ A, (f x - s) ^ 3 / K := Finset.sum_nonneg (fun x hx =>
      div_nonneg (pow_nonneg (sub_nonneg.mpr ((hmemA x).mp hx).le) 3) hK.le)
    have h4 : (0 : ℝ) ≤ (B.card : ℝ) / K := div_nonneg (Nat.cast_nonneg _) hK.le
    have h5 := le_trans (mul_le_mul h1 h2 h4 (le_trans h3 h1)) key
    rw [← Finset.sum_div] at h5
    have h6 : (∑ x ∈ A, (f x - s) ^ 3) / K * ((B.card : ℝ) / K)
        = (∑ x ∈ A, (f x - s) ^ 3) * (B.card : ℝ) / K ^ 2 := by ring
    rw [h6, div_le_iff₀ (by positivity)] at h5
    exact h5
  · -- the denominators are positive
    intro x hx y hy w hw
    rw [hscal x hx y w]
    exact div_pos
      (pairSum_pos ha hrow hw (lt_of_le_of_lt ((hmemB y).mp hy) ((hmemA x).mp hx)))
      (pow_pos (sub_pos.mpr ((hmemA x).mp hx)) 3)
  · -- the inequality for the pairs in `A × B`, from the integrated all-pairs inequality
    intro w hw
    have hT1 := four_mul_integrated hInt f a ha hrow w hw
    have hterm : ∀ x ∈ A, ∀ y ∈ B,
        (∑ j ∈ diffSet x y, w j * (a x j / max (f x - s) 0 ^ 3) * a y j)⁻¹
          ≤ 6 * ((f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)) := by
      intro x hx y hy
      have hxs : 0 < f x - s := sub_pos.mpr ((hmemA x).mp hx)
      have hys : f y ≤ s := (hmemB y).mp hy
      have hS := pairSum_pos ha hrow hw (lt_of_le_of_lt hys ((hmemA x).mp hx))
      have e : 6 * ((f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j))
          = (f x - f y) ^ 3 / ∑ j ∈ diffSet x y, w j * a x j * a y j := by
        field_simp
      rw [hscal x hx y w, inv_div, e]
      exact div_le_div_of_nonneg_right
        (pow_le_pow_left₀ hxs.le (by linarith : f x - s ≤ f x - f y) 3) hS.le
    have hsub : ∀ x ∈ A, B ⊆ univ.filter (fun y : Cube ι => f y < f x) := by
      intro x hx y hy
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, lt_of_le_of_lt ((hmemB y).mp hy) ((hmemA x).mp hx)⟩
    have hGnn : ∀ x : Cube ι, ∀ y ∈ univ.filter (fun y : Cube ι => f y < f x),
        0 ≤ 6 * ((f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)) := by
      intro x y hy
      have hlt := (Finset.mem_filter.mp hy).2
      exact mul_nonneg (by norm_num) (div_nonneg (pow_nonneg (by linarith) 3)
        (mul_nonneg (by norm_num) (pairSum_pos ha hrow hw hlt).le))
    have h7 : ∑ j, meanAbsIncr f j / w j ≤ M * ∑ j, (w j)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hM j) (inv_pos.mpr (hw j)).le
    have h8 : (0 : ℝ) ≤ 4 ^ Fintype.card ι := by positivity
    have h9 := mul_le_mul_of_nonneg_left h7 h8
    calc ∑ x ∈ A, ∑ y ∈ B,
          (∑ j ∈ diffSet x y, w j * (a x j / max (f x - s) 0 ^ 3) * a y j)⁻¹
        ≤ ∑ x ∈ A, ∑ y ∈ B,
            6 * ((f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)) :=
          Finset.sum_le_sum (fun x hx => Finset.sum_le_sum (fun y hy => hterm x hx y hy))
      _ ≤ ∑ x ∈ A, ∑ y ∈ univ.filter (fun y : Cube ι => f y < f x),
            6 * ((f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)) :=
          Finset.sum_le_sum (fun x hx => Finset.sum_le_sum_of_subset_of_nonneg (hsub x hx)
            (fun y hy _ => hGnn x y hy))
      _ ≤ ∑ x, ∑ y ∈ univ.filter (fun y : Cube ι => f y < f x),
            6 * ((f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun x _ _ => Finset.sum_nonneg (fun y hy => hGnn x y hy))
      _ = 6 * ∑ x, ∑ y ∈ univ.filter (fun y : Cube ι => f y < f x),
            (f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
      _ ≤ 3 / 2 * 4 ^ Fintype.card ι * M * ∑ j, (w j)⁻¹ := by linarith

end Level

/-- The third-moment inequality (Theorem 7.6 of the paper, first inequality) from the integrated
all-pairs inequality (Proposition 7.4). -/
theorem thirdMoment_of_integratedAllPairs :
    IntegratedAllPairsInequality → ThirdMomentInequality := by
  intro hInt ι _ _ f K a ha hsum hrow M hM0 hM s
  have h := Level.thirdMoment_core hInt f a ha hsum hrow hM0 hM s
  have h4 : (4 : ℝ) ^ Fintype.card ι = 2 ^ Fintype.card ι * 2 ^ Fintype.card ι := by
    rw [← mul_pow]
    norm_num
  have h2 : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  rw [div_mul_div_comm, div_le_iff₀ (mul_pos h2 h2)]
  rw [h4] at h
  linarith

namespace Level

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The third-moment inequality on the other side (Theorem 7.6 of the paper, second inequality):
`E[((s - f)⁺)^3] · Pr[f ≥ s] ≤ (3/2) K² M`. It is the third-moment inequality for `-f` and `-s`. -/
theorem thirdMoment_lower (hTM : ThirdMomentInequality) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    (ha : ∀ x j, 0 ≤ a x j) {K : ℝ} (hsum : ∀ x, ∑ j, a x j ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j, meanAbsIncr f j ≤ M) (s : ℝ) :
    (∑ x, max (s - f x) 0 ^ 3) / 2 ^ Fintype.card ι
        * (((univ.filter (fun y : Cube ι => s ≤ f y)).card : ℝ) / 2 ^ Fintype.card ι)
      ≤ 3 / 2 * K ^ 2 * M := by
  have hrow' : ∀ x y, |(fun x => -f x) x - (fun x => -f x) y| ≤ ∑ j ∈ diffSet x y, a x j := by
    intro x y
    change |-f x - -f y| ≤ ∑ j ∈ diffSet x y, a x j
    rw [neg_sub_neg, abs_sub_comm]
    exact hrow x y
  have hM' : ∀ j, meanAbsIncr (fun x => -f x) j ≤ M := by
    intro j
    have e : meanAbsIncr (fun x => -f x) j = meanAbsIncr f j := by
      unfold meanAbsIncr
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      change |-f x - -f (flipSet x {j})| = |f x - f (flipSet x {j})|
      rw [neg_sub_neg, abs_sub_comm]
    rw [e]
    exact hM j
  have h := hTM ι (fun x => -f x) K a ha hsum hrow' M hM0 hM' (-s)
  have e1 : ∀ x, max ((fun x => -f x) x - -s) 0 = max (s - f x) 0 := by
    intro x
    change max (-f x - -s) 0 = max (s - f x) 0
    rw [neg_sub_neg]
  have e2 : (univ.filter (fun y : Cube ι => (fun x => -f x) y ≤ -s))
      = univ.filter (fun y : Cube ι => s ≤ f y) := by
    apply Finset.filter_congr
    intro y _
    change -f y ≤ -s ↔ s ≤ f y
    exact neg_le_neg_iff
  simp only [e1] at h
  rw [e2] at h
  exact h

/-- Two separated sets (Corollary 7.7 of the paper). If `f` has rows of cost at most `K`
everywhere, `M ≥ 0` bounds all `L_j = meanAbsIncr f j`, and `f ≥ s + θ` on `A`, `f ≤ s` on `B`
with `θ ≥ 0`, then `2 θ^3 μ(A) μ(B) ≤ 3 K² M` (`μ` the uniform probability on the cube). -/
theorem separated_sets (hTM : ThirdMomentInequality) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    (ha : ∀ x j, 0 ≤ a x j) {K : ℝ} (hsum : ∀ x, ∑ j, a x j ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j, meanAbsIncr f j ≤ M)
    (A B : Finset (Cube ι)) (s θ : ℝ) (hθ : 0 ≤ θ)
    (hA : ∀ x ∈ A, s + θ ≤ f x) (hB : ∀ y ∈ B, f y ≤ s) :
    2 * θ ^ 3 * ((A.card : ℝ) / 2 ^ Fintype.card ι) * ((B.card : ℝ) / 2 ^ Fintype.card ι)
      ≤ 3 * K ^ 2 * M := by
  have h := hTM ι f K a ha hsum hrow M hM0 hM s
  have h2 : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  -- `θ^3 #A ≤ ∑_x ((f x - s)⁺)^3`
  have h1 : θ ^ 3 * (A.card : ℝ) ≤ ∑ x, max (f x - s) 0 ^ 3 := by
    calc θ ^ 3 * (A.card : ℝ) = ∑ _x ∈ A, θ ^ 3 := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ x ∈ A, max (f x - s) 0 ^ 3 := by
          apply Finset.sum_le_sum
          intro x hx
          exact pow_le_pow_left₀ hθ (le_max_of_le_left (by linarith [hA x hx])) 3
      _ ≤ ∑ x, max (f x - s) 0 ^ 3 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun x _ _ => pow_nonneg (le_max_right _ _) 3)
  -- `#B ≤ #{f ≤ s}`
  have h3 : (B.card : ℝ) ≤ ((univ.filter (fun y : Cube ι => f y ≤ s)).card : ℝ) := by
    have hsub : B ⊆ univ.filter (fun y : Cube ι => f y ≤ s) := by
      intro y hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB y hy⟩
    exact_mod_cast Finset.card_le_card hsub
  have h5 : θ ^ 3 * (A.card : ℝ) / 2 ^ Fintype.card ι * ((B.card : ℝ) / 2 ^ Fintype.card ι)
      ≤ (∑ x, max (f x - s) 0 ^ 3) / 2 ^ Fintype.card ι
        * (((univ.filter (fun y : Cube ι => f y ≤ s)).card : ℝ) / 2 ^ Fintype.card ι) :=
    mul_le_mul (div_le_div_of_nonneg_right h1 h2.le) (div_le_div_of_nonneg_right h3 h2.le)
      (div_nonneg (Nat.cast_nonneg _) h2.le)
      (div_nonneg (Finset.sum_nonneg fun x _ => pow_nonneg (le_max_right _ _) 3) h2.le)
  have h6 : 2 * θ ^ 3 * ((A.card : ℝ) / 2 ^ Fintype.card ι) * ((B.card : ℝ) / 2 ^ Fintype.card ι)
      = 2 * (θ ^ 3 * (A.card : ℝ) / 2 ^ Fintype.card ι
          * ((B.card : ℝ) / 2 ^ Fintype.card ι)) := by ring
  rw [h6]
  linarith

end Level

end AaronsonAmbainis
