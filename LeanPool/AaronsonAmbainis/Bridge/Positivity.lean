/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.TwoSided.Overlap
public import LeanPool.AaronsonAmbainis.Bridge.Basic

/-!
# Positivity of the sums that are inverted; the antipodal and the all-pairs inequality

In Lean `x⁻¹ = 0` when `x = 0`. The propositions `AntipodalInequality`, `AllPairsInequality` and
`TwoSidedInequality` contain inverses of sums of row entries. If one of these sums could vanish,
the Lean statement would say less than the statement of the paper, in which reciprocals are
taken of positive numbers only. It cannot:

* `antipodal_inner_pos` — on `Z(g)` the sum `∑_j w_j λ^u_j λ^{ū}_j` is positive (the first
  assertion of Theorem 4.3 of the paper);
* `allPairs_inner_pos` — for `g x = 1`, `g y = 0` the sum `∑_{j ∈ Δ(x,y)} w_j λ^x_j λ^y_j` is
  positive (the first assertion of Proposition 5.2);
* `row_norm_ge_one` — at a point of a non-constant `g` every row has `‖λ‖ ≥ 1` (Lemma 2.4 (ii)).

(The first two are instances of the last assertion of the overlap lemma, Lemma 4.1 of the paper,
which is `AaronsonAmbainis.overlap_pos` in `TwoSided/Overlap.lean`.)

Then two further forms of the antipodal and of the all-pairs inequality are compared with the
propositions:

* `antipodal_iff_onZone : AntipodalInequality ↔ AntipodalOnZone` (rows are given only on `Z(g)`
  and its antipodes, where Theorem 4.3 assumes a row at every point);
* `allPairs_iff_nonconstant : AllPairsInequality ↔ AllPairsNonconstant` (non-constant `g`,
  factor `2^(n-1)`: the inequality of Proposition 5.2, which `AllPairsInequality` states
  multiplied by `2`).

Nothing here says that either of these two inequalities holds. The propositions are proved in
`Chain.lean` (`antipodalInequality`, `allPairsInequality`).
-/

@[expose] public section

namespace AaronsonAmbainis.Bridge

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem diffSet_antipode (u : Cube ι) : diffSet u (antipode u) = univ := by
  ext i
  simp [diffSet, antipode]

omit [Fintype ι] [DecidableEq ι] in
theorem antipode_antipode (x : Cube ι) : antipode (antipode x) = x := by
  funext i
  simp [antipode]

omit [Fintype ι] in
/-- The all-ones vector is a row of every `g` at every point (Lemma 2.4 (i) of the paper). -/
theorem isRow_one (g : Cube ι → Bool) (x : Cube ι) : IsRow g x (fun _ => 1) := by
  refine ⟨fun _ => zero_le_one, fun S hS => ?_⟩
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, AaronsonAmbainis.Bridge.flipSet_empty] at hS
    exact hS rfl
  change (1 : ℝ) ≤ ∑ _j ∈ S, (1 : ℝ)
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast Finset.one_le_card.mpr hne

/-- No junk value in `AntipodalInequality`: on the zone the inner sum is positive. -/
theorem antipodal_inner_pos {g : Cube ι → Bool} {u : Cube ι} (hu : u ∈ zone g) {w : ι → ℝ}
    (hw : ∀ j, 0 < w j) {lam : Cube ι → ι → ℝ}
    (h1 : IsRow g u (lam u)) (h2 : IsRow g (antipode u) (lam (antipode u))) :
    0 < ∑ j, w j * lam u j * lam (antipode u) j := by
  have hu' : g u = true ∧ g (antipode u) = false := AaronsonAmbainis.mem_zone.mp hu
  have hne : g u ≠ g (antipode u) := by
    rw [hu'.1, hu'.2]
    exact fun h => Bool.noConfusion h
  have h := AaronsonAmbainis.overlap_pos hne h1 h2 hw
  rw [diffSet_antipode] at h
  exact h

/-- No junk value in `AllPairsInequality`: for a one `x` and a zero `y` of `g` the inner sum is
positive. -/
theorem allPairs_inner_pos {g : Cube ι → Bool} {x y : Cube ι} (hx : g x = true) (hy : g y = false)
    {w : ι → ℝ} (hw : ∀ j, 0 < w j) {lam : Cube ι → ι → ℝ}
    (h1 : IsRow g x (lam x)) (h2 : IsRow g y (lam y)) :
    0 < ∑ j ∈ diffSet x y, w j * lam x j * lam y j := by
  have hne : g x ≠ g y := by
    rw [hx, hy]
    exact fun h => Bool.noConfusion h
  exact AaronsonAmbainis.overlap_pos hne h1 h2 hw

/-- No junk value in `TwoSidedInequality`: if `g` takes another value somewhere, every row at
`x` has total weight at least `1` (Lemma 2.4 (ii) of the paper). -/
theorem row_norm_ge_one {g : Cube ι → Bool} {x y : Cube ι} (hxy : g y ≠ g x) {lam : ι → ℝ}
    (h : IsRow g x lam) : 1 ≤ ∑ j, lam j := by
  have h1 : 1 ≤ ∑ j ∈ diffSet x y, lam j := by
    apply h.2
    rw [AaronsonAmbainis.Bridge.flipSet_diffSet]
    exact hxy
  exact h1.trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => h.1 j))

/-! ### The antipodal inequality with rows on the zone and its antipodes -/

/-- The antipodal inequality with rows given only on `Z(g)` and on its antipodes: if `g` is a
Boolean function, `w ∈ (0,∞)^n`, and for every `u ∈ Z(g)` the vectors `λ^u` and `λ^ū` are rows of
`g` at `u` and at `ū`, then `∑_{u ∈ Z(g)} (∑_j w_j λ^u_j λ^ū_j)^{-1} ≤ ∑_j b_j(g) / w_j`.
Theorem 4.3 of the paper states this inequality under the assumption of a row at every point. -/
def AntipodalOnZone : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool) (w : ι → ℝ), (∀ j, 0 < w j) →
  ∀ (lam : Cube ι → ι → ℝ),
    (∀ u ∈ zone g, IsRow g u (lam u) ∧ IsRow g (antipode u) (lam (antipode u))) →
    ∑ u ∈ zone g, 1 / (∑ j, w j * lam u j * lam (antipode u) j) ≤ ∑ j, (bdry g j : ℝ) / w j

/-- A row field given on `Z(g)` and its antipodes, extended by the all-ones vector elsewhere. -/
noncomputable def extendRows (g : Cube ι → Bool) (lam : Cube ι → ι → ℝ) : Cube ι → ι → ℝ :=
  fun x => if x ∈ zone g ∨ antipode x ∈ zone g then lam x else fun _ => 1

theorem extendRows_pos {g : Cube ι → Bool} {lam : Cube ι → ι → ℝ} {x : Cube ι}
    (h : x ∈ zone g ∨ antipode x ∈ zone g) : extendRows g lam x = lam x := by
  unfold extendRows
  exact ite_eq_left h

theorem extendRows_neg {g : Cube ι → Bool} {lam : Cube ι → ι → ℝ} {x : Cube ι}
    (h : ¬ (x ∈ zone g ∨ antipode x ∈ zone g)) : extendRows g lam x = fun _ => 1 := by
  unfold extendRows
  exact ite_eq_right h

theorem antipodal_iff_onZone : AntipodalInequality ↔ AntipodalOnZone := by
  constructor
  · intro h ι _ _ g w hw lam hrow
    have hrow' : ∀ x, IsRow g x (extendRows g lam x) := by
      intro x
      by_cases hx : x ∈ zone g ∨ antipode x ∈ zone g
      · rw [extendRows_pos hx]
        rcases hx with hx | hx
        · exact (hrow x hx).1
        · have h2 := (hrow (antipode x) hx).2
          rw [antipode_antipode] at h2
          exact h2
      · rw [extendRows_neg hx]
        exact isRow_one g x
    have h1 := h ι g w hw (extendRows g lam) hrow'
    have e : ∑ u ∈ zone g, 1 / (∑ j, w j * lam u j * lam (antipode u) j)
        = ∑ u ∈ zone g,
            (∑ j, w j * extendRows g lam u j * extendRows g lam (antipode u) j)⁻¹ := by
      apply Finset.sum_congr rfl
      intro u hu
      have hu2 : antipode (antipode u) ∈ zone g := by
        rw [antipode_antipode]
        exact hu
      rw [extendRows_pos (Or.inl hu), extendRows_pos (Or.inr hu2), one_div]
    rw [e]
    exact h1
  · intro h ι _ _ g w hw lam hrow
    have h1 := h ι g w hw lam (fun u _ => ⟨hrow u, hrow (antipode u)⟩)
    simp only [one_div] at h1
    exact h1

/-! ### The all-pairs inequality with the factor `2^(n-1)` -/

theorem two_pow_eq {n : ℕ} (hn : 1 ≤ n) : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.sub_add_cancel hn).symm⟩
  rw [Nat.add_sub_cancel, pow_succ]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem nonempty_of_ne {g : Cube ι → Bool} {x y : Cube ι} (h : g x ≠ g y) : Nonempty ι := by
  by_contra hcon
  have : IsEmpty ι := not_nonempty_iff.mp hcon
  exact h (congrArg g (Subsingleton.elim x y))

omit [DecidableEq ι] in
theorem one_le_card_of_ne {g : Cube ι → Bool} {x y : Cube ι} (h : g x ≠ g y) :
    1 ≤ Fintype.card ι := by
  have : Nonempty ι := nonempty_of_ne h
  exact Fintype.card_pos

/-- The all-pairs inequality (the inequality of Proposition 5.2 of the paper) for non-constant `g`,
written as one sum over the pairs: with `O = g⁻¹(1)`, `N = g⁻¹(0)`, a row `λ^x` of `g` at every
point `x` and `w ∈ (0,∞)^n`,
`∑_{(x,y) ∈ O × N} (∑_{j ∈ Δ(x,y)} w_j λ^x_j λ^y_j)^{-1} ≤ 2^(n-1) ∑_j b_j(g) / w_j`.
(Proposition 5.2 does not assume that `g` is not constant. For non-constant `g` one has `n ≥ 1`,
so that the exponent `n - 1`, a difference of natural numbers, is the usual difference.) -/
def AllPairsNonconstant : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool), (∃ x y, g x ≠ g y) →
  ∀ (lam : Cube ι → ι → ℝ), (∀ x, IsRow g x (lam x)) → ∀ (w : ι → ℝ), (∀ j, 0 < w j) →
    ∑ p ∈ (univ.filter fun x : Cube ι => g x = true) ×ˢ
          (univ.filter fun y : Cube ι => g y = false),
        1 / (∑ j ∈ diffSet p.1 p.2, w j * lam p.1 j * lam p.2 j)
      ≤ 2 ^ (Fintype.card ι - 1) * ∑ j, (bdry g j : ℝ) / w j

theorem allPairs_lhs_eq (g : Cube ι → Bool) (lam : Cube ι → ι → ℝ) (w : ι → ℝ) :
    ∑ p ∈ (univ.filter fun x : Cube ι => g x = true) ×ˢ
          (univ.filter fun y : Cube ι => g y = false),
        1 / (∑ j ∈ diffSet p.1 p.2, w j * lam p.1 j * lam p.2 j)
      = ∑ x ∈ univ.filter (fun x : Cube ι => g x = true),
          ∑ y ∈ univ.filter (fun y : Cube ι => g y = false),
            (∑ j ∈ diffSet x y, w j * lam x j * lam y j)⁻¹ := by
  rw [Finset.sum_product]
  simp only [one_div]

theorem allPairs_iff_nonconstant : AllPairsInequality ↔ AllPairsNonconstant := by
  constructor
  · intro h ι _ _ g hnc lam hrow w hw
    obtain ⟨x, y, hxy⟩ := hnc
    have h1 := h ι g w hw lam hrow
    rw [allPairs_lhs_eq]
    rw [two_pow_eq (one_le_card_of_ne hxy), mul_assoc] at h1
    exact le_of_mul_le_mul_left h1 (by norm_num)
  · intro h ι _ _ g w hw lam hrow
    by_cases hnc : ∃ x y, g x ≠ g y
    · have h1 := h ι g hnc lam hrow w hw
      obtain ⟨x, y, hxy⟩ := hnc
      rw [allPairs_lhs_eq] at h1
      rw [two_pow_eq (one_le_card_of_ne hxy), mul_assoc]
      exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    · have hz : ∑ x ∈ univ.filter (fun x : Cube ι => g x = true),
          ∑ y ∈ univ.filter (fun y : Cube ι => g y = false),
            (∑ j ∈ diffSet x y, w j * lam x j * lam y j)⁻¹ = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        apply Finset.sum_eq_zero
        intro y hy
        exfalso
        apply hnc
        refine ⟨x, y, ?_⟩
        rw [(Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2]
        exact fun h => Bool.noConfusion h
      rw [hz, mul_zero]
      exact mul_nonneg (by positivity)
        (Finset.sum_nonneg fun j _ => div_nonneg (Nat.cast_nonneg _) (hw j).le)

end AaronsonAmbainis.Bridge
