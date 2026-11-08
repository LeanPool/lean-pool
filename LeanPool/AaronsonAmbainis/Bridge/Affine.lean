/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.Bridge.Basic
public import LeanPool.AaronsonAmbainis.Level.Basic

/-!
# `mean`, `variance`, `inflR` under affine maps; degenerate cases

* `mean`, `variance`, `inflR` of `a + b * g`                  (`mean_affine`, `variance_affine`,
  `inflR_affine`): the change of normalisation `[0,1] ↔ [-1,1]` multiplies variance and
  influence by the same factor `4`.
* The hypothesis `0 < variance f` of `MainTheorem` forces `1 ≤ d` and a nonempty index type
  (`aa_hyps_force`): the instances `d = 0` and `ι = ∅` of `MainTheorem` are vacuous, and these
  are exactly the instances in which no coordinate can have positive influence.
* `variance f ≤ 1` if `|f| ≤ 1`, `variance P ≤ 1/4` if `0 ≤ P ≤ 1`.

The elementary facts on the variance that are used here are in `Level/Basic.lean`.
-/

@[expose] public section

namespace AaronsonAmbainis.Bridge

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mean_affine (a b : ℝ) (g : Cube ι → ℝ) :
    mean (fun x => a + b * g x) = a + b * mean g := by
  have hne : (2 : ℝ) ^ Fintype.card ι ≠ 0 := by positivity
  simp only [mean]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_cube,
    ← Finset.mul_sum, add_div, mul_div_cancel_left₀ a hne, mul_div_assoc]

theorem variance_affine (a b : ℝ) (g : Cube ι → ℝ) :
    variance (fun x => a + b * g x) = b ^ 2 * variance g := by
  have h : ∀ x : Cube ι, (a + b * g x - (a + b * mean g)) ^ 2 = b ^ 2 * (g x - mean g) ^ 2 :=
    fun x => by ring
  simp only [variance, mean_affine, h]
  rw [← Finset.mul_sum, mul_div_assoc]

theorem inflR_affine (a b : ℝ) (g : Cube ι → ℝ) (j : ι) :
    inflR (fun x => a + b * g x) j = b ^ 2 * inflR g j := by
  have h : ∀ x : Cube ι, ((a + b * g x - (a + b * g (flipSet x {j}))) / 2) ^ 2
      = b ^ 2 * ((g x - g (flipSet x {j})) / 2) ^ 2 := fun x => by ring
  simp only [inflR, h]
  rw [← Finset.mul_sum, mul_div_assoc]

/-! ### Degenerate cases -/

/-- Degree `0` forces variance `0`: the `d = 0` instance of `MainTheorem` is vacuous. -/
theorem variance_eq_zero_of_degree_zero {f : Cube ι → ℝ} (h : HasDegreeLE f 0) :
    variance f = 0 :=
  Level.variance_eq_zero_of_const f (hasDegreeLE_zero_const h)

/-- The hypotheses of `MainTheorem` force `d ≥ 1` and a nonempty index type. In particular the
division by a power of `d` in the printed forms of the bounds is never a division by zero under
the hypotheses. -/
theorem aa_hyps_force {f : Cube ι → ℝ} {d : ℕ} (hdeg : HasDegreeLE f d) (hv : 0 < variance f) :
    1 ≤ d ∧ Nonempty ι := by
  constructor
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [variance_eq_zero_of_degree_zero hdeg] at hv
      exact absurd hv (lt_irrefl 0)
    · exact hd
  · by_contra hne
    have : IsEmpty ι := not_nonempty_iff.mp hne
    rw [Level.variance_eq_zero_of_isEmpty f] at hv
    exact lt_irrefl 0 hv

/-! ### Size of the variance -/

/-- A `[0,1]`-valued function has variance at most `1/4`. -/
theorem variance_le_quarter {P : Cube ι → ℝ} (h : ∀ x, 0 ≤ P x ∧ P x ≤ 1) :
    variance P ≤ 1 / 4 := by
  have hpos : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  refine (Level.variance_le_sq_dist P (1 / 2)).trans ?_
  rw [div_le_iff₀ hpos]
  have h1 : ∑ x : Cube ι, (P x - 1 / 2) ^ 2 ≤ ∑ _x : Cube ι, (1 / 4 : ℝ) :=
    Finset.sum_le_sum (fun x _ => by
      obtain ⟨h0, h1⟩ := h x
      nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)])
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_cube] at h1
  linarith

/-- A `[-1,1]`-valued function has variance at most `1`. -/
theorem variance_le_one {f : Cube ι → ℝ} (h : ∀ x, |f x| ≤ 1) : variance f ≤ 1 := by
  have hpos : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  refine (Level.variance_le_sq_dist f 0).trans ?_
  rw [div_le_iff₀ hpos]
  have h1 : ∑ x : Cube ι, (f x - 0) ^ 2 ≤ ∑ _x : Cube ι, (1 : ℝ) :=
    Finset.sum_le_sum (fun x _ => by
      have h2 := abs_le.mp (h x)
      have h3 : 0 ≤ 1 - f x := by linarith [h2.2]
      have h4 : 0 ≤ 1 + f x := by linarith [h2.1]
      nlinarith [mul_nonneg h3 h4])
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_cube] at h1
  linarith

end AaronsonAmbainis.Bridge
