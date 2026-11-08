/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.NormNum
public import LeanPool.AaronsonAmbainis.Row.Main

/-!
# The hypothesis `0 < m` of `BlockInequality` is needed

A check of the statement, not used in the proof of the main theorem. In Lean `π / 0 = 0`, so at
`m = 0` the hypothesis `N (1 - cos (π / m)) ≤ 2` holds for every `N`, while the right side
`4 d² m²` is `0`. Witness: `f = chi {()}` on `Cube Unit` and the single block `{()}`; the left
side is `2`. (Lemma 6.4 of the paper assumes `m ≥ 1`.)
-/

@[expose] public section

namespace AaronsonAmbainis
namespace Row

open Finset

/-- `BlockInequality` with the hypothesis `0 < m` deleted is false. -/
theorem not_blockInequality_without_pos :
    ¬ (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
        HasDegreeLE f d →
      ∀ (x : Cube ι) (β : Type) [Fintype β] (S : β → Finset ι) (N m : ℕ),
        (∀ i, (univ.filter fun b : β => i ∈ S b).card ≤ N) →
        (N : ℝ) * (1 - Real.cos (Real.pi / (m : ℝ))) ≤ 2 →
        ∑ b, |f x - f (flipSet x (S b))| ≤ 4 * (d : ℝ) ^ 2 * (m : ℝ) ^ 2) := by
  intro h
  have hf : ∀ x : Cube Unit, |chi ({()} : Finset Unit) x| ≤ 1 := by
    intro x
    rw [chi_eq_prod_sgn, Finset.prod_singleton]
    exact (abs_sgn _).le
  have hdeg : HasDegreeLE (chi ({()} : Finset Unit)) 1 :=
    hasDegreeLE_chi ({()} : Finset Unit) (by simp)
  have hc : ((1 : ℕ) : ℝ) * (1 - Real.cos (Real.pi / ((0 : ℕ) : ℝ))) ≤ 2 := by
    rw [Nat.cast_zero, div_zero, Real.cos_zero, sub_self, mul_zero]
    norm_num
  have h1 := h Unit 1 (chi {()}) hf hdeg (zero Unit) Unit (fun _ => {()}) 1 0
    (fun i => Finset.card_le_one_of_subsingleton _) hc
  have e2 : chi ({()} : Finset Unit) (flipSet (zero Unit) {()}) = -1 := by
    rw [chi_flipSet, Finset.prod_singleton]
    simp [zero]
  simp only [Fintype.sum_unique, chi_zero, e2] at h1
  have h2 : (1 : ℝ) - -1 ≤ 4 * ((1 : ℕ) : ℝ) ^ 2 * ((0 : ℕ) : ℝ) ^ 2 := (le_abs_self _).trans h1
  norm_num at h2

end Row
end AaronsonAmbainis
