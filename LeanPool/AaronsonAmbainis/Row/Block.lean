/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.Row.Sensitivity
public import LeanPool.AaronsonAmbainis.Row.Gadget

/-!
# The block inequality from Markov's inequality

`blockInequality_of_markov : MarkovEndpoint → BlockInequality` is the block inequality (Lemma 6.4
of the paper), with Markov's inequality at an endpoint as a hypothesis.

The gadget `G = Row.gadget a x S m c` with `c = 1 - cos (π / m)` is bounded by `1`, has degree at
most `d * m`, and satisfies `G(0) = f x`, `G(e_b) = f (flipSet x (S b))`; the sensitivity lemma
(`Row.sum_abs_sub_unit_le`) then gives the bound `4 (d m)²`.
-/

@[expose] public section

namespace AaronsonAmbainis

open Finset

/-- The block inequality, given Markov's inequality at an endpoint. -/
theorem blockInequality_of_markov : MarkovEndpoint → BlockInequality := by
  intro hM ι _ _ d f hf hdeg x β _ S N m hm hN hNc
  classical
  obtain ⟨a, ha, hfa⟩ := hdeg
  have hc : (0 : ℝ) ≤ 1 - Real.cos (Real.pi / (m : ℝ)) := by
    linarith [Real.cos_le_one (Real.pi / (m : ℝ))]
  have hbd : ∀ z : Cube ι, |∑ T, a T * chi T z| ≤ 1 := fun z => by
    rw [← hfa z]
    exact hf z
  have key := Row.sum_abs_sub_unit_le hM
    (Row.gadget a x S m (1 - Real.cos (Real.pi / (m : ℝ)))) (d * m)
    (Row.abs_gadget_le_one a hbd x S N m _ hc hN hNc)
    (Row.hasDegreeLE_gadget a d ha x S m _)
  have hterm : ∀ b : β, |f x - f (flipSet x (S b))|
      = |Row.gadget a x S m (1 - Real.cos (Real.pi / (m : ℝ))) (Row.zero β)
          - Row.gadget a x S m (1 - Real.cos (Real.pi / (m : ℝ))) (Row.unit b)| := by
    intro b
    rw [Row.gadget_zero, Row.gadget_unit a x S m hm b, ← hfa x, ← hfa (flipSet x (S b))]
  rw [Finset.sum_congr rfl (fun b _ => hterm b)]
  calc ∑ b, |Row.gadget a x S m (1 - Real.cos (Real.pi / (m : ℝ))) (Row.zero β)
          - Row.gadget a x S m (1 - Real.cos (Real.pi / (m : ℝ))) (Row.unit b)|
      ≤ 4 * ((d * m : ℕ) : ℝ) ^ 2 := key
    _ = 4 * (d : ℝ) ^ 2 * (m : ℝ) ^ 2 := by
        push_cast
        ring

end AaronsonAmbainis
