/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF

/-!
Reciprocal-pair comparisons for `1 / ((2j+1) * (2j+2))`.
The positive-index bounds use reciprocal-quadratic terms whose sums telescope.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

namespace ECRuntime

/-- Elementary real-algebra comparison of the three positive denominators. -/
private theorem stage191_denominator_bounds (x : Real) (hx : 1 ≤ x) :
    (4 * x * (x+1)) ≤ ((2*x+1) * (2*x+2)) ∧
      ((2*x+1) * (2*x+2)) ≤ (4 * (x+1) * (x+2)) := by
  constructor <;> nlinarith

/-- Each dyadic pair is trapped between adjacent telescoping terms.
Unlike the Stage 189 limit, this is a purely rational inequality. -/
theorem proposed_randomInitialStake_pairReciprocalBounds
    (j : Nat) (hj : 1 ≤ j) :
    1 / (4 * ((j : Real) + 1) * ((j : Real) + 2)) ≤
      1 / ((2 * (j : Real) + 1) * (2 * (j : Real) + 2)) ∧
    1 / ((2 * (j : Real) + 1) * (2 * (j : Real) + 2)) ≤
      1 / (4 * (j : Real) * ((j : Real) + 1)) := by
  have hx : (1 : Real) ≤ (j : Real) := by exact_mod_cast hj
  obtain ⟨hupperDen, hlowerDen⟩ := stage191_denominator_bounds (j : Real) hx
  have hleft : (0 : Real) < 4 * ((j : Real)+1) * ((j : Real)+2) := by positivity
  have hmid : (0 : Real) < (2 * (j : Real)+1) * (2 * (j : Real)+2) := by positivity
  have hright : (0 : Real) < 4 * (j : Real) * ((j : Real)+1) := by positivity
  constructor
  · exact (div_le_div_iff₀ hleft hmid).2 (by nlinarith)
  · exact (div_le_div_iff₀ hmid hright).2 (by nlinarith)

/-- The dyadic pair is exactly the positive reciprocal-quadratic summand. -/
theorem stage191_dyadicPair_eq_reciprocal (j : Nat) :
    (((2*j+1 : Nat) : Real)⁻¹ - ((2*j+2 : Nat) : Real)⁻¹) =
      1 / ((2 * (j : Real)+1) * (2 * (j : Real)+2)) := by
  have h1 : (((2*j+1 : Nat) : Real)) = 2 * (j : Real)+1 := by
    push_cast
    ring
  have h2 : (((2*j+2 : Nat) : Real)) = 2 * (j : Real)+2 := by
    push_cast
    ring
  rw [h1, h2]
  have hn1 : (2 * (j : Real)+1) ≠ 0 := by positivity
  have hn2 : (2 * (j : Real)+2) ≠ 0 := by positivity
  field_simp [hn1, hn2]
  ring

end ECRuntime
