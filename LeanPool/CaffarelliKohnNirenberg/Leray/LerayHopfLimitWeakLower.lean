/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith

/-!
# Weak lower semicontinuity of Hilbert norms

This is the Hilbert-space lower-semicontinuity step used for the slice and
dissipation bounds in `prop:leray-hopf-limit`.
-/

public section

open Filter
open scoped InnerProductSpace



namespace CKN.Leray

/-- A weakly convergent family with uniformly bounded norms has a limit with
the same norm bound. -/
theorem norm_le_of_tendsto_inner_and_uniform_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {α : Type*} {l : Filter α} [NeBot l] {v : α → E} {a : E} {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ᶠ x in l, ‖v x‖ ≤ C)
    (hinner : Tendsto (fun x => ⟪v x, a⟫_ℝ) l (nhds (‖a‖ ^ 2))) :
    ‖a‖ ≤ C := by
  have hpairBound : ∀ᶠ x in l, ⟪v x, a⟫_ℝ ≤ C * ‖a‖ := by
    filter_upwards [hbound] with x hx
    exact (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  have hnormSq : ‖a‖ ^ 2 ≤ C * ‖a‖ :=
    le_of_tendsto_of_tendsto hinner tendsto_const_nhds hpairBound
  by_contra hnot
  have hlt : C < ‖a‖ := lt_of_not_ge hnot
  have hpos : 0 < ‖a‖ := lt_of_le_of_lt hC hlt
  nlinarith only [hnormSq, hlt, hpos]

end CKN.Leray
