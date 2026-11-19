/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import LeanPool.HubbardMoments.Defs
public import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
# The square-lattice torus

`HubbardMoments.torus L` (defined in `HubbardMoments.Defs`) is the `L × L` square lattice
with periodic boundary conditions: the box product of two cycle graphs on `L` vertices,
built from Mathlib's `SimpleGraph.cycleGraph` and `SimpleGraph.boxProd`.

## Main results

* `torus_isRegularOfDegree`: for `L ≥ 3`, the torus is regular of degree `z = 4`.
* `torus_cliqueFree_three`: for `L ≠ 3`, the torus has no triangle;
  `torus_three_not_cliqueFree`: for `L = 3` it has one (three sites of one row).

## Not covered

For `L = 2` the two neighbours along each axis coincide and the degree is 2, and for
`L ≤ 1` there are no edges. The paper's lattices have `L ≥ 3`.
-/

@[expose] public section

namespace HubbardMoments

open SimpleGraph

private theorem torus_isRegularOfDegree_default (L : ℕ) (hL : 3 ≤ L) :
    (torus L).IsRegularOfDegree 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 3 := ⟨L - 3, by omega⟩
  intro x
  rw [degree_boxProd, cycleGraph_degree_three_le, cycleGraph_degree_three_le]

/-- For `L ≥ 3`, every torus site has four neighbors under any neighbor-set enumeration. -/
theorem torus_isRegularOfDegree (L : ℕ) (hL : 3 ≤ L) [LocallyFinite (torus L)] :
    (torus L).IsRegularOfDegree 4 := by
  convert torus_isRegularOfDegree_default L hL

/-- Torus regularity with the neighbor enumeration induced by the ambient finite type. -/
theorem torus_isRegularOfDegree_of_fintype (L : ℕ) (hL : 3 ≤ L) :
    @SimpleGraph.IsRegularOfDegree (Fin L × Fin L) (torus L)
      (fun v => Subtype.fintype (Membership.mem ((torus L).neighborSet v))) 4 := by
  exact @torus_isRegularOfDegree L hL
    (fun v => Subtype.fintype (Membership.mem ((torus L).neighborSet v)))

open Fin.CommRing in
/-- The cycle `C_L` has no triangle unless `L = 3`: three sites pairwise one step apart
around a cycle force `1 = 0` or `3 = 0` modulo `L`. -/
theorem cycleGraph_cliqueFree_three {L : ℕ} (hL : L ≠ 3) : (cycleGraph L).CliqueFree 3 := by
  match L, hL with
  | 0, _ => rw [cycleGraph_zero_eq_bot]; exact cliqueFree_bot (by norm_num)
  | 1, _ => rw [cycleGraph_one_eq_bot]; exact cliqueFree_bot (by norm_num)
  | n + 2, hL =>
    intro s hs
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := is3Clique_iff.1 hs
    rw [cycleGraph_adj] at hab hac hbc
    -- `(a - b) + (b - c) = a - c` with each difference `±1`.
    have key : (1 : Fin (n + 2)) = 0 ∨ (3 : Fin (n + 2)) = 0 := by
      rcases hab with h₁ | h₁ <;> rcases hac with h₂ | h₂ <;> rcases hbc with h₃ | h₃
      · left; linear_combination -h₁ + h₂ - h₃
      · left; linear_combination h₁ - h₂ - h₃
      · right; linear_combination -h₁ - h₂ - h₃
      · left; linear_combination -h₁ - h₂ + h₃
      · left; linear_combination -h₁ - h₂ + h₃
      · right; linear_combination -h₁ - h₂ - h₃
      · left; linear_combination h₁ - h₂ - h₃
      · left; linear_combination -h₁ + h₂ - h₃
    rcases key with h | h
    · exact one_ne_zero h
    · have h3 : ((3 : ℕ) : Fin (n + 2)) = 0 := by exact_mod_cast h
      rw [Fin.natCast_eq_zero] at h3
      have : n ≤ 1 := by have := Nat.le_of_dvd (by norm_num) h3; omega
      interval_cases n
      · norm_num at h3
      · exact hL rfl

/-- **The torus has no triangle unless `L = 3`.** An edge of the box product changes one
coordinate, so a triangle lies in one row or one column, i.e. in a cycle `C_L`. -/
theorem torus_cliqueFree_three {L : ℕ} (hL : L ≠ 3) : (torus L).CliqueFree 3 := by
  have hC := cycleGraph_cliqueFree_three hL
  intro s hs
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := is3Clique_iff.1 hs
  simp only [torus, boxProd_adj] at hab hac hbc
  rcases hab with ⟨hab, hab'⟩ | ⟨hab, hab'⟩ <;> rcases hac with ⟨hac, hac'⟩ | ⟨hac, hac'⟩ <;>
    rcases hbc with ⟨hbc, hbc'⟩ | ⟨hbc, hbc'⟩
  · exact hC _ (is3Clique_triple_iff.2 ⟨hab, hac, hbc⟩)
  · exact hbc.ne (hab'.symm.trans hac')
  · exact hac.ne (hab'.trans hbc')
  · exact hab.ne (hac'.trans hbc'.symm)
  · exact hab.ne (hac'.trans hbc'.symm)
  · exact hac.ne (hab'.trans hbc')
  · exact hbc.ne (hab'.symm.trans hac')
  · exact hC _ (is3Clique_triple_iff.2 ⟨hab, hac, hbc⟩)

/-- The `3 × 3` torus has a triangle: the three sites of a row. -/
theorem torus_three_not_cliqueFree : ¬ (torus 3).CliqueFree 3 := fun h =>
  h {(0, 0), (1, 0), (2, 0)} (is3Clique_triple_iff.2 (by decide))

end HubbardMoments
