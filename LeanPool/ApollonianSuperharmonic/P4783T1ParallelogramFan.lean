/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

public import Mathlib.Analysis.Convex.Combination

-- [TABLET NODE: P4783T1ParallelogramFan]

/-!
# P4783T1ParallelogramFan

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4783T1ParallelogramFan
    {E : Type*} [AddCommGroup E] [Module Real E]
    (A u v : E) (x y : Real)
    (hx : 0 ≤ x) (hx' : x ≤ 1) (hy : 0 ≤ y) (hy' : y ≤ 1) :
    let O := A + (1 / 2 : Real) • u + (1 / 2 : Real) • v
    let z := A + x • u + y • v
    z ∈ convexHull Real ({A, A + u, O} : Set E) ∨
    z ∈ convexHull Real ({A + u, A + u + v, O} : Set E) ∨
    z ∈ convexHull Real ({A + u + v, A + v, O} : Set E) ∨
    z ∈ convexHull Real ({A + v, A, O} : Set E) := by
-- BODY
  dsimp only
  have triangle (P Q R : E) (a b c : Real)
      (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : a + b + c = 1) :
      a • P + b • Q + c • R ∈ convexHull Real ({P, Q, R} : Set E) := by
    apply mem_convexHull_of_exists_fintype (ι := Fin 3) ![a, b, c] ![P, Q, R]
    · intro i
      fin_cases i
      · exact ha
      · exact hb
      · exact hc
    · simpa [Fin.sum_univ_succ, add_assoc] using hs
    · intro i
      fin_cases i <;> simp
    · simp [Fin.sum_univ_succ, add_assoc]
  by_cases hxy : y ≤ x
  · by_cases hsum : x + y ≤ 1
    · left
      convert triangle A (A + u) (A + (1 / 2 : Real) • u + (1 / 2 : Real) • v)
        (1 - x - y) (x - y) (2 * y) (by linarith) (by linarith)
        (by linarith) (by ring) using 1; module
    · right; left
      convert triangle (A + u) (A + u + v)
        (A + (1 / 2 : Real) • u + (1 / 2 : Real) • v)
        (x - y) (x + y - 1) (2 - 2 * x) (by linarith) (by linarith)
        (by linarith) (by ring) using 1; module
  · by_cases hsum : x + y ≤ 1
    · right; right; right
      convert triangle (A + v) A (A + (1 / 2 : Real) • u + (1 / 2 : Real) • v)
        (y - x) (1 - x - y) (2 * x) (by linarith) (by linarith)
        (by linarith) (by ring) using 1; module
    · right; right; left
      convert triangle (A + u + v) (A + v)
        (A + (1 / 2 : Real) • u + (1 / 2 : Real) • v)
        (x + y - 1) (y - x) (2 - 2 * y) (by linarith) (by linarith)
        (by linarith) (by ring) using 1; module

end ApollonianSuperharmonic

end
