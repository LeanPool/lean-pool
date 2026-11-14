/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.AllowedSubtileIncidence
public import LeanPool.ApollonianSuperharmonic.P4630T1RingIndex
public import Mathlib.LinearAlgebra.Matrix.Notation

-- [TABLET NODE: P4630T1ExteriorNeighbors]

/-!
# P4630T1ExteriorNeighbors

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4630T1ExteriorNeighbors
    {a b : PeriodicSubtileIndex} (h : AllowedSubtileIncidence a b)
    (ha : a.first = 0 ∧ a.second = 0)
    (hb : ¬ (b.first = 0 ∧ b.second = 0)) :
    ∃ i k, b = P4630T1RingIndex i k := by
-- BODY
  have table : ∀ {a b}, AllowedSubtileIncidence a b →
      ((a.first = 0 ∧ a.second = 0) →
        ¬ (b.first = 0 ∧ b.second = 0) →
        ∃ i k, b = P4630T1RingIndex i k) ∧
      ((b.first = 0 ∧ b.second = 0) →
        ¬ (a.first = 0 ∧ a.second = 0) →
        ∃ i k, a = P4630T1RingIndex i k) := by
    intro a b e
    induction e with
    | symm _ ih => exact ih.symm
    | _ =>
      simp [P4630T1RingIndex, Fin.exists_fin_succ,
        PeriodicSubtileIndex.mk.injEq] at *; omega
  exact (table h).1 ha hb

end ApollonianSuperharmonic

end
