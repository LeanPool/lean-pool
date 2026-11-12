/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3381T1TriangleDeterminant
public import Mathlib.Analysis.Convex.Combination

-- [TABLET NODE: P3652T1TriangleFaceRestriction]

/-!
# P3652T1TriangleFaceRestriction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3652T1TriangleFaceRestriction (v : Fin 3 → Real × Real)
    (hv : P3381T1TriangleDeterminant v ≠ 0) (s t : Set (Fin 3)) :
    convexHull Real (v '' s) ∩ convexHull Real (v '' t) =
      convexHull Real (v '' (s ∩ t)) := by
-- BODY
  classical
  have ha : AffineIndependent Real v := by
    apply (affineIndependent_iff_of_fintype Real v).mpr
    intro w hw hs i
    rw [Finset.weightedVSub_eq_linear_combination _ hw] at hs
    have hw' : w 0 + w 1 + w 2 = 0 := by
      simpa [Fin.sum_univ_succ, add_assoc] using hw
    have hx : w 0 * (v 0).1 + (w 1 * (v 1).1 + w 2 * (v 2).1) = 0 := by
      simpa [Fin.sum_univ_succ] using congrArg Prod.fst hs
    have hy : w 0 * (v 0).2 + (w 1 * (v 1).2 + w 2 * (v 2).2) = 0 := by
      simpa [Fin.sum_univ_succ] using congrArg Prod.snd hs
    have hx' : w 1 * ((v 1).1 - (v 0).1) + w 2 * ((v 2).1 - (v 0).1) = 0 := by
      linear_combination hx - (v 0).1 * hw'
    have hy' : w 1 * ((v 1).2 - (v 0).2) + w 2 * ((v 2).2 - (v 0).2) = 0 := by
      linear_combination hy - (v 0).2 * hw'
    have h1 : w 1 * P3381T1TriangleDeterminant v = 0 := by
      dsimp [P3381T1TriangleDeterminant]
      linear_combination ((v 2).2 - (v 0).2) * hx' - ((v 2).1 - (v 0).1) * hy'
    have h2 : w 2 * P3381T1TriangleDeterminant v = 0 := by
      dsimp [P3381T1TriangleDeterminant]
      linear_combination ((v 1).1 - (v 0).1) * hy' - ((v 1).2 - (v 0).2) * hx'
    have hw1 : w 1 = 0 := (mul_eq_zero.mp h1).resolve_right hv
    have hw2 : w 2 = 0 := (mul_eq_zero.mp h2).resolve_right hv
    have hw0 : w 0 = 0 := by linarith
    fin_cases i <;> assumption
  have hfin : (Set.range v).Finite := Set.finite_range v
  have hsfin : (v '' s).Finite := s.toFinite.image v
  have htfin : (v '' t).Finite := t.toFinite.image v
  have ha' : AffineIndependent Real ((↑) : hfin.toFinset → Real × Real) := by
    change AffineIndependent Real ((↑) : (↑hfin.toFinset : Set (Real × Real)) → Real × Real)
    rw [Set.Finite.coe_toFinset]
    exact ha.range
  have his : hsfin.toFinset ⊆ hfin.toFinset := by
    intro x hx
    exact hfin.mem_toFinset.mpr (Set.image_subset_range _ _ (hsfin.mem_toFinset.mp hx))
  have hit : htfin.toFinset ⊆ hfin.toFinset := by
    intro x hx
    exact hfin.mem_toFinset.mpr (Set.image_subset_range _ _ (htfin.mem_toFinset.mp hx))
  have h := ha'.convexHull_inter his hit
  simpa only [Finset.coe_inter, Set.Finite.coe_toFinset,
    ← Set.image_inter ha.injective] using h.symm

end ApollonianSuperharmonic

end
