/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4715T1Hexagon
public import Mathlib.Analysis.Convex.Combination

-- [TABLET NODE: P4780T1HullHalfspaces]

/-!
# P4780T1HullHalfspaces

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4780T1HullHalfspaces :
    P4715T1Hexagon = {p : Real × Real |
      -2 ≤ 2 * p.1 - p.2 ∧ 2 * p.1 - p.2 ≤ 0 ∧
      -1 ≤ p.1 - 2 * p.2 ∧ p.1 - 2 * p.2 ≤ 1 ∧
      -2 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ 0} := by
-- BODY
  let V := Set.range (P4715T1Position ∘ P4715T1BoundaryCycle)
  apply Set.Subset.antisymm
  · unfold P4715T1Hexagon
    apply convexHull_min
    · rintro p ⟨j, rfl⟩
      fin_cases j <;>
        norm_num [P4715T1Position, P4715T1BoundaryCycle, P4715T1Offsets]
    · have l1 : IsLinearMap Real (fun p : Real × Real => 2 * p.1 - p.2) := by
        constructor <;> intros <;> simp <;> ring
      have l2 : IsLinearMap Real (fun p : Real × Real => p.1 - 2 * p.2) := by
        constructor <;> intros <;> simp <;> ring
      have l3 : IsLinearMap Real (fun p : Real × Real => p.1 + p.2) := by
        constructor <;> intros <;> simp <;> ring
      have c1 := convex_halfSpace_ge l1 (-2)
      have c2 := convex_halfSpace_le l1 0
      have c3 := convex_halfSpace_ge l2 (-1)
      have c4 := convex_halfSpace_le l2 1
      have c5 := convex_halfSpace_ge l3 (-2)
      have c6 := convex_halfSpace_le l3 0
      simpa only [Set.ofPred_and, Set.inter_assoc] using
        (((((c1.inter c2).inter c3).inter c4).inter c5).inter c6)
  · intro p hq
    rcases hq with ⟨hxlo, hxhi, hylo, hyhi, hzlo, hzhi⟩
    have htri (a b c : Real × Real) (u v w : Real)
        (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hsum : u + v + w = 1)
        (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V)
        (hp : u • a + v • b + w • c = p) : p ∈ P4715T1Hexagon := by
      let ww : Fin 3 → Real := ![u, v, w]
      let zz : Fin 3 → Real × Real := ![a, b, c]
      apply mem_convexHull_of_exists_fintype (w := ww) (z := zz)
      · intro i
        fin_cases i <;> simp? [ww] <;> assumption
      · simp [ww, Fin.sum_univ_succ]
        linarith
      · intro i
        fin_cases i <;> simp? [zz] <;> assumption
      · simpa [ww, zz, Fin.sum_univ_succ, add_assoc] using hp
    have hv0 : (0, 0) ∈ V := by
      exact ⟨0, by norm_num [P4715T1Position, P4715T1BoundaryCycle, P4715T1Offsets]⟩
    have hv1 : (-1/3, -2/3) ∈ V := by
      exact ⟨1, by norm_num [P4715T1Position, P4715T1BoundaryCycle, P4715T1Offsets]⟩
    have hv2 : (-1, -1) ∈ V := by
      exact ⟨2, by simp [P4715T1Position, P4715T1BoundaryCycle,
        P4715T1Offsets]⟩
    have hv3 : (-4/3, -2/3) ∈ V := by
      exact ⟨3, by simp [P4715T1Position, P4715T1BoundaryCycle,
        P4715T1Offsets]; norm_num⟩
    have hv4 : (-1, 0) ∈ V := by
      exact ⟨4, by simp [P4715T1Position, P4715T1BoundaryCycle,
        P4715T1Offsets]⟩
    have hv5 : (-1/3, 1/3) ∈ V := by
      exact ⟨5, by simp [P4715T1Position, P4715T1BoundaryCycle,
        P4715T1Offsets]; norm_num⟩
    by_cases hA : p.2 ≤ p.1
    · apply htri (0, 0) (-1/3, -2/3) (-1, -1)
          (1 - (p.1 - 2 * p.2)) (3 * (p.1 - p.2)) (-(2 * p.1 - p.2))
      · linarith
      · linarith
      · linarith
      · ring
      · exact hv0
      · exact hv1
      · exact hv2
      · ext <;> simp <;> ring
    · by_cases hB : p.1 ≤ -1
      · apply htri (-1, -1) (-4/3, -2/3) (-1, 0)
            (2 * p.1 - p.2 + 2) (-3 * (p.1 + 1)) (p.1 + p.2 + 2)
        · linarith
        · linarith
        · linarith
        · ring
        · exact hv2
        · exact hv3
        · exact hv4
        · ext <;> simp <;> ring
      · by_cases hC : 0 ≤ p.2
        · apply htri (-1, 0) (-1/3, 1/3) (0, 0)
              (-p.1 - p.2) (3 * p.2) (1 + p.1 - 2 * p.2)
          · linarith
          · linarith
          · linarith
          · ring
          · exact hv4
          · exact hv5
          · exact hv0
          · ext <;> simp <;> ring
        · apply htri (0, 0) (-1, -1) (-1, 0)
              (1 + p.1) (-p.2) (p.2 - p.1)
          · linarith
          · linarith
          · linarith
          · ring
          · exact hv0
          · exact hv2
          · exact hv4
          · ext <;> simp

end ApollonianSuperharmonic

end
