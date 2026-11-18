/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import LeanPool.ApollonianSuperharmonic.P3650T1ExposedCorner

/-!
# Affine basis at an exposed polygon corner

Adapted from Wesley Pegden's Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/-- The three vertices at an exposed corner form the height-coordinate affine basis. -/
theorem ExposedCornerAffineBasis :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (E : P3650T1ExposedCorner p), ∃ A :
            AffineBasis (Fin 3) Real (Real × Real), (∀ i, A i = ![p.vertex (E.b - 1), p.vertex
            E.b, p.vertex (E.b + 1)] i) ∧ E.height = A.coord 1 ) := by
  classical
  intro n p E
  let a := p.vertex (E.b - 1)
  let b := p.vertex E.b
  let c := p.vertex (E.b + 1)
  let v : Fin 3 → Real × Real := ![a, b, c]
  have hdet : (b.1 - a.1) * (c.2 - a.2) -
      (c.1 - a.1) * (b.2 - a.2) ≠ 0 := by
    simpa [P3381T1TriangleDeterminant, a, b, c] using E.nondegenerate
  have hind : AffineIndependent Real v := by
    apply (affineIndependent_iff_of_fintype Real v).mpr
    intro z hz hsum i
    rw [Finset.weightedVSub_eq_linear_combination Finset.univ hz] at hsum
    have hz' : z 0 + z 1 + z 2 = 0 := by
      simpa [Fin.sum_univ_succ, ← add_assoc] using hz
    have hx : z 0 * a.1 + z 1 * b.1 + z 2 * c.1 = 0 := by
      simpa [Fin.sum_univ_succ, v, ← add_assoc] using congrArg Prod.fst hsum
    have hy : z 0 * a.2 + z 1 * b.2 + z 2 * c.2 = 0 := by
      simpa [Fin.sum_univ_succ, v, ← add_assoc] using congrArg Prod.snd hsum
    have hx' : z 1 * (b.1 - a.1) + z 2 * (c.1 - a.1) = 0 := by
      linear_combination hx - a.1 * hz'
    have hy' : z 1 * (b.2 - a.2) + z 2 * (c.2 - a.2) = 0 := by
      linear_combination hy - a.2 * hz'
    have hz1 : z 1 = 0 := by
      apply (mul_eq_zero.mp (show z 1 * ((b.1 - a.1) * (c.2 - a.2) -
          (c.1 - a.1) * (b.2 - a.2)) = 0 by
        linear_combination (c.2 - a.2) * hx' - (c.1 - a.1) * hy')).resolve_right hdet
    have hz2 : z 2 = 0 := by
      apply (mul_eq_zero.mp (show z 2 * ((b.1 - a.1) * (c.2 - a.2) -
          (c.1 - a.1) * (b.2 - a.2)) = 0 by
        linear_combination (b.1 - a.1) * hy' - (b.2 - a.2) * hx')).resolve_right hdet
    fin_cases i <;> simp_all
  have hspan : affineSpan Real (Set.range v) = ⊤ := by
    apply hind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
    simp [Module.finrank_prod]
  let A : AffineBasis (Fin 3) Real (Real × Real) := ⟨v, hind, hspan⟩
  refine ⟨A, fun _ => rfl, ?_⟩
  apply AffineMap.ext_on A.tot
  rintro x ⟨i, rfl⟩
  fin_cases i <;> simp only [AffineBasis.coord_apply]
  · exact E.height_prev
  · exact E.height_top
  · exact E.height_next

end ApollonianSuperharmonic

end
