/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Topology.MetricSpace.Pseudo.Real

public import LeanPool.ApollonianSuperharmonic.P3381T1TriangleDeterminant
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Topology.Algebra.Ring.Real

-- [TABLET NODE: P3381T1AffineTriangleMap]

/-!
# P3381T1AffineTriangleMap

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3381T1AffineTriangleMap (p q : Fin 3 → Real × Real)
    (hp : P3381T1TriangleDeterminant p ≠ 0)
    (hq : P3381T1TriangleDeterminant q ≠ 0) :
    ∃ h : (Real × Real) ≃ₜ (Real × Real),
      ∀ w : Fin 3 → Real, (∑ i, w i) = 1 →
        h (∑ i, w i • p i) = ∑ i, w i • q i := by
-- BODY
  let place (v : Fin 3 → Real × Real) (x : Real × Real) : Real × Real :=
    ((v 0).1 + x.1 * ((v 1).1 - (v 0).1) + x.2 * ((v 2).1 - (v 0).1),
    (v 0).2 + x.1 * ((v 1).2 - (v 0).2) + x.2 * ((v 2).2 - (v 0).2))
  let coord (v : Fin 3 → Real × Real) (x : Real × Real) : Real × Real :=
    (((x.1 - (v 0).1) * ((v 2).2 - (v 0).2) -
      ((v 2).1 - (v 0).1) * (x.2 - (v 0).2)) / P3381T1TriangleDeterminant v,
    (((v 1).1 - (v 0).1) * (x.2 - (v 0).2) -
      (x.1 - (v 0).1) * ((v 1).2 - (v 0).2)) / P3381T1TriangleDeterminant v)
  have hplace (v : Fin 3 → Real × Real)
      (hv : P3381T1TriangleDeterminant v ≠ 0) (x : Real × Real) :
      place v (coord v x) = x := by
    apply Prod.ext <;>
      dsimp [place, coord] <;>
      field_simp <;>
      simp only [P3381T1TriangleDeterminant, Prod.fst_sub, Prod.snd_sub] <;> ring
  have hcoord (v : Fin 3 → Real × Real)
      (hv : P3381T1TriangleDeterminant v ≠ 0) (x : Real × Real) :
      coord v (place v x) = x := by
    apply Prod.ext <;>
      dsimp [place, coord] <;>
      field_simp <;>
      simp only [P3381T1TriangleDeterminant, Prod.fst_sub, Prod.snd_sub] <;> ring
  let h : (Real × Real) ≃ₜ (Real × Real) :=
    { toFun := fun x => place q (coord p x)
      invFun := fun x => place p (coord q x)
      left_inv := fun x => by
        change place p (coord q (place q (coord p x))) = x
        rw [hcoord q hq, hplace p hp]
      right_inv := fun x => by
        change place q (coord p (place p (coord q x))) = x
        rw [hcoord p hp, hplace q hq]
      continuous_toFun := by dsimp [place, coord]; fun_prop
      continuous_invFun := by dsimp [place, coord]; fun_prop }
  refine ⟨h, ?_⟩
  intro w hw
  have hw0 : w 0 = 1 - w 1 - w 2 := by
    simp only [Fin.sum_univ_three] at hw
    linarith
  apply Prod.ext <;>
    simp only [h, Fin.sum_univ_three,
      Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    dsimp [place, coord] <;>
    rw [hw0] <;>
    field_simp <;>
    simp only [P3381T1TriangleDeterminant, Prod.fst_sub, Prod.snd_sub] <;> ring

end ApollonianSuperharmonic

end
