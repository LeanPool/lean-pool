/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.Ring

public import LeanPool.ApollonianSuperharmonic.P4994T6Rotation
public import LeanPool.ApollonianSuperharmonic.TriangularLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.TriangularSignedHeight

-- [TABLET NODE: P4994T6RotationLaws]

/-!
# P4994T6RotationLaws

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4994T6RotationLaws :
    (∀ n x y, TriangularLatticeAdjacent (P4994T6Rotation n x)
        (P4994T6Rotation n y) ↔ TriangularLatticeAdjacent x y) ∧
    (∀ n x y z, TriangularSignedHeight (P4994T6Rotation n x)
        (P4994T6Rotation n y) (P4994T6Rotation n z) =
      TriangularSignedHeight x y z) ∧
    (∀ p, P4994T6Rotation 6 p = p) ∧
    (∀ m n p, P4994T6Rotation (m + n) p =
      P4994T6Rotation n (P4994T6Rotation m p)) := by
-- BODY
  have step_adj (x y : Int × Int) :
      TriangularLatticeAdjacent (x.1 - x.2, x.1) (y.1 - y.2, y.1) ↔
        TriangularLatticeAdjacent x y := by
    rcases x with ⟨x₁, x₂⟩
    rcases y with ⟨y₁, y₂⟩
    simp only [TriangularLatticeAdjacent, Prod.mk_sub_mk, Prod.mk.injEq]
    omega
  have step_height (x y z : Int × Int) :
      TriangularSignedHeight (x.1 - x.2, x.1) (y.1 - y.2, y.1)
        (z.1 - z.2, z.1) = TriangularSignedHeight x y z := by
    simp only [TriangularSignedHeight]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    induction n with
    | zero => intro x y; rfl
    | succ n ih =>
        intro x y
        exact (step_adj (P4994T6Rotation n x) (P4994T6Rotation n y)).trans
          (ih x y)
  · intro n
    induction n with
    | zero => intro x y z; rfl
    | succ n ih =>
        intro x y z
        exact (step_height (P4994T6Rotation n x) (P4994T6Rotation n y)
          (P4994T6Rotation n z)).trans (ih x y z)
  · intro p
    ext <;> simp [P4994T6Rotation]
  · intro m n
    induction n with
    | zero => intro p; rfl
    | succ n ih =>
        intro p
        change ((P4994T6Rotation (m + n) p).1 -
          (P4994T6Rotation (m + n) p).2, (P4994T6Rotation (m + n) p).1) =
          ((P4994T6Rotation n (P4994T6Rotation m p)).1 -
            (P4994T6Rotation n (P4994T6Rotation m p)).2,
            (P4994T6Rotation n (P4994T6Rotation m p)).1)
        rw [ih]

end ApollonianSuperharmonic

end
