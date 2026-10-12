/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import LeanPool.LiebThirring.Electrostatics.SlicingExceptional
import LeanPool.LiebThirring.Electrostatics.FaceMeasureGeometry
import LeanPool.LiebThirring.Electrostatics.ShellAssemblyGeometry

/-!
# Coordinate lines and finite crossing times

Each tie on a nonexceptional coordinate line has an explicit transverse crossing time.
-/

public section

open Set

namespace LiebThirring

/-- Insert the coordinate along which the line is sliced. -/
@[expose] def coordinateLine (a : Fin 3) (q : Planar) (t : ℝ) : Position :=
  WithLp.toLp 2 (a.insertNth t (fun i => q i))

@[simp] theorem coordinateLine_apply_same (a : Fin 3) (q : Planar) (t : ℝ) :
    coordinateLine a q t a = t :=
by
  dsimp only [coordinateLine]
  exact Fin.insertNth_apply_same (α := fun _ => ℝ) a _ _

@[simp] theorem coordinateLine_apply_succAbove (a : Fin 3) (q : Planar) (t : ℝ)
    (i : Fin 2) : coordinateLine a q t (a.succAbove i) = q i :=
by
  dsimp only [coordinateLine]
  exact Fin.insertNth_apply_succAbove (α := fun _ => ℝ) a _ _ i

@[simp] theorem planeProjection_coordinateLine (a : Fin 3) (q : Planar) (t : ℝ) :
    planeProjection a (coordinateLine a q t) = q := by
  ext i
  exact coordinateLine_apply_succAbove a q t i

theorem coordinateLine_eq_affine (a : Fin 3) (q : Planar) (t : ℝ) :
    coordinateLine a q t = coordinateLine a q 0 + t • coordinateLine a 0 1 := by
  ext i
  revert i
  rw [a.forall_iff_succAbove]
  constructor
  · simp
  · intro j
    simp

theorem contDiff_coordinateLine (a : Fin 3) (q : Planar) (n : WithTop ℕ∞) :
    ContDiff ℝ n (coordinateLine a q) := by
  have he : coordinateLine a q =
      (fun t : ℝ => coordinateLine a q 0 + t • coordinateLine a 0 1) :=
    funext (coordinateLine_eq_affine a q)
  rw [he]
  exact contDiff_const.add (contDiff_id.smul contDiff_const)

end LiebThirring

end
