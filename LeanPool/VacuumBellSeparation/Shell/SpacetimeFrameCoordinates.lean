/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.LorentzFrameMap

/-!
# Actual time-first finite coordinates for the original spacetime frame

The Euclidean four-norm is the actual WithLp 2 norm used by root.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation

open Matrix

/-- Time, then the three spatial components, on the original carrier. -/
def spacetimeFrameCoordinates : Spacetime ≃ₗ[ℝ] (Fin 4 → ℝ) where
  toFun x := Fin.cons x.1 (WithLp.ofLp x.2)
  invFun a := (a 0, WithLp.toLp 2 (Fin.tail a))
  left_inv x := by apply Prod.ext <;> rfl
  right_inv a := Fin.cons_self_tail a
  map_add' x y := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  map_smul' a x := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

@[simp] theorem spacetimeFrameCoordinates_zero (x : Spacetime) :
    spacetimeFrameCoordinates x 0 = x.1 := rfl

@[simp] theorem spacetimeFrameCoordinates_succ (x : Spacetime) (i : Fin 3) :
    spacetimeFrameCoordinates x i.succ = x.2 i := rfl

@[simp] theorem spacetimeFrameCoordinates_one (x : Spacetime) :
    spacetimeFrameCoordinates x 1 = x.2 0 := spacetimeFrameCoordinates_succ x 0

@[simp] theorem spacetimeFrameCoordinates_two (x : Spacetime) :
    spacetimeFrameCoordinates x 2 = x.2 1 := spacetimeFrameCoordinates_succ x 1

@[simp] theorem spacetimeFrameCoordinates_three (x : Spacetime) :
    spacetimeFrameCoordinates x 3 = x.2 2 := spacetimeFrameCoordinates_succ x 2

/-- The literal time-first standard basis transported to the physical carrier. -/
def spacetimeFrameBasis : Module.Basis (Fin 4) ℝ Spacetime :=
  (Pi.basisFun ℝ (Fin 4)).map spacetimeFrameCoordinates.symm

@[simp] theorem spacetimeFrameBasis_repr (x : Spacetime) (i : Fin 4) :
    spacetimeFrameBasis.repr x i = spacetimeFrameCoordinates x i := by
  change (Pi.basisFun ℝ (Fin 4)).repr (spacetimeFrameCoordinates x) i = _
  exact Pi.basisFun_repr _ _ _ _

@[simp] theorem spacetimeFrameBasis_zero : spacetimeFrameBasis 0 = (1, 0) := by
  apply spacetimeFrameCoordinates.injective
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [spacetimeFrameBasis, Pi.basisFun_apply, spacetimeFrameCoordinates,
      Fin.tail]

@[simp] theorem spacetimeFrameBasis_succ (j : Fin 3) :
    spacetimeFrameBasis j.succ = spacetimeAxis j := by
  apply spacetimeFrameCoordinates.injective
  ext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [spacetimeFrameBasis, Pi.basisFun_apply, spacetimeFrameCoordinates, spacetimeAxis]
  · simp [spacetimeFrameBasis, Pi.basisFun_apply, spacetimeFrameCoordinates, spacetimeAxis,
      Fin.tail, Pi.single_apply]

@[simp] theorem spacetimeFrameBasis_one :
    spacetimeFrameBasis 1 = spacetimeAxis 0 := spacetimeFrameBasis_succ 0

@[simp] theorem spacetimeFrameBasis_two :
    spacetimeFrameBasis 2 = spacetimeAxis 1 := spacetimeFrameBasis_succ 1

@[simp] theorem spacetimeFrameBasis_three :
    spacetimeFrameBasis 3 = spacetimeAxis 2 := spacetimeFrameBasis_succ 2

/-- Spacetime column matrix given by `fun i j => spacetimeFrameCoordinates (![w, e, f, n] j) i`. -/
def spacetimeColumnMatrix (w e f n : Spacetime) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => spacetimeFrameCoordinates (![w, e, f, n] j) i

theorem spacetimeColumnMatrix_col_zero (w e f n : Spacetime) :
    (fun i => spacetimeColumnMatrix w e f n i 0) = spacetimeFrameCoordinates w := rfl

theorem spacetimeColumnMatrix_col_one (w e f n : Spacetime) :
    (fun i => spacetimeColumnMatrix w e f n i 1) = spacetimeFrameCoordinates e := rfl

theorem spacetimeColumnMatrix_col_two (w e f n : Spacetime) :
    (fun i => spacetimeColumnMatrix w e f n i 2) = spacetimeFrameCoordinates f := rfl

theorem spacetimeColumnMatrix_col_three (w e f n : Spacetime) :
    (fun i => spacetimeColumnMatrix w e f n i 3) = spacetimeFrameCoordinates n := rfl

theorem lorentzFrameLinear_toMatrix (e f : Spacetime) :
    LinearMap.toMatrix spacetimeFrameBasis spacetimeFrameBasis (lorentzFrameLinear e f) =
      spacetimeColumnMatrix (lorentzFrameFuture e f) e f (lorentzFrameNormal e f) := by
  ext i j
  rw [LinearMap.toMatrix_apply, spacetimeFrameBasis_repr]
  fin_cases j
  · change spacetimeFrameCoordinates (lorentzFrameLinear e f (spacetimeFrameBasis 0)) i =
      spacetimeFrameCoordinates (lorentzFrameFuture e f) i
    rw [spacetimeFrameBasis_zero, lorentzFrameLinear_time]
  · change spacetimeFrameCoordinates
      (lorentzFrameLinear e f (spacetimeFrameBasis (0 : Fin 3).succ)) i =
      spacetimeFrameCoordinates e i
    rw [spacetimeFrameBasis_succ, lorentzFrameLinear_first]
  · change spacetimeFrameCoordinates
      (lorentzFrameLinear e f (spacetimeFrameBasis (1 : Fin 3).succ)) i =
      spacetimeFrameCoordinates f i
    rw [spacetimeFrameBasis_succ, lorentzFrameLinear_second]
  · change spacetimeFrameCoordinates
      (lorentzFrameLinear e f (spacetimeFrameBasis (2 : Fin 3).succ)) i =
      spacetimeFrameCoordinates (lorentzFrameNormal e f) i
    rw [spacetimeFrameBasis_succ, lorentzFrameLinear_third]

end VacuumBellSeparation
