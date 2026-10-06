/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMollifierGeneral

/-!
# The regularized mild equation

The heat evolution and the time-integrated Leray-Stokes term in
`eq:reg-mild`, with values in the real spatial `L²` carriers.
-/

public section

open MeasureTheory

noncomputable section

namespace CKN.Leray

/-- The Stokes integrand in the mild equation, set to zero at its integrable
endpoint `s = t`. -/
@[expose]
def regularizedMildStokesIntegrand (F : ℝ → RealTensorL2) (t s : ℝ) :
    RealVectorL2 :=
  if hs : s < t then realStokesOperator (sub_pos.mpr hs) (F s) else 0

/-- The Bochner integral in the mild equation, as an element of real spatial
`L²`. -/
@[expose]
def regularizedMildStokesIntegral (F : ℝ → RealTensorL2) (t : ℝ) :
    RealVectorL2 :=
  ∫ s in Set.Icc 0 t, regularizedMildStokesIntegrand F t s

/-- The right hand side of `eq:reg-mild` for a given initial field and tensor
trajectory. -/
@[expose]
def regularizedMildRightHandSide (b : RealVectorL2)
    (F : ℝ → RealTensorL2) (t : ℝ) (ht : 0 ≤ t) : RealVectorL2 :=
  realHeatOperator t ht b - regularizedMildStokesIntegral F t

/-- A velocity and tensor trajectory satisfy the real `L²` mild equation
`eq:reg-mild`. -/
@[expose]
def SatisfiesRegularizedMildEquation (b : RealVectorL2)
    (u : ℝ → RealVectorL2) (F : ℝ → RealTensorL2) : Prop :=
  ∀ t (ht : 0 ≤ t), u t = regularizedMildRightHandSide b F t ht

end CKN.Leray

end
