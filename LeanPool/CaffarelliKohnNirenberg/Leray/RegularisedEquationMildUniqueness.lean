/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedGlobalMild
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedMildInitialData
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildLocalSolution
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildLocalMap
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildLocalParameters
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierCoordinateL2Bridge
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet

/-!
# Uniqueness for the interval regularized mild identity

An interval mild path with the prescribed mollified initial state agrees
with the zero-force global mild curve on that interval.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

private theorem regularizedMildTrajectory_forcedEquation
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2) (T : ℝ) (hT : 0 ≤ T)
    (U : C(RegularizedMildTimeInterval T, RealVectorL2))
    (hU : IsRegularizedMildTrajectory ρ ε hε b T U) :
    ∀ t : RegularizedMildTimeInterval T,
      U t = forcedMildRHS b (fun _ => 0)
        (regularizedMildClampedTensorTrajectory ρ ε hε T hT U) t.1 t.2.1 := by
  intro t
  rw [hU t]
  simp only [forcedMildRHS, forcedForceDuhamel_zero, add_zero,
    regularizedMildRightHandSide]
  congr 1
  apply regularizedMildStokesIntegral_congr_Icc
  intro s hs
  have hsT : s ∈ RegularizedMildTimeInterval T :=
    ⟨hs.1, hs.2.trans t.2.2⟩
  simp only [regularizedMildClampedTensorTrajectory, dite_eq_left hsT,
    regularizedMildTimeClamp_eq_of_mem T hT hsT]

/-- Uniqueness identifies a same-velocity mild path on a closed finite
interval with the global zero-force regularized curve. -/
theorem regularizedMildIntervalPath_eq_global
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2) (hb : RegularizedMildJData b)
    (T : ℝ) (hT : 0 ≤ T)
    (U : C(RegularizedMildTimeInterval T, RealVectorL2))
    (hU : IsRegularizedMildTrajectory ρ ε hε b T U) :
    ∀ t : RegularizedMildTimeInterval T,
      U t = regularizedGlobalMildCurve ρ ε hε b hb t.1 := by
  let V : C(RegularizedMildTimeInterval T, RealVectorL2) :=
    ⟨fun t => regularizedGlobalMildCurve ρ ε hε b hb t.1,
      (regularizedGlobalMildCurve_continuous ρ ε hε b hb).comp
        continuous_subtype_val⟩
  have hV : IsRegularizedMildTrajectory ρ ε hε b T V := by
    exact regularizedGlobalMildCurve_isTrajectory ρ ε hε b hb T
  have hUnique := forcedMildSolution_unique ρ ε hε b stronglyMeasurable_const
    (fun S => by simp) T hT U V
    (regularizedMildTrajectory_forcedEquation ρ ε hε b T hT U hU)
    (regularizedMildTrajectory_forcedEquation ρ ε hε b T hT V hV)
  intro t
  have hEq := congrArg (fun W : C(RegularizedMildTimeInterval T, RealVectorL2) => W t)
    hUnique
  exact hEq

/-- The L² path encoded by a coordinate field with the local mild identity
is the restriction of the global zero-force mild curve. -/
theorem regularizedMildIntervalField_slice_eq_global
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a)
    (u : ParabolicPoint → Vec3) (T : ℝ) (hT : 0 ≤ T)
    (hSlice : ∀ t : ℝ, t ∈ Set.Icc 0 T →
      MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hL2Continuous : Continuous (fun t : Set.Icc (0 : ℝ) T =>
      realVectorL2OfCoordinateFunction
        (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2)))
    (hMild : ∀ t : ℝ, (ht : t ∈ Set.Icc 0 T) →
      realVectorL2OfCoordinateFunction
        (fun x : Vec3 => u (x, t)) (hSlice t ht) =
      realHeatOperator t ht.1
        (realVectorL2OfCoordinateFunction
          (regUniformMollifiedInitial ρ ε hε a)
          (regMollifiedInitial_isInJ ρ ε hε ha).1) -
      regularizedMildStokesIntegral
        (regularizedMildTensorTrajectory ρ ε hε
          (fun s => realVectorL2OfCoordinateFunction
            (fun x : Vec3 => u
              (x, (regularizedMildTimeClamp T hT s : Set.Icc 0 T).1))
            (hSlice
              (regularizedMildTimeClamp T hT s : Set.Icc 0 T).1
              (regularizedMildTimeClamp T hT s : Set.Icc 0 T).2))) t) :
    ∀ t : ℝ, (ht : t ∈ Set.Icc 0 T) →
      realVectorL2OfCoordinateFunction
        (fun x : Vec3 => u (x, t)) (hSlice t ht) =
        regularizedGlobalMildCurve ρ ε hε
          (realVectorL2OfCoordinateFunction
            (regUniformMollifiedInitial ρ ε hε a)
            (regMollifiedInitial_isInJ ρ ε hε ha).1)
          (regUniformMollifiedInitial_mildJData ρ ε hε ha) t := by
  let b : RealVectorL2 := realVectorL2OfCoordinateFunction
    (regUniformMollifiedInitial ρ ε hε a)
    (regMollifiedInitial_isInJ ρ ε hε ha).1
  let hb : RegularizedMildJData b := regUniformMollifiedInitial_mildJData ρ ε hε ha
  let U : C(RegularizedMildTimeInterval T, RealVectorL2) :=
    ⟨fun t => realVectorL2OfCoordinateFunction
        (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2), hL2Continuous⟩
  have hTrajectory : IsRegularizedMildTrajectory ρ ε hε b T U := by
    intro t
    change realVectorL2OfCoordinateFunction
        (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2) =
      regularizedMildRightHandSide b
        (fun s => if hs : s ∈ RegularizedMildTimeInterval T then
          regularizedMildTensor ρ ε hε (U ⟨s, hs⟩) else 0) t.1 t.2.1
    rw [hMild t.1 t.2]
    unfold regularizedMildRightHandSide
    congr 1
    apply regularizedMildStokesIntegral_congr_Icc
    intro s hs
    have hsT : s ∈ RegularizedMildTimeInterval T :=
      ⟨hs.1, hs.2.trans t.2.2⟩
    simp only [regularizedMildTensorTrajectory, dite_eq_left hsT]
    rw [regularizedMildTimeClamp_eq_of_mem T hT hsT]
    rfl
  have hEq := regularizedMildIntervalPath_eq_global ρ ε hε b hb T hT U hTrajectory
  intro t ht
  exact hEq ⟨t, ht⟩

end CKN.Leray

end
