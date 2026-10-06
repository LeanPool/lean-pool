/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEquationIntervalPressure
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEquationMildUniqueness
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEquationZeroForce

/-!
# Identification of an interval mild path

The same-velocity mild identity identifies the interval path with the
zero-force forced construction on that interval.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- A coordinate field satisfying the same-velocity mild identity has the
zero-force forced regularized curve as its spatial `L²` path. -/
theorem regularisedIntervalMildCurve_eq_forcedRegCurve
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a)
    (u : ParabolicPoint → Vec3) (T : ℝ) (hT : 0 < T)
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
          (regularisedIntervalMildCurve u T hT.le hSlice)) t) :
    ∀ t : ℝ, (ht : t ∈ Set.Icc 0 T) →
      regularisedIntervalMildCurve u T hT.le hSlice t =
        forcedRegCurve ρ ε hε ha CKN.isLocallySquareIntegrableForce_zero t := by
  intro t ht
  have hGlobal := regularizedMildIntervalField_slice_eq_global
    ρ ε hε a ha u T hT.le hSlice hL2Continuous hMild
  have hForced := forcedRegCurve_zero_eq_regularizedGlobalMildCurve ρ ε hε a ha t
  have hSlicePath : regularisedIntervalMildCurve u T hT.le hSlice t =
      realVectorL2OfCoordinateFunction
        (fun x : Vec3 => u (x, t)) (hSlice t ht) := by
    simp [regularisedIntervalMildCurve,
      regularizedMildTimeClamp_eq_of_mem T hT.le ht]
  rw [hSlicePath]
  exact (hGlobal t ht).trans hForced.symm

end CKN.Leray

end
