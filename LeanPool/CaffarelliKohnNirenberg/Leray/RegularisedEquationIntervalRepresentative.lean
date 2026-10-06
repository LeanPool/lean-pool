/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEquationMildIdentification
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierCoordinateL2Bridge
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedConstruction

/-!
# Coordinate representatives of the interval mild path

The interval mild identity identifies each positive-time coordinate slice
almost everywhere with the representative of its zero-force construction.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The coordinate velocity of an interval mild path agrees almost everywhere
on each slice with the representative of its forced zero-force curve. -/
theorem regularisedInterval_velocity_ae_eq_forcedRegRep
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
      (fun x : Vec3 => u (x, t)) =ᵐ[volume]
        (fun x : Vec3 => forcedRegRep ρ ε hε ha
          CKN.isLocallySquareIntegrableForce_zero (x, t)) := by
  intro t ht
  have hpath := regularisedIntervalMildCurve_eq_forcedRegCurve
    ρ ε hε a ha u T hT hSlice hL2Continuous hMild t ht
  have hUcurve : realVectorL2OfCoordinateFunction
      (fun x : Vec3 => u (x, t)) (hSlice t ht) =
      regularisedIntervalMildCurve u T hT.le hSlice t := by
    simp [regularisedIntervalMildCurve,
      regularizedMildTimeClamp_eq_of_mem T hT.le ht]
  have hclass := hUcurve.trans hpath |>.trans
    (forcedRegRep_class ρ ε hε ha CKN.isLocallySquareIntegrableForce_zero t).symm
  have hrep := congrArg realVectorL2Representative hclass
  have huRep := realVectorL2OfCoordinateFunction_rep
    (fun x : Vec3 => u (x, t)) (hSlice t ht)
  have hvRep := realVectorL2OfCoordinateFunction_rep
    (fun x : Vec3 => forcedRegRep ρ ε hε ha
      CKN.isLocallySquareIntegrableForce_zero (x, t))
    (forcedRegRep_memLp ρ ε hε ha CKN.isLocallySquareIntegrableForce_zero t)
  filter_upwards [huRep, hvRep] with x hxU hxV
  calc
    u (x, t) = realVectorL2Representative
        (realVectorL2OfCoordinateFunction (fun y : Vec3 => u (y, t))
          (hSlice t ht)) x := hxU.symm
    _ = realVectorL2Representative
        (realVectorL2OfCoordinateFunction
          (fun y : Vec3 => forcedRegRep ρ ε hε ha
            CKN.isLocallySquareIntegrableForce_zero (y, t))
          (forcedRegRep_memLp ρ ε hε ha CKN.isLocallySquareIntegrableForce_zero t)) x :=
      congrFun hrep x
    _ = forcedRegRep ρ ε hε ha CKN.isLocallySquareIntegrableForce_zero (x, t) := hxV

end CKN.Leray

end
