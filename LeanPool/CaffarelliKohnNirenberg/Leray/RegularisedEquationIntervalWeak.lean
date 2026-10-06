/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalTimeWeak

/-!
# The weak momentum identity on a finite mild interval

The zero-force regularized momentum identity transfers to a coordinate
velocity satisfying the same mild equation on a finite interval.
-/

public section

open MeasureTheory Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

abbrev regularisedEquationIntervalWeakParabolicTopology :
    TopologicalSpace ParabolicPoint := inferInstance

local instance regularisedIntervalWeakNormedAddCommGroup :
    NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

local instance regularisedIntervalWeakNormedSpace : NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))

/-- A same-velocity mild path satisfies the forced weak momentum identity on
its finite regularity interval. -/
theorem regularisedInterval_weakMomentum
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
          (regularisedIntervalMildCurve u T hT.le hSlice)) t)
    (hUcontinuous : letI : TopologicalSpace ParabolicPoint :=
      regularisedEquationIntervalWeakParabolicTopology
      ∀ i : Fin 3, ContinuousOn (fun z => u z i)
        (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hDcontinuous : letI : TopologicalSpace ParabolicPoint :=
      regularisedEquationIntervalWeakParabolicTopology
      ∀ i j : Fin 3, ContinuousOn
        (fun z => spatialPartial (fun y => u y i) j z)
        (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hPcontinuous : letI : TopologicalSpace ParabolicPoint :=
      regularisedEquationIntervalWeakParabolicTopology
      ContinuousOn
      (regularisedIntervalCanonicalPressure ρ ε hε u T hT.le hSlice)
      (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hUjoint : letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
      letI : NormedAddCommGroup ParabolicPoint :=
        inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
      letI : NormedSpace ℝ ParabolicPoint :=
        inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
      ∀ i : Fin 3, ContDiffOn ℝ 1 (fun z => u z i)
        (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (φ : ParabolicPoint → Vec3)
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3)
      (Set.univ : Set Vec3) (Set.Ioo 0 T)) :
    ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Set.Ioo 0 T),
      (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
        - ∑ i : Fin 3, ∑ j : Fin 3,
          regUniformMollifiedVelocity ρ ε hε u z j * u z i *
            spatialPartial (fun y => φ y i) j z
        + ∑ i : Fin 3, ∑ j : Fin 3,
          spatialPartial (fun y => u y i) j z *
            spatialPartial (fun y => φ y i) j z
        - regularisedIntervalCanonicalPressure ρ ε hε u T hT.le hSlice z *
          (∑ i : Fin 3, spatialPartial (fun y => φ y i) i z)) = 0 := by
  have hUspatial (t : ℝ) (ht : t ∈ Set.Ioc 0 T) (i : Fin 3) :
      ContDiff ℝ 1 (fun x : Vec3 => u (x, t) i) := by
    rw [← contDiffOn_univ]
    exact (hUjoint i).comp (contDiff_prodMk_left t).contDiffOn
      (fun x _ => ⟨Set.mem_univ _, ht⟩)
  exact regularisedR12_weakMomentum_spatial ρ ε hε a ha u T hT
    hSlice hL2Continuous hMild hUcontinuous hDcontinuous hPcontinuous hUspatial φ hφ

end CKN.Leray

end
