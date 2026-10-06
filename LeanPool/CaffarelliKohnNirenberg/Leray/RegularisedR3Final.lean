/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR3FinalCore

/-!
# (R3) of `thm:regularised` on a finite interval

The statement of `CKN.Leray.regularisedR3Final_core` with every continuity
hypothesis for the product topology on space-time, which is the parabolic
topology.
-/

public section

open MeasureTheory Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- A continuous function for the product topology is continuous for the
parabolic metric topology, which is the same topology. -/
private theorem regularisedR3Final_continuousOn_of_prod
    {f : ParabolicPoint → ℝ} {S : Set ParabolicPoint}
    (h : @ContinuousOn ParabolicPoint ℝ instTopologicalSpaceProd _ f S) :
    ContinuousOn f S := by
  have h' : ContinuousOn (fun z : Vec3 × ℝ => f z) S := h
  exact h'.comp parabolicHomeomorph.continuous.continuousOn (fun _ hz => hz)

section

local instance regularisedR3FinalNormedAddCommGroup :
    NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

local instance regularisedR3FinalNormedSpace : NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))

local instance (priority := 10000) regularisedR3FinalTopology :
    TopologicalSpace ParabolicPoint :=
  instTopologicalSpaceProd

/-- (R3) of `thm:regularised` on a finite interval: the same-velocity mild
identity `eq:reg-mild` on `[0, T]` and the classical regularity on `(0, T]`
give the regularized momentum equation in divergence and transport form on
`(0, T)`, and the pressure is the canonical Riesz pressure of each slice
(R4). -/
theorem regularised_R3_on_interval
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a)
    (u : ParabolicPoint → Vec3) (T : ℝ) (hT : 0 < T)
    (hSlice : ∀ t : ℝ, t ∈ Set.Icc 0 T →
      MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hL2Continuous : Continuous (fun t : Set.Icc (0 : ℝ) T =>
      realVectorL2OfCoordinateFunction
        (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2)))
    (hDivFree : ∀ t : ℝ, t ∈ Set.Icc 0 T →
      CKN.IsWeakDivFreeL2 (fun x : Vec3 => u (x, t)))
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
    (hUcontinuous : ∀ i : Fin 3, ContinuousOn (fun z => u z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hDcontinuous : ∀ i j : Fin 3, ContinuousOn
      (fun z => spatialPartial (fun y => u y i) j z)
      (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hDDcontinuous : ∀ i j k : Fin 3, ContinuousOn
      (fun z => spatialPartial
        (fun y => spatialPartial (fun x => u x i) j y) k z)
      (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hDtcontinuous : ∀ i : Fin 3, ContinuousOn
      (fun z => timePartial (fun y => u y i) z)
      (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hPcontinuous : ContinuousOn
      (regularisedIntervalCanonicalPressure ρ ε hε u T hT.le hSlice)
      (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hDpcontinuous : ∀ i : Fin 3, ContinuousOn
      (fun z => spatialPartial
        (fun y => regularisedIntervalCanonicalPressure ρ ε hε u T hT.le hSlice y)
        i z)
      (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hUjoint : ∀ i : Fin 3, ContDiffOn ℝ 1 (fun z => u z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hDdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T),
      ∀ i j : Fin 3, DifferentiableAt ℝ
        (fun x : Vec3 => spatialPartial (fun y => u y i) j (x, z.2)) z.1)
    (hPdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T),
      DifferentiableAt ℝ
        (fun x : Vec3 => regularisedIntervalCanonicalPressure
          ρ ε hε u T hT.le hSlice (x, z.2)) z.1) :
    (∀ z : ParabolicPoint,
      z ∈ spaceTimeSet (Set.univ : Set Vec3) (Set.Ioo 0 T) →
      ∀ i : Fin 3,
        timePartial (fun y => u y i) z -
          (∑ j : Fin 3, spatialPartial
            (fun y => spatialPartial (fun x => u x i) j y) j z) +
          (∑ j : Fin 3,
            spatialPartial
              (fun y => regUniformMollifiedVelocity ρ ε hε u y j * u y i) j z) +
          spatialPartial
            (fun y => regularisedIntervalCanonicalPressure
              ρ ε hε u T hT.le hSlice y) i z = 0) ∧
    (∀ z : ParabolicPoint,
      z ∈ spaceTimeSet (Set.univ : Set Vec3) (Set.Ioo 0 T) →
      ∀ i : Fin 3,
        timePartial (fun y => u y i) z -
          (∑ j : Fin 3, spatialPartial
            (fun y => spatialPartial (fun x => u x i) j y) j z) +
          (∑ j : Fin 3, regUniformMollifiedVelocity ρ ε hε u z j *
            spatialPartial (fun y => u y i) j z) +
          spatialPartial
            (fun y => regularisedIntervalCanonicalPressure
              ρ ε hε u T hT.le hSlice y) i z = 0) ∧
    (∀ t : ℝ, (ht : t ∈ Set.Icc 0 T) →
      (fun x : Vec3 => regularisedIntervalCanonicalPressure
        ρ ε hε u T hT.le hSlice (x, t)) =ᵐ[volume]
      rieszPressureSliceRepresentative 2 (by norm_num)
        (forcedPressureTensorLp (regularizedMildTensor ρ ε hε
          (realVectorL2OfCoordinateFunction (fun x : Vec3 => u (x, t))
            (hSlice t ht))))) :=
  regularisedR3Final_core ρ ε hε a ha u T hT hSlice hL2Continuous hDivFree hMild
    (fun i => regularisedR3Final_continuousOn_of_prod (hUcontinuous i))
    (fun i j => regularisedR3Final_continuousOn_of_prod (hDcontinuous i j))
    (fun i j k => regularisedR3Final_continuousOn_of_prod (hDDcontinuous i j k))
    (fun i => regularisedR3Final_continuousOn_of_prod (hDtcontinuous i))
    (regularisedR3Final_continuousOn_of_prod hPcontinuous)
    (fun i => regularisedR3Final_continuousOn_of_prod (hDpcontinuous i))
    hUjoint hDdiff hPdiff

end

end CKN.Leray

end
