/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalContract

/-!
# The classical time derivative of the regularized velocity

The time-derivative theorem for velocities that satisfy the regularized
equation weakly applies to the pointwise regularized velocity and the
canonical pressure of `thm:regularised`. Its hypotheses are supplied by:
- the Bessel lift of the global regularized mild curve;
- the pressure regularity;
- the spatial regularity of the velocity.
-/

public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace CKN.Leray

open CKN CKN.Foundation.Parabolic

/-- The classical time derivative of the regularized velocity, from the
time-derivative theorem for velocities satisfying the regularized equation
weakly, the Bessel lift and the pressure regularity. -/
theorem regR12_hasDerivAt_of_inputs (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a)
    (hPath : ∀ T : ℝ, 0 ≤ T → ∃ v : C(RegularizedMildTimeInterval T,
        BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2),
      ∀ t : RegularizedMildTimeInterval T,
        regularisedBesselSobolevToL2CLM ((2 * 2 : ℕ) : ℝ) (by positivity) (v t) =
          complexifyVectorL2 (regR12Curve ρ ε hε a ha t.1))
    (hPress :
      let p : ParabolicPoint → ℝ := forcedQuadPressure ρ ε hε (regR12Curve ρ ε hε a ha)
      ContinuousOn p (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) ∧
      (∀ i : Fin 3, ContinuousOn (fun z => spatialPartial (fun y => p y) i z)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
      (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1) ∧
      (∀ δ T : ℝ, 0 < δ → δ < T → ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Icc δ T),
          |p z| ≤ C ∧ ∀ i : Fin 3, |spatialPartial (fun y => p y) i z| ≤ C) ∧
      (∀ δ T : ℝ, 0 < δ → δ < T →
        MemLp p 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))) ∧
        ∀ i : Fin 3, MemLp (fun z => spatialPartial (fun y => p y) i z) 2
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))))
    (hTimeDerivative : ∀ (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
      (a : Vec3 → Vec3) (ha : CKN.IsInJ a)
      (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
      (_hCurve : ∀ t : ℝ, 0 ≤ t →
        (fun x : Vec3 => u (x, t)) =ᵐ[volume]
          realVectorL2Representative
            (regularizedGlobalMildCurve ρ ε hε
              (realVectorL2OfCoordinateFunction (regUniformMollifiedInitial ρ ε hε a)
                (regMollifiedInitial_isInJ ρ ε hε ha).1)
              (regUniformMollifiedInitial_mildJData ρ ε hε ha) t))
      (_hPressure : ∀ z : ParabolicPoint, 0 < z.2 →
        p z = forcedQuadPressure ρ ε hε
          (regularizedGlobalMildCurve ρ ε hε
            (realVectorL2OfCoordinateFunction (regUniformMollifiedInitial ρ ε hε a)
              (regMollifiedInitial_isInJ ρ ε hε ha).1)
            (regUniformMollifiedInitial_mildJData ρ ε hε ha)) z)
      (_hU : ∀ i : Fin 3, ContinuousOn (fun z => u z i)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
      (_hD : ∀ i j : Fin 3, ContinuousOn
        (fun z => spatialPartial (fun y => u y i) j z)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
      (_hDD : ∀ i j k : Fin 3, ContinuousOn
        (fun z => spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
      (_hP : ContinuousOn p (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
      (_hDp : ∀ i : Fin 3, ContinuousOn (fun z => spatialPartial (fun y => p y) i z)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
      (_hUdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), ∀ i : Fin 3,
        DifferentiableAt ℝ (fun x : Vec3 => u (x, z.2) i) z.1)
      (_hDdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), ∀ i j : Fin 3,
        DifferentiableAt ℝ (fun x : Vec3 => spatialPartial (fun y => u y i) j (x, z.2)) z.1)
      (_hPdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1),
      ∀ z : ParabolicPoint, 0 < z.2 → ∀ i : Fin 3,
        HasDerivAt (fun s : ℝ => u (z.1, s) i)
          ((∑ j : Fin 3, spatialPartial
              (fun y => spatialPartial (fun x => u x i) j y) j z) -
            (∑ j : Fin 3, regUniformMollifiedVelocity ρ ε hε u z j *
              spatialPartial (fun y => u y i) j z) -
            spatialPartial (fun y => p y) i z) z.2) :
    ∀ z : ParabolicPoint, 0 < z.2 → ∀ i : Fin 3,
      HasDerivAt (fun s : ℝ => regR12Velocity ρ ε hε a ha (z.1, s) i)
        (regR12TimeRHS ρ ε hε (regR12Velocity ρ ε hε a ha)
          (forcedQuadPressure ρ ε hε (regR12Curve ρ ε hε a ha)) z i) z.2 := by
  obtain ⟨hPc, hDpc, hPdiff, -, -⟩ := hPress
  exact hTimeDerivative ρ ε hε a ha (regR12Velocity ρ ε hε a ha)
    (forcedQuadPressure ρ ε hε (regR12Curve ρ ε hε a ha))
    (regR12Velocity_slice_ae_eq_curve ρ ε hε a ha hPath) (fun _ _ => rfl)
    (regR12Velocity_continuousOn ρ ε hε a ha hPath)
    (regR12Velocity_D_continuousOn ρ ε hε a ha hPath)
    (regR12Velocity_DD_continuousOn ρ ε hε a ha hPath) hPc hDpc
    (fun z hz i => (regR12Velocity_differentiableAt ρ ε hε a ha hPath z hz i i).1)
    (fun z hz i j => (regR12Velocity_differentiableAt ρ ε hε a ha hPath z hz i j).2) hPdiff

end CKN.Leray
