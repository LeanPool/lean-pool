/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalAssembly
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalR4
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalR5
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR3Global

/-!
# The regularized solutions of `thm:regularised`

The regularized velocity is the pointwise velocity of the global regularized
mild curve, and the pressure is its canonical Riesz pressure. They satisfy
(R1)–(R5) of `thm:regularised`, in the form used by the direct limiting
argument for `thm:leray`, given:
- the continuous lift of the curve to the Bessel potential space of order four;
- the regularity of the pressure;
- the classical time derivative of the velocity;
- joint continuous differentiability from continuous partial derivatives.
-/

public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace CKN.Leray

open CKN CKN.Foundation.Parabolic

/-- The regularized velocities of `thm:regularised`. -/
@[expose]
def regR12Uε (ρ : RegMollifierProfile) (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) :
    ParabolicPoint → Vec3 :=
  if hε : 0 < ε then regR12Velocity ρ ε hε a ha else 0

/-- The regularized pressures of `thm:regularised`. -/
@[expose]
def regR12Pε (ρ : RegMollifierProfile) (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) :
    ParabolicPoint → ℝ :=
  if hε : 0 < ε then forcedQuadPressure ρ ε hε (regR12Curve ρ ε hε a ha) else 0

/-- `thm:regularised`, (R1)–(R5), for the regularized velocities and
pressures. -/
theorem regR12_regularised (ρ : RegMollifierProfile)
    (hPath : ∀ (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) (hε : 0 < ε),
      ∀ T : ℝ, 0 ≤ T → ∃ v : C(RegularizedMildTimeInterval T,
        BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2),
      ∀ t : RegularizedMildTimeInterval T,
        regularisedBesselSobolevToL2CLM ((2 * 2 : ℕ) : ℝ) (by positivity) (v t) =
          complexifyVectorL2 (regR12Curve ρ ε hε a ha t.1))
    (hPress : ∀ (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) (hε : 0 < ε),
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
    (hTime : ∀ (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) (hε : 0 < ε),
      ∀ z : ParabolicPoint, 0 < z.2 → ∀ i : Fin 3,
      HasDerivAt (fun s : ℝ => regR12Velocity ρ ε hε a ha (z.1, s) i)
        (regR12TimeRHS ρ ε hε (regR12Velocity ρ ε hε a ha)
          (forcedQuadPressure ρ ε hε (regR12Curve ρ ε hε a ha)) z i) z.2)
    (hJoint : ∀ (f g : ParabolicPoint → ℝ),
      (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        DifferentiableAt ℝ (fun x : Vec3 => f (x, z.2)) z.1) →
      (∀ j : Fin 3, ContinuousOn (fun z => spatialPartial f j z)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) →
      (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        HasDerivAt (fun s : ℝ => f (z.1, s)) (g z) z.2) →
      ContinuousOn g (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) →
      letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
      letI : NormedAddCommGroup ParabolicPoint :=
        inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
      letI : NormedSpace ℝ ParabolicPoint :=
        inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
      ContDiffOn ℝ 1 f (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) :
    ∀ (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ)
      (hε : 0 < ε),
      let u := regR12Uε ρ a ha ε
      let p := regR12Pε ρ a ha ε
      let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
        spatialPartial (fun y => u y i) j z
      let DD : ParabolicPoint → Fin 3 → Fin 3 → Vec3 := fun z i j k =>
        spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z
      let Dt : ParabolicPoint → Vec3 := fun z i =>
        timePartial (fun y => u y i) z
      let Dp : ParabolicPoint → Vec3 := fun z i =>
        spatialPartial (fun y => p y) i z
      (∃ hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume,
        Continuous (fun t : Set.Ici (0 : ℝ) =>
          CKN.Leray.realVectorL2OfCoordinateFunction
            (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2)) ∧
        (fun x : Vec3 => u (x, 0)) =ᵐ[volume]
          CKN.Leray.regUniformMollifiedInitial ρ ε hε a ∧
        ∀ t : ℝ, 0 ≤ t → CKN.IsWeakDivFreeL2 (fun x => u (x, t))) ∧
      (∀ i : Fin 3, ContinuousOn (fun z => u z i)
          (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
      (∀ i j, ContinuousOn (fun z => D z i j)
          (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
      (∀ i j k, ContinuousOn (fun z => DD z i j k)
          (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
      (∀ i, ContinuousOn (fun z => Dt z i)
          (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
      ContinuousOn p (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) ∧
      (∀ i, ContinuousOn (fun z => Dp z i)
          (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
      (letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
       letI : NormedAddCommGroup ParabolicPoint :=
         inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
       letI : NormedSpace ℝ ParabolicPoint :=
         inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
       ∀ i, ContDiffOn ℝ 1 (fun z => u z i)
          (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
      (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), ∀ i j,
        DifferentiableAt ℝ (fun x : Vec3 => D (x, z.2) i j) z.1) ∧
      (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1) ∧
      (∀ δ T : ℝ, 0 < δ → δ < T →
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Icc δ T),
            vec3EuclideanNorm (u z) ≤ C ∧ |p z| ≤ C ∧
            (∀ i j, |D z i j| ≤ C) ∧
            (∀ i j k, |DD z i j k| ≤ C) ∧
            (∀ i, |Dt z i| ≤ C) ∧
            (∀ i, |Dp z i| ≤ C)) ∧
      (∀ δ T : ℝ, 0 < δ → δ < T →
        (∀ i, MemLp (fun z : ParabolicPoint => u z i) 2
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
        (∀ i j, MemLp (fun z : ParabolicPoint => D z i j) 2
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
        (∀ i j k, MemLp (fun z : ParabolicPoint => DD z i j k) 2
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
        (∀ i, MemLp (fun z : ParabolicPoint => Dt z i) 2
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
        MemLp p 2 (volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      (∀ z : ParabolicPoint, 0 < z.2 → ∀ i : Fin 3,
        Dt z i - (∑ j : Fin 3, DD z i j j) +
          (∑ j : Fin 3,
            CKN.Leray.regUniformMollifiedVelocity ρ ε hε u z j * D z i j) +
          Dp z i = 0) ∧
      (∀ t : ℝ, 0 < t →
        ∃ hF : ∀ i j : Fin 3, MemLp
            (fun x : Vec3 =>
              CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                u (x, t) j) (ENNReal.ofReal (2 : ℝ)) volume,
          (fun x : Vec3 => p (x, t)) =ᵐ[volume]
            CKN.Leray.rieszPressureSliceRepresentative (2 : ℝ) (by norm_num)
              (fun i j => (hF i j).toLp
                (fun x : Vec3 =>
                  CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                    u (x, t) j)) ∧
          ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
            (∫ x : Vec3, p (x, t) * spatialLaplacian ψ x) =
              -∑ i : Fin 3, ∑ j : Fin 3,
                ∫ x : Vec3,
                  CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                    u (x, t) j * mixedSecond ψ i j x) ∧
      (∀ t : ℝ, 0 ≤ t →
        eLpNorm (CKN.Leray.regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
          2 * CKN.Leray.regUniformDissipation u D t =
            eLpNorm (CKN.Leray.regMollifyVector ρ ε hε
              (CKN.Leray.regUniformSpatialField a)) 2 volume ^ (2 : ℕ)) := by
  intro a ha ε hε
  have hu : regR12Uε ρ a ha ε = regR12Velocity ρ ε hε a ha := by
    simp only [regR12Uε, hε, ↓reduceDIte]
  have hp : regR12Pε ρ a ha ε = forcedQuadPressure ρ ε hε (regR12Curve ρ ε hε a ha) := by
    simp only [regR12Pε, hε, ↓reduceDIte]
    rfl
  simp only [hu, hp]
  have hCurve := regR12Velocity_slice_ae_eq_curve ρ ε hε a ha (hPath a ha ε hε)
  have hR12 := regR12_R1R2 ρ ε hε a ha (hPath a ha ε hε) (hPress a ha ε hε)
    (hTime a ha ε hε) hJoint
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ := hR12
  refine ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, ?_, ?_, ?_⟩
  · exact regularisedR3Global_of_mildCurve ρ ε hε a ha _ _ hCurve (fun _ _ => rfl)
      ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩
  · intro t ht
    exact regR12_R4 ρ ε hε (regR12Curve ρ ε hε a ha) _ t (hCurve t ht.le)
  · exact regR12_R5 ρ ε hε a ha _ hCurve
      (fun i j => regUniform_continuousOn_pullback (c3 i j) (fun z hz => hz)) c8

end CKN.Leray
