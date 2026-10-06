/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegEquicontinuityMain
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitTenThirds
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegPressureBound
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureSlices
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegPressureL2
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformMomentum
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformMollified
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcePressureLocalBound
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitMeasurability
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureSpaceTime

/-!
# Reg Equicontinuity Inputs Data

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Extracts the regularized sequence data used by the equicontinuity estimate. -/
theorem regEquicontinuity_data_of_regularised_contract
    (ρ : RegMollifierProfile)
    (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
    (pε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → ℝ)
    (hregularised : ∀ (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ)
      (hε : 0 < ε),
      let u := uε a ha ε
      let p := pε a ha ε
      let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
        spatialPartial (fun y => u y i) j z
      let DD : ParabolicPoint → Fin 3 → Fin 3 → Vec3 := fun z i j k =>
        spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z
      let Dt : ParabolicPoint → Vec3 := fun z i => timePartial (fun y => u y i) z
      let Dp : ParabolicPoint → Vec3 := fun z i => spatialPartial (fun y => p y) i z
      (∃ hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume,
        Continuous (fun t : Set.Ici (0 : ℝ) =>
          realVectorL2OfCoordinateFunction
            (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2)) ∧
        (fun x : Vec3 => u (x, 0)) =ᵐ[volume]
          regUniformMollifiedInitial ρ ε hε a ∧
        ∀ t : ℝ, 0 ≤ t → CKN.IsWeakDivFreeL2 (fun x => u (x, t))) ∧
      (∀ i : Fin 3, ContinuousOn (fun z => u z i)
        (spaceTimeSet Set.univ (Ioi 0))) ∧
      (∀ i j, ContinuousOn (fun z => D z i j)
        (spaceTimeSet Set.univ (Ioi 0))) ∧
      (∀ i j k, ContinuousOn (fun z => DD z i j k)
        (spaceTimeSet Set.univ (Ioi 0))) ∧
      (∀ i, ContinuousOn (fun z => Dt z i)
        (spaceTimeSet Set.univ (Ioi 0))) ∧
      ContinuousOn p (spaceTimeSet Set.univ (Ioi 0)) ∧
      (∀ i, ContinuousOn (fun z => Dp z i)
        (spaceTimeSet Set.univ (Ioi 0))) ∧
      (letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
       letI : NormedAddCommGroup ParabolicPoint :=
         inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
       letI : NormedSpace ℝ ParabolicPoint :=
         inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
       ∀ i, ContDiffOn ℝ 1 (fun z => u z i)
         (spaceTimeSet Set.univ (Ioi 0))) ∧
      (∀ z ∈ spaceTimeSet Set.univ (Ioi 0), ∀ i j,
        DifferentiableAt ℝ (fun x : Vec3 => D (x, z.2) i j) z.1) ∧
      (∀ z ∈ spaceTimeSet Set.univ (Ioi 0),
        DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1) ∧
      (∀ δ T : ℝ, 0 < δ → δ < T →
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ z ∈ spaceTimeSet Set.univ (Icc δ T),
            vec3EuclideanNorm (u z) ≤ C ∧ |p z| ≤ C ∧
            (∀ i j, |D z i j| ≤ C) ∧
            (∀ i j k, |DD z i j k| ≤ C) ∧
            (∀ i, |Dt z i| ≤ C) ∧ (∀ i, |Dp z i| ≤ C)) ∧
      (∀ δ T : ℝ, 0 < δ → δ < T →
        (∀ i, MemLp (fun z : ParabolicPoint => u z i) 2
          (volume.restrict (spaceTimeSet Set.univ (Ioo δ T)))) ∧
        (∀ i j, MemLp (fun z : ParabolicPoint => D z i j) 2
          (volume.restrict (spaceTimeSet Set.univ (Ioo δ T)))) ∧
        (∀ i j k, MemLp (fun z : ParabolicPoint => DD z i j k) 2
          (volume.restrict (spaceTimeSet Set.univ (Ioo δ T)))) ∧
        (∀ i, MemLp (fun z : ParabolicPoint => Dt z i) 2
          (volume.restrict (spaceTimeSet Set.univ (Ioo δ T)))) ∧
        MemLp p 2 (volume.restrict
          (spaceTimeSet Set.univ (Ioo δ T)))) ∧
      (∀ z : ParabolicPoint, 0 < z.2 → ∀ i : Fin 3,
        Dt z i - (∑ j : Fin 3, DD z i j j) +
          (∑ j : Fin 3,
            regUniformMollifiedVelocity ρ ε hε u z j * D z i j) + Dp z i = 0) ∧
      (∀ t : ℝ, 0 < t →
        ∃ hF : ∀ i j : Fin 3, MemLp
            (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t) i *
              u (x, t) j) (ENNReal.ofReal 2) volume,
          (fun x : Vec3 => p (x, t)) =ᵐ[volume]
            rieszPressureSliceRepresentative 2 (by norm_num)
              (fun i j => (hF i j).toLp
                (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                  u (x, t) j)) ∧
          ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
            (∫ x : Vec3, p (x, t) * spatialLaplacian ψ x) =
              -∑ i : Fin 3, ∑ j : Fin 3,
                ∫ x : Vec3,
                  regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                    u (x, t) j * mixedSecond ψ i j x) ∧
      (∀ t : ℝ, 0 ≤ t →
        eLpNorm (regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
          2 * regUniformDissipation u D t =
        eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a))
          2 volume ^ (2 : ℕ))) :
    ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (εseq : ℕ → ℝ) (_hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1),
      (∀ n t, 0 ≤ t →
        MemLp (fun x : Vec3 => uε a ha (εseq n) (x, t)) 2 volume) ∧
      (∀ n t, 0 ≤ t →
        IsWeakDivFreeL2 (fun x : Vec3 => uε a ha (εseq n) (x, t))) ∧
      (∀ n i, ContinuousOn
        (fun z => uε a ha (εseq n) z i)
        (spaceTimeSet Set.univ (Ioi (0 : ℝ)))) ∧
      (∀ n i j, ContinuousOn
        (fun z => spatialPartial (fun y => uε a ha (εseq n) y i) j z)
        (spaceTimeSet Set.univ (Ioi (0 : ℝ)))) ∧
      (∀ n i j k, ContinuousOn
        (fun z => spatialPartial
          (fun y => spatialPartial (fun x => uε a ha (εseq n) x i) j y) k z)
        (spaceTimeSet Set.univ (Ioi (0 : ℝ)))) ∧
      (∀ n i, ContinuousOn
        (fun z => timePartial (fun y => uε a ha (εseq n) y i) z)
        (spaceTimeSet Set.univ (Ioi (0 : ℝ)))) ∧
      (∀ n, ContinuousOn (pε a ha (εseq n))
        (spaceTimeSet Set.univ (Ioi (0 : ℝ)))) ∧
      (∀ n i, ContinuousOn
        (fun z => spatialPartial (fun y => pε a ha (εseq n) y) i z)
        (spaceTimeSet Set.univ (Ioi (0 : ℝ)))) ∧
      (letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
       letI : NormedAddCommGroup ParabolicPoint :=
         inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
       letI : NormedSpace ℝ ParabolicPoint :=
         inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
       ∀ n i, ContDiffOn ℝ 1 (fun z => uε a ha (εseq n) z i)
         (spaceTimeSet Set.univ (Ioi (0 : ℝ)))) ∧
      (∀ n z, z ∈ spaceTimeSet Set.univ (Ioi (0 : ℝ)) →
        ∀ i j, DifferentiableAt ℝ
          (fun x : Vec3 => spatialPartial
            (fun y => uε a ha (εseq n) y i) j (x, z.2)) z.1) ∧
      (∀ n z, z ∈ spaceTimeSet Set.univ (Ioi (0 : ℝ)) →
        DifferentiableAt ℝ (fun x : Vec3 => pε a ha (εseq n) (x, z.2)) z.1) ∧
      (∀ n δ T, 0 < δ → δ < T → ∃ M : ℝ, 0 ≤ M ∧
        ∀ z ∈ spaceTimeSet Set.univ (Icc δ T), ∀ i,
          |timePartial (fun y => uε a ha (εseq n) y i) z| ≤ M) ∧
      (∀ n z, 0 < z.2 → ∀ i : Fin 3,
        timePartial (fun y => uε a ha (εseq n) y i) z -
          (∑ j : Fin 3, spatialPartial
            (fun y => spatialPartial (fun x => uε a ha (εseq n) x i) j y) j z) +
          (∑ j : Fin 3,
            regUniformMollifiedVelocity ρ (εseq n) (_hseq n).1
              (uε a ha (εseq n)) z j *
              spatialPartial (fun y => uε a ha (εseq n) y i) j z) +
          spatialPartial (fun y => pε a ha (εseq n) y) i z = 0) ∧
      (∀ n t, 0 ≤ t →
        eLpNorm (regUniformVelocitySlice (uε a ha (εseq n)) t) 2 volume ^ (2 : ℕ) +
          2 * regUniformDissipation (uε a ha (εseq n))
            (fun z i j => spatialPartial (fun y => uε a ha (εseq n) y i) j z) t =
        eLpNorm (regMollifyVector ρ (εseq n) (_hseq n).1
          (regUniformSpatialField a)) 2 volume ^ (2 : ℕ)) := by
  intro a ha εseq hseq
  have hparts (n : ℕ) :
      (∀ t, 0 ≤ t → MemLp (fun x : Vec3 => uε a ha (εseq n) (x, t)) 2 volume) ∧
      (∀ t, 0 ≤ t → IsWeakDivFreeL2
        (fun x : Vec3 => uε a ha (εseq n) (x, t))) ∧
      (∀ i, ContinuousOn (fun z => uε a ha (εseq n) z i)
        (spaceTimeSet Set.univ (Ioi (0 : ℝ)))) ∧
      (∀ i j, ContinuousOn
        (fun z => spatialPartial (fun y => uε a ha (εseq n) y i) j z)
        (spaceTimeSet Set.univ (Ioi (0 : ℝ)))) ∧
      (∀ i j k, ContinuousOn (fun z => spatialPartial
        (fun y => spatialPartial (fun x => uε a ha (εseq n) x i) j y) k z)
        (spaceTimeSet Set.univ (Ioi (0 : ℝ)))) ∧
      (∀ i, ContinuousOn (fun z => timePartial
        (fun y => uε a ha (εseq n) y i) z)
        (spaceTimeSet Set.univ (Ioi (0 : ℝ)))) ∧
      ContinuousOn (pε a ha (εseq n))
        (spaceTimeSet Set.univ (Ioi (0 : ℝ))) ∧
      (∀ i, ContinuousOn
        (fun z => spatialPartial (fun y => pε a ha (εseq n) y) i z)
        (spaceTimeSet Set.univ (Ioi (0 : ℝ)))) ∧
      (letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
       letI : NormedAddCommGroup ParabolicPoint :=
         inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
       letI : NormedSpace ℝ ParabolicPoint :=
         inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
       ∀ i, ContDiffOn ℝ 1
         (fun z => uε a ha (εseq n) z i)
         (spaceTimeSet Set.univ (Ioi (0 : ℝ)))) ∧
      (∀ z, z ∈ spaceTimeSet Set.univ (Ioi (0 : ℝ)) → ∀ i j,
        DifferentiableAt ℝ (fun x : Vec3 => spatialPartial
          (fun y => uε a ha (εseq n) y i) j (x, z.2)) z.1) ∧
      (∀ z, z ∈ spaceTimeSet Set.univ (Ioi (0 : ℝ)) →
        DifferentiableAt ℝ (fun x : Vec3 => pε a ha (εseq n) (x, z.2)) z.1) ∧
      (∀ δ T, 0 < δ → δ < T → ∃ M : ℝ, 0 ≤ M ∧
        ∀ z ∈ spaceTimeSet Set.univ (Icc δ T), ∀ i,
          |timePartial (fun y => uε a ha (εseq n) y i) z| ≤ M) ∧
      (∀ z, 0 < z.2 → ∀ i : Fin 3,
        timePartial (fun y => uε a ha (εseq n) y i) z -
          (∑ j : Fin 3, spatialPartial
            (fun y => spatialPartial (fun x => uε a ha (εseq n) x i) j y) j z) +
          (∑ j : Fin 3,
            regUniformMollifiedVelocity ρ (εseq n) (hseq n).1
              (uε a ha (εseq n)) z j *
              spatialPartial (fun y => uε a ha (εseq n) y i) j z) +
          spatialPartial (fun y => pε a ha (εseq n) y) i z = 0) ∧
      (∀ t, 0 ≤ t →
        eLpNorm (regUniformVelocitySlice (uε a ha (εseq n)) t) 2 volume ^ (2 : ℕ) +
          2 * regUniformDissipation (uε a ha (εseq n))
            (fun z i j => spatialPartial (fun y => uε a ha (εseq n) y i) j z) t =
        eLpNorm (regMollifyVector ρ (εseq n) (hseq n).1
          (regUniformSpatialField a)) 2 volume ^ (2 : ℕ)) := by
    rcases hregularised a ha (εseq n) (hseq n).1 with
      ⟨hFirst, hUc, hDc, hDDc, hDtc, hpc, hDpc, hC1,
        hDdiff, hpDiff, hBound, _hLocal, hPDE, _hR4, hR5⟩
    rcases hFirst with ⟨hSlice, _hCurve, _hInitial, hDiv⟩
    refine ⟨hSlice, hDiv, hUc, hDc, hDDc, hDtc, hpc, hDpc,
      hC1, hDdiff, hpDiff, ?_, ?_, ?_⟩
    · intro δ T hδ hδT
      obtain ⟨M, hM, hMbound⟩ := hBound δ T hδ hδT
      exact ⟨M, hM, fun z hz i => (hMbound z hz).2.2.2.2.1 i⟩
    · intro z hz i
      simpa using hPDE z hz i
    · exact hR5
  exact ⟨fun n => (hparts n).1, fun n => (hparts n).2.1,
    fun n => (hparts n).2.2.1, fun n => (hparts n).2.2.2.1,
    fun n => (hparts n).2.2.2.2.1, fun n => (hparts n).2.2.2.2.2.1,
    fun n => (hparts n).2.2.2.2.2.2.1, fun n => (hparts n).2.2.2.2.2.2.2.1,
    fun n => (hparts n).2.2.2.2.2.2.2.2.1,
    fun n => (hparts n).2.2.2.2.2.2.2.2.2.1,
    fun n => (hparts n).2.2.2.2.2.2.2.2.2.2.1,
    fun n => (hparts n).2.2.2.2.2.2.2.2.2.2.2.1,
    fun n => (hparts n).2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun n => (hparts n).2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Obtains a uniform positive-time ten-thirds bound from the regularized energy identity. -/
theorem regEquicontinuity_regularized_velocity_tenThirds_bound
    (ρ : RegMollifierProfile)
    (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
    (pε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → ℝ)
    (hregularised : ∀ (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ)
      (hε : 0 < ε),
      let u := uε a ha ε
      let p := pε a ha ε
      let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
        spatialPartial (fun y => u y i) j z
      let DD : ParabolicPoint → Fin 3 → Fin 3 → Vec3 := fun z i j k =>
        spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z
      let Dt : ParabolicPoint → Vec3 := fun z i => timePartial (fun y => u y i) z
      let Dp : ParabolicPoint → Vec3 := fun z i => spatialPartial (fun y => p y) i z
      (∃ hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume,
        Continuous (fun t : Set.Ici (0 : ℝ) =>
          realVectorL2OfCoordinateFunction
            (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2)) ∧
        (fun x : Vec3 => u (x, 0)) =ᵐ[volume]
          regUniformMollifiedInitial ρ ε hε a ∧
        ∀ t : ℝ, 0 ≤ t → CKN.IsWeakDivFreeL2 (fun x => u (x, t))) ∧
      (∀ i : Fin 3, ContinuousOn (fun z => u z i)
        (spaceTimeSet Set.univ (Ioi 0))) ∧
      (∀ i j, ContinuousOn (fun z => D z i j)
        (spaceTimeSet Set.univ (Ioi 0))) ∧
      (∀ i j k, ContinuousOn (fun z => DD z i j k)
        (spaceTimeSet Set.univ (Ioi 0))) ∧
      (∀ i, ContinuousOn (fun z => Dt z i)
        (spaceTimeSet Set.univ (Ioi 0))) ∧
      ContinuousOn p (spaceTimeSet Set.univ (Ioi 0)) ∧
      (∀ i, ContinuousOn (fun z => Dp z i)
        (spaceTimeSet Set.univ (Ioi 0))) ∧
      (letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
       letI : NormedAddCommGroup ParabolicPoint :=
         inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
       letI : NormedSpace ℝ ParabolicPoint :=
         inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
       ∀ i, ContDiffOn ℝ 1 (fun z => u z i)
         (spaceTimeSet Set.univ (Ioi 0))) ∧
      (∀ z ∈ spaceTimeSet Set.univ (Ioi 0), ∀ i j,
        DifferentiableAt ℝ (fun x : Vec3 => D (x, z.2) i j) z.1) ∧
      (∀ z ∈ spaceTimeSet Set.univ (Ioi 0),
        DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1) ∧
      (∀ δ T : ℝ, 0 < δ → δ < T →
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ z ∈ spaceTimeSet Set.univ (Icc δ T),
            vec3EuclideanNorm (u z) ≤ C ∧ |p z| ≤ C ∧
            (∀ i j, |D z i j| ≤ C) ∧
            (∀ i j k, |DD z i j k| ≤ C) ∧
            (∀ i, |Dt z i| ≤ C) ∧ (∀ i, |Dp z i| ≤ C)) ∧
      (∀ δ T : ℝ, 0 < δ → δ < T →
        (∀ i, MemLp (fun z : ParabolicPoint => u z i) 2
          (volume.restrict (spaceTimeSet Set.univ (Ioo δ T)))) ∧
        (∀ i j, MemLp (fun z : ParabolicPoint => D z i j) 2
          (volume.restrict (spaceTimeSet Set.univ (Ioo δ T)))) ∧
        (∀ i j k, MemLp (fun z : ParabolicPoint => DD z i j k) 2
          (volume.restrict (spaceTimeSet Set.univ (Ioo δ T)))) ∧
        (∀ i, MemLp (fun z : ParabolicPoint => Dt z i) 2
          (volume.restrict (spaceTimeSet Set.univ (Ioo δ T)))) ∧
        MemLp p 2 (volume.restrict
          (spaceTimeSet Set.univ (Ioo δ T)))) ∧
      (∀ z : ParabolicPoint, 0 < z.2 → ∀ i : Fin 3,
        Dt z i - (∑ j : Fin 3, DD z i j j) +
          (∑ j : Fin 3,
            regUniformMollifiedVelocity ρ ε hε u z j * D z i j) + Dp z i = 0) ∧
      (∀ t : ℝ, 0 < t →
        ∃ hF : ∀ i j : Fin 3, MemLp
          (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t) i *
            u (x, t) j) (ENNReal.ofReal 2) volume,
          (fun x : Vec3 => p (x, t)) =ᵐ[volume]
            rieszPressureSliceRepresentative 2 (by norm_num)
              (fun i j => (hF i j).toLp
                (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                  u (x, t) j)) ∧
          ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
            (∫ x : Vec3, p (x, t) * spatialLaplacian ψ x) =
              -∑ i : Fin 3, ∑ j : Fin 3,
                ∫ x : Vec3,
                  regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                    u (x, t) j * mixedSecond ψ i j x) ∧
      (∀ t : ℝ, 0 ≤ t →
        eLpNorm (regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
          2 * regUniformDissipation u D t =
        eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a))
          2 volume ^ (2 : ℕ)))
    (a : Vec3 → Vec3) (ha : IsInJ a)
    (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (n : ℕ) (i : Fin 3),
      MemLp (fun z : ParabolicPoint => uε a ha (εseq n) z i)
        (ENNReal.ofReal (10 / 3 : ℝ)) regUniformPositiveTimeMeasure ∧
      eLpNorm (fun z : ParabolicPoint => uε a ha (εseq n) z i)
        (ENNReal.ofReal (10 / 3 : ℝ)) regUniformPositiveTimeMeasure ≤
          ENNReal.ofReal B := by
  classical
  let hdata := regEquicontinuity_data_of_regularised_contract
    ρ uε pε hregularised a ha εseq hseq
  rcases hdata with ⟨hSlice, _, hUc, hDc, _, _, _, _, _, _, _, _, _, hR5⟩
  let A : ℝ≥0∞ := eLpNorm (regUniformSpatialField a) 2 volume
  have hInitial : MemLp (regUniformSpatialField a) 2 volume :=
    lerayHopfLimit_initialField_memLp a ha.1
  have hAfin : A < ⊤ := by
    exact hInitial.eLpNorm_lt_top
  let K : ℝ≥0∞ := CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)
  let C : ℝ≥0∞ := K ^ (10 / 3 : ℝ) * A ^ (4 / 3 : ℝ) * A ^ (2 : ℕ)
  have hKfin : K < ⊤ := by
    apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    exact (Classical.choose_spec CKN.sobolev_L6_global).1
  have hCfin : C < ⊤ := by
    apply ENNReal.mul_lt_top
    · exact ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hKfin.ne)
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hAfin.ne)
    · exact ENNReal.pow_lt_top hAfin
  let B : ℝ := 1 + C.toReal
  have hB0 : 0 ≤ B := by positivity
  have hCleB : C ≤ ENNReal.ofReal B := by
    change C ≤ ENNReal.ofReal (1 + C.toReal)
    calc
      C = ENNReal.ofReal C.toReal := (ENNReal.ofReal_toReal hCfin.ne).symm
      _ ≤ ENNReal.ofReal (1 + C.toReal) := ENNReal.ofReal_le_ofReal (by
        have h := add_le_add_left
          (show (0 : ℝ) ≤ 1 by norm_num) C.toReal
        simpa only [zero_add] using h)
  have hBpow : ENNReal.ofReal B ≤ ENNReal.ofReal B ^ (10 / 3 : ℝ) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hB0 (by norm_num : (0 : ℝ) ≤ 10 / 3)]
    apply ENNReal.ofReal_le_ofReal
    apply Real.self_le_rpow_of_one_le
    · dsimp [B]
      exact le_add_of_nonneg_right (ENNReal.toReal_nonneg (a := C))
    · norm_num
  have hUBound (n : ℕ) (i : Fin 3) :
      MemLp (fun z : ParabolicPoint => uε a ha (εseq n) z i)
        (ENNReal.ofReal (10 / 3 : ℝ)) regUniformPositiveTimeMeasure ∧
      eLpNorm (fun z : ParabolicPoint => uε a ha (εseq n) z i)
        (ENNReal.ofReal (10 / 3 : ℝ)) regUniformPositiveTimeMeasure ≤
          ENNReal.ofReal B := by
    let U : ParabolicPoint → Vec3 := uε a ha (εseq n)
    let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
      spatialPartial (fun y => U y i) j z
    have hEnergy := lerayLimit_regularised_energy_bounds
      ρ a ha (εseq n) (hseq n).1 U D (hUc n) (hDc n) (hR5 n)
    have hGrawEq :
        (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Vec3,
          ENNReal.ofReal (spatialGradientSq U D (x, t)) ∂volume ∂volume) =
        (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Vec3,
          ENNReal.ofReal (spatialGradientSq
            (lerayLimitPiecewise (spaceTimeSet Set.univ (Ioi (0 : ℝ))) U
              (fun z => regUniformMollifiedInitial ρ (εseq n) (hseq n).1 a z.1))
            (lerayLimitPiecewise (spaceTimeSet Set.univ (Ioi (0 : ℝ))) D
              (fun _ => 0)) (x, t)) ∂volume ∂volume) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      apply lintegral_congr_ae
      filter_upwards [] with x
      let z : ParabolicPoint := (x, t)
      have hz : z ∈ spaceTimeSet Set.univ (Ioi (0 : ℝ)) := by
        change x ∈ Set.univ ∧ 0 < t
        exact ⟨Set.mem_univ _, ht⟩
      have hDeq :
          lerayLimitPiecewise (spaceTimeSet Set.univ (Ioi (0 : ℝ))) D
            (fun _ => 0) z = D z := by
        change (spaceTimeSet Set.univ (Ioi (0 : ℝ))).piecewise D
          (fun _ => 0) z = D z
        rw [Set.piecewise_eq_of_mem _ _ _ hz]
      change ENNReal.ofReal (spatialGradientSq U D z) =
        ENNReal.ofReal (spatialGradientSq
          (lerayLimitPiecewise (spaceTimeSet Set.univ (Ioi (0 : ℝ))) U
            (fun z => regUniformMollifiedInitial ρ (εseq n) (hseq n).1 a z.1))
          (lerayLimitPiecewise (spaceTimeSet Set.univ (Ioi (0 : ℝ))) D
            (fun _ => 0)) z)
      simp [spatialGradientSq, hDeq]
    have hGraw :
        (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Vec3,
          ENNReal.ofReal (spatialGradientSq U D (x, t)) ∂volume ∂volume) ≤ A ^ (2 : ℕ) := by
      rw [hGrawEq]
      exact hEnergy.2.2
    have hTen := lerayLimit_regularised_component_tenThirds
      (ρ := ρ) (uε := uε) (pε := pε)
      (hregularised := hregularised) a ha (εseq n) (hseq n).1 i
    have hPow :
        eLpNorm (fun z : ParabolicPoint => U z i)
            (ENNReal.ofReal (10 / 3 : ℝ))
            (volume.restrict (spaceTimeSet Set.univ (Ioi (0 : ℝ)))) ^
              (10 / 3 : ℝ) ≤ C := by
      calc
        _ ≤ (CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)) ^
              (10 / 3 : ℝ) * A ^ (4 / 3 : ℝ) *
                (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Vec3,
                  ENNReal.ofReal (spatialGradientSq U D (x, t))
                    ∂volume ∂volume) := hTen.2
        _ ≤ C := by
          dsimp [C, K, A]
          exact mul_le_mul_of_nonneg_left hGraw (by positivity)
    have hNorm :
        eLpNorm (fun z : ParabolicPoint => U z i)
          (ENNReal.ofReal (10 / 3 : ℝ))
          (volume.restrict (spaceTimeSet Set.univ (Ioi (0 : ℝ)))) ≤
            ENNReal.ofReal B := by
      apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 10 / 3)).1
      exact (hPow.trans hCleB).trans hBpow
    constructor
    · simpa [regUniformPositiveTimeMeasure, U] using hTen.1
    · simpa [regUniformPositiveTimeMeasure, U] using hNorm
  exact ⟨B, hB0, hUBound⟩

private theorem regEquicontinuity_eLpNormENNReal_pow_eq_lintegral
    (r : ℝ) (hr : 0 < r) {f : ℝ → ℝ≥0∞}
    (hf : AEStronglyMeasurable f (volume : Measure ℝ)) :
    eLpNorm f (ENNReal.ofReal r) volume ^ r = ∫⁻ t, f t ^ r ∂volume := by
  have hr0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hr.le, ← ENNReal.rpow_mul]
  rw [one_div_mul_cancel hr.ne', ENNReal.rpow_one]
  apply lintegral_congr_ae
  filter_upwards [] with t
  simp

/-- Transfers a positive-time ten-thirds bound through spatial mollification. -/
theorem regEquicontinuity_mollified_velocity_tenThirds_bound
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3)
    (hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hUc : ∀ i : Fin 3, ContinuousOn (fun z => u z i)
      (spaceTimeSet Set.univ (Ioi (0 : ℝ))))
    (hC1 : letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
       letI : NormedAddCommGroup ParabolicPoint :=
         inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
       letI : NormedSpace ℝ ParabolicPoint :=
         inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
       ∀ i, ContDiffOn ℝ 1 (fun z => u z i)
         (spaceTimeSet Set.univ (Ioi (0 : ℝ))))
    (hU : ∀ j : Fin 3,
      MemLp (fun z : ParabolicPoint => u z j)
        (ENNReal.ofReal (10 / 3 : ℝ)) regUniformPositiveTimeMeasure)
    (BU : ℝ) (hBU : 0 ≤ BU)
    (hUbound : ∀ j : Fin 3,
        eLpNorm (fun z : ParabolicPoint => u z j)
        (ENNReal.ofReal (10 / 3 : ℝ)) regUniformPositiveTimeMeasure ≤
          ENNReal.ofReal BU) :
    ∀ i : Fin 3,
      MemLp (fun z : ParabolicPoint =>
        regUniformMollifiedVelocity ρ ε hε u z i)
          (ENNReal.ofReal (10 / 3 : ℝ)) regUniformPositiveTimeMeasure ∧
        eLpNorm (fun z : ParabolicPoint =>
        regUniformMollifiedVelocity ρ ε hε u z i)
          (ENNReal.ofReal (10 / 3 : ℝ)) regUniformPositiveTimeMeasure ≤
        ENNReal.ofReal (3 * BU) := by
  classical
  let S : Set (Vec3 × ℝ) := Set.univ ×ˢ Ioi (0 : ℝ)
  let J : Vec3 × ℝ → Vec3 := fun z =>
    regUniformMollifiedVelocity ρ ε hε u (z.1, z.2)
  let Ubar : Vec3 × ℝ → Vec3 :=
    S.piecewise (fun z => u (z.1, z.2)) (fun _ => 0)
  let Jbar : Vec3 × ℝ → Vec3 := S.piecewise J (fun _ => 0)
  let q : ℝ≥0∞ := ENNReal.ofReal (10 / 3 : ℝ)
  let r : ℝ := 10 / 3
  have hSmeas : MeasurableSet S := by
    exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi
  have hPositiveProduct : regUniformPositiveTimeMeasure =
      (volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ))) := by
    change ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
      (Set.univ ×ˢ Ioi (0 : ℝ)) = _
    rw [← Measure.prod_restrict (μ := (volume : Measure Vec3))
      (ν := (volume : Measure ℝ)) Set.univ (Ioi (0 : ℝ))]
    simp [Measure.restrict_univ]
  have hProductRestrict :
      (volume : Measure (Vec3 × ℝ)).restrict S =
        (volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ))) := by
    rw [Measure.volume_eq_prod]
    rw [← Measure.prod_restrict (μ := (volume : Measure Vec3))
      (ν := (volume : Measure ℝ)) Set.univ (Ioi (0 : ℝ))]
    simp [Measure.restrict_univ]
  have hPositiveTimeMeasure : regUniformPositiveTimeMeasure =
      (volume : Measure (Vec3 × ℝ)).restrict S :=
    hPositiveProduct.trans hProductRestrict.symm
  have hUcont (i : Fin 3) :
      ContinuousOn (fun z : Vec3 × ℝ => u (z.1, z.2) i) S := by
    exact (hUc i).comp
      CKN.Foundation.Parabolic.continuous_prod_to_parabolicPoint.continuousOn
      (by
        intro z hz
        exact hz)
  have hUbarCont : ContinuousOn (fun z : Vec3 × ℝ => u (z.1, z.2)) S := by
    apply continuousOn_pi.mpr
    intro i
    exact hUcont i
  have hUbarMeas : Measurable Ubar := by
    simpa [Ubar] using lerayLimit_measurableOn_extension S hSmeas
      (fun z : Vec3 × ℝ => u (z.1, z.2)) (fun _ => 0)
      hUbarCont continuousOn_const
  have hJcont : ∀ i : Fin 3, ContinuousOn (fun z => J z i) S := by
    have hshift : ∀ z ∈ S, ∀ y : Vec3, (z.1 - y, z.2) ∈ S := by
      intro z hz y
      change z.1 - y ∈ Set.univ ∧ 0 < z.2
      exact ⟨Set.mem_univ _, hz.2⟩
    have hpositive : ∀ z ∈ S, 0 < z.2 := fun _ hz => hz.2
    simpa [J, S, CKN.spaceTimeSet] using regUniform_mollified_velocity_continuousOn
      ρ ε hε (fun t ht => hSlice t ht.le) hC1 hpositive hshift
  have hJbarMeas : Measurable Jbar := by
    simpa [Jbar] using lerayLimit_measurableOn_extension S hSmeas J (fun _ => 0)
      (by
        apply continuousOn_pi.mpr
        exact hJcont)
      continuousOn_const
  have hUbarCompMeas (j : Fin 3) :
      Measurable (fun z : Vec3 × ℝ => Ubar z j) :=
    (measurable_pi_apply j).comp hUbarMeas
  have hJbarCompMeas (i : Fin 3) :
      Measurable (fun z : Vec3 × ℝ => Jbar z i) :=
    (measurable_pi_apply i).comp hJbarMeas
  let fU : Fin 3 → ℝ → ℝ≥0∞ := fun j t =>
    eLpNorm (fun x : Vec3 => Ubar (x, t) j) q volume
  let fJ : Fin 3 → ℝ → ℝ≥0∞ := fun i t =>
    eLpNorm (fun x : Vec3 => Jbar (x, t) i) q volume
  have hfUmeas (j : Fin 3) : Measurable (fU j) := by
    simpa [fU, q] using measurable_eLpNorm_slice
      ((hUbarCompMeas j).stronglyMeasurable)
      (by norm_num [q]) ENNReal.ofReal_ne_top volume
  have hfJmeas (i : Fin 3) : Measurable (fJ i) := by
    simpa [fJ, q] using measurable_eLpNorm_slice
      ((hJbarCompMeas i).stronglyMeasurable)
      (by norm_num [q]) ENNReal.ofReal_ne_top volume
  have hUbarMem (j : Fin 3) :
      MemLp (fun z : Vec3 × ℝ => Ubar z j) q volume := by
    have hpos := hU j
    rw [hPositiveTimeMeasure] at hpos
    have hcomp : (fun z : Vec3 × ℝ => Ubar z j) =
        S.indicator (fun z : Vec3 × ℝ => u (z.1, z.2) j) := by
      funext z
      by_cases hz : z ∈ S <;> simp [Ubar, Set.indicator, hz]
    rw [hcomp, memLp_indicator_iff_restrict hSmeas]
    exact hpos
  have hUbarBound (j : Fin 3) :
      eLpNorm (fun z : Vec3 × ℝ => Ubar z j) q volume ≤ ENNReal.ofReal BU := by
    have hpos := hUbound j
    rw [hPositiveTimeMeasure] at hpos
    have hcomp : (fun z : Vec3 × ℝ => Ubar z j) =
        S.indicator (fun z : Vec3 × ℝ => u (z.1, z.2) j) := by
      funext z
      by_cases hz : z ∈ S <;> simp [Ubar, Set.indicator, hz]
    rw [hcomp, eLpNorm_indicator_eq_eLpNorm_restrict hSmeas]
    exact hpos
  have hUbarPos (z : Vec3 × ℝ) (hz : z ∈ S) :
      Ubar z = u (z.1, z.2) := by
    simp [Ubar, hz]
  have hJbarPos (z : Vec3 × ℝ) (hz : z ∈ S) : Jbar z = J z := by
    simp [Jbar, hz]
  have hUbarNeg (z : Vec3 × ℝ) (hz : z ∉ S) : Ubar z = 0 := by
    simp [Ubar, hz]
  have hJbarNeg (z : Vec3 × ℝ) (hz : z ∉ S) : Jbar z = 0 := by
    simp [Jbar, hz]
  have hUprodPow (j : Fin 3) :
      eLpNorm (fun z : Vec3 × ℝ => Ubar z j) q
        (volume : Measure (Vec3 × ℝ)) ^ r =
        ∫⁻ t : ℝ, fU j t ^ r ∂(volume : Measure ℝ) := by
    simpa [q, r, fU] using eLpNorm_spaceTime_pow_eq_integral_slice
      (10 / 3 : ℝ) (by norm_num)
      ((hUbarCompMeas j).aestronglyMeasurable)
  have hJprodPow (i : Fin 3) :
      eLpNorm (fun z : Vec3 × ℝ => Jbar z i) q
        (volume : Measure (Vec3 × ℝ)) ^ r =
        ∫⁻ t : ℝ, fJ i t ^ r ∂(volume : Measure ℝ) := by
    simpa [q, r, fJ] using eLpNorm_spaceTime_pow_eq_integral_slice
      (10 / 3 : ℝ) (by norm_num)
      ((hJbarCompMeas i).aestronglyMeasurable)
  have hUtimeNormBound (j : Fin 3) :
      eLpNorm (fU j) q volume ≤ ENNReal.ofReal BU := by
    have hid := regEquicontinuity_eLpNormENNReal_pow_eq_lintegral r
      (by norm_num : 0 < r)
      ((hfUmeas j).aestronglyMeasurable)
    have hpow : eLpNorm (fU j) q volume ^ r ≤ (ENNReal.ofReal BU) ^ r := by
      calc
        _ = ∫⁻ t : ℝ, fU j t ^ r ∂volume := hid
        _ = eLpNorm (fun z : Vec3 × ℝ => Ubar z j) q volume ^ r :=
          (hUprodPow j).symm
        _ ≤ (ENNReal.ofReal BU) ^ r :=
          ENNReal.rpow_le_rpow (hUbarBound j) (by norm_num)
    exact (ENNReal.rpow_le_rpow_iff (by norm_num : 0 < r)).1 hpow
  have hUsliceMem : ∀ᵐ t : ℝ ∂(volume : Measure ℝ),
      ∀ j : Fin 3, MemLp (fun x : Vec3 => Ubar (x, t) j) q volume := by
    have hfin (j : Fin 3) : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), fU j t < ⊤ := by
      have hIntegral : (∫⁻ t : ℝ, fU j t ^ r ∂volume) < ⊤ := by
        rw [← hUprodPow j]
        exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
          (hUbarMem j).eLpNorm_ne_top
      have hpowfinite : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), fU j t ^ r < ⊤ := by
        exact ae_lt_top' ((hfUmeas j).pow_const r).aemeasurable hIntegral.ne
      filter_upwards [hpowfinite] with t ht
      exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : 0 < r)).1 ht
    have h0 := hfin 0
    have h1 := hfin 1
    have h2 := hfin 2
    filter_upwards [h0, h1, h2] with t ht0 ht1 ht2
    intro j
    have htop : fU j t < ⊤ := by
      fin_cases j <;> assumption
    rw [memLp_iff]
    simpa [fU, q] using htop
  have hJsliceBound : ∀ i : Fin 3, ∀ᵐ t : ℝ ∂(volume : Measure ℝ),
      fJ i t ≤ ∑ j : Fin 3, fU j t := by
    intro i
    filter_upwards [hUsliceMem] with t hUmem
    by_cases ht : 0 < t
    · have hUrawMem (j : Fin 3) :
          MemLp (fun x : Vec3 => u (x, t) j) q volume := by
        apply (memLp_congr_ae ?_).2 (hUmem j)
        filter_upwards [] with x
        exact congrArg (fun v : Vec3 => v j)
          (hUbarPos (x, t) ⟨Set.mem_univ _, ht⟩).symm
      have hcontract := regMollifyVector_component_eLpNorm_le_sum
        ρ ε hε (u := fun x : Vec3 => u (x, t))
        (p := q) (by norm_num [q]) (by norm_num [q]) (hSlice t ht.le)
        hUrawMem i
      have hJeq : (fun x : Vec3 => Jbar (x, t) i) =
          fun x : Vec3 => J (x, t) i := by
        funext x
        exact congrArg (fun v : Vec3 => v i)
          (hJbarPos (x, t) ⟨Set.mem_univ _, ht⟩)
      have hUeq (j : Fin 3) : (fun x : Vec3 => Ubar (x, t) j) =
          fun x : Vec3 => u ((x, t) : ParabolicPoint) j := by
        funext x
        exact congrArg (fun v : Vec3 => v j)
          (hUbarPos (x, t) ⟨Set.mem_univ _, ht⟩)
      calc
        fJ i t = eLpNorm (fun x : Vec3 => J (x, t) i) q volume :=
          eLpNorm_congr_ae (Filter.Eventually.of_forall fun x => congrFun hJeq x)
        _ ≤ ∑ j : Fin 3, eLpNorm (fun x : Vec3 => u (x, t) j) q volume := by
          have hJfun : (fun x : Vec3 => J (x, t) i) =
              (fun x : Vec3 =>
                (WithLp.ofLp (regMollifyVector ρ ε hε
                  (regUniformSpatialField (fun y : Vec3 => u (y, t)))
                  (WithLp.toLp 2 x))) i) := by
            have hsliceField : regUniformVelocitySlice u t =
                regUniformSpatialField (fun y : Vec3 => u (y, t)) := by
              funext x
              rfl
            funext x
            change (WithLp.ofLp (regMollifyVector ρ ε hε
              (regUniformVelocitySlice u t) (WithLp.toLp 2 x))) i = _
            rw [hsliceField]
          rw [hJfun]
          exact hcontract
        _ = ∑ j : Fin 3, fU j t := by
          apply Finset.sum_congr rfl
          intro j hj
          calc
            eLpNorm (fun x : Vec3 => u (x, t) j) q volume =
                eLpNorm (fun x : Vec3 => Ubar (x, t) j) q volume :=
              eLpNorm_congr_ae
                (Filter.Eventually.of_forall fun x => congrFun (hUeq j).symm x)
            _ = fU j t := rfl
    · have htn : t ≤ 0 := le_of_not_gt ht
      have htS (x : Vec3) : (x, t) ∉ S := by
        change ¬ (x ∈ Set.univ ∧ 0 < t)
        simp [htn]
      have hJzero (x : Vec3) : Jbar (x, t) i = 0 := by
        apply congrArg (fun v : Vec3 => v i)
        exact hJbarNeg (x, t) (htS x)
      have hUzero (j : Fin 3) (x : Vec3) : Ubar (x, t) j = 0 := by
        apply congrArg (fun v : Vec3 => v j)
        exact hUbarNeg (x, t) (htS x)
      simp [fJ, fU, hJzero, hUzero]
  have hJtimeNormBound (i : Fin 3) :
      eLpNorm (fJ i) q volume ≤ ENNReal.ofReal (3 * BU) := by
    calc
      eLpNorm (fJ i) q volume ≤
          eLpNorm (fun t : ℝ => ∑ j : Fin 3, fU j t) q volume := by
        apply eLpNorm_mono_enorm_ae ((hfJmeas i).aestronglyMeasurable)
        filter_upwards [hJsliceBound i] with t ht
        simpa using ht
      _ ≤ ∑ j : Fin 3, eLpNorm (fU j) q volume :=
        eLpNorm_sum_le (p := q) (s := Finset.univ)
          (f := fun j t => fU j t) (by norm_num [q])
      _ ≤ ∑ j : Fin 3, ENNReal.ofReal BU :=
        Finset.sum_le_sum fun j hj => hUtimeNormBound j
      _ = ENNReal.ofReal (3 * BU) := by
        simp [Finset.sum_const]
  have hJglobalBound (i : Fin 3) :
      eLpNorm (fun z : Vec3 × ℝ => Jbar z i) q volume ≤
        ENNReal.ofReal (3 * BU) := by
    apply (ENNReal.rpow_le_rpow_iff (by norm_num : 0 < r)).1
    calc
      eLpNorm (fun z : Vec3 × ℝ => Jbar z i) q volume ^ r =
          eLpNorm (fJ i) q volume ^ r := by
            rw [hJprodPow i,
              regEquicontinuity_eLpNormENNReal_pow_eq_lintegral r
                (by norm_num : 0 < r) ((hfJmeas i).aestronglyMeasurable)]
      _ ≤ ENNReal.ofReal (3 * BU) ^ r :=
        ENNReal.rpow_le_rpow (hJtimeNormBound i) (by norm_num)
  have hthreeBU : ENNReal.ofReal (3 * BU) = 3 * ENNReal.ofReal BU := by
    rw [show (3 : ℝ) * BU = BU * 3 by ring]
    rw [ENNReal.ofReal_mul hBU]
    rw [show ENNReal.ofReal (3 : ℝ) = (3 : ℝ≥0∞) by norm_num]
    exact mul_comm (ENNReal.ofReal BU) (3 : ℝ≥0∞)
  have hJposMem (i : Fin 3) :
      MemLp (fun z : ParabolicPoint => J z i) q regUniformPositiveTimeMeasure := by
    rw [memLp_iff]
    have hposBound : eLpNorm (fun z : ParabolicPoint => J z i) q
        regUniformPositiveTimeMeasure ≤ 3 * ENNReal.ofReal BU := by
      rw [hPositiveTimeMeasure]
      change eLpNorm (fun z : Vec3 × ℝ => J z i)
        q ((volume : Measure (Vec3 × ℝ)).restrict S) ≤ _
      rw [← eLpNorm_indicator_eq_eLpNorm_restrict hSmeas]
      have hcomp : (fun z : Vec3 × ℝ => Jbar z i) =
          S.indicator (fun z : Vec3 × ℝ => J z i) := by
        funext z
        by_cases hz : z ∈ S <;> simp [Jbar, hz]
      calc
        _ ≤ ENNReal.ofReal (3 * BU) := by
          rw [← hcomp]
          exact hJglobalBound i
        _ = 3 * ENNReal.ofReal BU := hthreeBU
    exact lt_of_le_of_lt hposBound
      (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)
  have hJposBound (i : Fin 3) :
      eLpNorm (fun z : ParabolicPoint => J z i) q regUniformPositiveTimeMeasure ≤
        ENNReal.ofReal (3 * BU) := by
    rw [hPositiveTimeMeasure]
    change eLpNorm (fun z : Vec3 × ℝ => J z i)
      q ((volume : Measure (Vec3 × ℝ)).restrict S) ≤ _
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict hSmeas]
    have hcomp : (fun z : Vec3 × ℝ => Jbar z i) =
        S.indicator (fun z : Vec3 × ℝ => J z i) := by
      funext z
      by_cases hz : z ∈ S <;> simp [Jbar, hz]
    rw [← hcomp]
    exact hJglobalBound i
  intro i
  exact ⟨hJposMem i, hJposBound i⟩


end CKN.Leray

end
