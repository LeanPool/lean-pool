/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedInitialData
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierCoordinateL2Bridge
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureLp
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessRepresentative

/-!
# Conditions for regularized solutions and their compactness limits

The regularity, energy and convergence assumptions shared by the Leray
compactness and solution assembly theorems.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- Regularity, equation, pressure, and energy conditions for one regularized solution. -/
@[expose] def lerayAssemblyRegularisedConditions
    (ρ : CKN.Leray.RegMollifierProfile)
    (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
    (pε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → ℝ)
    (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) (hε : 0 < ε) : Prop :=
      let u := uε a ha ε
      let p := pε a ha ε
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
              (CKN.Leray.regUniformSpatialField a)) 2 volume ^ (2 : ℕ))

/-- The local convergence, integrability and weak-gradient data of a Leray limit. -/
@[expose] def lerayAssemblyLocalLimitData
    (ρ : CKN.Leray.RegMollifierProfile)
    (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
    (a : Vec3 → Vec3) (ha : IsInJ a) (εseq : ℕ → ℝ)
    (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1) (σ : ℕ → ℕ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3) (T : ℝ) : Prop :=
  let μ : Measure ParabolicPoint :=
    volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))
  let U : ℕ → ParabolicPoint → Vec3 :=
    fun n => uε a ha (εseq (σ n))
  let J : ℕ → ParabolicPoint → Vec3 := fun n =>
    CKN.Leray.regUniformMollifiedVelocity ρ (εseq (σ n))
      (by exact (hseq (σ n)).1) (U n)
  let Dseq : ℕ → ParabolicPoint → Fin 3 → Vec3 := fun n z i j =>
    spatialPartial (fun y => U n y i) j z
  AEStronglyMeasurable u μ ∧ AEStronglyMeasurable Du μ ∧
  MemLp u 2 μ ∧ MemLp Du 2 μ ∧
  Tendsto (fun n => eLpNorm (U n - u) 2 μ) atTop (nhds 0) ∧
  (∀ i j, ∀ w : ParabolicPoint → ℝ, MemLp w 2 μ →
    Tendsto (fun n => ∫ z in spaceTimeSet
        (Set.univ : Set Vec3) (Ioo 0 T), Dseq n z i j * w z)
      atTop (nhds (∫ z in spaceTimeSet
        (Set.univ : Set Vec3) (Ioo 0 T), Du z i j * w z))) ∧
  (∀ q : ℝ, 2 ≤ q → q < 10 / 3 →
    Tendsto (fun n => eLpNorm (U n - u) (ENNReal.ofReal q) μ)
      atTop (nhds 0)) ∧
  (∀ n, MemLp (U n) 3 μ) ∧
  (∀ n, MemLp (J n) 3 μ) ∧ MemLp u 3 μ ∧
  Tendsto (fun n => eLpNorm (J n - u) 3 μ) atTop (nhds 0) ∧
  (∀ t : ℝ, 0 < t → ∀ w : Vec3 → Vec3,
    MemLp w 2 volume →
    Tendsto (fun n => ∫ x : Vec3, ∑ i : Fin 3,
        U n (x, t) i * w x i) atTop
      (nhds (∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * w x i))) ∧
  (∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ i : Fin 3,
    HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => u (x, t) i) (fun x => Du (x, t) i))

/-- Compactness and convergence data produced by the Leray limit argument. -/
@[expose] def lerayAssemblyCompactnessLimitContract
    (ρ : CKN.Leray.RegMollifierProfile)
    (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3) : Prop :=
  ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
      (_hεseq : Tendsto εseq atTop (nhds 0)),
      ∃ σ : ℕ → ℕ, ∃ u : ParabolicPoint → Vec3,
        ∃ Du : ParabolicPoint → Fin 3 → Vec3,
        StrictMono σ ∧ Tendsto σ atTop atTop ∧
        Tendsto (fun n => εseq (σ n)) atTop (nhds 0) ∧
        (∀ x : Vec3, u (x, 0) = a x) ∧
        (∀ T : ℝ, 0 < T →
          lerayAssemblyLocalLimitData ρ uε a ha εseq hseq σ u Du T) ∧
        (∀ z : Vec3 × ℝ, 0 < z.2 →
          u (parabolicHomeomorph.symm z) =
            CKN.Leray.compactnessMollifiedLimit
              (fun n => fun y =>
                uε a ha (εseq (σ n)) (parabolicHomeomorph.symm y)) σ z)

end CKN

end
