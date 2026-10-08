/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformMomentum
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformIntegrationByParts
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationBasics

/-!
# Reg Uniform Local Energy Flux

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open scoped Topology ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The product topology on parabolic space-time points used in this weak identity. -/
abbrev regUniformParabolicTopologyLocalEnergyFlux : TopologicalSpace ParabolicPoint :=
  inferInstance

/-- The product normed additive group used for spatial and temporal regularity. -/
local instance regUniformLocalEnergyFluxNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

/-- The product real normed space used for spatial and temporal derivatives. -/
local instance regUniformLocalEnergyFluxNormedSpace : NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))

/-- The product topology on parabolic space-time points used in this weak identity. -/
local instance (priority := 10000) regUniformLocalEnergyFluxTopologicalSpace :
    TopologicalSpace ParabolicPoint :=
  instTopologicalSpaceProd

private def regUniformSpatialGradientDensity
    (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3)
    (z : Vec3 × ℝ) : ℝ :=
  spatialGradientSq u Du ((z.1, z.2) : ParabolicPoint)

/- The finite sums in the local energy identity are assembled only after each
   scalar flux has been integrated. -/
private theorem regUniform_integral_finite_flux_sum_zero
    {X : Type*} [MeasurableSpace X] (S : Set X) (μ : Measure X)
    (T : Fin 3 → X → ℝ) (D G C : Fin 3 → Fin 3 → X → ℝ)
    (P : Fin 3 → X → ℝ)
    (hT : ∀ i, Integrable (T i) (μ.restrict S))
    (hD : ∀ i j, Integrable (D i j) (μ.restrict S))
    (hG : ∀ i j, Integrable (G i j) (μ.restrict S))
    (hC : ∀ i j, Integrable (C i j) (μ.restrict S))
    (hP : ∀ i, Integrable (P i) (μ.restrict S))
    (hTzero : ∀ i, (∫ x in S, T i x ∂μ) = 0)
    (hDzero : ∀ i j, (∫ x in S, D i j x ∂μ) = 0)
    (hGzero : ∀ i j, (∫ x in S, G i j x ∂μ) = 0)
    (hCzero : ∀ i j, (∫ x in S, C i j x ∂μ) = 0)
    (hPzero : ∀ i, (∫ x in S, P i x ∂μ) = 0) :
    (∫ x in S,
      (∑ i : Fin 3, T i x) - 2 * (∑ i : Fin 3, ∑ j : Fin 3, D i j x) +
        (∑ i : Fin 3, ∑ j : Fin 3, G i j x) +
        (∑ i : Fin 3, ∑ j : Fin 3, C i j x) + 2 * (∑ i : Fin 3, P i x)
      ∂μ) = 0 := by
  have hTsum : Integrable (fun x => ∑ i : Fin 3, T i x) (μ.restrict S) :=
    integrable_finsetSum Finset.univ fun i hi => hT i
  have hDsum : Integrable (fun x => ∑ i : Fin 3, ∑ j : Fin 3, D i j x)
      (μ.restrict S) :=
    integrable_finsetSum Finset.univ fun i hi =>
      integrable_finsetSum Finset.univ fun j hj => hD i j
  have hGsum : Integrable (fun x => ∑ i : Fin 3, ∑ j : Fin 3, G i j x)
      (μ.restrict S) :=
    integrable_finsetSum Finset.univ fun i hi =>
      integrable_finsetSum Finset.univ fun j hj => hG i j
  have hCsum : Integrable (fun x => ∑ i : Fin 3, ∑ j : Fin 3, C i j x)
      (μ.restrict S) :=
    integrable_finsetSum Finset.univ fun i hi =>
      integrable_finsetSum Finset.univ fun j hj => hC i j
  have hPsum : Integrable (fun x => ∑ i : Fin 3, P i x) (μ.restrict S) :=
    integrable_finsetSum Finset.univ fun i hi => hP i
  have hTsumZero : (∫ x in S, ∑ i : Fin 3, T i x ∂μ) = 0 := by
    rw [integral_finsetSum Finset.univ (fun i hi => hT i)]
    simp_rw [hTzero]
    simp
  have hDsumZero : (∫ x in S, ∑ i : Fin 3, ∑ j : Fin 3, D i j x ∂μ) = 0 := by
    rw [integral_finsetSum Finset.univ (fun i hi =>
      integrable_finsetSum Finset.univ fun j hj => hD i j)]
    simp_rw [integral_finsetSum Finset.univ (fun j hj => hD _ j)]
    simp_rw [hDzero]
    simp
  have hGsumZero : (∫ x in S, ∑ i : Fin 3, ∑ j : Fin 3, G i j x ∂μ) = 0 := by
    rw [integral_finsetSum Finset.univ (fun i hi =>
      integrable_finsetSum Finset.univ fun j hj => hG i j)]
    simp_rw [integral_finsetSum Finset.univ (fun j hj => hG _ j)]
    simp_rw [hGzero]
    simp
  have hCsumZero : (∫ x in S, ∑ i : Fin 3, ∑ j : Fin 3, C i j x ∂μ) = 0 := by
    rw [integral_finsetSum Finset.univ (fun i hi =>
      integrable_finsetSum Finset.univ fun j hj => hC i j)]
    simp_rw [integral_finsetSum Finset.univ (fun j hj => hC _ j)]
    simp_rw [hCzero]
    simp
  have hPsumZero : (∫ x in S, ∑ i : Fin 3, P i x ∂μ) = 0 := by
    rw [integral_finsetSum Finset.univ (fun i hi => hP i)]
    simp_rw [hPzero]
    simp
  have hDtwice := hDsum.const_mul 2
  have hPtwice := hPsum.const_mul 2
  have hAB := hTsum.sub hDtwice
  have hABC := hAB.add hGsum
  have hABCD := hABC.add hCsum
  have hABzero : (∫ x in S,
      (∑ i : Fin 3, T i x) - 2 * (∑ i : Fin 3, ∑ j : Fin 3, D i j x) ∂μ) = 0 := by
    rw [integral_sub hTsum hDtwice, integral_const_mul, hTsumZero, hDsumZero]
    simp
  have hABCzero : (∫ x in S,
      (∑ i : Fin 3, T i x) - 2 * (∑ i : Fin 3, ∑ j : Fin 3, D i j x) +
        (∑ i : Fin 3, ∑ j : Fin 3, G i j x) ∂μ) = 0 := by
    calc
      _ = (∫ x in S, (∑ i : Fin 3, T i x) -
            2 * (∑ i : Fin 3, ∑ j : Fin 3, D i j x) ∂μ) +
          ∫ x in S, ∑ i : Fin 3, ∑ j : Fin 3, G i j x ∂μ := by
        exact integral_add' hAB hGsum
      _ = 0 := by rw [hABzero, hGsumZero]; simp
  have hABCDzero : (∫ x in S,
      (∑ i : Fin 3, T i x) - 2 * (∑ i : Fin 3, ∑ j : Fin 3, D i j x) +
        (∑ i : Fin 3, ∑ j : Fin 3, G i j x) +
        (∑ i : Fin 3, ∑ j : Fin 3, C i j x) ∂μ) = 0 := by
    calc
      _ = (∫ x in S,
            (∑ i : Fin 3, T i x) -
              2 * (∑ i : Fin 3, ∑ j : Fin 3, D i j x) +
              (∑ i : Fin 3, ∑ j : Fin 3, G i j x) ∂μ) +
          ∫ x in S, ∑ i : Fin 3, ∑ j : Fin 3, C i j x ∂μ := by
        exact integral_add' hABC hCsum
      _ = 0 := by rw [hABCzero, hCsumZero]; simp
  calc
    _ = (∫ x in S,
          (∑ i : Fin 3, T i x) -
            2 * (∑ i : Fin 3, ∑ j : Fin 3, D i j x) +
            (∑ i : Fin 3, ∑ j : Fin 3, G i j x) +
            (∑ i : Fin 3, ∑ j : Fin 3, C i j x) ∂μ) +
        ∫ x in S, 2 * (∑ i : Fin 3, P i x) ∂μ := by
      exact integral_add' hABCD hPtwice
    _ = 0 := by rw [hABCDzero, integral_const_mul, hPsumZero]; simp

private theorem regUniform_spatial_product_partial_continuousOn
    {S : Set (Vec3 × ℝ)} {F G : Vec3 × ℝ → ℝ} (j : Fin 3)
    (hF : ContinuousOn F S) (hG : ContinuousOn G S)
    (hDF : ContinuousOn (fun z : Vec3 × ℝ => spatialPartial F j z) S)
    (hDG : ContinuousOn (fun z : Vec3 × ℝ => spatialPartial G j z) S)
    (hFd : ∀ z ∈ S, DifferentiableAt ℝ (fun x : Vec3 => F (x, z.2)) z.1)
    (hGd : ∀ z ∈ S, DifferentiableAt ℝ (fun x : Vec3 => G (x, z.2)) z.1) :
    ContinuousOn (fun z : Vec3 × ℝ => spatialPartial (fun y => F y * G y) j z) S := by
  apply ContinuousOn.congr ((hF.mul hDG).add (hG.mul hDF))
  intro z hz
  exact regUniform_spatialPartial_mul z.1 z.2 j (hFd z hz) (hGd z hz)

private theorem regUniform_time_product_partial_continuousOn
    {S : Set (Vec3 × ℝ)} {F G : Vec3 × ℝ → ℝ}
    (hF : ContinuousOn F S) (hG : ContinuousOn G S)
    (hDF : ContinuousOn (fun z : Vec3 × ℝ => timePartial F z) S)
    (hDG : ContinuousOn (fun z : Vec3 × ℝ => timePartial G z) S)
    (hFd : ∀ z ∈ S, DifferentiableAt ℝ (fun t : ℝ => F (z.1, t)) z.2)
    (hGd : ∀ z ∈ S, DifferentiableAt ℝ (fun t : ℝ => G (z.1, t)) z.2) :
    ContinuousOn (fun z : Vec3 × ℝ => timePartial (fun y => F y * G y) z) S := by
  apply ContinuousOn.congr ((hF.mul hDG).add (hG.mul hDF))
  intro z hz
  exact regUniform_timePartial_mul z.1 z.2 (hFd z hz) (hGd z hz)

private theorem regUniform_compact_spatial_derivative_integrable
    {S : Set (Vec3 × ℝ)} {F : Vec3 × ℝ → ℝ} (j : Fin 3)
    (hS : IsOpen S) (hDF : ContinuousOn (fun z : Vec3 × ℝ => spatialPartial F j z) S)
    (hFc : HasCompactSupport F) (hFs : tsupport F ⊆ S) :
    Integrable (fun z : Vec3 × ℝ => spatialPartial F j z) (volume.restrict S) := by
  have hc := CKN.hasCompactSupport_spatialPartial hFc j
  have hs := (CKN.tsupport_spatialPartial_subset j).trans hFs
  simpa only [one_mul] using
    (regUniform_integrable_mul_of_tsupport_subset
      (F := fun _ => (1 : ℝ)) hS continuousOn_const hDF hc hs).mono_measure
        Measure.restrict_le_self

private theorem regUniform_compact_time_derivative_integrable
    {S : Set (Vec3 × ℝ)} {F : Vec3 × ℝ → ℝ}
    (hS : IsOpen S) (hDF : ContinuousOn (fun z : Vec3 × ℝ => timePartial F z) S)
    (hFc : HasCompactSupport F) (hFs : tsupport F ⊆ S) :
    Integrable (fun z : Vec3 × ℝ => timePartial F z) (volume.restrict S) := by
  have hc := CKN.hasCompactSupport_timePartial hFc
  have hs := (CKN.tsupport_timePartial_subset F).trans hFs
  simpa only [one_mul] using
    (regUniform_integrable_mul_of_tsupport_subset
      (F := fun _ => (1 : ℝ)) hS continuousOn_const hDF hc hs).mono_measure
        Measure.restrict_le_self

private theorem regUniform_localized_spatial_flux_integrable
    {Ω : Set Vec3} {I : Set ℝ} {F ψ : Vec3 × ℝ → ℝ} (j : Fin 3)
    (hS : IsOpen (spaceTimeSet Ω I))
    (hF : ContinuousOn F (spaceTimeSet Ω I))
    (hDF : ContinuousOn (fun z : Vec3 × ℝ => spatialPartial F j z) (spaceTimeSet Ω I))
    (hFd : ∀ z ∈ spaceTimeSet Ω I, DifferentiableAt ℝ (fun x : Vec3 => F (x, z.2)) z.1)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    Integrable (fun z : Vec3 × ℝ => spatialPartial (fun y => F y * ψ y) j z)
      (volume.restrict (spaceTimeSet Ω I)) := by
  have hψd (z : Vec3 × ℝ) (hz : z ∈ spaceTimeSet Ω I) :=
    regUniform_contDiffOn_spatialSlice_differentiableAt hS
      (hψ.1.of_le (by norm_num)).contDiffOn hz
  have hpartial := regUniform_spatial_product_partial_continuousOn j
    hF hψ.1.continuous.continuousOn hDF (spatialPartial_contDiff hψ.1 j).continuous.continuousOn
    hFd (fun z hz => hψd z hz)
  exact regUniform_compact_spatial_derivative_integrable j hS hpartial hψ.2.1.mul_left
    (tsupport_mul_subset_right.trans hψ.2.2)

private theorem regUniform_localized_spatial_flux_integral_zero
    {Ω : Set Vec3} {I : Set ℝ} {F ψ : Vec3 × ℝ → ℝ} (j : Fin 3)
    (hS : IsOpen (spaceTimeSet Ω I))
    (hF : ContinuousOn F (spaceTimeSet Ω I))
    (hDF : ContinuousOn (fun z : Vec3 × ℝ => spatialPartial F j z) (spaceTimeSet Ω I))
    (hFd : ∀ z ∈ spaceTimeSet Ω I, DifferentiableAt ℝ (fun x : Vec3 => F (x, z.2)) z.1)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    (∫ (z : Vec3 × ℝ) in spaceTimeSet Ω I, spatialPartial (fun y => F y * ψ y)
      j z ∂volume) = 0 := by
  have hψd (z : Vec3 × ℝ) (hz : z ∈ spaceTimeSet Ω I) :=
    regUniform_contDiffOn_spatialSlice_differentiableAt hS
      (hψ.1.of_le (by norm_num)).contDiffOn hz
  have hpartial := regUniform_spatial_product_partial_continuousOn j
    hF hψ.1.continuous.continuousOn hDF (spatialPartial_contDiff hψ.1 j).continuous.continuousOn
    hFd (fun z hz => hψd z hz)
  exact regUniform_integral_spatialPartial_eq_zero j hS (hF.mul hψ.1.continuous.continuousOn)
    hpartial (fun z hz => (hFd z hz).mul (hψd z hz)) hψ.2.1.mul_left
    (tsupport_mul_subset_right.trans hψ.2.2)

private theorem regUniform_localized_time_flux_integrable
    {Ω : Set Vec3} {I : Set ℝ} {F ψ : Vec3 × ℝ → ℝ}
    (hS : IsOpen (spaceTimeSet Ω I))
    (hF : ContinuousOn F (spaceTimeSet Ω I))
    (hDF : ContinuousOn (fun z : Vec3 × ℝ => timePartial F z) (spaceTimeSet Ω I))
    (hFd : ∀ z ∈ spaceTimeSet Ω I, DifferentiableAt ℝ (fun t : ℝ => F (z.1, t)) z.2)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    Integrable (fun z : Vec3 × ℝ => timePartial (fun y => F y * ψ y) z)
      (volume.restrict (spaceTimeSet Ω I)) := by
  have hψd (z : Vec3 × ℝ) (hz : z ∈ spaceTimeSet Ω I) :=
    regUniform_contDiffOn_timeSlice_differentiableAt hS
      (hψ.1.of_le (by norm_num)).contDiffOn hz
  have hpartial := regUniform_time_product_partial_continuousOn
    hF hψ.1.continuous.continuousOn hDF
    (CKN.Core.Step3.timePartial_contDiff_full hψ.1).continuous.continuousOn
    hFd (fun z hz => hψd z hz)
  exact regUniform_compact_time_derivative_integrable hS hpartial hψ.2.1.mul_left
    (tsupport_mul_subset_right.trans hψ.2.2)

private theorem regUniform_localized_time_flux_integral_zero
    {Ω : Set Vec3} {I : Set ℝ} {F ψ : Vec3 × ℝ → ℝ}
    (hS : IsOpen (spaceTimeSet Ω I))
    (hF : ContinuousOn F (spaceTimeSet Ω I))
    (hDF : ContinuousOn (fun z : Vec3 × ℝ => timePartial F z) (spaceTimeSet Ω I))
    (hFd : ∀ z ∈ spaceTimeSet Ω I, DifferentiableAt ℝ (fun t : ℝ => F (z.1, t)) z.2)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    (∫ (z : Vec3 × ℝ) in spaceTimeSet Ω I, timePartial (fun y => F y * ψ y) z ∂volume) = 0 := by
  have hψd (z : Vec3 × ℝ) (hz : z ∈ spaceTimeSet Ω I) :=
    regUniform_contDiffOn_timeSlice_differentiableAt hS
      (hψ.1.of_le (by norm_num)).contDiffOn hz
  have hpartial := regUniform_time_product_partial_continuousOn
    hF hψ.1.continuous.continuousOn hDF
    (CKN.Core.Step3.timePartial_contDiff_full hψ.1).continuous.continuousOn
    hFd (fun z hz => hψd z hz)
  exact regUniform_integral_timePartial_eq_zero hS (hF.mul hψ.1.continuous.continuousOn)
    hpartial (fun z hz => (hFd z hz).mul (hψd z hz)) hψ.2.1.mul_left
    (tsupport_mul_subset_right.trans hψ.2.2)

private theorem regUniform_spatial_test_derivative_mem
    {Ω : Set Vec3} {I : Set ℝ} {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) (j : Fin 3) :
    (fun z : Vec3 × ℝ => spatialPartial ψ j z) ∈ spaceTimeTestFunction (V := ℝ) Ω I := by
  exact ⟨spatialPartial_contDiff hψ.1 j,
    CKN.hasCompactSupport_spatialPartial hψ.2.1 j,
    (CKN.tsupport_spatialPartial_subset j).trans hψ.2.2⟩

private theorem regUniform_mollified_spatial_slice_differentiableAt
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) {z : Vec3 × ℝ}
    (hdiv : CKN.IsWeakDivFreeL2 (fun x : Vec3 => u (x, z.2))) (i : Fin 3) :
    DifferentiableAt ℝ
      (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, z.2) i) z.1 := by
  have hsmooth := regUniformMollifiedInitial_contDiff ρ ε hε
    (CKN.weakDivFreeL2_isInJ hdiv)
  have hcoord := hsmooth.continuousLinearMap_comp
    (ContinuousLinearMap.proj (R := ℝ) i)
  exact hcoord.differentiable (by norm_num) z.1

/-- Compact support makes the integrated flux terms vanish in
`lem:reg-local-energy`. -/
theorem regUniform_local_energy_flux_integral_zero
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (hSliceL2 : ∀ t : ℝ, 0 ≤ t →
      MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hWeakDivFree : ∀ t : ℝ, 0 ≤ t →
      CKN.IsWeakDivFreeL2 (fun x : Vec3 => u (x, t)))
    (hUcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyLocalEnergyFlux
      ∀ i : Fin 3, ContinuousOn (fun z => u z i)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyLocalEnergyFlux
      ∀ i j : Fin 3, ContinuousOn
        (fun z => spatialPartial (fun y => u y i) j z)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDDcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyLocalEnergyFlux
      ∀ i j k : Fin 3, ContinuousOn
        (fun z => spatialPartial
          (fun y => spatialPartial (fun x => u x i) j y) k z)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDtcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyLocalEnergyFlux
      ∀ i : Fin 3, ContinuousOn
        (fun z => timePartial (fun y => u y i) z)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hPcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyLocalEnergyFlux
      ContinuousOn p (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDpcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyLocalEnergyFlux
      ∀ i : Fin 3, ContinuousOn
        (fun z => spatialPartial (fun y => p y) i z)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hUcontDiff : letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
      letI : NormedAddCommGroup ParabolicPoint :=
        inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
      letI : NormedSpace ℝ ParabolicPoint :=
        inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
      ∀ i : Fin 3, ContDiffOn ℝ 1 (fun z => u z i)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      ∀ i j : Fin 3,
        DifferentiableAt ℝ (fun x : Vec3 =>
          spatialPartial (fun y => u y i) j (x, z.2)) z.1)
    (hPdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1)
    (ψ : ParabolicPoint → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ)
      (Set.univ : Set Vec3) (Ioi 0)) :
    let S : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)
    let Ui (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => u z i
    let D (i j : Fin 3) : Vec3 × ℝ → ℝ :=
      fun z => spatialPartial (fun y => u y i) j z
    let J (i : Fin 3) : Vec3 × ℝ → ℝ :=
      fun z => regUniformMollifiedVelocity ρ ε hε u z i
    let Phi : Vec3 × ℝ → ℝ := fun z => ψ z
    let H (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => Ui i z * Ui i z
    let W (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => Ui i z * Phi z
    let V (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => H i z * Phi z
    let GradTest (j : Fin 3) : Vec3 × ℝ → ℝ :=
      fun z => spatialPartial Phi j z
    let TimeFlux (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => V i z
    let DiffFlux (i j : Fin 3) : Vec3 × ℝ → ℝ :=
      fun z => D i j z * W i z
    let TestGradientFlux (i j : Fin 3) : Vec3 × ℝ → ℝ :=
      fun z => H i z * GradTest j z
    let ConvFlux (i j : Fin 3) : Vec3 × ℝ → ℝ :=
      fun z => J j z * V i z
    let PressureFlux (i : Fin 3) : Vec3 × ℝ → ℝ :=
      fun z => (fun y : Vec3 × ℝ => p y) z * W i z
    let FluxResidual : Vec3 × ℝ → ℝ := fun z =>
      (∑ i : Fin 3, CKN.timePartialProd (TimeFlux i) z) -
        2 * (∑ i : Fin 3, ∑ j : Fin 3,
          CKN.spatialPartialProd (DiffFlux i j) j z) +
        (∑ i : Fin 3, ∑ j : Fin 3,
          CKN.spatialPartialProd (TestGradientFlux i j) j z) +
        (∑ i : Fin 3, ∑ j : Fin 3,
          CKN.spatialPartialProd (ConvFlux i j) j z) +
        2 * (∑ i : Fin 3,
          CKN.spatialPartialProd (PressureFlux i) i z)
    (∫ z in S, FluxResidual z ∂volume) = 0 := by
  let S : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)
  have hS : IsOpen S := isOpen_univ.prod isOpen_Ioi
  have hpull {F : ParabolicPoint → ℝ}
      (hF : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyLocalEnergyFlux
        ContinuousOn F (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) :
      ContinuousOn (fun z : Vec3 × ℝ => F z) S :=
    regUniform_continuousOn_pullback hF (fun z hz => ⟨Set.mem_univ _, hz.2⟩)
  let Ui (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => u z i
  let D (i j : Fin 3) : Vec3 × ℝ → ℝ :=
    fun z => spatialPartial (fun y => u y i) j z
  let J (i : Fin 3) : Vec3 × ℝ → ℝ :=
    fun z => regUniformMollifiedVelocity ρ ε hε u z i
  let H (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => Ui i z * Ui i z
  have hU (i : Fin 3) : ContinuousOn (Ui i) S := hpull (hUcont i)
  have hD (i j : Fin 3) : ContinuousOn (D i j) S := hpull (hDcont i j)
  have hDD (i j : Fin 3) : ContinuousOn (fun z : Vec3 × ℝ => spatialPartial (D i j) j z) S :=
    hpull (hDDcont i j j)
  have hDt (i : Fin 3) : ContinuousOn (fun z : Vec3 × ℝ => timePartial (Ui i) z) S :=
    hpull (hDtcont i)
  have hP : ContinuousOn (fun z : Vec3 × ℝ => p z) S := hpull hPcont
  have hDp (i : Fin 3) : ContinuousOn (fun z : Vec3 × ℝ => spatialPartial p i z) S :=
    hpull (hDpcont i)
  have hUd (i : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) :
      DifferentiableAt ℝ (fun x : Vec3 => Ui i (x, z.2)) z.1 :=
    regUniform_contDiffOn_spatialSlice_differentiableAt hS (hUcontDiff i) hz
  have hUtd (i : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) :
      DifferentiableAt ℝ (fun t : ℝ => Ui i (z.1, t)) z.2 :=
    regUniform_contDiffOn_timeSlice_differentiableAt hS (hUcontDiff i) hz
  have hDd (i j : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) :
      DifferentiableAt ℝ (fun x : Vec3 => D i j (x, z.2)) z.1 := hDdiff z hz i j
  have hJ := regUniform_mollified_velocity_continuousOn
    ρ ε hε (S := S) (fun t ht => hSliceL2 t (le_of_lt ht)) hUcontDiff
    (fun z hz => hz.2) (fun z hz y => ⟨Set.mem_univ _, hz.2⟩)
  have hDJ := regUniform_mollified_velocity_spatialPartial_continuousOn
    ρ ε hε (S := S) (fun t ht => hSliceL2 t (le_of_lt ht)) hUcontDiff
    (fun z hz => hz.2) (fun z hz y => ⟨Set.mem_univ _, hz.2⟩)
  have hJd (i : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) :
      DifferentiableAt ℝ (fun x : Vec3 => J i (x, z.2)) z.1 :=
    regUniform_mollified_spatial_slice_differentiableAt ρ ε hε u
      (hWeakDivFree z.2 (le_of_lt hz.2)) i
  have hH (i : Fin 3) : ContinuousOn (H i) S := (hU i).mul (hU i)
  have hDH (i j : Fin 3) : ContinuousOn (fun z : Vec3 × ℝ => spatialPartial (H i) j z) S :=
    regUniform_spatial_product_partial_continuousOn j
      (hU i) (hU i) (hD i j) (hD i j) (hUd i) (hUd i)
  have hDtH (i : Fin 3) : ContinuousOn (fun z : Vec3 × ℝ => timePartial (H i) z) S :=
    regUniform_time_product_partial_continuousOn
      (hU i) (hU i) (hDt i) (hDt i) (hUtd i) (hUtd i)
  have hHd (i : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) :
      DifferentiableAt ℝ (fun x : Vec3 => H i (x, z.2)) z.1 :=
    (hUd i z hz).mul (hUd i z hz)
  have hDHdiff (i j : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial (fun y => D i j y * Ui i y) j z) S :=
    regUniform_spatial_product_partial_continuousOn j
      (hD i j) (hU i) (hDD i j) (hD i j) (hDd i j) (hUd i)
  have hDHconv (i j : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial (fun y => J j y * H i y) j z) S :=
    regUniform_spatial_product_partial_continuousOn j
      (hJ j) (hH i) (hDJ j j) (hDH i j) (hJd j) (hHd i)
  have hDHpressure (i : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial (fun y => p y * Ui i y) i z) S :=
    regUniform_spatial_product_partial_continuousOn i
      hP (hU i) (hDp i) (hD i i) (fun z hz => hPdiff z hz) (hUd i)
  have hTimeInt (i : Fin 3) := regUniform_localized_time_flux_integrable hS
    (hH i) (hDtH i) (fun z hz => (hUtd i z hz).mul (hUtd i z hz)) hψ
  have hTimeZero (i : Fin 3) := regUniform_localized_time_flux_integral_zero hS
    (hH i) (hDtH i) (fun z hz => (hUtd i z hz).mul (hUtd i z hz)) hψ
  have hDiffInt (i j : Fin 3) := regUniform_localized_spatial_flux_integrable j hS
    ((hD i j).mul (hU i)) (hDHdiff i j)
    (fun z hz => (hDd i j z hz).mul (hUd i z hz)) hψ
  have hDiffZero (i j : Fin 3) := regUniform_localized_spatial_flux_integral_zero j hS
    ((hD i j).mul (hU i)) (hDHdiff i j)
    (fun z hz => (hDd i j z hz).mul (hUd i z hz)) hψ
  have hGradInt (i j : Fin 3) := regUniform_localized_spatial_flux_integrable j hS
    (hH i) (hDH i j) (hHd i) (regUniform_spatial_test_derivative_mem hψ j)
  have hGradZero (i j : Fin 3) := regUniform_localized_spatial_flux_integral_zero j hS
    (hH i) (hDH i j) (hHd i) (regUniform_spatial_test_derivative_mem hψ j)
  have hConvInt (i j : Fin 3) := regUniform_localized_spatial_flux_integrable j hS
    ((hJ j).mul (hH i)) (hDHconv i j)
    (fun z hz => (hJd j z hz).mul (hHd i z hz)) hψ
  have hConvZero (i j : Fin 3) := regUniform_localized_spatial_flux_integral_zero j hS
    ((hJ j).mul (hH i)) (hDHconv i j)
    (fun z hz => (hJd j z hz).mul (hHd i z hz)) hψ
  have hPressureInt (i : Fin 3) := regUniform_localized_spatial_flux_integrable i hS
    (hP.mul (hU i)) (hDHpressure i)
    (fun z hz => (hPdiff z hz).mul (hUd i z hz)) hψ
  have hPressureZero (i : Fin 3) := regUniform_localized_spatial_flux_integral_zero i hS
    (hP.mul (hU i)) (hDHpressure i)
    (fun z hz => (hPdiff z hz).mul (hUd i z hz)) hψ
  convert
    regUniform_integral_finite_flux_sum_zero S volume
      (fun i z => timePartial (fun y => H i y * ψ y) z)
      (fun i j z => spatialPartial (fun y => (D i j y * Ui i y) * ψ y) j z)
      (fun i j z => spatialPartial (fun y => H i y * spatialPartial ψ j y) j z)
      (fun i j z => spatialPartial (fun y => (J j y * H i y) * ψ y) j z)
      (fun i z => spatialPartial (fun y => (p y * Ui i y) * ψ y) i z)
      hTimeInt hDiffInt hGradInt hConvInt hPressureInt
      hTimeZero hDiffZero hGradZero hConvZero hPressureZero using 1
  simp only [CKN.timePartialProd, CKN.spatialPartialProd, S, Ui, D, J, H, mul_assoc]
  apply integral_congr_ae
  filter_upwards [] with z
  congr 1

end CKN.Leray

end
