/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformMomentum
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformIntegrationByParts
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformLocalEnergyFlux
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationBasics

/-!
# Reg Uniform Local Energy

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open scoped Topology ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

abbrev regUniformParabolicTopologyLocalEnergy : TopologicalSpace ParabolicPoint :=
  inferInstance

local instance regUniformLocalEnergyNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

local instance regUniformLocalEnergyNormedSpace : NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))

local instance (priority := 10000) regUniformLocalEnergyTopologicalSpace :
    TopologicalSpace ParabolicPoint :=
  instTopologicalSpaceProd

private def regUniformSpatialGradientDensity
    (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3)
    (z : Vec3 × ℝ) : ℝ :=
  spatialGradientSq u Du ((z.1, z.2) : ParabolicPoint)

/-- The pointwise regularized equation (R3) gives the local energy identity
in `lem:reg-local-energy`. -/
theorem regUniform_local_energy_identity
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (hSliceL2 : ∀ t : ℝ, 0 ≤ t →
      MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hWeakDivFree : ∀ t : ℝ, 0 ≤ t →
      CKN.IsWeakDivFreeL2 (fun x : Vec3 => u (x, t)))
    (hUcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyLocalEnergy
      ∀ i : Fin 3, ContinuousOn (fun z => u z i)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyLocalEnergy
      ∀ i j : Fin 3, ContinuousOn
        (fun z => spatialPartial (fun y => u y i) j z)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDDcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyLocalEnergy
      ∀ i j k : Fin 3, ContinuousOn
        (fun z => spatialPartial
          (fun y => spatialPartial (fun x => u x i) j y) k z)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDtcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyLocalEnergy
      ∀ i : Fin 3, ContinuousOn
        (fun z => timePartial (fun y => u y i) z)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hPcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyLocalEnergy
      ContinuousOn p (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDpcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyLocalEnergy
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
    (hEquation : ∀ z : ParabolicPoint, 0 < z.2 → ∀ i : Fin 3,
      timePartial (fun y => u y i) z -
        (∑ j : Fin 3, spatialPartial
          (fun y => spatialPartial (fun x => u x i) j y) j z) +
        (∑ j : Fin 3, regUniformMollifiedVelocity ρ ε hε u z j *
          spatialPartial (fun y => u y i) j z) +
        spatialPartial (fun y => p y) i z = 0)
    (ψ : ParabolicPoint → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ)
      (Set.univ : Set Vec3) (Ioi 0)) :
    2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        spatialGradientSq u
          (fun z i j => spatialPartial (fun y => u y i) j z) z * ψ z =
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        (vec3EuclideanNorm (u z)) ^ (2 : ℕ) *
            (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z) +
          ∑ i : Fin 3,
            ((vec3EuclideanNorm (u z)) ^ (2 : ℕ) *
                regUniformMollifiedVelocity ρ ε hε u z i +
              2 * p z * u z i) * spatialPartial ψ i z := by
  let S : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)
  let Smetric : Set ParabolicPoint :=
    spaceTimeSet (Set.univ : Set Vec3) (Ioi (0 : ℝ))
  have hSopen : IsOpen S := isOpen_univ.prod isOpen_Ioi
  have hSmeas : MeasurableSet S :=
    MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi
  have hSsymm : ∀ z ∈ S, ((z.1, z.2) : ParabolicPoint) ∈ Smetric := by
    intro z hz
    exact ⟨Set.mem_univ _, hz.2⟩
  let Ui (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => u z i
  let D (i j : Fin 3) : Vec3 × ℝ → ℝ :=
    fun z => spatialPartial (fun y => u y i) j z
  let DD (i j k : Fin 3) : Vec3 × ℝ → ℝ :=
    fun z => spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z
  let Dt (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => timePartial (fun y => u y i) z
  let Dp (i : Fin 3) : Vec3 × ℝ → ℝ :=
    fun z => spatialPartial (fun y => p y) i z
  let J (i : Fin 3) : Vec3 × ℝ → ℝ :=
    fun z => regUniformMollifiedVelocity ρ ε hε u z i
  let Phi : Vec3 × ℝ → ℝ := fun z => ψ z
  let H (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => Ui i z * Ui i z
  let W (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => Ui i z * Phi z
  let V (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => H i z * Phi z
  let GradTest (j : Fin 3) : Vec3 × ℝ → ℝ :=
    fun z => spatialPartial (Phi) j z
  let TimeFlux (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => V i z
  let DiffFlux (i j : Fin 3) : Vec3 × ℝ → ℝ :=
    fun z => D i j z * W i z
  let TestGradientFlux (i j : Fin 3) : Vec3 × ℝ → ℝ :=
    fun z => H i z * GradTest j z
  let ConvFlux (i j : Fin 3) : Vec3 × ℝ → ℝ :=
    fun z => J j z * V i z
  let PressureFlux (i : Fin 3) : Vec3 × ℝ → ℝ :=
    fun z => (fun y : Vec3 × ℝ => p y) z * W i z
  have hDui (i j : Fin 3) (z : Vec3 × ℝ) : D i j z = spatialPartial (Ui i) j z := rfl
  have hDtUi (i : Fin 3) (z : Vec3 × ℝ) : Dt i z = timePartial (Ui i) z := rfl
  have hPhiCont : ContinuousOn Phi S := by
    change ContinuousOn (show ParabolicPoint → ℝ from ψ) S
    exact (show Continuous (show ParabolicPoint → ℝ from ψ) from
      hψ.1.continuous).continuousOn
  have hPhiTimeCont : ContinuousOn
      (fun z : Vec3 × ℝ => timePartial (Phi) z) S := by
    change ContinuousOn (fun z : Vec3 × ℝ => timePartial ψ z) S
    exact (CKN.Core.Step3.timePartial_contDiff_full hψ.1).continuous.continuousOn
  have hPhiSpaceCont (j : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial (Phi) j z) S := by
    change ContinuousOn (fun z : Vec3 × ℝ => spatialPartial ψ j z) S
    exact (spatialPartial_contDiff hψ.1 j).continuous.continuousOn
  have hPhiSpaceCompact (j : Fin 3) : HasCompactSupport
      (fun z : Vec3 × ℝ => spatialPartial (Phi) j z) := by
    change HasCompactSupport (fun z : Vec3 × ℝ => spatialPartial ψ j z)
    exact CKN.hasCompactSupport_spatialPartial hψ.2.1 j
  have hPhiSpaceSupport (j : Fin 3) : tsupport
      (fun z : Vec3 × ℝ => spatialPartial (Phi) j z) ⊆ S := by
    change tsupport (fun z : Vec3 × ℝ => spatialPartial ψ j z) ⊆ S
    exact CKN.tsupport_spatialPartial_subset j |>.trans hψ.2.2
  have hU (i : Fin 3) : ContinuousOn (Ui i) S := by
    simpa [Ui] using regUniform_continuousOn_pullback (hUcont i) hSsymm
  have hD (i j : Fin 3) : ContinuousOn (D i j) S := by
    simpa [D] using regUniform_continuousOn_pullback (hDcont i j) hSsymm
  have hP : ContinuousOn (fun z : Vec3 × ℝ => p z) S := by
    exact regUniform_continuousOn_pullback hPcont hSsymm
  have hJcontMetric := regUniform_mollified_velocity_continuousOn
    ρ ε hε (S := S) (fun t ht => hSliceL2 t (le_of_lt ht))
    hUcontDiff (fun z hz => hz.2)
      (fun z hz y => ⟨Set.mem_univ _, hz.2⟩)
  have hJ (i : Fin 3) : ContinuousOn (J i) S := by simpa [J] using hJcontMetric i
  have hJdiv (z : Vec3 × ℝ) (hz : z ∈ S) :
      ∑ j : Fin 3, spatialPartial (J j) j z = 0 := by
    change ∑ j : Fin 3,
      spatialPartial (fun y => regUniformMollifiedVelocity ρ ε hε u y j) j z = 0
    exact regUniform_mollified_velocity_divergence_eq_zero ρ ε hε u z.2
      (hWeakDivFree z.2 (le_of_lt hz.2)) z.1
  have hUiSpatialDiff (z : Vec3 × ℝ) (hz : z ∈ S) (i : Fin 3) : DifferentiableAt ℝ (fun x : Vec3 => Ui i (x, z.2)) z.1 := regUniform_contDiffOn_spatialSlice_differentiableAt hSopen (hUcontDiff i) hz
  have hUiTimeDiff (z : Vec3 × ℝ) (hz : z ∈ S) (i : Fin 3) : DifferentiableAt ℝ (fun t : ℝ => Ui i (z.1, t)) z.2 := regUniform_contDiffOn_timeSlice_differentiableAt hSopen (hUcontDiff i) hz
  have hDdiff' (z : Vec3 × ℝ) (hz : z ∈ S) (i j : Fin 3) : DifferentiableAt ℝ (fun x : Vec3 => D i j (x, z.2)) z.1 := by simpa [D] using hDdiff z hz i j
  have hPdiff' (z : Vec3 × ℝ) (hz : z ∈ S) : DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1 := hPdiff z hz
  have hPhiSpatialDiff (z : Vec3 × ℝ) (hz : z ∈ S) : DifferentiableAt ℝ (fun x : Vec3 => Phi (x, z.2)) z.1 := regUniform_contDiffOn_spatialSlice_differentiableAt hSopen ((hψ.1.of_le (by norm_num)).contDiffOn) hz
  have hPhiTimeDiff (z : Vec3 × ℝ) (hz : z ∈ S) : DifferentiableAt ℝ (fun t : ℝ => Phi (z.1, t)) z.2 := regUniform_contDiffOn_timeSlice_differentiableAt hSopen ((hψ.1.of_le (by norm_num)).contDiffOn) hz
  have hJdiff (z : Vec3 × ℝ) (hz : z ∈ S) (i : Fin 3) :
      DifferentiableAt ℝ (fun x : Vec3 => J i (x, z.2)) z.1 := by
    let aₜ : Vec3 → Vec3 := fun x => u (x, z.2)
    have haₜ : CKN.IsInJ aₜ :=
      CKN.weakDivFreeL2_isInJ (hWeakDivFree z.2 (le_of_lt hz.2))
    have hsmooth := regUniformMollifiedInitial_contDiff ρ ε hε haₜ
    have hcoord : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec3 => regUniformMollifiedInitial ρ ε hε aₜ x i) := by
      exact hsmooth.continuousLinearMap_comp
        (ContinuousLinearMap.proj (R := ℝ) i)
    have heq : (fun x : Vec3 => J i (x, z.2)) =
        fun x => regUniformMollifiedInitial ρ ε hε aₜ x i := by
      funext x
      rfl
    rw [heq]
    exact hcoord.differentiable (by norm_num) z.1
  have hDivU (z : Vec3 × ℝ) (hz : z ∈ S) :
      ∑ i : Fin 3, D i i z = 0 := by
    let aₜ : Vec3 → Vec3 := fun x => u (x, z.2)
    have hC1 : ∀ i : Fin 3, ContDiff ℝ 1 (fun x : Vec3 => aₜ x i) := by
      intro i
      have hslice : ContDiffOn ℝ 1 (fun x : Vec3 => aₜ x i) Set.univ := by
        exact (hUcontDiff i).comp (by fun_prop) (by
          intro x hx
          exact ⟨Set.mem_univ _, hz.2⟩)
      exact contDiffOn_univ.mp hslice
    have hdiv := regUniform_weakDivFree_contDiff_divergence_eq_zero hC1
      (hWeakDivFree z.2 (le_of_lt hz.2)) z.1
    simpa [D, aₜ, spatialPartial] using hdiv
  have hEquationProd (z : Vec3 × ℝ) (hz : z ∈ S) (i : Fin 3) :
      Dt i z - (∑ j : Fin 3, DD i j j z) +
        (∑ j : Fin 3, J j z * D i j z) + Dp i z = 0 := by
    have h := hEquation ((z.1, z.2) : ParabolicPoint) hz.2 i
    simpa [Dt, DD, D, Dp, J] using h
  have hHspatial (i j : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) :
      spatialPartial (show ParabolicPoint → ℝ from H i) j z =
        2 * Ui i z * D i j z := by
    change spatialPartial
        (fun y : Vec3 × ℝ => Ui i y * Ui i y) j z = _
    calc
      _ = Ui i z * spatialPartial (Ui i) j z +
            Ui i z * spatialPartial (Ui i) j z :=
        regUniform_spatialPartial_mul z.1 z.2 j
          (hUiSpatialDiff z hz i) (hUiSpatialDiff z hz i)
      _ = 2 * Ui i z * spatialPartial (Ui i) j z := by ring
      _ = 2 * Ui i z * D i j z := by rw [← hDui i j z]
  have hHtime (i : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) :
      timePartial (show ParabolicPoint → ℝ from H i) z =
        2 * Ui i z * Dt i z := by
    change timePartial
        (fun y : Vec3 × ℝ => Ui i y * Ui i y) z = _
    calc
      _ = Ui i z * timePartial (Ui i) z +
            Ui i z * timePartial (Ui i) z :=
        regUniform_timePartial_mul z.1 z.2
          (hUiTimeDiff z hz i) (hUiTimeDiff z hz i)
      _ = 2 * Ui i z * timePartial (Ui i) z := by ring
      _ = 2 * Ui i z * Dt i z := by rw [← hDtUi i z]
  have hHdiff (i : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) (j : Fin 3) :
      DifferentiableAt ℝ (fun x : Vec3 => H i (x, z.2)) z.1 := by
    change DifferentiableAt ℝ
      (fun x : Vec3 => Ui i (x, z.2) * Ui i (x, z.2)) z.1
    exact (hUiSpatialDiff z hz i).mul (hUiSpatialDiff z hz i)
  have hHcont (i : Fin 3) : ContinuousOn (H i) S := (hU i).mul (hU i)
  have hWpartial (i j : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) :
      CKN.spatialPartialProd (W i) j z =
        Ui i z * spatialPartial Phi j z + Phi z * D i j z := by
    change spatialPartial
        (fun y : Vec3 × ℝ => Ui i y * Phi y) j z = _
    calc
      _ = Ui i z * spatialPartial Phi j z +
            Phi z * spatialPartial (Ui i) j z :=
        regUniform_spatialPartial_mul z.1 z.2 j
          (hUiSpatialDiff z hz i) (hPhiSpatialDiff z hz)
      _ = Ui i z * spatialPartial Phi j z + Phi z * D i j z := by
        rw [← hDui i j z]
  have hWdiff (i : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) (j : Fin 3) :
      DifferentiableAt ℝ (fun x : Vec3 => W i (x, z.2)) z.1 := by
    change DifferentiableAt ℝ
      (fun x : Vec3 => Ui i (x, z.2) * Phi (x, z.2)) z.1
    exact (hUiSpatialDiff z hz i).mul (hPhiSpatialDiff z hz)
  have hVpartial (i j : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) :
      CKN.spatialPartialProd (V i) j z =
        2 * Ui i z * D i j z * Phi z + H i z * spatialPartial Phi j z := by
    change spatialPartial
        (show ParabolicPoint → ℝ from fun y => H i y * Phi y) j
          ((z.1, z.2) : ParabolicPoint) = _
    rw [regUniform_spatialPartial_mul z.1 z.2 j
      (hHdiff i z hz j) (hPhiSpatialDiff z hz)]
    rw [hHspatial i j z hz]
    ring
  have hVdiff (i : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) (j : Fin 3) :
      DifferentiableAt ℝ (fun x : Vec3 => V i (x, z.2)) z.1 := by
    change DifferentiableAt ℝ
      (fun x : Vec3 => H i (x, z.2) * Phi (x, z.2)) z.1
    exact (hHdiff i z hz j).mul (hPhiSpatialDiff z hz)
  have hPhiSecondCont (j : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial (GradTest j) j z) S := by
    have hsmooth := CKN.Core.Step3.spatialSecondPartial_contDiff_full hψ.1 j j
    change ContinuousOn
      (fun z : Vec3 × ℝ => spatialSecondPartial ψ j j z) S
    exact hsmooth.continuous.continuousOn
  have hPhiSecondDiff (z : Vec3 × ℝ) (hz : z ∈ S) (j : Fin 3) :
      DifferentiableAt ℝ (fun x : Vec3 => GradTest j (x, z.2)) z.1 := by
    have hsmooth := spatialPartial_contDiff hψ.1 j
    exact regUniform_contDiffOn_spatialSlice_differentiableAt hSopen
      (hsmooth.of_le (by norm_num)).contDiffOn hz
  have hHtimeDiff (i : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) :
      DifferentiableAt ℝ (fun t : ℝ => H i (z.1, t)) z.2 := by
    change DifferentiableAt ℝ
      (fun t : ℝ => Ui i (z.1, t) * Ui i (z.1, t)) z.2
    exact (hUiTimeDiff z hz i).mul (hUiTimeDiff z hz i)
  have hVtime (i : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) :
      CKN.timePartialProd (TimeFlux i) z =
        CKN.timePartialProd (H i) z * Phi z +
          H i z * CKN.timePartialProd Phi z := by
    change timePartial
      (show ParabolicPoint → ℝ from fun y => H i y * Phi y)
      ((z.1, z.2) : ParabolicPoint) = _
    simpa [CKN.timePartialProd, add_comm, mul_comm, mul_left_comm, mul_assoc] using
      regUniform_timePartial_mul z.1 z.2
        (hHtimeDiff i z hz) (hPhiTimeDiff z hz)
  have hDiffFluxPartial (i j : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) :
      CKN.spatialPartialProd (DiffFlux i j) j z =
        spatialPartial (D i j) j z * W i z +
          D i j z * CKN.spatialPartialProd (W i) j z := by
    change spatialPartial
        (show ParabolicPoint → ℝ from fun y => D i j y * W i y) j
          ((z.1, z.2) : ParabolicPoint) = _
    simpa [CKN.spatialPartialProd, add_comm, mul_comm, mul_left_comm, mul_assoc] using
      regUniform_spatialPartial_mul z.1 z.2 j
        (hDdiff' z hz i j) (hWdiff i z hz j)
  have hTestGradientFluxPartial (i j : Fin 3)
      (z : Vec3 × ℝ) (hz : z ∈ S) :
      CKN.spatialPartialProd (TestGradientFlux i j) j z =
        CKN.spatialPartialProd (H i) j z * GradTest j z +
          H i z * CKN.spatialPartialProd (GradTest j) j z := by
    change spatialPartial
        (show ParabolicPoint → ℝ from fun y => H i y * GradTest j y) j
          ((z.1, z.2) : ParabolicPoint) = _
    simpa [CKN.spatialPartialProd, add_comm, mul_comm, mul_left_comm, mul_assoc] using
      regUniform_spatialPartial_mul z.1 z.2 j
        (hHdiff i z hz j) (hPhiSecondDiff z hz j)
  have hConvFluxPartial (i j : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) :
      CKN.spatialPartialProd (ConvFlux i j) j z =
        spatialPartial (J j) j z * V i z +
          J j z * CKN.spatialPartialProd (V i) j z := by
    change spatialPartial
        (show ParabolicPoint → ℝ from fun y => J j y * V i y) j
          ((z.1, z.2) : ParabolicPoint) = _
    simpa [CKN.spatialPartialProd, add_comm, mul_comm, mul_left_comm, mul_assoc] using
      regUniform_spatialPartial_mul z.1 z.2 j
        (hJdiff z hz j) (hVdiff i z hz j)
  have hPressureFluxPartial (i : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) :
      CKN.spatialPartialProd (PressureFlux i) i z =
        Dp i z * W i z +
          (fun y : Vec3 × ℝ => p y) z *
            CKN.spatialPartialProd (W i) i z := by
    change spatialPartial
        (show ParabolicPoint → ℝ from fun y => p y * W i y) i
          ((z.1, z.2) : ParabolicPoint) = _
    simpa [CKN.spatialPartialProd, add_comm, mul_comm, mul_left_comm, mul_assoc] using
      regUniform_spatialPartial_mul z.1 z.2 i
        (hPdiff' z hz) (hWdiff i z hz i)
  let HeatTest : Vec3 × ℝ → ℝ := fun z => CKN.timePartialProd Phi z +
    ∑ i : Fin 3, CKN.spatialPartialProd (GradTest i) i z
  let EnergyResidual : Vec3 × ℝ → ℝ := fun z =>
    2 * regUniformSpatialGradientDensity u
        (fun z i j => spatialPartial (fun y => u y i) j z) z * Phi z -
      vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ) * HeatTest z -
      ∑ i : Fin 3,
        (vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ) * J i z +
          2 * p (z.1, z.2) * Ui i z) * GradTest i z
  let FluxResidual : Vec3 × ℝ → ℝ := fun z =>
    (∑ i : Fin 3, CKN.timePartialProd (TimeFlux i) z) -
      2 * ∑ i : Fin 3, ∑ j : Fin 3, CKN.spatialPartialProd (DiffFlux i j) j z +
      ∑ i : Fin 3, ∑ j : Fin 3, CKN.spatialPartialProd (TestGradientFlux i j) j z +
      ∑ i : Fin 3, ∑ j : Fin 3, CKN.spatialPartialProd (ConvFlux i j) j z +
      2 * ∑ i : Fin 3, CKN.spatialPartialProd (PressureFlux i) i z
  have hHeatTestCont : ContinuousOn HeatTest S := by
    change ContinuousOn (fun z : Vec3 × ℝ => timePartial Phi z +
      ∑ i : Fin 3, spatialPartial (GradTest i) i z) S
    exact hPhiTimeCont.add
      (continuousOn_finsetSum Finset.univ fun i hi => hPhiSecondCont i)
  have hHeatTestSupport' : tsupport HeatTest ⊆ tsupport Phi := by
    refine closure_minimal ?_ (isClosed_tsupport Phi)
    intro z hz
    by_contra hnot
    apply hz
    have ht := timePartial_eq_zero_off_tsupport hnot
    have hss (i : Fin 3) : spatialPartial (GradTest i) i z = 0 := by
      change spatialSecondPartial Phi i i z = 0
      exact spatialSecondPartial_eq_zero_off_tsupport hnot i i
    change timePartial Phi z +
      ∑ i : Fin 3, spatialPartial (GradTest i) i z = 0
    rw [ht]
    simp [hss]
  have hHeatTestSupport : tsupport HeatTest ⊆ S :=
    hHeatTestSupport'.trans hψ.2.2
  have hHeatTestCompact : HasCompactSupport HeatTest := by
    exact hψ.2.1.isCompact.of_isClosed_subset
      (isClosed_tsupport _) hHeatTestSupport'
  have hEnergyDensityCont : ContinuousOn
      (fun z : Vec3 × ℝ => spatialGradientSq u
        (fun z i j => spatialPartial (fun y => u y i) j z)
        ((z.1, z.2) : ParabolicPoint)) S := by
    change ContinuousOn (fun z : Vec3 × ℝ =>
      ∑ i : Fin 3, ∑ j : Fin 3, (D i j z) ^ (2 : ℕ)) S
    exact continuousOn_finsetSum Finset.univ fun i hi =>
      continuousOn_finsetSum Finset.univ fun j hj => (hD i j).pow 2
  have hNormSqCont : ContinuousOn
      (fun z : Vec3 × ℝ => vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ)) S := by
    apply ContinuousOn.congr (continuousOn_finsetSum Finset.univ
      fun i hi => hHcont i)
    intro z hz
    change (Real.sqrt (∑ i : Fin 3, (u (z.1, z.2) i) ^ (2 : ℕ))) ^ (2 : ℕ) = _
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i hi => sq_nonneg (u (z.1, z.2) i))]
    simp [H, Ui, pow_two]
  have hHeatInt : Integrable (fun z : Vec3 × ℝ =>
      vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ) * HeatTest z) volume :=
    regUniform_integrable_mul_of_tsupport_subset hSopen hNormSqCont
      hHeatTestCont hHeatTestCompact hHeatTestSupport
  have hFluxCoeffCont (i : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ =>
        vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ) * J i z +
          2 * p (z.1, z.2) * Ui i z) S := by
    apply ContinuousOn.congr
      ((hNormSqCont.mul (hJ i)).add ((hP.mul (hU i)).const_mul 2))
    intro z hz
    cases z
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  have hFluxTermInt (i : Fin 3) : Integrable
      (fun z : Vec3 × ℝ =>
        (vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ) * J i z +
          2 * p (z.1, z.2) * Ui i z) * GradTest i z) volume :=
    regUniform_integrable_mul_of_tsupport_subset hSopen
      (hFluxCoeffCont i) (hPhiSpaceCont i) (hPhiSpaceCompact i)
      (hPhiSpaceSupport i)
  have hBaseInt : Integrable (fun z : Vec3 × ℝ => spatialGradientSq u
        (fun z i j => spatialPartial (fun y => u y i) j z)
        ((z.1, z.2) : ParabolicPoint) * Phi z) (volume.restrict S) :=
    (regUniform_integrable_mul_of_tsupport_subset (S := S) hSopen
      hEnergyDensityCont hPhiCont (hψ.2.1) hψ.2.2).mono_measure
        Measure.restrict_le_self
  have hLeftInt : Integrable (fun z : Vec3 × ℝ =>
      2 * (spatialGradientSq u
        (fun z i j => spatialPartial (fun y => u y i) j z)
        ((z.1, z.2) : ParabolicPoint) * Phi z)) (volume.restrict S) :=
    hBaseInt.const_mul 2
  have hRightInt : Integrable (fun z : Vec3 × ℝ =>
      vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ) * HeatTest z +
        ∑ i : Fin 3,
          (vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ) * J i z +
            2 * p (z.1, z.2) * Ui i z) * GradTest i z)
      (volume.restrict S) := by
    apply (hHeatInt.mono_measure Measure.restrict_le_self).add
    exact integrable_finsetSum Finset.univ fun i hi =>
      (hFluxTermInt i).mono_measure Measure.restrict_le_self
  have hFluxZero : (∫ z in S, FluxResidual z ∂volume) = 0 := by
    simpa [S] using (regUniform_local_energy_flux_integral_zero ρ ε hε u p
      hSliceL2 hWeakDivFree hUcont hDcont hDDcont hDtcont hPcont hDpcont
      hUcontDiff hDdiff hPdiff ψ hψ)
  have hNormSqFormula (z : Vec3 × ℝ) :
      vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ) = ∑ i : Fin 3, H i z := by
    change (Real.sqrt (∑ i : Fin 3, (u (z.1, z.2) i) ^ (2 : ℕ))) ^ (2 : ℕ) = _
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i hi => sq_nonneg (u (z.1, z.2) i))]
    simp [H, Ui, pow_two]
  have hWeightedZero (z : Vec3 × ℝ) (hz : z ∈ S) :
      ∑ i : Fin 3, 2 * W i z *
        (Dt i z - (∑ j : Fin 3, DD i j j z) +
          (∑ j : Fin 3, J j z * D i j z) + Dp i z) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hEquationProd z hz i]
    ring
  have hEnergyGradient (z : Vec3 × ℝ) :
      regUniformSpatialGradientDensity u
        (fun z i j => spatialPartial (fun y => u y i) j z)
        z =
        ∑ i : Fin 3, ∑ j : Fin 3, (D i j z) ^ (2 : ℕ) := by
    unfold regUniformSpatialGradientDensity CKN.spatialGradientSq
    rfl
  have hDsecond (z : Vec3 × ℝ) (i j : Fin 3) : spatialPartial (D i j) j z = DD i j j z := rfl
  have hFluxExpansion (z : Vec3 × ℝ) (hz : z ∈ S) :
      (∑ i : Fin 3, 2 * W i z *
        (Dt i z - (∑ j : Fin 3, DD i j j z) +
          (∑ j : Fin 3, J j z * D i j z) + Dp i z)) =
        FluxResidual z + EnergyResidual z := by
    change (∑ i : Fin 3, 2 * W i z *
        (Dt i z - (∑ j : Fin 3, DD i j j z) +
          (∑ j : Fin 3, J j z * D i j z) + Dp i z)) =
      ((∑ i : Fin 3, CKN.timePartialProd (TimeFlux i) z) -
        2 * (∑ i : Fin 3, ∑ j : Fin 3,
          CKN.spatialPartialProd (DiffFlux i j) j z) +
        (∑ i : Fin 3, ∑ j : Fin 3,
          CKN.spatialPartialProd (TestGradientFlux i j) j z) +
        (∑ i : Fin 3, ∑ j : Fin 3,
          CKN.spatialPartialProd (ConvFlux i j) j z) +
        2 * (∑ i : Fin 3,
          CKN.spatialPartialProd (PressureFlux i) i z)) +
      (2 * regUniformSpatialGradientDensity u
          (fun z i j => spatialPartial (fun y => u y i) j z) z * Phi z -
        vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ) * HeatTest z -
        ∑ i : Fin 3,
          (vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ) * J i z +
            2 * p (z.1, z.2) * Ui i z) * GradTest i z)
    have hHspatialProd (i j : Fin 3) :
        CKN.spatialPartialProd (H i) j z = 2 * Ui i z * D i j z := by
      change spatialPartial (show ParabolicPoint → ℝ from H i) j z = _
      exact hHspatial i j z hz
    have hHtimeProd (i : Fin 3) :
        CKN.timePartialProd (H i) z = 2 * Ui i z * Dt i z := by
      change timePartial (show ParabolicPoint → ℝ from H i) z = _
      exact hHtime i z hz
    have hTimeExpand :
        (∑ i : Fin 3, CKN.timePartialProd (TimeFlux i) z) =
          ∑ i : Fin 3, (2 * Ui i z * Dt i z * Phi z +
            H i z * CKN.timePartialProd Phi z) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hVtime i z hz, hHtimeProd i]
    have hDiffExpand :
        (∑ i : Fin 3, ∑ j : Fin 3,
          CKN.spatialPartialProd (DiffFlux i j) j z) =
          ∑ i : Fin 3, ∑ j : Fin 3,
          (spatialPartial (D i j) j z * W i z +
              D i j z * (Ui i z * GradTest j z + Phi z * D i j z)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hDiffFluxPartial i j z hz, hWpartial i j z hz]
    have hTestExpand :
        (∑ i : Fin 3, ∑ j : Fin 3,
          CKN.spatialPartialProd (TestGradientFlux i j) j z) =
          ∑ i : Fin 3, ∑ j : Fin 3,
            (2 * Ui i z * D i j z * GradTest j z +
              H i z * CKN.spatialPartialProd (GradTest j) j z) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hTestGradientFluxPartial i j z hz, hHspatialProd i]
    have hConvExpand :
        (∑ i : Fin 3, ∑ j : Fin 3,
          CKN.spatialPartialProd (ConvFlux i j) j z) =
          ∑ i : Fin 3, ∑ j : Fin 3,
            (spatialPartial (J j) j z * V i z +
              J j z * (2 * Ui i z * D i j z * Phi z +
                H i z * GradTest j z)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hConvFluxPartial i j z hz, hVpartial i j z hz]
    have hPressureExpand :
        (∑ i : Fin 3, CKN.spatialPartialProd (PressureFlux i) i z) =
          ∑ i : Fin 3,
            (Dp i z * W i z +
              p (z.1, z.2) * (Ui i z * GradTest i z + Phi z * D i i z)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hPressureFluxPartial i z hz, hWpartial i i z hz]
    rw [hTimeExpand, hDiffExpand, hTestExpand, hConvExpand, hPressureExpand]
    have hConvDivZero :
        (∑ i : Fin 3, ∑ j : Fin 3,
          spatialPartial (J j) j z * V i z) = 0 := by
      calc
        _ = ∑ j : Fin 3, (∑ i : Fin 3, V i z) *
            spatialPartial (J j) j z := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j hj
          rw [← Finset.mul_sum]
          ring
        _ = (∑ i : Fin 3, V i z) *
            ∑ j : Fin 3, spatialPartial (J j) j z := by
          rw [← Finset.mul_sum]
        _ = 0 := by rw [hJdiv z hz]; simp
    have hPressureDivZero :
        (∑ i : Fin 3, p (z.1, z.2) * (Phi z * D i i z)) = 0 := by
      calc
        _ = ∑ i : Fin 3, (p (z.1, z.2) * Phi z) * D i i z := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (p (z.1, z.2) * Phi z) * ∑ i : Fin 3, D i i z := by
          rw [← Finset.mul_sum]
        _ = 0 := by rw [hDivU z hz]; ring
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [hConvDivZero, hPressureDivZero]
    simp_rw [hDsecond z]
    rw [hEnergyGradient z, hNormSqFormula z]
    have hTestLaplacian :
        (∑ i : Fin 3, ∑ j : Fin 3,
          H i z * CKN.spatialPartialProd (GradTest j) j z) =
        ∑ i : Fin 3, H i z *
          ∑ j : Fin 3, CKN.spatialPartialProd (GradTest j) j z := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.mul_sum]
    have hPressureGradient :
        (∑ i : Fin 3, ∑ j : Fin 3,
          J j z * (H i z * GradTest j z)) =
        ∑ i : Fin 3, (∑ j : Fin 3, H j z * J i z) * GradTest i z := by
      calc
        _ = ∑ j : Fin 3, ∑ i : Fin 3,
            J j z * (H i z * GradTest j z) := by rw [Finset.sum_comm]
        _ = ∑ j : Fin 3, ∑ i : Fin 3,
            H i z * J j z * GradTest j z := by
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = ∑ j : Fin 3, (∑ i : Fin 3, H i z * J j z) *
            GradTest j z := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_mul]
        _ = ∑ i : Fin 3, (∑ j : Fin 3, H j z * J i z) *
            GradTest i z := by rfl
    simp only [HeatTest]
    rw [hTestLaplacian, hPressureGradient]
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    have hDiffSum :
        (∑ i : Fin 3, 2 * W i z * ∑ j : Fin 3, DD i j j z) =
          2 * ∑ i : Fin 3, ∑ j : Fin 3, DD i j j z * W i z := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have hConvSum :
        (∑ i : Fin 3, 2 * W i z * ∑ j : Fin 3, J j z * D i j z) =
          2 * ∑ i : Fin 3, ∑ j : Fin 3,
            J j z * Ui i z * D i j z * Phi z := by
      simp only [W]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have hGradientSum :
        (2 * (∑ i : Fin 3, ∑ j : Fin 3, D i j z ^ 2)) * Phi z =
          2 * ∑ i : Fin 3, ∑ j : Fin 3, Phi z * D i j z ^ 2 := by
      calc
        _ = 2 * ((∑ i : Fin 3, ∑ j : Fin 3, D i j z ^ 2) * Phi z) := by ring
        _ = 2 * (∑ i : Fin 3, ∑ j : Fin 3, Phi z * D i j z ^ 2) := by
          congr 1
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    rw [hDiffSum, hConvSum, hGradientSum]
    simp only [W, H]
    have hTimeTerms :
        (∑ i : Fin 3, 2 * (Ui i z * Phi z) * Dt i z) =
          ∑ i : Fin 3, 2 * Ui i z * Dt i z * Phi z := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hCrossTerms :
        2 * (∑ i : Fin 3, ∑ j : Fin 3,
          D i j z * (Ui i z * GradTest j z)) =
          ∑ i : Fin 3, ∑ j : Fin 3,
            2 * Ui i z * D i j z * GradTest j z := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have hDpTerms :
        (∑ i : Fin 3, 2 * (Ui i z * Phi z) * Dp i z) =
          2 * ∑ i : Fin 3, Dp i z * (Ui i z * Phi z) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hJGradientTerms :
        (∑ i : Fin 3, (∑ j : Fin 3, Ui j z * Ui j z * J i z) * GradTest i z) =
          ∑ i : Fin 3, (∑ j : Fin 3, Ui j z * Ui j z) * J i z * GradTest i z := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        _ = (∑ j : Fin 3, Ui j z * Ui j z * J i z) * GradTest i z := by
          rw [← Finset.sum_mul]
        _ = ((∑ j : Fin 3, Ui j z * Ui j z) * J i z) * GradTest i z := by
          conv_lhs => rw [← Finset.sum_mul]
    simp_rw [mul_add]
    rw [hTimeTerms, hCrossTerms, hDpTerms, hJGradientTerms]
    have hConvCanonical :
        2 * (∑ i : Fin 3, ∑ j : Fin 3,
          J j z * Ui i z * D i j z * Phi z) =
          ∑ i : Fin 3, ∑ j : Fin 3,
            J j z * (2 * Ui i z * D i j z * Phi z) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have hPressureCanonical :
        2 * (∑ i : Fin 3, p (z.1, z.2) * (Ui i z * GradTest i z)) =
          ∑ i : Fin 3, 2 * p (z.1, z.2) * Ui i z * GradTest i z := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    simp_rw [add_mul]
    rw [hConvCanonical, hPressureCanonical]
    have hTimeTestSum :
        (∑ i : Fin 3, Ui i z * Ui i z * CKN.timePartialProd Phi z) =
          CKN.timePartialProd Phi z * ∑ i : Fin 3, Ui i z * Ui i z := by
      calc
        _ = (∑ i : Fin 3, Ui i z * Ui i z) * CKN.timePartialProd Phi z := by
          rw [← Finset.sum_mul]
        _ = _ := by ring
    have hSpaceTestSum :
        (∑ i : Fin 3, Ui i z * Ui i z *
          ∑ j : Fin 3, CKN.spatialPartialProd (GradTest j) j z) =
          (∑ i : Fin 3, Ui i z * Ui i z) *
            ∑ j : Fin 3, CKN.spatialPartialProd (GradTest j) j z := by
      rw [← Finset.sum_mul]
    rw [hTimeTestSum, hSpaceTestSum]
    simp_rw [Finset.sum_add_distrib]
    ring_nf
    have hTimeCanonical :
        (∑ i : Fin 3, Ui i z * Dt i z * Phi z * 2) =
          ∑ i : Fin 3, Phi z * Ui i z * Dt i z * 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hTimeCanonical]
    ring_nf
  have hEnergyResidualPoint (z : Vec3 × ℝ) (hz : z ∈ S) :
      EnergyResidual z = -FluxResidual z := by
    calc
      EnergyResidual z = (FluxResidual z + EnergyResidual z) - FluxResidual z := by ring
      _ = -FluxResidual z := by
        rw [← hFluxExpansion z hz, hWeightedZero z hz]
        ring
  have hEnergyResidualZero : (∫ z in S, EnergyResidual z ∂volume) = 0 := by
    calc
      _ = ∫ z in S, -FluxResidual z ∂volume := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hSmeas] with z hz
        exact hEnergyResidualPoint z hz
      _ = -∫ z in S, FluxResidual z ∂volume := by rw [integral_neg]
      _ = 0 := by rw [hFluxZero]; simp
  have hEnergyDecomp : (∫ z in S, EnergyResidual z ∂volume) =
      2 * (∫ z in S, spatialGradientSq u
          (fun z i j => spatialPartial (fun y => u y i) j z)
          ((z.1, z.2) : ParabolicPoint) * Phi z ∂volume) -
        ∫ z in S, (vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ) * HeatTest z +
          ∑ i : Fin 3,
            (vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ) * J i z +
              2 * p (z.1, z.2) * Ui i z) * GradTest i z) ∂volume := by
    have hpoint (z : Vec3 × ℝ) : EnergyResidual z =
        2 * (spatialGradientSq u
          (fun z i j => spatialPartial (fun y => u y i) j z)
          ((z.1, z.2) : ParabolicPoint) * Phi z) -
          (vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ) * HeatTest z +
            ∑ i : Fin 3,
              (vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ) * J i z +
                2 * p (z.1, z.2) * Ui i z) * GradTest i z) := by
      change 2 * regUniformSpatialGradientDensity u
          (fun z i j => spatialPartial (fun y => u y i) j z) z * Phi z -
        vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ) * HeatTest z -
        ∑ i : Fin 3,
          (vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ) * J i z +
            2 * p (z.1, z.2) * Ui i z) * GradTest i z = _
      rw [show regUniformSpatialGradientDensity u
          (fun z i j => spatialPartial (fun y => u y i) j z) z =
          spatialGradientSq u
            (fun z i j => spatialPartial (fun y => u y i) j z)
            ((z.1, z.2) : ParabolicPoint) by rfl]
      ring
    rw [setIntegral_congr_fun hSmeas (fun z hz => hpoint z),
      integral_sub hLeftInt hRightInt, integral_const_mul]
  rw [hEnergyDecomp] at hEnergyResidualZero
  change 2 * (∫ z : Vec3 × ℝ in S,
      spatialGradientSq u (fun z i j => spatialPartial (fun y => u y i) j z)
        ((z.1, z.2) : ParabolicPoint) * Phi z) =
    ∫ z : Vec3 × ℝ in S,
      vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ) * HeatTest z +
        ∑ i : Fin 3,
          (vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ) * J i z +
            2 * p (z.1, z.2) * Ui i z) * GradTest i z
  linarith only [hEnergyResidualZero]

end CKN.Leray

end
