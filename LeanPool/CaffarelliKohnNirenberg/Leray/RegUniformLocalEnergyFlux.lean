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

abbrev regUniformParabolicTopologyLocalEnergyFlux : TopologicalSpace ParabolicPoint :=
  inferInstance

local instance regUniformLocalEnergyFluxNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

local instance regUniformLocalEnergyFluxNormedSpace : NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))

local instance (priority := 10000) regUniformLocalEnergyFluxTopologicalSpace :
    TopologicalSpace ParabolicPoint :=
  instTopologicalSpaceProd

private def regUniformSpatialGradientDensity
    (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3)
    (z : Vec3 × ℝ) : ℝ :=
  spatialGradientSq u Du ((z.1, z.2) : ParabolicPoint)

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
  have hDui (i j : Fin 3) (z : Vec3 × ℝ) :
      D i j z = spatialPartial (Ui i) j z := rfl
  have hDtUi (i : Fin 3) (z : Vec3 × ℝ) :
      Dt i z = timePartial (Ui i) z := rfl
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
  have hPhiTimeCompact : HasCompactSupport
      (fun z : Vec3 × ℝ => timePartial (Phi) z) := by
    change HasCompactSupport (fun z : Vec3 × ℝ => timePartial ψ z)
    exact CKN.hasCompactSupport_timePartial hψ.2.1
  have hPhiTimeSupport : tsupport
      (fun z : Vec3 × ℝ => timePartial (Phi) z) ⊆ S := by
    change tsupport (fun z : Vec3 × ℝ => timePartial ψ z) ⊆ S
    exact (CKN.tsupport_timePartial_subset ψ).trans hψ.2.2
  have hU (i : Fin 3) : ContinuousOn (Ui i) S := by
    have hpull := regUniform_continuousOn_pullback (hUcont i) hSsymm
    simpa [Ui] using hpull
  have hD (i j : Fin 3) : ContinuousOn (D i j) S := by
    have hpull := regUniform_continuousOn_pullback (hDcont i j) hSsymm
    simpa [D] using hpull
  have hDD (i j k : Fin 3) : ContinuousOn (DD i j k) S := by
    have hpull := regUniform_continuousOn_pullback (hDDcont i j k) hSsymm
    simpa [DD] using hpull
  have hDt (i : Fin 3) : ContinuousOn (Dt i) S := by
    have hpull := regUniform_continuousOn_pullback (hDtcont i) hSsymm
    simpa [Dt] using hpull
  have hP : ContinuousOn (fun z : Vec3 × ℝ => p z) S := by
    have hpull := regUniform_continuousOn_pullback hPcont hSsymm
    simpa using hpull
  have hDp (i : Fin 3) : ContinuousOn (Dp i) S := by
    have hpull := regUniform_continuousOn_pullback (hDpcont i) hSsymm
    simpa [Dp] using hpull
  have hJcontMetric := regUniform_mollified_velocity_continuousOn
    ρ ε hε (S := S) (fun t ht => hSliceL2 t (le_of_lt ht))
    hUcontDiff (fun z hz => hz.2)
      (fun z hz y => ⟨Set.mem_univ _, hz.2⟩)
  have hJpartialMetric := regUniform_mollified_velocity_spatialPartial_continuousOn
    ρ ε hε (S := S) (fun t ht => hSliceL2 t (le_of_lt ht))
    hUcontDiff (fun z hz => hz.2)
      (fun z hz y => ⟨Set.mem_univ _, hz.2⟩)
  have hJ (i : Fin 3) : ContinuousOn (J i) S := by
    simpa [J] using hJcontMetric i
  have hJpartial (i j : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial (J i) j z) S := by
    change ContinuousOn (fun z : Vec3 × ℝ => spatialPartial
      (fun y : Vec3 × ℝ => regUniformMollifiedVelocity ρ ε hε u y i) j z) S
    exact hJpartialMetric i j
  have hUiSpatialDiff (z : Vec3 × ℝ) (hz : z ∈ S) (i : Fin 3) :
      DifferentiableAt ℝ (fun x : Vec3 => Ui i (x, z.2)) z.1 :=
    regUniform_contDiffOn_spatialSlice_differentiableAt hSopen
      (hUcontDiff i) hz
  have hUiTimeDiff (z : Vec3 × ℝ) (hz : z ∈ S) (i : Fin 3) :
      DifferentiableAt ℝ (fun t : ℝ => Ui i (z.1, t)) z.2 :=
    regUniform_contDiffOn_timeSlice_differentiableAt hSopen
      (hUcontDiff i) hz
  have hDdiff' (z : Vec3 × ℝ) (hz : z ∈ S) (i j : Fin 3) :
      DifferentiableAt ℝ (fun x : Vec3 => D i j (x, z.2)) z.1 := by
    simpa [D] using hDdiff z hz i j
  have hPdiff' (z : Vec3 × ℝ) (hz : z ∈ S) :
      DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1 :=
    hPdiff z hz
  have hPhiSpatialDiff (z : Vec3 × ℝ) (hz : z ∈ S) :
      DifferentiableAt ℝ (fun x : Vec3 => Phi (x, z.2)) z.1 := by
    exact regUniform_contDiffOn_spatialSlice_differentiableAt hSopen
      ((hψ.1.of_le (by norm_num)).contDiffOn) hz
  have hPhiTimeDiff (z : Vec3 × ℝ) (hz : z ∈ S) :
      DifferentiableAt ℝ (fun t : ℝ => Phi (z.1, t)) z.2 := by
    exact regUniform_contDiffOn_timeSlice_differentiableAt hSopen
      ((hψ.1.of_le (by norm_num)).contDiffOn) hz
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
  have hHspatialCont (i j : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial (H i) j z) S := by
    apply ContinuousOn.congr ((hU i).mul (hD i j) |>.const_mul 2)
    intro z hz
    change spatialPartial (H i) j z = 2 * (Ui i z * D i j z)
    rw [hHspatial i j z hz]
    ring
  have hHtimeCont (i : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => timePartial (H i) z) S := by
    apply ContinuousOn.congr ((hU i).mul (hDt i) |>.const_mul 2)
    intro z hz
    change timePartial (H i) z = 2 * (Ui i z * Dt i z)
    rw [hHtime i z hz]
    ring
  have hHdiff (i : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) (j : Fin 3) :
      DifferentiableAt ℝ (fun x : Vec3 => H i (x, z.2)) z.1 := by
    change DifferentiableAt ℝ
      (fun x : Vec3 => Ui i (x, z.2) * Ui i (x, z.2)) z.1
    exact (hUiSpatialDiff z hz i).mul (hUiSpatialDiff z hz i)
  have hHcont (i : Fin 3) : ContinuousOn (H i) S :=
    (hU i).mul (hU i)
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
  have hWpartialCont (i j : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial (W i) j z) S := by
    apply ContinuousOn.congr
      ((hU i).mul (hPhiSpaceCont j) |>.add
        ((hPhiCont).mul (hD i j)))
    intro z hz
    exact hWpartial i j z hz
  have hWcont (i : Fin 3) : ContinuousOn (W i) S :=
    (hU i).mul hPhiCont
  have hWcompact (i : Fin 3) : HasCompactSupport (W i) := by
    change HasCompactSupport (Ui i * Phi)
    exact hψ.2.1.mul_left
  have hWsupport (i : Fin 3) : tsupport (W i) ⊆ S := by
    change tsupport (Ui i * Phi) ⊆ S
    exact tsupport_mul_subset_right.trans hψ.2.2
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
  have hVpartialCont (i j : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial (V i) j z) S := by
    apply ContinuousOn.congr
      (((hU i).mul (hD i j) |>.const_mul 2).mul hPhiCont |>.add
        ((hHcont i).mul (hPhiSpaceCont j)))
    intro z hz
    change CKN.spatialPartialProd (V i) j z =
      (2 * (Ui i z * D i j z)) * Phi z + H i z * spatialPartial Phi j z
    simpa only [CKN.spatialPartialProd, mul_assoc] using hVpartial i j z hz
  have hVcont (i : Fin 3) : ContinuousOn (V i) S :=
    (hHcont i).mul hPhiCont
  have hTimeFluxCont (i : Fin 3) : ContinuousOn (TimeFlux i) S :=
    hVcont i
  have hVcompact (i : Fin 3) : HasCompactSupport (V i) := by
    change HasCompactSupport (H i * Phi)
    exact hψ.2.1.mul_left
  have hVsupport (i : Fin 3) : tsupport (V i) ⊆ S := by
    change tsupport (H i * Phi) ⊆ S
    exact tsupport_mul_subset_right.trans hψ.2.2
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
  have hTimeFluxPartialCont (i : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => timePartial (TimeFlux i) z) S := by
    apply ContinuousOn.congr
      ((hHtimeCont i).mul hPhiCont |>.add (hHcont i |>.mul hPhiTimeCont))
    intro z hz
    exact hVtime i z hz
  have hTimeFluxCompact (i : Fin 3) : HasCompactSupport (TimeFlux i) := by
    change HasCompactSupport (H i * Phi)
    exact hψ.2.1.mul_left
  have hTimeFluxSupport (i : Fin 3) : tsupport (TimeFlux i) ⊆ S := by
    change tsupport (H i * Phi) ⊆ S
    exact tsupport_mul_subset_right.trans hψ.2.2
  have hTimeFluxDiff (i : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) :
      DifferentiableAt ℝ (fun t : ℝ => TimeFlux i (z.1, t)) z.2 := by
    change DifferentiableAt ℝ
      (fun t : ℝ => H i (z.1, t) * Phi (z.1, t)) z.2
    exact (hHtimeDiff i z hz).mul (hPhiTimeDiff z hz)
  have hTimeFluxIntegralZero (i : Fin 3) :
      (∫ z in S, timePartial (TimeFlux i) z ∂volume) = 0 := by
    exact regUniform_integral_timePartial_eq_zero hSopen (hTimeFluxCont i)
      (hTimeFluxPartialCont i) (fun z hz => hTimeFluxDiff i z hz)
      (hTimeFluxCompact i) (hTimeFluxSupport i)
  have hDpartialCont (i j : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial (D i j) j z) S := by
    have hpull := regUniform_continuousOn_pullback
      (hDDcont i j j) hSsymm
    change ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial
        (fun y : Vec3 × ℝ => spatialPartial
          (fun x : Vec3 × ℝ => u x i) j y) j z) S
    exact hpull
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
  have hDiffFluxPartialCont (i j : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial (DiffFlux i j) j z) S := by
    apply ContinuousOn.congr
      ((hDpartialCont i j).mul (hWcont i) |>.add
        ((hD i j).mul (hWpartialCont i j)))
    intro z hz
    exact hDiffFluxPartial i j z hz
  have hDiffFluxCont (i j : Fin 3) : ContinuousOn (DiffFlux i j) S :=
    (hD i j).mul (hWcont i)
  have hDiffFluxDiff (i j : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) :
      DifferentiableAt ℝ (fun x : Vec3 => DiffFlux i j (x, z.2)) z.1 := by
    change DifferentiableAt ℝ
      (fun x : Vec3 => D i j (x, z.2) * W i (x, z.2)) z.1
    exact (hDdiff' z hz i j).mul (hWdiff i z hz j)
  have hDiffFluxCompact (i j : Fin 3) : HasCompactSupport (DiffFlux i j) := by
    change HasCompactSupport (D i j * W i)
    exact (hWcompact i).mul_left
  have hDiffFluxSupport (i j : Fin 3) : tsupport (DiffFlux i j) ⊆ S := by
    change tsupport (D i j * W i) ⊆ S
    exact tsupport_mul_subset_right.trans (hWsupport i)
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
  have hTestGradientFluxPartialCont (i j : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial (TestGradientFlux i j) j z) S := by
    apply ContinuousOn.congr
      ((hHspatialCont i j).mul (hPhiSpaceCont j) |>.add
        ((hHcont i).mul (hPhiSecondCont j)))
    intro z hz
    exact hTestGradientFluxPartial i j z hz
  have hTestGradientFluxCont (i j : Fin 3) :
      ContinuousOn (TestGradientFlux i j) S :=
    (hHcont i).mul (hPhiSpaceCont j)
  have hTestGradientFluxDiff (i j : Fin 3) (z : Vec3 × ℝ)
      (hz : z ∈ S) : DifferentiableAt ℝ
        (fun x : Vec3 => TestGradientFlux i j (x, z.2)) z.1 := by
    change DifferentiableAt ℝ
      (fun x : Vec3 => H i (x, z.2) * GradTest j (x, z.2)) z.1
    exact (hHdiff i z hz j).mul (hPhiSecondDiff z hz j)
  have hTestGradientFluxCompact (i j : Fin 3) :
      HasCompactSupport (TestGradientFlux i j) := by
    change HasCompactSupport (H i * GradTest j)
    exact (hPhiSpaceCompact j).mul_left
  have hTestGradientFluxSupport (i j : Fin 3) :
      tsupport (TestGradientFlux i j) ⊆ S := by
    change tsupport (H i * GradTest j) ⊆ S
    exact tsupport_mul_subset_right.trans (hPhiSpaceSupport j)
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
  have hConvFluxPartialCont (i j : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial (ConvFlux i j) j z) S := by
    apply ContinuousOn.congr
      ((hJpartial j j).mul (hVcont i) |>.add ((hJ j).mul (hVpartialCont i j)))
    intro z hz
    exact hConvFluxPartial i j z hz
  have hConvFluxCont (i j : Fin 3) : ContinuousOn (ConvFlux i j) S :=
    (hJ j).mul (hVcont i)
  have hConvFluxDiff (i j : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) :
      DifferentiableAt ℝ (fun x : Vec3 => ConvFlux i j (x, z.2)) z.1 := by
    change DifferentiableAt ℝ
      (fun x : Vec3 => J j (x, z.2) * V i (x, z.2)) z.1
    exact (hJdiff z hz j).mul (hVdiff i z hz j)
  have hConvFluxCompact (i j : Fin 3) : HasCompactSupport (ConvFlux i j) := by
    change HasCompactSupport (J j * V i)
    exact (hVcompact i).mul_left
  have hConvFluxSupport (i j : Fin 3) : tsupport (ConvFlux i j) ⊆ S := by
    change tsupport (J j * V i) ⊆ S
    exact tsupport_mul_subset_right.trans (hVsupport i)
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
  have hPressureFluxPartialCont (i : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial (PressureFlux i) i z) S := by
    apply ContinuousOn.congr
      ((hDp i).mul (hWcont i) |>.add
        ((hP).mul (hWpartialCont i i)))
    intro z hz
    exact hPressureFluxPartial i z hz
  have hPressureFluxCont (i : Fin 3) :
      ContinuousOn (PressureFlux i) S := (hP).mul (hWcont i)
  have hPressureFluxDiff (i : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) :
      DifferentiableAt ℝ
        (fun x : Vec3 => PressureFlux i (x, z.2)) z.1 := by
    change DifferentiableAt ℝ
      (fun x : Vec3 => p (x, z.2) * W i (x, z.2)) z.1
    exact (hPdiff' z hz).mul (hWdiff i z hz i)
  have hPressureFluxCompact (i : Fin 3) :
      HasCompactSupport (PressureFlux i) := by
    change HasCompactSupport ((fun z : Vec3 × ℝ => p z) * W i)
    exact (hWcompact i).mul_left
  have hPressureFluxSupport (i : Fin 3) :
      tsupport (PressureFlux i) ⊆ S := by
    change tsupport ((fun z : Vec3 × ℝ => p z) * W i) ⊆ S
    exact tsupport_mul_subset_right.trans (hWsupport i)
  have hSpatialFluxZero {F : Vec3 × ℝ → ℝ} (j : Fin 3)
      (hFc : ContinuousOn F S)
      (hFdc : ContinuousOn (fun z => spatialPartial (F) j z) S)
      (hFd : ∀ z ∈ S, DifferentiableAt ℝ
        (fun x : Vec3 => F (x, z.2)) z.1)
      (hFcc : HasCompactSupport F) (hFs : tsupport F ⊆ S) :
      (∫ z in S, spatialPartial (F) j z ∂volume) = 0 :=
    regUniform_integral_spatialPartial_eq_zero j hSopen hFc hFdc hFd hFcc hFs
  have hSpatialFluxInt {F : Vec3 × ℝ → ℝ} (j : Fin 3)
      (hFdc : ContinuousOn (fun z => spatialPartial (F) j z) S)
      (hFcc : HasCompactSupport F) (hFs : tsupport F ⊆ S) :
      Integrable (fun z : Vec3 × ℝ => spatialPartial (F) j z)
        (volume.restrict S) := by
    have hc := CKN.hasCompactSupport_spatialPartial hFcc j
    have hs := (CKN.tsupport_spatialPartial_subset j).trans hFs
    simpa only [one_mul] using
      (regUniform_integrable_mul_of_tsupport_subset
        (F := fun _ : Vec3 × ℝ => (1 : ℝ)) (G := fun z => spatialPartial F j z)
        (S := S) hSopen continuousOn_const hFdc hc hs).mono_measure
          Measure.restrict_le_self
  have hTimeFluxInt {F : Vec3 × ℝ → ℝ}
      (hFdc : ContinuousOn (fun z => timePartial (F) z) S)
      (hFcc : HasCompactSupport F) (hFs : tsupport F ⊆ S) :
      Integrable (fun z : Vec3 × ℝ => timePartial (F) z)
        (volume.restrict S) := by
    have hc := CKN.hasCompactSupport_timePartial hFcc
    have hs := (CKN.tsupport_timePartial_subset F).trans hFs
    simpa only [one_mul] using
      (regUniform_integrable_mul_of_tsupport_subset
        (F := fun _ : Vec3 × ℝ => (1 : ℝ)) (G := fun z => timePartial F z)
        (S := S) hSopen continuousOn_const hFdc hc hs).mono_measure
          Measure.restrict_le_self
  have hTimeFluxIntS (i : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => timePartial (TimeFlux i) z)
      (volume.restrict S) :=
    hTimeFluxInt (hTimeFluxPartialCont i)
      (hTimeFluxCompact i) (hTimeFluxSupport i)
  have hDiffFluxZero (i j : Fin 3) :
      (∫ z in S, spatialPartial (DiffFlux i j) j z ∂volume) = 0 :=
    hSpatialFluxZero j (hDiffFluxCont i j) (hDiffFluxPartialCont i j)
      (hDiffFluxDiff i j) (hDiffFluxCompact i j) (hDiffFluxSupport i j)
  have hDiffFluxIntS (i j : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => spatialPartial (DiffFlux i j) j z)
      (volume.restrict S) :=
    hSpatialFluxInt j (hDiffFluxPartialCont i j)
      (hDiffFluxCompact i j) (hDiffFluxSupport i j)
  have hTestGradientFluxZero (i j : Fin 3) :
      (∫ z in S,
        spatialPartial (TestGradientFlux i j) j z ∂volume) = 0 :=
    hSpatialFluxZero j (hTestGradientFluxCont i j)
      (hTestGradientFluxPartialCont i j) (hTestGradientFluxDiff i j)
      (hTestGradientFluxCompact i j) (hTestGradientFluxSupport i j)
  have hTestGradientFluxIntS (i j : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => spatialPartial (TestGradientFlux i j) j z)
      (volume.restrict S) :=
    hSpatialFluxInt j (hTestGradientFluxPartialCont i j)
      (hTestGradientFluxCompact i j) (hTestGradientFluxSupport i j)
  have hConvFluxZero (i j : Fin 3) :
      (∫ z in S, spatialPartial (ConvFlux i j) j z ∂volume) = 0 :=
    hSpatialFluxZero j (hConvFluxCont i j) (hConvFluxPartialCont i j)
      (hConvFluxDiff i j) (hConvFluxCompact i j) (hConvFluxSupport i j)
  have hConvFluxIntS (i j : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => spatialPartial (ConvFlux i j) j z)
      (volume.restrict S) :=
    hSpatialFluxInt j (hConvFluxPartialCont i j)
      (hConvFluxCompact i j) (hConvFluxSupport i j)
  have hPressureFluxZero (i : Fin 3) :
      (∫ z in S, spatialPartial (PressureFlux i) i z ∂volume) = 0 :=
    hSpatialFluxZero i (hPressureFluxCont i) (hPressureFluxPartialCont i)
      (hPressureFluxDiff i) (hPressureFluxCompact i) (hPressureFluxSupport i)
  have hPressureFluxIntS (i : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => spatialPartial (PressureFlux i) i z)
      (volume.restrict S) :=
    hSpatialFluxInt i (hPressureFluxPartialCont i)
      (hPressureFluxCompact i) (hPressureFluxSupport i)
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
  have hsumInt {f : Fin 3 → Vec3 × ℝ → ℝ}
      (hf : ∀ i, Integrable (f i) (volume.restrict S)) :
      Integrable (fun z => ∑ i : Fin 3, f i z) (volume.restrict S) :=
    integrable_finsetSum Finset.univ fun i hi => hf i
  have hsumZero {f : Fin 3 → Vec3 × ℝ → ℝ}
      (hf : ∀ i, Integrable (f i) (volume.restrict S))
      (hz : ∀ i, (∫ z in S, f i z ∂volume) = 0) :
      (∫ z in S, ∑ i : Fin 3, f i z ∂volume) = 0 := by
    rw [integral_finsetSum Finset.univ (fun i hi => hf i)]
    simp_rw [hz]
    simp
  have hdoubleInt {f : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
      (hf : ∀ i j, Integrable (f i j) (volume.restrict S)) :
      Integrable (fun z => ∑ i : Fin 3, ∑ j : Fin 3, f i j z)
        (volume.restrict S) :=
    integrable_finsetSum Finset.univ fun i hi =>
      integrable_finsetSum Finset.univ fun j hj => hf i j
  have hdoubleZero {f : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
      (hf : ∀ i j, Integrable (f i j) (volume.restrict S))
      (hz : ∀ i j, (∫ z in S, f i j z ∂volume) = 0) :
      (∫ z in S, ∑ i : Fin 3, ∑ j : Fin 3, f i j z ∂volume) = 0 := by
    rw [integral_finsetSum Finset.univ (fun i hi =>
      integrable_finsetSum Finset.univ fun j hj => hf i j)]
    simp_rw [integral_finsetSum Finset.univ (fun j hj => hf _ j)]
    simp_rw [hz]
    simp
  let TimeSum : Vec3 × ℝ → ℝ := fun z =>
    ∑ i : Fin 3, timePartial (TimeFlux i) z
  let DiffSum : Vec3 × ℝ → ℝ := fun z =>
    ∑ i : Fin 3, ∑ j : Fin 3, spatialPartial (DiffFlux i j) j z
  let TestGradSum : Vec3 × ℝ → ℝ := fun z =>
    ∑ i : Fin 3, ∑ j : Fin 3, spatialPartial (TestGradientFlux i j) j z
  let ConvSum : Vec3 × ℝ → ℝ := fun z =>
    ∑ i : Fin 3, ∑ j : Fin 3, spatialPartial (ConvFlux i j) j z
  let PressureSum : Vec3 × ℝ → ℝ := fun z =>
    ∑ i : Fin 3, spatialPartial (PressureFlux i) i z
  have hTimeSumInt := hsumInt hTimeFluxIntS
  have hTimeSumZero := hsumZero hTimeFluxIntS hTimeFluxIntegralZero
  have hDiffSumInt := hdoubleInt hDiffFluxIntS
  have hDiffSumZero := hdoubleZero hDiffFluxIntS hDiffFluxZero
  have hTestGradSumInt := hdoubleInt hTestGradientFluxIntS
  have hTestGradSumZero := hdoubleZero hTestGradientFluxIntS hTestGradientFluxZero
  have hConvSumInt := hdoubleInt hConvFluxIntS
  have hConvSumZero := hdoubleZero hConvFluxIntS hConvFluxZero
  have hPressureSumInt := hsumInt hPressureFluxIntS
  have hPressureSumZero := hsumZero hPressureFluxIntS hPressureFluxZero
  have hDiffTwiceInt := hDiffSumInt.const_mul 2
  have hPressureTwiceInt := hPressureSumInt.const_mul 2
  have hABInt := hTimeSumInt.sub hDiffTwiceInt
  have hABCInt := hABInt.add hTestGradSumInt
  have hCoreInt := hABCInt.add hConvSumInt
  have hFluxInt : Integrable FluxResidual (volume.restrict S) := by
    dsimp [FluxResidual, TimeSum, DiffSum, TestGradSum, ConvSum, PressureSum]
    exact (hCoreInt.add hPressureTwiceInt)
  have hFluxZero : (∫ z in S, FluxResidual z ∂volume) = 0 := by
    have hABzero : (∫ z in S, TimeSum z - 2 * DiffSum z ∂volume) = 0 := by
      rw [integral_sub hTimeSumInt hDiffTwiceInt, integral_const_mul,
        hTimeSumZero, hDiffSumZero]
      simp
    have hABTestIntegral :
        (∫ z in S, TimeSum z - 2 * DiffSum z + TestGradSum z ∂volume) =
          (∫ z in S, TimeSum z - 2 * DiffSum z ∂volume) +
            ∫ z in S, TestGradSum z ∂volume := by
      simpa [TimeSum, DiffSum, TestGradSum] using
        (integral_add' hABInt hTestGradSumInt)
    have hCoreZero : (∫ z in S,
        TimeSum z - 2 * DiffSum z + TestGradSum z + ConvSum z ∂volume) = 0 := by
      calc
        _ = (∫ z in S, TimeSum z - 2 * DiffSum z + TestGradSum z ∂volume) +
            ∫ z in S, ConvSum z ∂volume := integral_add' hABCInt hConvSumInt
        _ = 0 := by
          rw [hABTestIntegral]
          rw [hABzero, hTestGradSumZero, hConvSumZero]
          simp
    have hCorePressureIntegral :
        (∫ z in S,
          TimeSum z - 2 * DiffSum z + TestGradSum z + ConvSum z +
            2 * PressureSum z ∂volume) =
          (∫ z in S,
            TimeSum z - 2 * DiffSum z + TestGradSum z + ConvSum z ∂volume) +
            ∫ z in S, 2 * PressureSum z ∂volume := by
      exact integral_add' hCoreInt hPressureTwiceInt
    change (∫ z in S,
      (TimeSum z - 2 * DiffSum z + TestGradSum z + ConvSum z) +
        2 * PressureSum z ∂volume) = 0
    rw [hCorePressureIntegral, hCoreZero, integral_const_mul, hPressureSumZero]
    simp
  exact hFluxZero

end CKN.Leray

end
