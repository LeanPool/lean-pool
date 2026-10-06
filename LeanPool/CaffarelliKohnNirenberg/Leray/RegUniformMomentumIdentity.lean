/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformMomentum
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.MomentumIntegrand
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationBasics

/-!
# Reg Uniform Momentum Identity

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open scoped Topology ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

abbrev regUniformParabolicTopologyMomentumIdentity : TopologicalSpace ParabolicPoint :=
  inferInstance

@[expose]
def regUniformParabolicHomeomorph : ParabolicPoint ≃ₜ Vec3 × ℝ := by
  exact parabolicHomeomorph

@[simp] private theorem regUniformParabolicHomeomorph_apply
    (z : ParabolicPoint) :
    regUniformParabolicHomeomorph z = (z.1, z.2) := rfl

@[simp] private theorem regUniformParabolicHomeomorph_symm_apply
    (z : Vec3 × ℝ) :
    regUniformParabolicHomeomorph.symm z = ((z.1, z.2) : ParabolicPoint) := rfl

local instance : NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

local instance : NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))

local instance (priority := 10000) : TopologicalSpace ParabolicPoint :=
  instTopologicalSpaceProd

/-- The pointwise equation (R3), positive-time regularity (R1)–(R2), and
weak solenoidality imply the regularized momentum identity in
`lem:reg-momentum`. -/
theorem regUniform_momentum_identity
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (hSliceL2 : ∀ t : ℝ, 0 ≤ t →
      MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hWeakDivFree : ∀ t : ℝ, 0 ≤ t →
      CKN.IsWeakDivFreeL2 (fun x : Vec3 => u (x, t)))
    (hUcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyMomentumIdentity
      ∀ i : Fin 3, ContinuousOn (fun z => u z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyMomentumIdentity
      ∀ i j : Fin 3, ContinuousOn
      (fun z => spatialPartial (fun y => u y i) j z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDDcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyMomentumIdentity
      ∀ i j k : Fin 3, ContinuousOn
      (fun z => spatialPartial (fun y => spatialPartial
        (fun x => u x i) j y) k z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDtcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyMomentumIdentity
      ∀ i : Fin 3, ContinuousOn
      (fun z => timePartial (fun y => u y i) z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hPcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyMomentumIdentity
      ContinuousOn p
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDpcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyMomentumIdentity
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
      ∀ i j : Fin 3, DifferentiableAt ℝ
        (fun x : Vec3 => spatialPartial (fun y => u y i) j (x, z.2)) z.1)
    (hPdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1)
    (hEquation : ∀ z : ParabolicPoint, 0 < z.2 → ∀ i : Fin 3,
      timePartial (fun y => u y i) z -
        (∑ j : Fin 3, spatialPartial
          (fun y => spatialPartial (fun x => u x i) j y) j z) +
        (∑ j : Fin 3, regUniformMollifiedVelocity ρ ε hε u z j *
          spatialPartial (fun y => u y i) j z) +
        spatialPartial (fun y => p y) i z = 0)
    (φ : ParabolicPoint → Vec3)
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3)
      (Set.univ : Set Vec3) (Ioi 0)) :
    ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
        - ∑ i : Fin 3, ∑ j : Fin 3,
          regUniformMollifiedVelocity ρ ε hε u z j * u z i *
            spatialPartial (fun y => φ y i) j z
        + ∑ i : Fin 3, ∑ j : Fin 3,
          spatialPartial (fun y => u y i) j z *
            spatialPartial (fun y => φ y i) j z
        - p z * (∑ i : Fin 3,
          spatialPartial (fun y => φ y i) i z)) = 0 := by
  let S : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)
  have hSopen : IsOpen S := by
    exact isOpen_univ.prod isOpen_Ioi
  have hSmeas : MeasurableSet S := by
    exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi
  let Smetric : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioi (0 : ℝ))
  have hJcontMetric := regUniform_mollified_velocity_continuousOn
    ρ ε hε (S := S) (fun t ht => hSliceL2 t (le_of_lt ht))
    hUcontDiff (fun z hz => hz.2) (fun z hz y => ⟨Set.mem_univ _, hz.2⟩)
  have hJpartialMetric := regUniform_mollified_velocity_spatialPartial_continuousOn
    ρ ε hε (S := S) (fun t ht => hSliceL2 t (le_of_lt ht))
    hUcontDiff (fun z hz => hz.2) (fun z hz y => ⟨Set.mem_univ _, hz.2⟩)
  have hJdiv : ∀ z ∈ S, ∑ j : Fin 3,
      spatialPartial (fun y => regUniformMollifiedVelocity ρ ε hε u y j)
        j z = 0 := by
    intro z hz
    exact regUniform_mollified_velocity_divergence_eq_zero ρ ε hε u z.2
      (hWeakDivFree z.2 (le_of_lt hz.2)) z.1
  have hφi (i : Fin 3) :
      (fun z : ParabolicPoint => φ z i) ∈
        spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioi 0) :=
    CKN.component_mem_spaceTimeTestFunction hφ i
  have hφspatialCont (i j : Fin 3) : Continuous
      (fun z : Vec3 × ℝ => spatialPartial (fun y => φ y i) j z) :=
    (spatialPartial_contDiff (hφi i).1 j).continuous
  have hφtimeCont (i : Fin 3) : Continuous
      (fun z : Vec3 × ℝ => timePartial (fun y => φ y i) z) :=
    (CKN.Core.Step3.timePartial_contDiff_full (hφi i).1).continuous
  let Ui (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => u z i
  let Phi (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => φ z i
  let D (i j : Fin 3) : Vec3 × ℝ → ℝ :=
    fun z => spatialPartial (fun y => u y i) j z
  let DD (i j k : Fin 3) : Vec3 × ℝ → ℝ :=
    fun z => spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z
  let Dt (i : Fin 3) : Vec3 × ℝ → ℝ :=
    fun z => timePartial (fun y => u y i) z
  let Dp (i : Fin 3) : Vec3 × ℝ → ℝ :=
    fun z => spatialPartial (fun y => p y) i z
  let J (j : Fin 3) : Vec3 × ℝ → ℝ :=
    fun z => regUniformMollifiedVelocity ρ ε hε u z j
  have hSsymm : ∀ z ∈ S, ((z.1, z.2) : ParabolicPoint) ∈ Smetric := by
    intro z hz
    exact ⟨Set.mem_univ _, hz.2⟩
  have hJcont (j : Fin 3) : ContinuousOn (J j) S := by
    simpa [J] using hJcontMetric j
  have hJpartialCont (i j : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial (J i) j z) S := by
    change ContinuousOn (fun z : Vec3 × ℝ => spatialPartial
      (fun y : Vec3 × ℝ => regUniformMollifiedVelocity ρ ε hε u y i) j z) S
    exact hJpartialMetric i j
  let Q (i : Fin 3) : Vec3 × ℝ → ℝ := fun z =>
    -(Ui i z * timePartial (Phi i) z)
      - ∑ j : Fin 3, J j z * Ui i z * spatialPartial (Phi i) j z
      + ∑ j : Fin 3, D i j z * spatialPartial (Phi i) j z
      - p z * spatialPartial (Phi i) i z
  have hJdiff : ∀ z ∈ S, ∀ j : Fin 3,
      DifferentiableAt ℝ (fun x : Vec3 => J j (x, z.2)) z.1 := by
    intro z hz j
    let aₜ : Vec3 → Vec3 := fun x => u (x, z.2)
    have hJₜ : CKN.IsInJ aₜ := CKN.weakDivFreeL2_isInJ
      (hWeakDivFree z.2 (le_of_lt hz.2))
    have hsmooth := regUniformMollifiedInitial_contDiff ρ ε hε hJₜ
    have hcoord : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec3 => regUniformMollifiedInitial ρ ε hε aₜ x j) := by
      exact hsmooth.continuousLinearMap_comp
        (ContinuousLinearMap.proj (R := ℝ) j)
    have hdiff := hcoord.differentiable (by norm_num) z.1
    have heq : (fun x : Vec3 => J j (x, z.2)) =
        fun x => regUniformMollifiedInitial ρ ε hε aₜ x j := by
      funext x
      rfl
    rw [heq]
    exact hdiff
  have hUiSpatialDiff (z : Vec3 × ℝ) (hz : z ∈ S) (i : Fin 3) :
      DifferentiableAt ℝ (fun x : Vec3 => Ui i (x, z.2)) z.1 := by
    exact regUniform_contDiffOn_spatialSlice_differentiableAt hSopen
      (hUcontDiff i) hz
  have hUiTimeDiff (z : Vec3 × ℝ) (hz : z ∈ S) (i : Fin 3) :
      DifferentiableAt ℝ (fun t : ℝ => Ui i (z.1, t)) z.2 := by
    exact regUniform_contDiffOn_timeSlice_differentiableAt hSopen
      (hUcontDiff i) hz
  have hPhiSpatialDiff (z : Vec3 × ℝ) (hz : z ∈ S) (i : Fin 3) :
      DifferentiableAt ℝ (fun x : Vec3 => Phi i (x, z.2)) z.1 := by
    exact regUniform_contDiffOn_spatialSlice_differentiableAt hSopen
      (((hφi i).1.of_le (by norm_num)).contDiffOn) hz
  have hPhiTimeDiff (z : Vec3 × ℝ) (hz : z ∈ S) (i : Fin 3) :
      DifferentiableAt ℝ (fun t : ℝ => Phi i (z.1, t)) z.2 := by
    exact regUniform_contDiffOn_timeSlice_differentiableAt hSopen
      (((hφi i).1.of_le (by norm_num)).contDiffOn) hz
  have hJpartialSlice : ∀ z ∈ S, ∀ j : Fin 3,
      DifferentiableAt ℝ (fun x : Vec3 => J j (x, z.2)) z.1 := hJdiff
  have hUiCont (i : Fin 3) : ContinuousOn (Ui i) S := by
    simpa [Ui, S, CKN.spaceTimeSet,
      regUniformParabolicHomeomorph_symm_apply] using
        regUniform_continuousOn_pullback (S := Smetric) (Sprod := S)
          (hUcont i) hSsymm
  have hDCont (i j : Fin 3) : ContinuousOn (D i j) S := by
    simpa [D, S, CKN.spaceTimeSet,
      regUniformParabolicHomeomorph_symm_apply] using
        regUniform_continuousOn_pullback (S := Smetric) (Sprod := S)
          (hDcont i j) hSsymm
  have hDDCont (i j k : Fin 3) : ContinuousOn (DD i j k) S := by
    simpa [DD, S, CKN.spaceTimeSet,
      regUniformParabolicHomeomorph_symm_apply] using
        regUniform_continuousOn_pullback (S := Smetric) (Sprod := S)
          (hDDcont i j k) hSsymm
  have hDtCont (i : Fin 3) : ContinuousOn (Dt i) S := by
    simpa [Dt, S, CKN.spaceTimeSet,
      regUniformParabolicHomeomorph_symm_apply] using
        regUniform_continuousOn_pullback (S := Smetric) (Sprod := S)
          (hDtcont i) hSsymm
  have hDpCont (i : Fin 3) : ContinuousOn (Dp i) S := by
    simpa [Dp, S, CKN.spaceTimeSet,
      regUniformParabolicHomeomorph_symm_apply] using
        regUniform_continuousOn_pullback (S := Smetric) (Sprod := S)
          (hDpcont i) hSsymm
  have hJCont (j : Fin 3) : ContinuousOn (J j) S := by
    simpa [J] using hJcont j
  have hPcont' : ContinuousOn p S := by
    change ContinuousOn (fun z : Vec3 × ℝ => p z) S
    simpa [S, CKN.spaceTimeSet,
      regUniformParabolicHomeomorph_symm_apply] using
        regUniform_continuousOn_pullback (S := Smetric) (Sprod := S)
          hPcont hSsymm
  have hPhiCont (i : Fin 3) : ContinuousOn (Phi i) S :=
    (hφi i).1.continuous.continuousOn
  have hPhiSpatialCont (i j : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial (Phi i) j z) S :=
    (hφspatialCont i j).continuousOn
  have hPhiTimeCont (i : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => timePartial (Phi i) z) S :=
    (hφtimeCont i).continuousOn
  have hPhiCompact (i : Fin 3) : HasCompactSupport (Phi i) := by
    change HasCompactSupport (fun z : Vec3 × ℝ => φ z i)
    exact (hφi i).2.1
  have hPhiSupport (i : Fin 3) : tsupport (Phi i) ⊆ S := by
    change tsupport (fun z : Vec3 × ℝ => φ z i) ⊆
      (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)
    have hsupport := (hφi i).2.2
    change tsupport (fun z : Vec3 × ℝ => φ z i) ⊆
      (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ) at hsupport
    exact hsupport
  have hPhiSpatialCompact (i j : Fin 3) : HasCompactSupport
      (fun z : Vec3 × ℝ => spatialPartial (Phi i) j z) :=
    CKN.hasCompactSupport_spatialPartial (hPhiCompact i) j
  have hPhiSpatialSupport (i j : Fin 3) : tsupport
      (fun z : Vec3 × ℝ => spatialPartial (Phi i) j z) ⊆ S :=
    (CKN.tsupport_spatialPartial_subset j).trans (hPhiSupport i)
  have hPhiTimeCompact (i : Fin 3) : HasCompactSupport
      (fun z : Vec3 × ℝ => timePartial (Phi i) z) :=
    CKN.hasCompactSupport_timePartial (hPhiCompact i)
  have hPhiTimeSupport (i : Fin 3) : tsupport
      (fun z : Vec3 × ℝ => timePartial (Phi i) z) ⊆ S :=
    (CKN.tsupport_timePartial_subset (Phi i)).trans (hPhiSupport i)
  have hUiSpatialDiff' (z : Vec3 × ℝ) (hz : z ∈ S) (i : Fin 3) :
      DifferentiableAt ℝ (fun x : Vec3 => Ui i (x, z.2)) z.1 := by
    simpa [Ui] using hUiSpatialDiff z hz i
  have hUiTimeDiff' (z : Vec3 × ℝ) (hz : z ∈ S) (i : Fin 3) :
      DifferentiableAt ℝ (fun t : ℝ => Ui i (z.1, t)) z.2 := by
    simpa [Ui] using hUiTimeDiff z hz i
  have hPhiSpatialDiff' (z : Vec3 × ℝ) (hz : z ∈ S) (i : Fin 3) :
      DifferentiableAt ℝ (fun x : Vec3 => Phi i (x, z.2)) z.1 := by
    simpa [Phi] using hPhiSpatialDiff z hz i
  have hPhiTimeDiff' (z : Vec3 × ℝ) (hz : z ∈ S) (i : Fin 3) :
      DifferentiableAt ℝ (fun t : ℝ => Phi i (z.1, t)) z.2 := by
    simpa [Phi] using hPhiTimeDiff z hz i
  let hG (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => Ui i z * Phi i z
  have hGcont (i : Fin 3) : ContinuousOn (hG i) S := by
    change ContinuousOn (Ui i * Phi i) S
    exact (hUiCont i).mul (hPhiCont i)
  have hGspatialFormula (i j : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) :
      spatialPartial (hG i) j z =
        Ui i z * spatialPartial (Phi i) j z +
          Phi i z * D i j z := by
    change spatialPartial (fun y : Vec3 × ℝ => u y i * φ y i) j z =
      u z i * spatialPartial (fun y : Vec3 × ℝ => φ y i) j z +
        φ z i * spatialPartial (fun y : Vec3 × ℝ => u y i) j z
    exact regUniform_spatialPartial_mul z.1 z.2 j
      (hUiSpatialDiff' z hz i) (hPhiSpatialDiff' z hz i)
  have hGspatialCont (i j : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial (hG i) j z) S := by
    apply ContinuousOn.congr
      ((hUiCont i).mul (hPhiSpatialCont i j) |>.add
        ((hPhiCont i).mul (hDCont i j)))
    intro z hz
    simpa [hG] using hGspatialFormula i j z hz
  have hGspatialDiff (i : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S)
      (j : Fin 3) : DifferentiableAt ℝ
        (fun x : Vec3 => hG i (x, z.2)) z.1 := by
    change DifferentiableAt ℝ
      (fun x : Vec3 => Ui i (x, z.2) * Phi i (x, z.2)) z.1
    exact (hUiSpatialDiff' z hz i).mul (hPhiSpatialDiff' z hz i)
  have hGcompact (i : Fin 3) : HasCompactSupport (hG i) := by
    change HasCompactSupport (Ui i * Phi i)
    exact (hPhiCompact i).mul_left (f := Ui i)
  have hGsupport (i : Fin 3) : tsupport (hG i) ⊆ S := by
    simpa [hG] using tsupport_mul_subset_right.trans (hPhiSupport i)
  have hTestTimeInt (i : Fin 3) : Integrable
      (fun z => Ui i z * timePartial (Phi i) z) volume :=
    regUniform_integrable_mul_of_tsupport_subset hSopen (hUiCont i)
      (hPhiTimeCont i) (hPhiTimeCompact i) (hPhiTimeSupport i)
  have hTestSpatialInt (i j : Fin 3) : Integrable
      (fun z => Ui i z * spatialPartial (Phi i) j z) volume :=
    regUniform_integrable_mul_of_tsupport_subset hSopen (hUiCont i)
      (hPhiSpatialCont i j) (hPhiSpatialCompact i j) (hPhiSpatialSupport i j)
  have hDTestSpatialInt (i j k : Fin 3) : Integrable
      (fun z => D i j z * spatialPartial (Phi k) j z) volume :=
    regUniform_integrable_mul_of_tsupport_subset hSopen (hDCont i j)
      (hPhiSpatialCont k j) (hPhiSpatialCompact k j) (hPhiSpatialSupport k j)
  have hJUTestSpatialInt (i j k : Fin 3) : Integrable
      (fun z => J j z * Ui i z * spatialPartial (Phi k) j z) volume := by
    have hbase := regUniform_integrable_mul_of_tsupport_subset hSopen
      ((hJCont j).mul (hUiCont i)) (hPhiSpatialCont k j)
      (hPhiSpatialCompact k j) (hPhiSpatialSupport k j)
    have hEq : (fun z => J j z * Ui i z * spatialPartial (Phi k) j z) =
        fun z => (J j z * Ui i z) * spatialPartial (Phi k) j z := by
      funext z
      rfl
    rw [hEq]
    exact hbase
  have hPTestSpatialInt (i : Fin 3) : Integrable
      (fun z => p z * spatialPartial (Phi i) i z) volume :=
    regUniform_integrable_mul_of_tsupport_subset hSopen hPcont'
      (hPhiSpatialCont i i) (hPhiSpatialCompact i i) (hPhiSpatialSupport i i)
  have hDpartialCont (i j : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial (D i j) j z) S := by
    have hpull := regUniform_continuousOn_pullback (S := Smetric) (Sprod := S)
      (hDDcont i j j) hSsymm
    change ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial
        (fun y : Vec3 × ℝ => spatialPartial
          (fun x : Vec3 × ℝ => u x i) j y) j z) S
    exact hpull
  have hDpartialDiff (i j : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) :
      DifferentiableAt ℝ (fun x : Vec3 => D i j (x, z.2)) z.1 := by
    simpa [D] using hDdiff z hz i j
  have hJdiff' (j : Fin 3) : ∀ z ∈ S,
      DifferentiableAt ℝ (fun x : Vec3 => J j (x, z.2)) z.1 := by
    intro z hz
    exact hJdiff z hz j
  have hIBPtime (i : Fin 3) :
      (∫ z in S, Ui i z * timePartial (Phi i) z ∂volume) =
        -∫ z in S, Dt i z * Phi i z ∂volume := by
    exact regUniform_integral_mul_timePartial_eq_neg hSopen (hUiCont i)
      (hDtCont i) (fun z hz => hUiTimeDiff' z hz i)
      (hPhiCont i) (hPhiTimeCont i) (fun z hz => hPhiTimeDiff' z hz i)
      (hPhiCompact i) (hPhiSupport i)
  have hIBPdiff (i j : Fin 3) :
      (∫ z in S, D i j z * spatialPartial (Phi i) j z ∂volume) =
        -∫ z in S, spatialPartial (D i j) j z * Phi i z ∂volume := by
    exact regUniform_integral_mul_spatialPartial_eq_neg j hSopen
      (hDCont i j) (hDpartialCont i j) (hDpartialDiff i j)
      (hPhiCont i) (hPhiSpatialCont i j) (fun z hz => hPhiSpatialDiff' z hz i)
      (hPhiCompact i) (hPhiSupport i)
  have hIBPpressure (i : Fin 3) :
      (∫ z in S, p z * spatialPartial (Phi i) i z ∂volume) =
        -∫ z in S, Dp i z * Phi i z ∂volume := by
    exact regUniform_integral_mul_spatialPartial_eq_neg i hSopen
      hPcont' (hDpCont i) hPdiff (hPhiCont i) (hPhiSpatialCont i i)
      (fun z hz => hPhiSpatialDiff' z hz i)
      (hPhiCompact i) (hPhiSupport i)
  have hIBPconv (i j : Fin 3) :
      (∫ z in S, J j z * spatialPartial (hG i) j z ∂volume) =
        -∫ z in S, spatialPartial (J j) j z * hG i z ∂volume := by
    exact regUniform_integral_mul_spatialPartial_eq_neg j hSopen
      (hJCont j) (hJpartialCont j j) (hJdiff' j)
      (hGcont i) (hGspatialCont i j)
      (fun z hz => hGspatialDiff i z hz j)
      (hGcompact i) (hGsupport i)
  have hGpartialCompact (i j : Fin 3) : HasCompactSupport
      (fun z => spatialPartial (hG i) j z) :=
    CKN.hasCompactSupport_spatialPartial (hGcompact i) j
  have hGpartialSupport (i j : Fin 3) : tsupport
      (fun z => spatialPartial (hG i) j z) ⊆ S :=
    (CKN.tsupport_spatialPartial_subset j).trans (hGsupport i)
  have hJderivGInt (i j : Fin 3) : Integrable
      (fun z => J j z * spatialPartial (hG i) j z) volume :=
    regUniform_integrable_mul_of_tsupport_subset hSopen (hJCont j)
      (hGspatialCont i j) (hGpartialCompact i j) (hGpartialSupport i j)
  have hJpartialGInt (i j : Fin 3) : Integrable
      (fun z => spatialPartial (J j) j z * hG i z) volume :=
    regUniform_integrable_mul_of_tsupport_subset hSopen
      (hJpartialCont j j) (hGcont i) (hGcompact i) (hGsupport i)
  have hJpartialGIntS (i j : Fin 3) : Integrable
      (fun z => spatialPartial (J j) j z * hG i z) (volume.restrict S) :=
    (hJpartialGInt i j).mono_measure Measure.restrict_le_self
  have hJpartialSumIntS (i : Fin 3) : Integrable
      (fun z => ∑ j : Fin 3, spatialPartial (J j) j z * hG i z)
      (volume.restrict S) := by
    apply integrable_finsetSum
    intro j hj
    exact hJpartialGIntS i j
  have hJpartialSumZero (i : Fin 3) :
      (∫ z in S, ∑ j : Fin 3,
        spatialPartial (J j) j z * hG i z ∂volume) = 0 := by
    have hpoint (z : Vec3 × ℝ) (hz : z ∈ S) :
        (∑ j : Fin 3, spatialPartial (J j) j z) * hG i z = 0 := by
      have hdiv : ∑ j : Fin 3,
          spatialPartial (J j) j z = 0 := by
        change ∑ j : Fin 3,
          spatialPartial
            (fun y : ParabolicPoint => regUniformMollifiedVelocity ρ ε hε u y j)
            j z = 0
        exact hJdiv z hz
      rw [hdiv]
      simp
    rw [setIntegral_congr_fun hSmeas (fun z hz => by
      rw [← Finset.sum_mul, hpoint z hz])]
    simp
  have hJpartialIBPSum (i : Fin 3) :
      (∫ z in S, ∑ j : Fin 3, J j z * spatialPartial (hG i) j z
        ∂volume) = 0 := by
    calc
      (∫ z in S, ∑ j : Fin 3,
          J j z * spatialPartial (hG i) j z ∂volume) =
          ∑ j : Fin 3, ∫ z in S,
            J j z * spatialPartial (hG i) j z ∂volume := by
        apply integral_finsetSum
        intro j hj
        exact (hJderivGInt i j).mono_measure Measure.restrict_le_self
      _ = -∑ j : Fin 3, ∫ z in S,
          spatialPartial (J j) j z * hG i z ∂volume := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        exact hIBPconv i j
      _ = -(∫ z in S, ∑ j : Fin 3,
          spatialPartial (J j) j z * hG i z ∂volume) := by
        have hsumIntegral :
            (∫ z in S, ∑ j : Fin 3,
              spatialPartial (J j) j z * hG i z ∂volume) =
              ∑ j : Fin 3, ∫ z in S,
                spatialPartial (J j) j z * hG i z ∂volume := by
          apply integral_finsetSum
          intro j hj
          exact hJpartialGIntS i j
        congr 1
        exact hsumIntegral.symm
      _ = 0 := by rw [hJpartialSumZero]; simp
  have hJDphiInt (i j : Fin 3) : Integrable
      (fun z => J j z * D i j z * Phi i z) volume :=
    regUniform_integrable_mul_of_tsupport_subset hSopen
      ((hJCont j).mul (hDCont i j)) (hPhiCont i)
      (hPhiCompact i) (hPhiSupport i)
  have hJDphiIntS (i j : Fin 3) : Integrable
      (fun z => J j z * D i j z * Phi i z) (volume.restrict S) :=
    (hJDphiInt i j).mono_measure Measure.restrict_le_self
  have hJUiDphiExpansion (i j : Fin 3) :
      (∫ z in S, J j z * spatialPartial (hG i) j z ∂volume) =
        (∫ z in S, J j z * Ui i z * spatialPartial (Phi i) j z ∂volume) +
          ∫ z in S, J j z * D i j z * Phi i z ∂volume := by
    have hpoint (z : Vec3 × ℝ) (hz : z ∈ S) :
        J j z * spatialPartial (hG i) j z =
          J j z * Ui i z * spatialPartial (Phi i) j z +
            J j z * D i j z * Phi i z := by
      rw [hGspatialFormula i j z hz]
      ring
    have hsum := setIntegral_congr_fun (μ := volume) hSmeas hpoint
    rw [integral_add
      ((hJUTestSpatialInt i j i).mono_measure Measure.restrict_le_self)
      (hJDphiIntS i j)] at hsum
    exact hsum
  have hConvSumZero (i : Fin 3) :
      (∫ z in S, ∑ j : Fin 3,
        J j z * Ui i z * spatialPartial (Phi i) j z ∂volume) =
      -∫ z in S, ∑ j : Fin 3,
        J j z * D i j z * Phi i z ∂volume := by
    have hleft :
        (∫ z in S, ∑ j : Fin 3,
          J j z * Ui i z * spatialPartial (Phi i) j z ∂volume) =
          ∑ j : Fin 3, ∫ z in S,
            J j z * Ui i z * spatialPartial (Phi i) j z ∂volume := by
      apply integral_finsetSum
      intro j hj
      exact (hJUTestSpatialInt i j i).mono_measure Measure.restrict_le_self
    have hright :
        (∫ z in S, ∑ j : Fin 3,
          J j z * D i j z * Phi i z ∂volume) =
          ∑ j : Fin 3, ∫ z in S, J j z * D i j z * Phi i z ∂volume := by
      apply integral_finsetSum
      intro j hj
      exact hJDphiIntS i j
    have hderivsum :
        (∫ z in S, ∑ j : Fin 3,
          J j z * spatialPartial (hG i) j z ∂volume) =
          ∑ j : Fin 3, ∫ z in S,
            J j z * spatialPartial (hG i) j z ∂volume := by
      apply integral_finsetSum
      intro j hj
      exact (hJderivGInt i j).mono_measure Measure.restrict_le_self
    have hsum :
        (∫ z in S, ∑ j : Fin 3,
          J j z * spatialPartial (hG i) j z ∂volume) =
          (∫ z in S, ∑ j : Fin 3,
            J j z * Ui i z * spatialPartial (Phi i) j z ∂volume) +
            ∫ z in S, ∑ j : Fin 3,
              J j z * D i j z * Phi i z ∂volume := by
      calc
        _ = ∑ j : Fin 3, ∫ z in S,
              J j z * spatialPartial (hG i) j z ∂volume := hderivsum
        _ = ∑ j : Fin 3, ((∫ z in S,
              J j z * Ui i z * spatialPartial (Phi i) j z ∂volume) +
              ∫ z in S, J j z * D i j z * Phi i z ∂volume) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hJUiDphiExpansion i j
        _ = (∑ j : Fin 3, ∫ z in S,
              J j z * Ui i z * spatialPartial (Phi i) j z ∂volume) +
              ∑ j : Fin 3, ∫ z in S, J j z * D i j z * Phi i z ∂volume :=
          Finset.sum_add_distrib
        _ = _ := by rw [← hleft, ← hright]
    rw [hleft, hright]
    have hzero := hJpartialIBPSum i
    rw [hsum, hleft, hright] at hzero
    exact eq_neg_of_add_eq_zero_left hzero
  have hDtPhiInt (i : Fin 3) : Integrable
      (fun z => Dt i z * Phi i z) volume :=
    regUniform_integrable_mul_of_tsupport_subset hSopen (hDtCont i)
      (hPhiCont i) (hPhiCompact i) (hPhiSupport i)
  have hDDPhiInt (i j : Fin 3) : Integrable
      (fun z => DD i j j z * Phi i z) volume :=
    regUniform_integrable_mul_of_tsupport_subset hSopen (hDDCont i j j)
      (hPhiCont i) (hPhiCompact i) (hPhiSupport i)
  have hDpPhiInt (i : Fin 3) : Integrable
      (fun z => Dp i z * Phi i z) volume :=
    regUniform_integrable_mul_of_tsupport_subset hSopen (hDpCont i)
      (hPhiCont i) (hPhiCompact i) (hPhiSupport i)
  have hQint (i : Fin 3) : Integrable (Q i) volume := by
    have hTime := (hTestTimeInt i).neg
    have hConv : Integrable
        (fun z => ∑ j : Fin 3,
          J j z * Ui i z * spatialPartial (Phi i) j z) volume := by
      apply integrable_finsetSum
      intro j hj
      exact hJUTestSpatialInt i j i
    have hDiff : Integrable
        (fun z => ∑ j : Fin 3,
          D i j z * spatialPartial (Phi i) j z) volume := by
      apply integrable_finsetSum
      intro j hj
      exact hDTestSpatialInt i j i
    exact hTime.sub hConv |>.add hDiff |>.sub (hPTestSpatialInt i)
  have hQintS (i : Fin 3) : Integrable (Q i) (volume.restrict S) :=
    (hQint i).mono_measure Measure.restrict_le_self
  let hPDECoeff (i : Fin 3) : Vec3 × ℝ → ℝ := fun z =>
    Dt i z - (∑ j : Fin 3, DD i j j z) +
      (∑ j : Fin 3, J j z * D i j z) + Dp i z
  have hPDEtimesPhiInt (i : Fin 3) : Integrable
      (fun z => hPDECoeff i z * Phi i z) volume := by
    have hDt := hDtPhiInt i
    have hDD : Integrable (fun z => ∑ j : Fin 3, DD i j j z * Phi i z) volume := by
      apply integrable_finsetSum
      intro j hj
      exact hDDPhiInt i j
    have hJD : Integrable
        (fun z => ∑ j : Fin 3, J j z * D i j z * Phi i z) volume := by
      apply integrable_finsetSum
      intro j hj
      exact hJDphiInt i j
    have hDp := hDpPhiInt i
    have hsum : (fun z => hPDECoeff i z * Phi i z) = fun z =>
        Dt i z * Phi i z - (∑ j : Fin 3, DD i j j z * Phi i z) +
          (∑ j : Fin 3, J j z * D i j z * Phi i z) + Dp i z * Phi i z := by
      funext z
      simp only [hPDECoeff, sub_mul, add_mul, Finset.sum_mul]
    rw [hsum]
    exact ((hDt.sub hDD).add hJD).add hDp
  have hPDEtimesPhiIntS (i : Fin 3) : Integrable
      (fun z => hPDECoeff i z * Phi i z) (volume.restrict S) :=
    (hPDEtimesPhiInt i).mono_measure Measure.restrict_le_self
  have hDtPhiIntS (i : Fin 3) : Integrable
      (fun z => Dt i z * Phi i z) (volume.restrict S) :=
    (hDtPhiInt i).mono_measure Measure.restrict_le_self
  have hTimeIntS (i : Fin 3) : Integrable
      (fun z => Ui i z * timePartial (Phi i) z) (volume.restrict S) :=
    (hTestTimeInt i).mono_measure Measure.restrict_le_self
  have hConvIntS (i : Fin 3) : Integrable
      (fun z => ∑ j : Fin 3,
        J j z * Ui i z * spatialPartial (Phi i) j z) (volume.restrict S) := by
    apply integrable_finsetSum
    intro j hj
    exact (hJUTestSpatialInt i j i).mono_measure Measure.restrict_le_self
  have hDiffIntS (i : Fin 3) : Integrable
      (fun z => ∑ j : Fin 3,
        D i j z * spatialPartial (Phi i) j z) (volume.restrict S) := by
    apply integrable_finsetSum
    intro j hj
    exact (hDTestSpatialInt i j i).mono_measure Measure.restrict_le_self
  have hPressureIntS (i : Fin 3) : Integrable
      (fun z => p z * spatialPartial (Phi i) i z) (volume.restrict S) :=
    (hPTestSpatialInt i).mono_measure Measure.restrict_le_self
  have hNegTimeIntS (i : Fin 3) : Integrable
      (fun z => -(Ui i z * timePartial (Phi i) z)) (volume.restrict S) :=
    (hTimeIntS i).neg
  have hNegTimeSubConvIntS (i : Fin 3) : Integrable
      (fun z => -(Ui i z * timePartial (Phi i) z) -
        ∑ j : Fin 3, J j z * Ui i z * spatialPartial (Phi i) j z)
      (volume.restrict S) := (hNegTimeIntS i).sub (hConvIntS i)
  have hNegTimeSubConvAddDiffIntS (i : Fin 3) : Integrable
      (fun z => (-(Ui i z * timePartial (Phi i) z) -
        ∑ j : Fin 3, J j z * Ui i z * spatialPartial (Phi i) j z) +
        ∑ j : Fin 3, D i j z * spatialPartial (Phi i) j z)
      (volume.restrict S) := (hNegTimeSubConvIntS i).add (hDiffIntS i)
  have hQdecomp (i : Fin 3) :
      (∫ z in S, Q i z ∂volume) =
        -(∫ z in S, Ui i z * timePartial (Phi i) z ∂volume)
          - (∫ z in S, ∑ j : Fin 3,
              J j z * Ui i z * spatialPartial (Phi i) j z ∂volume)
          + (∫ z in S, ∑ j : Fin 3,
              D i j z * spatialPartial (Phi i) j z ∂volume)
          - (∫ z in S, p z * spatialPartial (Phi i) i z ∂volume) := by
    dsimp [Q]
    rw [integral_sub (hNegTimeSubConvAddDiffIntS i) (hPressureIntS i),
      integral_add (hNegTimeSubConvIntS i) (hDiffIntS i),
      integral_sub (hNegTimeIntS i) (hConvIntS i), integral_neg,
      integral_finsetSum Finset.univ (fun j hj =>
        (hJUTestSpatialInt i j i).mono_measure Measure.restrict_le_self),
      integral_finsetSum Finset.univ (fun j hj =>
        (hDTestSpatialInt i j i).mono_measure Measure.restrict_le_self)]
  have hTimeTransform (i : Fin 3) :
      -(∫ z in S, Ui i z * timePartial (Phi i) z ∂volume) =
        ∫ z in S, Dt i z * Phi i z ∂volume := by
    rw [hIBPtime i]
    simp
  have hDiffTransform (i : Fin 3) :
      (∫ z in S, ∑ j : Fin 3,
        D i j z * spatialPartial (Phi i) j z ∂volume) =
      -∫ z in S, ∑ j : Fin 3, DD i j j z * Phi i z ∂volume := by
    calc
      _ = ∑ j : Fin 3, ∫ z in S,
          D i j z * spatialPartial (Phi i) j z ∂volume := by
        apply integral_finsetSum
        intro j hj
        exact (hDTestSpatialInt i j i).mono_measure Measure.restrict_le_self
      _ = -∑ j : Fin 3, ∫ z in S,
          DD i j j z * Phi i z ∂volume := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        have hIntEq :
            (∫ z in S, spatialPartial (D i j) j z * Phi i z ∂volume) =
              ∫ z in S, DD i j j z * Phi i z ∂volume := by
          apply setIntegral_congr_fun hSmeas
          intro z hz
          rfl
        rw [← hIntEq]
        exact hIBPdiff i j
      _ = -∫ z in S, ∑ j : Fin 3,
          DD i j j z * Phi i z ∂volume := by
        rw [integral_finsetSum Finset.univ (fun j hj =>
          (hDDPhiInt i j).mono_measure Measure.restrict_le_self)]
  have hPressureTransform (i : Fin 3) :
      -(∫ z in S, p z * spatialPartial (Phi i) i z ∂volume) =
        ∫ z in S, Dp i z * Phi i z ∂volume := by
    rw [hIBPpressure i]
    simp
  have hConvTransform (i : Fin 3) :
      -(∫ z in S, ∑ j : Fin 3,
        J j z * Ui i z * spatialPartial (Phi i) j z ∂volume) =
      ∫ z in S, ∑ j : Fin 3, J j z * D i j z * Phi i z ∂volume := by
    rw [hConvSumZero i]
    simp
  have hDDsumIntS (i : Fin 3) : Integrable
      (fun z => ∑ j : Fin 3, DD i j j z * Phi i z)
      (volume.restrict S) := by
    apply integrable_finsetSum
    intro j hj
    exact (hDDPhiInt i j).mono_measure Measure.restrict_le_self
  have hJDsumIntS (i : Fin 3) : Integrable
      (fun z => ∑ j : Fin 3, J j z * D i j z * Phi i z)
      (volume.restrict S) := by
    apply integrable_finsetSum
    intro j hj
    exact hJDphiIntS i j
  have hPDEdecomp (i : Fin 3) :
      (∫ z in S, hPDECoeff i z * Phi i z ∂volume) =
        (∫ z in S, Dt i z * Phi i z ∂volume)
          - (∫ z in S, ∑ j : Fin 3, DD i j j z * Phi i z ∂volume)
          + (∫ z in S, ∑ j : Fin 3, J j z * D i j z * Phi i z ∂volume)
          + (∫ z in S, Dp i z * Phi i z ∂volume) := by
    have hpoint (z : Vec3 × ℝ) :
        hPDECoeff i z * Phi i z =
          Dt i z * Phi i z - (∑ j : Fin 3, DD i j j z * Phi i z) +
            (∑ j : Fin 3, J j z * D i j z * Phi i z) + Dp i z * Phi i z := by
      simp only [hPDECoeff, sub_mul, add_mul, Finset.sum_mul]
    rw [setIntegral_congr_fun hSmeas (fun z hz => hpoint z)]
    have hsumInt : Integrable
        (fun z => Dt i z * Phi i z -
          (∑ j : Fin 3, DD i j j z * Phi i z) +
          (∑ j : Fin 3, J j z * D i j z * Phi i z))
        (volume.restrict S) :=
      (hDtPhiIntS i).sub (hDDsumIntS i) |>.add (hJDsumIntS i)
    have hDpS : Integrable (fun z => Dp i z * Phi i z)
        (volume.restrict S) := (hDpPhiInt i).mono_measure Measure.restrict_le_self
    have hcore :
        (∫ z in S,
          Dt i z * Phi i z -
            (∑ j : Fin 3, DD i j j z * Phi i z) +
            (∑ j : Fin 3, J j z * D i j z * Phi i z) ∂volume) =
          (∫ z in S, Dt i z * Phi i z ∂volume) -
            (∫ z in S, ∑ j : Fin 3, DD i j j z * Phi i z ∂volume) +
            (∫ z in S, ∑ j : Fin 3, J j z * D i j z * Phi i z ∂volume) := by
      calc
        _ = (∫ z in S,
              Dt i z * Phi i z -
                (∑ j : Fin 3, DD i j j z * Phi i z) ∂volume) +
              (∫ z in S, ∑ j : Fin 3, J j z * D i j z * Phi i z ∂volume) := by
          exact integral_add
            ((hDtPhiIntS i).sub (hDDsumIntS i)) (hJDsumIntS i)
        _ = _ := by
          rw [integral_sub (hDtPhiIntS i) (hDDsumIntS i)]
    calc
      (∫ z in S,
          Dt i z * Phi i z -
            (∑ j : Fin 3, DD i j j z * Phi i z) +
            (∑ j : Fin 3, J j z * D i j z * Phi i z) +
            Dp i z * Phi i z ∂volume) =
          (∫ z in S,
              Dt i z * Phi i z -
                (∑ j : Fin 3, DD i j j z * Phi i z) +
                (∑ j : Fin 3, J j z * D i j z * Phi i z) ∂volume) +
            (∫ z in S, Dp i z * Phi i z ∂volume) := by
        exact integral_add hsumInt hDpS
      _ = (∫ z in S, Dt i z * Phi i z ∂volume) -
            (∫ z in S, ∑ j : Fin 3, DD i j j z * Phi i z ∂volume) +
            (∫ z in S, ∑ j : Fin 3, J j z * D i j z * Phi i z ∂volume) +
            (∫ z in S, Dp i z * Phi i z ∂volume) := by
        rw [hcore,
          integral_finsetSum Finset.univ (fun j hj =>
            (hDDPhiInt i j).mono_measure Measure.restrict_le_self),
          integral_finsetSum Finset.univ (fun j hj => hJDphiIntS i j)]
  have hPDEzero (i : Fin 3) :
      (∫ z in S, hPDECoeff i z * Phi i z ∂volume) = 0 := by
    have hpoint (z : Vec3 × ℝ) (hz : z ∈ S) :
        hPDECoeff i z * Phi i z = 0 := by
      have heq := hEquation z hz.2 i
      have hcoeff : hPDECoeff i z = 0 := by
        simpa [hPDECoeff, D, DD, Dt, Dp, J] using heq
      rw [hcoeff]
      simp
    rw [setIntegral_congr_fun hSmeas hpoint]
    simp
  have hQzero (i : Fin 3) : (∫ z in S, Q i z ∂volume) = 0 := by
    rw [hQdecomp i]
    simp only [sub_eq_add_neg]
    rw [hTimeTransform i, hConvTransform i,
      hDiffTransform i, hPressureTransform i]
    have hcombine :
        (∫ z in S, Dt i z * Phi i z ∂volume)
          + (∫ z in S, ∑ j : Fin 3,
              J j z * D i j z * Phi i z ∂volume)
          - (∫ z in S, ∑ j : Fin 3,
              DD i j j z * Phi i z ∂volume)
          + (∫ z in S, Dp i z * Phi i z ∂volume) =
        ∫ z in S, hPDECoeff i z * Phi i z ∂volume := by
      calc
        _ = (∫ z in S, Dt i z * Phi i z ∂volume)
              - (∫ z in S, ∑ j : Fin 3, DD i j j z * Phi i z ∂volume)
              + (∫ z in S, ∑ j : Fin 3, J j z * D i j z * Phi i z ∂volume)
              + (∫ z in S, Dp i z * Phi i z ∂volume) := by ring
        _ = _ := hPDEdecomp i |>.symm
    exact (hcombine.trans (hPDEzero i))
  have hQsumIntS : Integrable (fun z => ∑ i : Fin 3, Q i z)
      (volume.restrict S) :=
    integrable_finsetSum Finset.univ (fun i hi => hQintS i)
  change (∫ z : Vec3 × ℝ in S,
    (-(∑ i : Fin 3, Ui i z * timePartial (Phi i) z)
      - ∑ i : Fin 3, ∑ j : Fin 3,
        J j z * Ui i z * spatialPartial (Phi i) j z
      + ∑ i : Fin 3, ∑ j : Fin 3,
        D i j z * spatialPartial (Phi i) j z
      - p z * (∑ i : Fin 3, spatialPartial (Phi i) i z))) = 0
  rw [setIntegral_congr_fun
    (g := fun z : Vec3 × ℝ => ∑ i : Fin 3, Q i z) hSmeas (fun z hz => by
    simp [Q, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.mul_sum])]
  rw [integral_finsetSum Finset.univ (fun i hi => hQintS i)]
  simp_rw [hQzero]
  simp
end CKN.Leray
end
