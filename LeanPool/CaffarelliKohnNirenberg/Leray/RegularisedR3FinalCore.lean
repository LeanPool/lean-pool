/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEquationIntervalWeak
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEquationIntervalComponent
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEquationResidual
public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformIntegrationByParts
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformMomentum
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedConvolutionSmooth
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedEnergyForm
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationBasics

/-!
# The regularized momentum equation on a finite interval: the core

(R3) of `thm:regularised` on `[0, T]`: a velocity that satisfies the regularized
mild equation `eq:reg-mild` on `[0, T]`, and has continuous slices and classical
regularity on `(0, T]`, solves the regularized momentum equation pointwise on
`(0, T)`. This holds in divergence form and, since `J_ε u` is divergence
free, in transport form. The pressure is the canonical Riesz pressure of each
slice, as in (R4). The interval weak momentum identity is tested against scalar
components. After integration by parts, the continuous residual vanishes.
-/

public section

open MeasureTheory Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

abbrev regularisedR3FinalBaseTopology :
    TopologicalSpace ParabolicPoint := inferInstance

section ProductRegularity

local instance regularisedR3FinalProductNormedAddCommGroup :
    NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

local instance regularisedR3FinalProductNormedSpace : NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))


private theorem regularisedR3Final_contDiffOn_mono
    {S S' : Set (Vec3 × ℝ)} {f : ParabolicPoint → ℝ}
    (hf : ContDiffOn ℝ 1 f S') (hSS' : S ⊆ S') : ContDiffOn ℝ 1 f S :=
  hf.mono hSS'

private theorem regularisedR3Final_contDiffOn_congr
    {S : Set (Vec3 × ℝ)} {f g : ParabolicPoint → ℝ}
    (hf : ContDiffOn ℝ 1 f S) (hfg : ∀ z ∈ S, f z = g z) :
    ContDiffOn ℝ 1 g S :=
  ContDiffOn.congr hf (fun z hz => (hfg z hz).symm)

end ProductRegularity

/-- The interval weak momentum identity determines the pointwise equation
and the canonical pressure of the regularized mild path (thm:regularised). -/
theorem regularisedR3Final_core
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
    (hUcontinuous : letI : TopologicalSpace ParabolicPoint :=
      regularisedR3FinalBaseTopology
      ∀ i : Fin 3, ContinuousOn (fun z => u z i)
        (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hDcontinuous : letI : TopologicalSpace ParabolicPoint :=
      regularisedR3FinalBaseTopology
      ∀ i j : Fin 3, ContinuousOn
        (fun z => spatialPartial (fun y => u y i) j z)
        (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hDDcontinuous : letI : TopologicalSpace ParabolicPoint :=
      regularisedR3FinalBaseTopology
      ∀ i j k : Fin 3, ContinuousOn
        (fun z => spatialPartial
          (fun y => spatialPartial (fun x => u x i) j y) k z)
        (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hDtcontinuous : letI : TopologicalSpace ParabolicPoint :=
      regularisedR3FinalBaseTopology
      ∀ i : Fin 3, ContinuousOn
        (fun z => timePartial (fun y => u y i) z)
        (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hPcontinuous : letI : TopologicalSpace ParabolicPoint :=
      regularisedR3FinalBaseTopology
      ContinuousOn
        (regularisedIntervalCanonicalPressure ρ ε hε u T hT.le hSlice)
        (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hDpcontinuous : letI : TopologicalSpace ParabolicPoint :=
      regularisedR3FinalBaseTopology
      ∀ i : Fin 3, ContinuousOn
        (fun z => spatialPartial
          (fun y => regularisedIntervalCanonicalPressure
            ρ ε hε u T hT.le hSlice y) i z)
        (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hUjoint : letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
      letI : NormedAddCommGroup ParabolicPoint :=
        inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
      letI : NormedSpace ℝ ParabolicPoint :=
        inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
      ∀ i : Fin 3, ContDiffOn ℝ 1 (fun z => u z i)
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
    (∀ t : ℝ, ∀ ht : t ∈ Set.Icc 0 T,
      (fun x : Vec3 => regularisedIntervalCanonicalPressure
        ρ ε hε u T hT.le hSlice (x, t)) =ᵐ[volume]
      rieszPressureSliceRepresentative 2 (by norm_num)
        (forcedPressureTensorLp (regularizedMildTensor ρ ε hε
          (realVectorL2OfCoordinateFunction (fun x : Vec3 => u (x, t))
            (hSlice t ht))))) := by
  classical
  let S : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T
  let Sreg : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ Set.Ioc 0 T
  have hSopen : IsOpen S := isOpen_univ.prod isOpen_Ioo
  have hSmeas : MeasurableSet S :=
    MeasurableSet.prod MeasurableSet.univ measurableSet_Ioo
  have hSsymm : ∀ z ∈ S, ((z.1, z.2) : ParabolicPoint) ∈
      spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T) := by
    intro z hz
    exact ⟨Set.mem_univ _, ⟨hz.2.1, le_of_lt hz.2.2⟩⟩
  let J : ParabolicPoint → Vec3 :=
    regUniformMollifiedVelocity ρ ε hε u
  let D (i j : Fin 3) : Vec3 × ℝ → ℝ := fun z =>
    spatialPartial (fun y => u y i) j z
  let DD (i j k : Fin 3) : Vec3 × ℝ → ℝ := fun z =>
    spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z
  let Dt (i : Fin 3) : Vec3 × ℝ → ℝ := fun z =>
    timePartial (fun y => u y i) z
  let P : ParabolicPoint → ℝ :=
    regularisedIntervalCanonicalPressure ρ ε hε u T hT.le hSlice
  let Dp (i : Fin 3) : Vec3 × ℝ → ℝ := fun z =>
    spatialPartial (fun y => P y) i z
  let Ui (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => u z i
  have hUiCont (i : Fin 3) : ContinuousOn (Ui i) S := by
    simpa [Ui, S, CKN.spaceTimeSet] using
      regUniform_continuousOn_pullback
        (S := spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T))
        (Sprod := S) (hUcontinuous i) hSsymm
  have hDCont (i j : Fin 3) : ContinuousOn (D i j) S := by
    simpa [D, S, CKN.spaceTimeSet] using
      regUniform_continuousOn_pullback
        (S := spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T))
        (Sprod := S) (hDcontinuous i j) hSsymm
  have hDDCont (i j k : Fin 3) : ContinuousOn (DD i j k) S := by
    simpa [DD, S, CKN.spaceTimeSet] using
      regUniform_continuousOn_pullback
        (S := spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T))
        (Sprod := S) (hDDcontinuous i j k) hSsymm
  have hDtCont (i : Fin 3) : ContinuousOn (Dt i) S := by
    simpa [Dt, S, CKN.spaceTimeSet] using
      regUniform_continuousOn_pullback
        (S := spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T))
        (Sprod := S) (hDtcontinuous i) hSsymm
  have hPCont : ContinuousOn (fun z : Vec3 × ℝ => P z) S := by
    simpa [P, S, CKN.spaceTimeSet] using
      regUniform_continuousOn_pullback
        (S := spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T))
        (Sprod := S) hPcontinuous hSsymm
  have hDpCont (i : Fin 3) : ContinuousOn (Dp i) S := by
    simpa [Dp, P, S, CKN.spaceTimeSet] using
      regUniform_continuousOn_pullback
        (S := spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T))
        (Sprod := S) (hDpcontinuous i) hSsymm
  have hUjointS (i : Fin 3) :
      letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
      letI : NormedAddCommGroup ParabolicPoint :=
        inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
      letI : NormedSpace ℝ ParabolicPoint :=
        inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
      ContDiffOn ℝ 1 (fun z : ParabolicPoint => u z i) S := by
    exact regularisedR3Final_contDiffOn_mono (hUjoint i)
      (fun z hz => hSsymm z hz)
  let uExt : ParabolicPoint → Vec3 := fun z => if z.2 ≤ T then u z else 0
  have hSliceExt (t : ℝ) (ht : 0 < t) :
      MemLp (fun x : Vec3 => uExt (x, t)) 2 volume := by
    by_cases htT : t ≤ T
    · have htIcc : t ∈ Set.Icc 0 T := ⟨le_of_lt ht, htT⟩
      simpa [uExt, htT] using hSlice t htIcc
    · simp [uExt, htT]
  have hExtSliceEq (t : ℝ) (htT : t ≤ T) :
      regUniformVelocitySlice uExt t = regUniformVelocitySlice u t := by
    funext x
    simp [regUniformVelocitySlice, uExt, htT]
  have hUExtContDiff (i : Fin 3) :
      letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
      letI : NormedAddCommGroup ParabolicPoint :=
        inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
      letI : NormedSpace ℝ ParabolicPoint :=
        inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
      ContDiffOn ℝ 1 (fun z : ParabolicPoint => uExt z i) S := by
    apply regularisedR3Final_contDiffOn_congr (hUjointS i)
    intro z hz
    simp [uExt, hz.2.2.le]
  have hSpositive : ∀ z ∈ S, 0 < z.2 := fun z hz => hz.2.1
  have hSshift : ∀ z ∈ S, ∀ y : Vec3, (z.1 - y, z.2) ∈ S := by
    intro z hz y
    exact ⟨Set.mem_univ _, hz.2⟩
  have hJcont := regUniform_mollified_velocity_continuousOn
    ρ ε hε (u := uExt) (S := S) hSliceExt hUExtContDiff
    hSpositive hSshift
  have hJpartialCont := regUniform_mollified_velocity_spatialPartial_continuousOn
    ρ ε hε (u := uExt) (S := S) hSliceExt hUExtContDiff
    hSpositive hSshift
  have hJCont (j : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => J (z.1, z.2) j) S := by
    apply (hJcont j).congr
    intro z hz
    change regUniformMollifiedVelocity ρ ε hε u
        ((z.1, z.2) : ParabolicPoint) j =
      regUniformMollifiedVelocity ρ ε hε uExt
        ((z.1, z.2) : ParabolicPoint) j
    unfold regUniformMollifiedVelocity
    rw [hExtSliceEq z.2 hz.2.2.le]
  have hJpartialC (j k : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial
        (fun y => J y j) k z) S := by
    apply (hJpartialCont j k).congr
    intro z hz
    change (fderiv ℝ (fun x : Vec3 =>
        regUniformMollifiedVelocity ρ ε hε u (x, z.2) j) z.1)
          (basisVec k) =
      (fderiv ℝ (fun x : Vec3 =>
        regUniformMollifiedVelocity ρ ε hε uExt (x, z.2) j) z.1)
          (basisVec k)
    have hfun : (fun x : Vec3 =>
        regUniformMollifiedVelocity ρ ε hε u (x, z.2) j) =
      (fun x : Vec3 =>
        regUniformMollifiedVelocity ρ ε hε uExt (x, z.2) j) := by
      funext x
      unfold regUniformMollifiedVelocity
      rw [hExtSliceEq z.2 hz.2.2.le]
    rw [hfun]
  have hJdiff (z : Vec3 × ℝ) (hz : z ∈ S) (j : Fin 3) :
      DifferentiableAt ℝ (fun x : Vec3 => J (x, z.2) j) z.1 := by
    let sliceU : Vec3 → Vec3 := fun x => u (x, z.2)
    have hat : MemLp sliceU 2 volume := hSlice z.2 ⟨hz.2.1.le, hz.2.2.le⟩
    have hsmooth := regUniformMollifiedInitial_contDiff_of_memLp ρ ε hε hat
    have hcoord : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec3 => regUniformMollifiedInitial ρ ε hε sliceU x j) :=
      hsmooth.continuousLinearMap_comp (ContinuousLinearMap.proj (R := ℝ) j)
    have hdiff := hcoord.differentiable (by norm_num) z.1
    have heq : (fun x : Vec3 => J (x, z.2) j) =
        fun x => regUniformMollifiedInitial ρ ε hε sliceU x j := by
      funext x
      rfl
    rw [heq]
    exact hdiff
  have hUiSpaceDiff (z : Vec3 × ℝ) (hz : z ∈ S) (i : Fin 3) :
      DifferentiableAt ℝ (fun x : Vec3 => Ui i (x, z.2)) z.1 := by
    simpa [Ui] using regUniform_contDiffOn_spatialSlice_differentiableAt
      hSopen (hUjointS i) hz
  have hUiTimeDiff (z : Vec3 × ℝ) (hz : z ∈ S) (i : Fin 3) :
      DifferentiableAt ℝ (fun t : ℝ => Ui i (z.1, t)) z.2 := by
    simpa [Ui] using regUniform_contDiffOn_timeSlice_differentiableAt
      hSopen (hUjointS i) hz
  have hDdiff' (z : Vec3 × ℝ) (hz : z ∈ S) (i j : Fin 3) :
      DifferentiableAt ℝ (fun x : Vec3 => D i j (x, z.2)) z.1 := by
    simpa [D] using hDdiff ((z.1, z.2) : ParabolicPoint) (by
      exact ⟨Set.mem_univ _, hz.2.1, hz.2.2.le⟩) i j
  have hPdiff' (z : Vec3 × ℝ) (hz : z ∈ S) :
      DifferentiableAt ℝ (fun x : Vec3 => P (x, z.2)) z.1 := by
    simpa [P] using hPdiff ((z.1, z.2) : ParabolicPoint) (by
      exact ⟨Set.mem_univ _, hz.2.1, hz.2.2.le⟩)
  have hUptimeDiff (z : Vec3 × ℝ) (hz : z ∈ S) (i : Fin 3) :
      DifferentiableAt ℝ (fun t : ℝ => Ui i (z.1, t)) z.2 := hUiTimeDiff z hz i
  let G (i j : Fin 3) : Vec3 × ℝ → ℝ := fun z => J (z.1, z.2) j * Ui i z
  have hGcont (i j : Fin 3) : ContinuousOn (G i j) S := by
    change ContinuousOn
      ((fun z : Vec3 × ℝ => J (z.1, z.2) j) * Ui i) S
    exact (hJCont j).mul (hUiCont i)
  have hGpartialFormula (i j : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) :
      spatialPartial (show ParabolicPoint → ℝ from G i j) j z =
        J (z.1, z.2) j * D i j z +
          Ui i z * spatialPartial (fun y => J y j) j z := by
    change spatialPartial
        (fun y : Vec3 × ℝ => J (y.1, y.2) j * Ui i y) j z = _
    exact regUniform_spatialPartial_mul z.1 z.2 j
      (hJdiff z hz j) (hUiSpaceDiff z hz i)
  have hGpartialCont (i j : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial (show ParabolicPoint → ℝ from G i j) j z) S := by
    apply ContinuousOn.congr
      ((hJCont j).mul (hDCont i j) |>.add ((hUiCont i).mul (hJpartialC j j)))
    intro z hz
    exact hGpartialFormula i j z hz
  have hGdiff (i j : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) :
      DifferentiableAt ℝ (fun x : Vec3 => G i j (x, z.2)) z.1 := by
    change DifferentiableAt ℝ
      (fun x : Vec3 => J (x, z.2) j * Ui i (x, z.2)) z.1
    exact (hJdiff z hz j).mul (hUiSpaceDiff z hz i)
  have hWeakVector : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3)
        (Set.univ : Set Vec3) (Set.Ioo 0 T) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Set.Ioo 0 T),
        (-(∑ k : Fin 3, u z k * timePartial (fun y => φ y k) z)
          - ∑ k : Fin 3, ∑ j : Fin 3,
            J z j * u z k * spatialPartial (fun y => φ y k) j z
          + ∑ k : Fin 3, ∑ j : Fin 3,
            spatialPartial (fun y => u y k) j z *
              spatialPartial (fun y => φ y k) j z
          - P z * (∑ k : Fin 3, spatialPartial (fun y => φ y k) k z)) = 0 := by
    intro φ hφ
    exact regularisedInterval_weakMomentum ρ ε hε a ha u T hT hSlice
      hL2Continuous hMild hUcontinuous hDcontinuous hPcontinuous hUjoint φ hφ
  have hDivPoint : ∀ z : ParabolicPoint,
      z ∈ spaceTimeSet (Set.univ : Set Vec3) (Set.Ioo 0 T) →
      ∀ i : Fin 3,
        timePartial (fun y => u y i) z -
          (∑ j : Fin 3, spatialPartial
            (fun y => spatialPartial (fun x => u x i) j y) j z) +
          (∑ j : Fin 3,
            spatialPartial (fun y => regUniformMollifiedVelocity ρ ε hε u y j * u y i) j z) +
          spatialPartial (fun y => regularisedIntervalCanonicalPressure
            ρ ε hε u T hT.le hSlice y) i z = 0 := by
    have hzero : ∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ (Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T →
      ∫ z in S,
          (timePartial (fun y => u y i) z -
            (∑ j : Fin 3, spatialPartial
              (fun y => spatialPartial (fun x => u x i) j y) j z) +
            (∑ j : Fin 3, spatialPartial
              (fun y => regUniformMollifiedVelocity ρ ε hε u y j * u y i) j z) +
            spatialPartial (fun y => P y) i z) * ψ z = 0 := by
      intro i ψ hψ hψc hψs
      have hψTest : ψ ∈ spaceTimeTestFunction (V := ℝ)
          (Set.univ : Set Vec3) (Set.Ioo 0 T) := ⟨hψ, hψc, hψs⟩
      have hscalar := regularisedInterval_scalarWeakMomentum_of_vector
        T u J (fun z i j => spatialPartial (fun y => u y i) j z) P
        hWeakVector i ψ hψTest
      have hPsiCont : ContinuousOn ψ S := hψ.continuous.continuousOn
      have hPsiTimeCont : ContinuousOn
          (fun z : Vec3 × ℝ => timePartial (show ParabolicPoint → ℝ from ψ) z) S := by
        have hfd : Continuous (fun z : Vec3 × ℝ =>
            (fderiv ℝ ψ z) (0, 1)) :=
          (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
        apply hfd.continuousOn.congr
        intro z hz
        exact timePartial_eq_joint_fderiv hψ z
      have hPsiSpaceCont (j : Fin 3) : ContinuousOn
          (fun z : Vec3 × ℝ => spatialPartial (show ParabolicPoint → ℝ from ψ) j z) S := by
        have hfd : Continuous (fun z : Vec3 × ℝ =>
            (fderiv ℝ ψ z) (basisVec j, 0)) :=
          (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
        apply hfd.continuousOn.congr
        intro z hz
        exact spatialPartial_eq_joint_fderiv hψ z j
      have hPsiC1On : ContDiffOn ℝ 1 ψ S :=
        (hψ.of_le (by norm_num)).contDiffOn
      have hPsiTimeDiff (z : Vec3 × ℝ) (hz : z ∈ S) :
          DifferentiableAt ℝ (fun t : ℝ => ψ (z.1, t)) z.2 :=
        regUniform_contDiffOn_timeSlice_differentiableAt hSopen hPsiC1On hz
      have hPsiSpaceDiff (z : Vec3 × ℝ) (hz : z ∈ S) :
          DifferentiableAt ℝ (fun x : Vec3 => ψ (x, z.2)) z.1 :=
        regUniform_contDiffOn_spatialSlice_differentiableAt hSopen hPsiC1On hz
      have hPsiTimeCompact : HasCompactSupport
          (fun z : Vec3 × ℝ => timePartial (show ParabolicPoint → ℝ from ψ) z) :=
        CKN.hasCompactSupport_timePartial hψc
      have hPsiTimeSupport : tsupport
          (fun z : Vec3 × ℝ => timePartial (show ParabolicPoint → ℝ from ψ) z) ⊆ S :=
        (CKN.tsupport_timePartial_subset ψ).trans hψs
      have hPsiSpaceCompact (j : Fin 3) : HasCompactSupport
          (fun z : Vec3 × ℝ => spatialPartial (show ParabolicPoint → ℝ from ψ) j z) :=
        CKN.hasCompactSupport_spatialPartial hψc j
      have hPsiSpaceSupport (j : Fin 3) : tsupport
          (fun z : Vec3 × ℝ => spatialPartial (show ParabolicPoint → ℝ from ψ) j z) ⊆ S :=
        (CKN.tsupport_spatialPartial_subset j).trans hψs
      have hAint (i : Fin 3) : Integrable
          (fun z : Vec3 × ℝ => Ui i z * timePartial (show ParabolicPoint → ℝ from ψ) z) (volume.restrict S) := by
        exact (regUniform_integrable_mul_of_tsupport_subset hSopen (hUiCont i)
          hPsiTimeCont hPsiTimeCompact hPsiTimeSupport).mono_measure Measure.restrict_le_self
      have hBint (i j : Fin 3) : Integrable
          (fun z : Vec3 × ℝ => G i j z * spatialPartial (show ParabolicPoint → ℝ from ψ) j z) (volume.restrict S) := by
        exact (regUniform_integrable_mul_of_tsupport_subset hSopen (hGcont i j)
          (hPsiSpaceCont j) (hPsiSpaceCompact j) (hPsiSpaceSupport j)).mono_measure
            Measure.restrict_le_self
      have hCint (i j : Fin 3) : Integrable
          (fun z : Vec3 × ℝ => D i j z * spatialPartial (show ParabolicPoint → ℝ from ψ) j z) (volume.restrict S) := by
        exact (regUniform_integrable_mul_of_tsupport_subset hSopen (hDCont i j)
          (hPsiSpaceCont j) (hPsiSpaceCompact j) (hPsiSpaceSupport j)).mono_measure
            Measure.restrict_le_self
      have hEint (i : Fin 3) : Integrable
          (fun z : Vec3 × ℝ => P (z.1, z.2) * spatialPartial (show ParabolicPoint → ℝ from ψ) i z) (volume.restrict S) := by
        exact (regUniform_integrable_mul_of_tsupport_subset hSopen hPCont
          (hPsiSpaceCont i) (hPsiSpaceCompact i) (hPsiSpaceSupport i)).mono_measure
            Measure.restrict_le_self
      have hR1int (i : Fin 3) : Integrable
          (fun z : Vec3 × ℝ => Dt i z * ψ z) (volume.restrict S) := by
        exact (regUniform_integrable_mul_of_tsupport_subset hSopen (hDtCont i)
          hPsiCont hψc hψs).mono_measure Measure.restrict_le_self
      have hR2int (i j : Fin 3) : Integrable
          (fun z : Vec3 × ℝ => spatialPartial (show ParabolicPoint → ℝ from G i j) j z * ψ z)
          (volume.restrict S) := by
        exact (regUniform_integrable_mul_of_tsupport_subset hSopen (hGpartialCont i j)
          hPsiCont hψc hψs).mono_measure Measure.restrict_le_self
      have hR3int (i j : Fin 3) : Integrable
          (fun z : Vec3 × ℝ => DD i j j z * ψ z) (volume.restrict S) := by
        exact (regUniform_integrable_mul_of_tsupport_subset hSopen (hDDCont i j j)
          hPsiCont hψc hψs).mono_measure Measure.restrict_le_self
      have hR4int (i : Fin 3) : Integrable
          (fun z : Vec3 × ℝ => Dp i z * ψ z) (volume.restrict S) := by
        exact (regUniform_integrable_mul_of_tsupport_subset hSopen (hDpCont i)
          hPsiCont hψc hψs).mono_measure Measure.restrict_le_self
      have hIBPtime (i : Fin 3) :
          (∫ z in S, Ui i z * timePartial (show ParabolicPoint → ℝ from ψ) z) =
          -∫ z in S, Dt i z * ψ z := by
        exact regUniform_integral_mul_timePartial_eq_neg hSopen (hUiCont i)
          (hDtCont i) (fun z hz => hUiTimeDiff z hz i)
          hPsiCont hPsiTimeCont hPsiTimeDiff hψc hψs
      have hIBPconv (i j : Fin 3) :
          (∫ z in S, G i j z * spatialPartial (show ParabolicPoint → ℝ from ψ) j z) =
          -∫ z in S, spatialPartial (show ParabolicPoint → ℝ from G i j) j z * ψ z := by
        exact regUniform_integral_mul_spatialPartial_eq_neg j hSopen
          (hGcont i j) (hGpartialCont i j) (hGdiff i j)
          hPsiCont (hPsiSpaceCont j) (fun z hz => hPsiSpaceDiff z hz)
          hψc hψs
      have hIBPdiff (i j : Fin 3) :
          (∫ z in S, D i j z * spatialPartial (show ParabolicPoint → ℝ from ψ) j z) =
          -∫ z in S, DD i j j z * ψ z := by
        exact regUniform_integral_mul_spatialPartial_eq_neg j hSopen
          (hDCont i j) (hDDCont i j j) (fun z hz => hDdiff' z hz i j)
          hPsiCont (hPsiSpaceCont j) (fun z hz => hPsiSpaceDiff z hz)
          hψc hψs
      have hIBPpressure (i : Fin 3) :
          (∫ z in S, P (z.1, z.2) * spatialPartial (show ParabolicPoint → ℝ from ψ) i z) =
          -∫ z in S, Dp i z * ψ z := by
        exact regUniform_integral_mul_spatialPartial_eq_neg i hSopen hPCont
          (hDpCont i) (fun z hz => hPdiff' z hz)
          hPsiCont (hPsiSpaceCont i) (fun z hz => hPsiSpaceDiff z hz)
          hψc hψs
      have hWeakProduct : ∫ z in S,
          (Dt i z - ∑ j : Fin 3, DD i j j z +
            ∑ j : Fin 3, spatialPartial (show ParabolicPoint → ℝ from G i j) j z + Dp i z) * ψ z = 0 := by
        let hscalarPairIntegrand : Vec3 × ℝ → ℝ := fun z =>
            (-(u (parabolicHomeomorph.symm z) i *
                timePartial (show ParabolicPoint → ℝ from ψ) (parabolicHomeomorph.symm z))
              - ∑ j : Fin 3, J (parabolicHomeomorph.symm z) j *
                  u (parabolicHomeomorph.symm z) i *
                spatialPartial (show ParabolicPoint → ℝ from ψ) j (parabolicHomeomorph.symm z)
              + ∑ j : Fin 3,
                spatialPartial (fun y => u y i) j (parabolicHomeomorph.symm z) *
                  spatialPartial (show ParabolicPoint → ℝ from ψ) j (parabolicHomeomorph.symm z)
              - P (parabolicHomeomorph.symm z) *
                spatialPartial (show ParabolicPoint → ℝ from ψ) i (parabolicHomeomorph.symm z))
        have hscalarS : ∫ z in S, hscalarPairIntegrand z = 0 := by
          have hbridge := CKN.setIntegral_parabolic_to_product
            (Ω := (Set.univ : Set Vec3)) (I := Set.Ioo 0 T)
            (F := fun z : ParabolicPoint =>
              (-(u z i * timePartial (show ParabolicPoint → ℝ from ψ) z)
                - ∑ j : Fin 3, J z j * u z i * spatialPartial (show ParabolicPoint → ℝ from ψ) j z
                + ∑ j : Fin 3, spatialPartial (fun y => u y i) j z *
                  spatialPartial (show ParabolicPoint → ℝ from ψ) j z
                - P z * spatialPartial (show ParabolicPoint → ℝ from ψ) i z))
          simpa [hscalarPairIntegrand, S, CKN.spaceTimeSet,
            parabolicHomeomorph_symm_apply] using hbridge.symm.trans hscalar
        have hA : Integrable (fun z : Vec3 × ℝ => Ui i z *
            timePartial (show ParabolicPoint → ℝ from ψ) z) (volume.restrict S) := hAint i
        have hB : Integrable (fun z : Vec3 × ℝ => ∑ j : Fin 3,
            G i j z * spatialPartial (show ParabolicPoint → ℝ from ψ) j z)
            (volume.restrict S) := by
          apply integrable_finsetSum
          intro j hj
          exact hBint i j
        have hC : Integrable (fun z : Vec3 × ℝ => ∑ j : Fin 3,
            D i j z * spatialPartial (show ParabolicPoint → ℝ from ψ) j z)
            (volume.restrict S) := by
          apply integrable_finsetSum
          intro j hj
          exact hCint i j
        have hE : Integrable (fun z : Vec3 × ℝ => P (z.1, z.2) *
            spatialPartial (show ParabolicPoint → ℝ from ψ) i z) (volume.restrict S) := hEint i
        have hNegA : Integrable (fun z : Vec3 × ℝ => -(Ui i z *
            timePartial (show ParabolicPoint → ℝ from ψ) z)) (volume.restrict S) := hA.neg
        have hAB : Integrable (fun z : Vec3 × ℝ => -(Ui i z *
            timePartial (show ParabolicPoint → ℝ from ψ) z) -
            ∑ j : Fin 3, G i j z * spatialPartial (show ParabolicPoint → ℝ from ψ) j z) (volume.restrict S) := hNegA.sub hB
        have hABC : Integrable (fun z : Vec3 × ℝ => -(Ui i z *
            timePartial (show ParabolicPoint → ℝ from ψ) z) -
            ∑ j : Fin 3, G i j z * spatialPartial (show ParabolicPoint → ℝ from ψ) j z +
            ∑ j : Fin 3, D i j z * spatialPartial (show ParabolicPoint → ℝ from ψ) j z) (volume.restrict S) := hAB.add hC
        have hWeakExpand :
            (∫ z in S, (-(Ui i z * timePartial (show ParabolicPoint → ℝ from ψ) z)
              - ∑ j : Fin 3, G i j z * spatialPartial (show ParabolicPoint → ℝ from ψ) j z
              + ∑ j : Fin 3, D i j z * spatialPartial (show ParabolicPoint → ℝ from ψ) j z
              - P (z.1, z.2) * spatialPartial (show ParabolicPoint → ℝ from ψ) i z)) =
            (-(∫ z in S, Ui i z * timePartial (show ParabolicPoint → ℝ from ψ) z))
              - (∫ z in S, ∑ j : Fin 3, G i j z * spatialPartial (show ParabolicPoint → ℝ from ψ) j z)
              + (∫ z in S, ∑ j : Fin 3, D i j z * spatialPartial (show ParabolicPoint → ℝ from ψ) j z)
              - (∫ z in S, P (z.1, z.2) * spatialPartial (show ParabolicPoint → ℝ from ψ) i z) := by
          rw [integral_sub hABC hE, integral_add hAB hC,
            integral_sub hNegA hB, integral_neg]
        have hBsum : (∫ z in S, ∑ j : Fin 3, G i j z *
            spatialPartial (show ParabolicPoint → ℝ from ψ) j z) =
            ∑ j : Fin 3, ∫ z in S, G i j z *
              spatialPartial (show ParabolicPoint → ℝ from ψ) j z := by
          apply integral_finsetSum
          intro j hj
          exact hBint i j
        have hCsum : (∫ z in S, ∑ j : Fin 3, D i j z *
            spatialPartial (show ParabolicPoint → ℝ from ψ) j z) =
            ∑ j : Fin 3, ∫ z in S, D i j z *
              spatialPartial (show ParabolicPoint → ℝ from ψ) j z := by
          apply integral_finsetSum
          intro j hj
          exact hCint i j
        have hIBPconvSum : (∫ z in S, ∑ j : Fin 3, G i j z *
            spatialPartial (show ParabolicPoint → ℝ from ψ) j z) =
            -∫ z in S, ∑ j : Fin 3, spatialPartial (show ParabolicPoint → ℝ from G i j) j z * ψ z := by
          rw [hBsum]
          calc
            _ = ∑ j : Fin 3, -(∫ z in S,
                spatialPartial (show ParabolicPoint → ℝ from G i j) j z * ψ z) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [hIBPconv i j]
            _ = -∫ z in S, ∑ j : Fin 3,
                spatialPartial (show ParabolicPoint → ℝ from G i j) j z * ψ z := by
              calc
                _ = -(∑ j : Fin 3, ∫ z in S,
                    spatialPartial (show ParabolicPoint → ℝ from G i j) j z * ψ z) := by
                  rw [Finset.sum_neg_distrib]
                _ = -∫ z in S, ∑ j : Fin 3,
                    spatialPartial (show ParabolicPoint → ℝ from G i j) j z * ψ z := by
                  congr 1
                  symm
                  apply integral_finsetSum
                  intro j hj
                  exact hR2int i j
        have hIBPdiffSum : (∫ z in S, ∑ j : Fin 3, D i j z *
            spatialPartial (show ParabolicPoint → ℝ from ψ) j z) =
            -∫ z in S, ∑ j : Fin 3, DD i j j z * ψ z := by
          rw [hCsum]
          calc
            _ = ∑ j : Fin 3, -(∫ z in S, DD i j j z * ψ z) := by
              apply Finset.sum_congr rfl
              intro j hj
              exact hIBPdiff i j
            _ = -∫ z in S, ∑ j : Fin 3, DD i j j z * ψ z := by
              calc
                _ = -(∑ j : Fin 3, ∫ z in S, DD i j j z * ψ z) := by
                  rw [Finset.sum_neg_distrib]
                _ = -∫ z in S, ∑ j : Fin 3, DD i j j z * ψ z := by
                  congr 1
                  symm
                  apply integral_finsetSum
                  intro j hj
                  exact hR3int i j
        have hRddSumInt : Integrable
            (fun z : Vec3 × ℝ => ∑ j : Fin 3, DD i j j z * ψ z)
            (volume.restrict S) := by
          apply integrable_finsetSum
          intro j hj
          exact hR3int i j
        have hRconvSumInt : Integrable
            (fun z : Vec3 × ℝ => ∑ j : Fin 3,
              spatialPartial (show ParabolicPoint → ℝ from G i j) j z * ψ z) (volume.restrict S) := by
          apply integrable_finsetSum
          intro j hj
          exact hR2int i j
        have hResidualExpand :
            (∫ z in S, (Dt i z - ∑ j : Fin 3, DD i j j z +
              ∑ j : Fin 3, spatialPartial (show ParabolicPoint → ℝ from G i j) j z + Dp i z) * ψ z) =
            (∫ z in S, Dt i z * ψ z) -
              (∫ z in S, ∑ j : Fin 3, DD i j j z * ψ z) +
              (∫ z in S, ∑ j : Fin 3, spatialPartial (show ParabolicPoint → ℝ from G i j) j z * ψ z) +
              (∫ z in S, Dp i z * ψ z) := by
          have hpoint (z : Vec3 × ℝ) :
              (Dt i z - ∑ j : Fin 3, DD i j j z +
                ∑ j : Fin 3, spatialPartial (show ParabolicPoint → ℝ from G i j) j z + Dp i z) * ψ z =
              Dt i z * ψ z - (∑ j : Fin 3, DD i j j z * ψ z) +
                (∑ j : Fin 3, spatialPartial (show ParabolicPoint → ℝ from G i j) j z * ψ z) + Dp i z * ψ z := by
            simp only [sub_mul, add_mul, Finset.sum_mul]
          calc
            _ = ∫ z in S, (Dt i z * ψ z -
                (∑ j : Fin 3, DD i j j z * ψ z) +
                (∑ j : Fin 3, spatialPartial (show ParabolicPoint → ℝ from G i j) j z * ψ z) +
                Dp i z * ψ z) := by
              apply integral_congr_ae
              filter_upwards [] with z
              exact hpoint z
            _ = (∫ z in S, Dt i z * ψ z) -
                (∫ z in S, ∑ j : Fin 3, DD i j j z * ψ z) +
                (∫ z in S, ∑ j : Fin 3, spatialPartial (show ParabolicPoint → ℝ from G i j) j z * ψ z) +
                (∫ z in S, Dp i z * ψ z) := by
              have hI1 : Integrable (fun z : Vec3 × ℝ => Dt i z * ψ z -
                  ∑ j : Fin 3, DD i j j z * ψ z) (volume.restrict S) :=
                (hR1int i).sub hRddSumInt
              have hI2 : Integrable (fun z : Vec3 × ℝ => Dt i z * ψ z -
                  ∑ j : Fin 3, DD i j j z * ψ z +
                  ∑ j : Fin 3, spatialPartial (show ParabolicPoint → ℝ from G i j) j z * ψ z)
                  (volume.restrict S) := hI1.add hRconvSumInt
              rw [integral_add hI2 (hR4int i), integral_add hI1 hRconvSumInt,
                integral_sub (hR1int i) hRddSumInt]
        have hTimeNeg :
            -(∫ z in S, Ui i z * timePartial (show ParabolicPoint → ℝ from ψ) z) =
            ∫ z in S, Dt i z * ψ z := by
          rw [hIBPtime i]
          simp
        have hConvNeg :
            -(∫ z in S, ∑ j : Fin 3, G i j z * spatialPartial (show ParabolicPoint → ℝ from ψ) j z) =
            ∫ z in S, ∑ j : Fin 3, spatialPartial (show ParabolicPoint → ℝ from G i j) j z * ψ z := by
          rw [hIBPconvSum]
          simp
        have hPressureNeg :
            -(∫ z in S, P (z.1, z.2) * spatialPartial (show ParabolicPoint → ℝ from ψ) i z) =
            ∫ z in S, Dp i z * ψ z := by
          rw [hIBPpressure i]
          simp
        have hWeakToResidual :
            (∫ z in S, (-(Ui i z * timePartial (show ParabolicPoint → ℝ from ψ) z)
              - ∑ j : Fin 3, G i j z * spatialPartial (show ParabolicPoint → ℝ from ψ) j z
              + ∑ j : Fin 3, D i j z * spatialPartial (show ParabolicPoint → ℝ from ψ) j z
              - P (z.1, z.2) * spatialPartial (show ParabolicPoint → ℝ from ψ) i z)) =
            (∫ z in S, (Dt i z - ∑ j : Fin 3, DD i j j z +
              ∑ j : Fin 3, spatialPartial (show ParabolicPoint → ℝ from G i j) j z + Dp i z) * ψ z) := by
          linarith only [hWeakExpand, hResidualExpand, hIBPtime i, hIBPconvSum,
            hIBPdiffSum, hIBPpressure i]
        have hscalarConverted :
            (∫ z in S, (-(Ui i z * timePartial (show ParabolicPoint → ℝ from ψ) z)
              - ∑ j : Fin 3, G i j z * spatialPartial (show ParabolicPoint → ℝ from ψ) j z
              + ∑ j : Fin 3, D i j z * spatialPartial (show ParabolicPoint → ℝ from ψ) j z
              - P (z.1, z.2) * spatialPartial (show ParabolicPoint → ℝ from ψ) i z)) = 0 := by
          simpa [hscalarPairIntegrand, Ui, G, D, P] using hscalarS
        rw [← hWeakToResidual]
        exact hscalarConverted
      exact hWeakProduct
    intro z hz i
    let R : Vec3 × ℝ → ℝ := fun z =>
      Dt i z - ∑ j : Fin 3, DD i j j z +
        ∑ j : Fin 3, spatialPartial (show ParabolicPoint → ℝ from G i j) j z + Dp i z
    have hRcont : ContinuousOn R S := by
      dsimp [R]
      apply ContinuousOn.add
      · apply ContinuousOn.add
        · exact (hDtCont i).sub (continuousOn_finsetSum _ fun j hj => hDDCont i j j)
        · exact continuousOn_finsetSum _ fun j hj => hGpartialCont i j
      · exact hDpCont i
    have hzeroR : ∀ ψ : Vec3 × ℝ → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ (Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T →
        ∫ z in S, R z * ψ z = 0 := by
      intro ψ hψ hψc hψs
      exact hzero i ψ hψ hψc hψs
    have hpoint := regularised_continuousResidual_eq_zero_of_tests
      T R hRcont hzeroR
    have hz' : ((z.1, z.2) : Vec3 × ℝ) ∈ S := by
      exact ⟨Set.mem_univ _, hz.2⟩
    exact hpoint (z.1, z.2) hz'
  refine ⟨hDivPoint, ?_, ?_⟩
  · intro z hz i
    have hzProd : ((z.1, z.2) : Vec3 × ℝ) ∈ S := ⟨Set.mem_univ _, hz.2⟩
    have ht : z.2 ∈ Set.Icc 0 T := ⟨le_of_lt hz.2.1, le_of_lt hz.2.2⟩
    have hJdiv : ∑ j : Fin 3, spatialPartial (fun y => J y j) j z = 0 :=
      regUniform_mollified_velocity_divergence_eq_zero ρ ε hε u z.2 (hDivFree z.2 ht) z.1
    have hGsum : ∑ j : Fin 3, spatialPartial (show ParabolicPoint → ℝ from G i j) j z =
        ∑ j : Fin 3, J z j * D i j z := by
      calc
        _ = ∑ j : Fin 3,
            (J z j * D i j z + Ui i z * spatialPartial (fun y => J y j) j z) :=
          Finset.sum_congr rfl fun j _ => hGpartialFormula i j z hzProd
        _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hJdiv, mul_zero, add_zero]
    have hdivG :
        timePartial (fun y => u y i) z -
          (∑ j : Fin 3, spatialPartial
            (fun y => spatialPartial (fun x => u x i) j y) j z) +
          (∑ j : Fin 3, spatialPartial (show ParabolicPoint → ℝ from G i j) j z) +
          spatialPartial (fun y => P y) i z = 0 := hDivPoint z hz i
    rw [hGsum] at hdivG
    exact hdivG
  · intro t ht
    exact regularisedIntervalCanonicalPressure_slice ρ ε hε u T hT.le hSlice t ht

end CKN.Leray

end
