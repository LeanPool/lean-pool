/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegMomentum
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegMomentumAssembly
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegLocalEnergyWeights
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitJConvContraction
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformIntegrationByParts
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformMomentum
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEquationIntervalRepresentative
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEquationWeakGradient
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEquationZeroForcePressure
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.MomentumIntegrand
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction

/-!
# The weak momentum identity on a finite mild interval

The zero-force regularized momentum identity transfers to a coordinate
velocity satisfying the same mild equation on a finite interval.
-/

public section

open MeasureTheory Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

abbrev regularisedEquationIntervalWeakParabolicTopology :
    TopologicalSpace ParabolicPoint := inferInstance

local instance regularisedIntervalWeakNormedAddCommGroup :
    NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

local instance regularisedIntervalWeakNormedSpace : NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))

/-- A same-velocity mild path satisfies the forced weak momentum identity on
its finite regularity interval. -/
theorem regularisedInterval_weakMomentum
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a)
    (u : ParabolicPoint → Vec3) (T : ℝ) (hT : 0 < T)
    (hSlice : ∀ t : ℝ, t ∈ Set.Icc 0 T →
      MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hL2Continuous : Continuous (fun t : Set.Icc (0 : ℝ) T =>
      realVectorL2OfCoordinateFunction
        (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2)))
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
      regularisedEquationIntervalWeakParabolicTopology
      ∀ i : Fin 3, ContinuousOn (fun z => u z i)
        (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hDcontinuous : letI : TopologicalSpace ParabolicPoint :=
      regularisedEquationIntervalWeakParabolicTopology
      ∀ i j : Fin 3, ContinuousOn
        (fun z => spatialPartial (fun y => u y i) j z)
        (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hPcontinuous : letI : TopologicalSpace ParabolicPoint :=
      regularisedEquationIntervalWeakParabolicTopology
      ContinuousOn
      (regularisedIntervalCanonicalPressure ρ ε hε u T hT.le hSlice)
      (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hUjoint : letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
      letI : NormedAddCommGroup ParabolicPoint :=
        inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
      letI : NormedSpace ℝ ParabolicPoint :=
        inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
      ∀ i : Fin 3, ContDiffOn ℝ 1 (fun z => u z i)
        (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (φ : ParabolicPoint → Vec3)
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3)
      (Set.univ : Set Vec3) (Set.Ioo 0 T)) :
    ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Set.Ioo 0 T),
      (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
        - ∑ i : Fin 3, ∑ j : Fin 3,
          regUniformMollifiedVelocity ρ ε hε u z j * u z i *
            spatialPartial (fun y => φ y i) j z
        + ∑ i : Fin 3, ∑ j : Fin 3,
          spatialPartial (fun y => u y i) j z *
            spatialPartial (fun y => φ y i) j z
        - regularisedIntervalCanonicalPressure ρ ε hε u T hT.le hSlice z *
          (∑ i : Fin 3, spatialPartial (fun y => φ y i) i z)) = 0 := by
  classical
  let φProd : Vec3 × ℝ → Vec3 := fun z => φ z
  have hφProd : φProd ∈ spaceTimeTestFunction (V := Vec3)
      (Set.univ : Set Vec3) (Set.Ioo 0 T) := by
    change φ ∈ spaceTimeTestFunction (V := Vec3)
      (Set.univ : Set Vec3) (Set.Ioo 0 T)
    exact hφ
  have hφProdEq : φProd = φ := by
    funext z
    rfl
  let S : Set (Vec3 × ℝ) :=
    spaceTimeSet (Set.univ : Set Vec3) (Set.Ioo 0 T)
  let Smetric : Set ParabolicPoint :=
    spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)
  let f : ParabolicPoint → Vec3 := fun _ => 0
  let hf : CKN.IsLocallySquareIntegrableForce f :=
    CKN.isLocallySquareIntegrableForce_zero
  let Urep : Vec3 × ℝ → Vec3 := forcedRegRep ρ ε hε ha hf
  let Drep (i j : Fin 3) : Vec3 × ℝ → ℝ :=
    fun z => forcedMollifiedGrad Urep z i j
  let U (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => u z i
  let D (i j : Fin 3) : Vec3 × ℝ → ℝ :=
    fun z => spatialPartial (fun y => u y i) j z
  let P : Vec3 × ℝ → ℝ :=
    regularisedIntervalCanonicalPressure ρ ε hε u T hT.le hSlice
  have hSmeas : MeasurableSet S :=
    MeasurableSet.prod MeasurableSet.univ measurableSet_Ioo
  have hSsymm : ∀ z ∈ S, ((z.1, z.2) : ParabolicPoint) ∈ Smetric := by
    intro z hz
    exact ⟨Set.mem_univ _, ⟨hz.2.1, le_of_lt hz.2.2⟩⟩
  have hUcontProd (i : Fin 3) : ContinuousOn (U i) S := by
    have hpull := regUniform_continuousOn_pullback (hUcontinuous i) hSsymm
    simpa [U] using hpull
  have hDcontProd (i j : Fin 3) : ContinuousOn (D i j) S := by
    have hpull := regUniform_continuousOn_pullback (hDcontinuous i j) hSsymm
    simpa [D] using hpull
  have hPcontProd : ContinuousOn P S := by
    have hpull := regUniform_continuousOn_pullback hPcontinuous hSsymm
    simpa [P] using hpull
  let uExt : ParabolicPoint → Vec3 := fun z => if z.2 ≤ T then u z else 0
  have hSliceExt (t : ℝ) (ht : 0 < t) :
      MemLp (fun x : Vec3 => uExt (x, t)) 2 volume := by
    by_cases htT : t ≤ T
    · have htIcc : t ∈ Set.Icc 0 T := ⟨le_of_lt ht, htT⟩
      simpa [uExt, htT] using hSlice t htIcc
    · simp [uExt, htT]
  let UextCurve : ℝ → RealVectorL2 := fun t =>
    if ht : 0 < t then
      realVectorL2OfCoordinateFunction (fun x : Vec3 => uExt (x, t))
        (hSliceExt t ht)
    else 0
  have hUcontDiffS (i : Fin 3) : ContDiffOn ℝ 1
      (fun z : ParabolicPoint => u z i) S := by
    exact (hUjoint i).mono (fun z hz => hSsymm z hz)
  have hUExtContDiff (i : Fin 3) : ContDiffOn ℝ 1
      (fun z : ParabolicPoint => uExt z i) S := by
    apply ContDiffOn.congr (hUcontDiffS i)
    intro z hz
    simp [uExt, hz.2.2.le]
  have hSpositive : ∀ z ∈ S, 0 < z.2 := fun z hz => hz.2.1
  have hSshift : ∀ z ∈ S, ∀ y : Vec3, (z.1 - y, z.2) ∈ S := by
    intro z hz y
    exact ⟨Set.mem_univ _, hz.2⟩
  have hJext := regUniform_mollified_velocity_continuousOn
    ρ ε hε (u := uExt) (S := S) hSliceExt hUExtContDiff hSpositive hSshift
  have hJcont (j : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => regUniformMollifiedVelocity ρ ε hε u z j) S := by
    apply (hJext j).congr
    intro z hz
    have hsame : (fun x : Vec3 => u (x, z.2)) =ᵐ[volume]
        fun x => uExt (x, z.2) := by
      filter_upwards [] with x
      simp [uExt, hz.2.2.le]
    have hrepExt : (fun x : Vec3 => uExt (x, z.2)) =ᵐ[volume]
        realVectorL2Representative (UextCurve z.2) := by
      simpa [UextCurve, hz.2.1] using
        (realVectorL2OfCoordinateFunction_rep
          (fun y : Vec3 => uExt (y, z.2)) (hSliceExt z.2 hz.2.1)).symm
    have hslice := hsame.trans hrepExt
    have hmoll := regMollifyVector_velocitySlice_eq ρ ε hε
      (U := UextCurve)
      (u := u) (t := z.2) hslice
    have hmollExt := regMollifyVector_velocitySlice_eq ρ ε hε
      (U := UextCurve) (u := uExt) (t := z.2) hrepExt
    have hmollEq := hmoll.trans hmollExt.symm
    have hpoint := congrArg (fun V : L2Vec3 => WithLp.ofLp V j)
      (congrFun hmollEq (WithLp.toLp 2 z.1))
    simpa [regUniformMollifiedVelocity] using hpoint
  let Uext (i : Fin 3) : Vec3 × ℝ → ℝ := S.piecewise (U i) 0
  let Dext (i j : Fin 3) : Vec3 × ℝ → ℝ := S.piecewise (D i j) 0
  let Jext (j : Fin 3) : Vec3 × ℝ → ℝ := S.piecewise
    (fun z => regUniformMollifiedVelocity ρ ε hε u z j) 0
  let Pext : Vec3 × ℝ → ℝ := S.piecewise P 0
  have hTimeDerivMeas : Measurable (timeDeriv φ) :=
    (contDiff_timeDeriv hφ.1).continuous.measurable
  have hSpaceDerivMeas (j : Fin 3) : Measurable (spaceDeriv j φ) :=
    (contDiff_spaceDeriv hφ.1 j).continuous.measurable
  have hStDivMeas : Measurable (stDiv φ) := by
    unfold stDiv
    apply Finset.measurable_sum
    intro i hi
    exact (continuous_apply i).measurable.comp (hSpaceDerivMeas i)
  have hUextMeas (i : Fin 3) : Measurable (Uext i) :=
    (hUcontProd i).measurable_piecewise continuousOn_const hSmeas
  have hDextMeas (i j : Fin 3) : Measurable (Dext i j) :=
    (hDcontProd i j).measurable_piecewise continuousOn_const hSmeas
  have hJextMeas (j : Fin 3) : Measurable (Jext j) :=
    (hJcont j).measurable_piecewise continuousOn_const hSmeas
  have hPextMeas : Measurable Pext :=
    hPcontProd.measurable_piecewise continuousOn_const hSmeas
  let Q : Vec3 × ℝ → ℝ := fun z =>
    -(∑ i : Fin 3, Uext i z * timeDeriv φ z i)
      - ∑ i : Fin 3, ∑ j : Fin 3,
        Jext j z * Uext i z * spaceDeriv j φ z i
      + ∑ i : Fin 3, ∑ j : Fin 3,
        Dext i j z * spaceDeriv j φ z i
      - Pext z * stDiv φ z
  have hQmeas : Measurable Q := by
    dsimp [Q]
    fun_prop
  have hVsm : StronglyMeasurable Urep :=
    forcedRegRep_stronglyMeasurable ρ ε hε ha hf
  have hVmeas : Measurable Urep := StronglyMeasurable.measurable hVsm
  have hJsm : StronglyMeasurable (regUniformMollifiedVelocity ρ ε hε Urep) :=
    lerayLimit_regUniformMollifiedVelocity_stronglyMeasurable ρ ε hε hVmeas
  have hJmeas : Measurable (regUniformMollifiedVelocity ρ ε hε Urep) :=
    StronglyMeasurable.measurable hJsm
  have hDsm : ∀ i j, StronglyMeasurable (Drep i j) := by
    intro i j
    exact forcedMollifiedGrad_stronglyMeasurable hVsm
      (fun t k => forcedRegRep_locallyIntegrable ρ ε hε ha hf t k) i j
  have hForcePsm : StronglyMeasurable (fun z : Vec3 × ℝ => forcePressure f hf z) :=
    stronglyMeasurable_forcePressure hf
  have hForcePmeas : Measurable (fun z : Vec3 × ℝ => forcePressure f hf z) :=
    StronglyMeasurable.measurable hForcePsm
  have hQuadPsm : StronglyMeasurable
      (forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf)) := by
    exact forcedQuadPressure_stronglyMeasurable ρ ε hε
      (continuous_forcedRegCurve ρ ε hε ha hf)
  have hQuadPmeas : Measurable
      (forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf)) :=
    StronglyMeasurable.measurable hQuadPsm
  have hForcedMeas : Measurable
      (forcedMomentumIntegrand ρ ε hε ha f hf φProd) := by
    unfold forcedMomentumIntegrand
    have hφProdMeas : Measurable φProd := hφProd.1.continuous.measurable
    have hφProdCoordMeas (i : Fin 3) : Measurable
        (fun z : Vec3 × ℝ => φProd z i) :=
      (measurable_pi_apply i).comp hφProdMeas
    have hUrepCoordMeas (i : Fin 3) : Measurable
        (fun z : Vec3 × ℝ => forcedRegRep ρ ε hε ha hf z i) :=
      (measurable_pi_apply i).comp hVmeas
    have hDmeas (i j : Fin 3) : Measurable
        (fun z : Vec3 × ℝ => forcedMollifiedGrad
          (forcedRegRep ρ ε hε ha hf) z i j) := by
      exact (forcedMollifiedGrad_stronglyMeasurable hVsm
        (forcedRegRep_locallyIntegrable ρ ε hε ha hf) i j).measurable
    fun_prop (disch := assumption)
  have hForceZero := forcePressure_zero_ae_on_interval T hT
  have hVelocityAE (t : ℝ) (ht : t ∈ Set.Ioo 0 T) :
      (fun x : Vec3 => u (x, t)) =ᵐ[volume] (fun x => Urep (x, t)) := by
    apply regularisedInterval_velocity_ae_eq_forcedRegRep
      ρ ε hε a ha u T hT hSlice hL2Continuous hMild t
    exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hGradientAE (t : ℝ) (ht : t ∈ Set.Ioo 0 T) (i j : Fin 3) :
      (fun x : Vec3 => Drep i j (x, t)) =ᵐ[volume] (fun x => D i j (x, t)) := by
    have hVae := hVelocityAE t ht
    have hloc := forcedRegRep_locallyIntegrable ρ ε hε ha hf t i
    have hC1 : ContDiff ℝ 1 (fun x : Vec3 => u (x, t) i) := by
      apply contDiffOn_univ.mp
      exact (hUjoint i).comp (by fun_prop) (by
        intro x hx
        exact ⟨Set.mem_univ _, ⟨ht.1, le_of_lt ht.2⟩⟩)
    simpa [Drep, Urep, D] using
      (forcedMollifiedGrad_ae_eq_classical_of_ae_eq Urep u t i j hloc hVae.symm hC1)
  have hTensorAE (t : ℝ) (ht : t ∈ Set.Ioo 0 T) (i j : Fin 3) :
      (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t) j * u (x, t) i) =ᵐ[volume]
      (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε Urep (x, t) j * Urep (x, t) i) := by
    have hUae := hVelocityAE t ht
    have hrepU : (fun x : Vec3 => u (x, t)) =ᵐ[volume]
        realVectorL2Representative (forcedRegCurve ρ ε hε ha hf t) :=
      hUae.trans (forcedRegRep_slice ρ ε hε ha hf t)
    have hrepV := forcedRegRep_slice ρ ε hε ha hf t
    have hUtensor := regPressureTensorSlice_ae_eq ρ ε hε hrepU j i
    have hVtensor := regPressureTensorSlice_ae_eq ρ ε hε hrepV j i
    have hEq := hUtensor.trans hVtensor.symm
    change regPressureTensorSlice ρ ε hε u t j i =ᵐ[volume]
      regPressureTensorSlice ρ ε hε Urep t j i
    exact hEq
  have hPressureAE (t : ℝ) (ht : t ∈ Set.Ioo 0 T)
    (hforce : (fun x : Vec3 => forcePressure f hf (x, t)) =ᵐ[volume] 0) :
      (fun x : Vec3 => P (x, t)) =ᵐ[volume]
        (fun x : Vec3 => forcedQuadPressure ρ ε hε
          (forcedRegCurve ρ ε hε ha hf) (x, t) + forcePressure f hf (x, t)) := by
    have hPath := regularisedIntervalMildCurve_eq_forcedRegCurve
      ρ ε hε a ha u T hT hSlice hL2Continuous hMild t
        ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hquad (x : Vec3) : P (x, t) = forcedQuadPressure ρ ε hε
        (forcedRegCurve ρ ε hε ha hf) (x, t) := by
      change forcedQuadPressure ρ ε hε
          (regularisedIntervalMildCurve u T hT.le hSlice) (x, t) = _
      exact congrArg (fun V : RealVectorL2 =>
        forcedQuadPressure ρ ε hε (fun _ : ℝ => V) (x, t)) hPath
    filter_upwards [hforce] with x hx
    rw [hquad x]
    simp [f, hx]
  have htime : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo 0 T)),
      ∀ᵐ x ∂(volume : Measure Vec3),
        Q (x, t) = forcedMomentumIntegrand ρ ε hε ha f hf φProd (x, t) := by
    filter_upwards [hForceZero, ae_restrict_mem measurableSet_Ioo] with t hPzero ht
    have hPzero' : (fun x : Vec3 => forcePressure f hf (x, t)) =ᵐ[volume] 0 := by
      simpa [f] using hPzero
    have hUae := hVelocityAE t ht
    have hDae : ∀ᵐ x ∂(volume : Measure Vec3), ∀ i j : Fin 3,
        Drep i j (x, t) = D i j (x, t) := by
      have h := ae_all_iff.2 fun i => ae_all_iff.2 fun j => hGradientAE t ht i j
      filter_upwards [h] with x hx
      exact hx
    have hTae : ∀ᵐ x ∂(volume : Measure Vec3), ∀ i j : Fin 3,
        regUniformMollifiedVelocity ρ ε hε u (x, t) j * u (x, t) i =
          regUniformMollifiedVelocity ρ ε hε Urep (x, t) j * Urep (x, t) i := by
      have h := ae_all_iff.2 fun i => ae_all_iff.2 fun j => hTensorAE t ht i j
      filter_upwards [h] with x hx
      exact hx
    have hPae : ∀ᵐ x ∂(volume : Measure Vec3), P (x, t) =
        forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (x, t) +
          forcePressure f hf (x, t) := hPressureAE t ht hPzero'
    filter_upwards [hUae, hDae, hTae, hPae, hPzero'] with x hUx hDx hTx hPx hForcePx
    have hxS : (x, t) ∈ S := ⟨Set.mem_univ _, ht⟩
    have hUcomp (i : Fin 3) : u (x, t) i = Urep (x, t) i := congrFun hUx i
    have hDcomp (i j : Fin 3) : Drep i j (x, t) = D i j (x, t) := hDx i j
    have hUextAt (i : Fin 3) : Uext i (x, t) = u (x, t) i := by
      change S.piecewise (U i) 0 (x, t) = u (x, t) i
      rw [Set.piecewise_eq_of_mem S (U i) 0 hxS]
    have hDextAt (i j : Fin 3) : Dext i j (x, t) = D i j (x, t) := by
      change S.piecewise (D i j) 0 (x, t) = D i j (x, t)
      rw [Set.piecewise_eq_of_mem S (D i j) 0 hxS]
    have hJextAt (j : Fin 3) : Jext j (x, t) =
        regUniformMollifiedVelocity ρ ε hε u (x, t) j := by
      change S.piecewise
        (fun z => regUniformMollifiedVelocity ρ ε hε u z j) 0 (x, t) = _
      rw [Set.piecewise_eq_of_mem S
        (fun z => regUniformMollifiedVelocity ρ ε hε u z j) 0 hxS]
    have hPextAt : Pext (x, t) = P (x, t) := by
      change S.piecewise P 0 (x, t) = P (x, t)
      rw [Set.piecewise_eq_of_mem S P 0 hxS]
    have hDforced (i j : Fin 3) :
        forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf) (x, t) i j = D i j (x, t) := by
      simpa [Drep, Urep] using hDx i j
    have hTxForced (i j : Fin 3) :
        regUniformMollifiedVelocity ρ ε hε u (x, t) j * u (x, t) i =
          regUniformMollifiedVelocity ρ ε hε (forcedRegRep ρ ε hε ha hf) (x, t) j *
            forcedRegRep ρ ε hε ha hf (x, t) i := by
      simpa [Urep] using hTx i j
    simp only [Q, hUextAt, hDextAt, hJextAt, hPextAt,
      forcedMomentumIntegrand, f, hPx, hDforced, hφProdEq, stDiv,
      Pi.zero_apply, zero_mul]
    simp_rw [hTxForced]
    simp only [hUcomp, Urep]
    ring
  have hEqSet : MeasurableSet
      {z : Vec3 × ℝ | Q z = forcedMomentumIntegrand ρ ε hε ha f hf φProd z} :=
    measurableSet_eq_fun hQmeas hForcedMeas
  have hQae : Q =ᵐ[(volume : Measure (Vec3 × ℝ)).restrict S]
      forcedMomentumIntegrand ρ ε hε ha f hf φProd := by
    change Q =ᵐ[(volume : Measure ParabolicPoint).restrict
      (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioo 0 T))]
      forcedMomentumIntegrand ρ ε hε ha f hf φProd
    rw [restrict_spaceTimeSet_eq_prod (Set.Ioo 0 T)]
    exact (Measure.ae_prod_iff_ae_ae hEqSet).2
      ((Measure.ae_ae_comm hEqSet).2 htime)
  have hForcedIoi := integral_forcedMomentumIntegrand_eq_zero
    ρ ε hε ha hf hφProd.1 hφProd.2.1 (by
      intro z hz
      exact ⟨Set.mem_univ _, (hφProd.2.2 hz).2.1⟩)
  have hForcedS : ∫ z in S, forcedMomentumIntegrand ρ ε hε ha f hf φProd z = 0 := by
    have hsetIoi : ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Set.Ioi 0),
        forcedMomentumIntegrand ρ ε hε ha f hf φProd z =
        ∫ z : ParabolicPoint, forcedMomentumIntegrand ρ ε hε ha f hf φProd z :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
        forcedMomentumIntegrand_eq_zero ρ ε hε ha f hf (φ := φProd) (z := z)
          (fun h => hz ⟨Set.mem_univ _, (hφProd.2.2 h).2.1⟩)
    have hsetS : ∫ z in S, forcedMomentumIntegrand ρ ε hε ha f hf φProd z =
        ∫ z : ParabolicPoint, forcedMomentumIntegrand ρ ε hε ha f hf φProd z :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
        forcedMomentumIntegrand_eq_zero ρ ε hε ha f hf (φ := φProd) (z := z)
          (fun h => hz (hφProd.2.2 h))
    calc
      ∫ z in S, forcedMomentumIntegrand ρ ε hε ha f hf φProd z =
          ∫ z : ParabolicPoint, forcedMomentumIntegrand ρ ε hε ha f hf φProd z := hsetS
      _ = ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Set.Ioi 0),
          forcedMomentumIntegrand ρ ε hε ha f hf φProd z := hsetIoi.symm
      _ = 0 := hForcedIoi
  have hQzero : ∫ z in S, Q z = 0 := by
    rw [integral_congr_ae hQae]
    exact hForcedS
  let targetIntegrand : Vec3 × ℝ → ℝ := fun z =>
    -(∑ i : Fin 3, u ((z.1, z.2) : ParabolicPoint) i *
        timePartial (fun y => φ y i) (z.1, z.2))
      - ∑ i : Fin 3, ∑ j : Fin 3,
        regUniformMollifiedVelocity ρ ε hε u ((z.1, z.2) : ParabolicPoint) j *
          u ((z.1, z.2) : ParabolicPoint) i *
          spatialPartial (fun y => φ y i) j (z.1, z.2)
      + ∑ i : Fin 3, ∑ j : Fin 3,
        spatialPartial (fun y => u y i) j (z.1, z.2) *
          spatialPartial (fun y => φ y i) j (z.1, z.2)
      - P ((z.1, z.2) : ParabolicPoint) *
        (∑ i : Fin 3, spatialPartial (fun y => φ y i) i (z.1, z.2))
  have hTargetQ : ∀ z ∈ S, targetIntegrand z = Q z := by
    intro z hz
    have hTime (i : Fin 3) :
        timePartial (fun y : ParabolicPoint => φ y i) (z.1, z.2) =
          timeDeriv φ (z.1, z.2) i :=
      timePartial_eq_timeDeriv' hφ.1 i (z.1, z.2)
    have hSpace (i j : Fin 3) :
        spatialPartial (fun y : ParabolicPoint => φ y i) j (z.1, z.2) =
          spaceDeriv j φ (z.1, z.2) i :=
      spatialPartial_eq_spaceDeriv' hφ.1 i j (z.1, z.2)
    simp [targetIntegrand, Q, U, D, Uext, Dext, Jext, Pext,
      hTime, hSpace, hz, stDiv]
  change ∫ z in S, targetIntegrand z = 0
  calc
    ∫ z in S, targetIntegrand z = ∫ z in S, Q z :=
      setIntegral_congr_fun (μ := volume) hSmeas hTargetQ
    _ = 0 := hQzero

end CKN.Leray

end
