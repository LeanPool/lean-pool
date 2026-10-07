/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegEquicontinuity
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegPressureL2
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformIntegrationByParts
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformSlices
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformTenThirds
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildNonlinearity
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildLocalParameters
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierCoordinateL2Bridge
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedMildInitialData
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildLocalSolution
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildLocalMap
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedTransportCutoff
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitMeasurability
public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Spatial tails of regularized Leray solutions

The local energy identity and the uniform global energy bounds control the
velocity outside large balls, as in `lem:reg-tails`.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

private theorem regTails_spatialField_memLp {a : Vec3 → Vec3}
    (ha : MemLp a 2 volume) : MemLp (regUniformSpatialField a) 2 volume := by
  have hcoord : MemLp (fun x : L2Vec3 => a (WithLp.ofLp x)) 2 volume :=
    ha.comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin 3))
  exact hcoord.continuousLinearMap_comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap

/-- The positive-time spacetime measure is the product of spatial volume and
one-dimensional volume restricted to positive times. -/
theorem regTails_positiveTimeMeasure_eq_product :
    regUniformPositiveTimeMeasure =
      (volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ))) := by
  unfold regUniformPositiveTimeMeasure
  change ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
      ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)) = _
  rw [← Measure.prod_restrict (μ := (volume : Measure Vec3))
    (ν := (volume : Measure ℝ)) Set.univ (Ioi (0 : ℝ))]
  simp [Measure.restrict_univ]

/-- Extending the spatial gradient by zero off positive spacetime preserves
measurability, so the global dissipation can be integrated by slices. -/
@[expose]
noncomputable def regTailsPositiveGradientExtension
    (D : ParabolicPoint → Fin 3 → Vec3) :
    ParabolicPoint → Fin 3 → Vec3 := by
  classical
  exact (spaceTimeSet (Set.univ : Set Vec3) (Ioi (0 : ℝ))).piecewise D 0

theorem regTails_positiveGradientExtension_measurable
    (D : ParabolicPoint → Fin 3 → Vec3)
    (hDcont : ∀ i j, ContinuousOn (fun z : ParabolicPoint => D z i j)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi (0 : ℝ)))) :
    Measurable (regTailsPositiveGradientExtension D) := by
  classical
  let S : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioi (0 : ℝ))
  have hSopen : IsOpen S := by
    simpa [S] using isOpen_spaceTimeSet (Set.univ : Set Vec3) (Ioi (0 : ℝ))
      isOpen_univ isOpen_Ioi
  have hSmeas : MeasurableSet S := hSopen.measurableSet
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  have hzero : ContinuousOn (fun _ : ParabolicPoint => (0 : ℝ)) Sᶜ := continuousOn_const
  have hm := lerayLimit_measurableOn_extension S hSmeas
    (fun z : ParabolicPoint => D z i j) (fun _ => 0) (hDcont i j) hzero
  have hcoord : (fun z : ParabolicPoint => (regTailsPositiveGradientExtension D) z i j) =
      S.piecewise (fun z => D z i j) (fun _ => 0) := by
    funext z
    by_cases hz : z ∈ S <;> simp [regTailsPositiveGradientExtension, S, hz]
  rw [hcoord]
  exact hm

/-- A product of compact smooth spatial and positive-time tests is an
admissible scalar space-time test. -/
theorem regTails_scalarTimeProduct_test
    (q : Vec3 → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hqc : HasCompactSupport q) (η : ℝ → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηI : tsupport η ⊆ Ioi (0 : ℝ)) :
    (fun z : Vec3 × ℝ => q z.1 * η z.2) ∈
      spaceTimeTestFunction (V := ℝ) Set.univ (Ioi (0 : ℝ)) := by
  let φ : Vec3 × ℝ → ℝ := fun z => q z.1 * η z.2
  have hφd : ContDiff ℝ (⊤ : ℕ∞) φ := by
    exact (hq.comp (ContinuousLinearMap.fst ℝ Vec3 ℝ).contDiff).mul
      (hη.comp (ContinuousLinearMap.snd ℝ Vec3 ℝ).contDiff)
  have hSupport : Function.support φ ⊆ tsupport q ×ˢ tsupport η := by
    intro z hz
    have hφz : φ z ≠ 0 := Function.mem_support.mp hz
    constructor
    · by_contra hx
      have hqz : q z.1 = 0 := by
        by_contra hne
        exact hx (subset_tsupport q (Function.mem_support.mpr hne))
      exact hφz (by simp [φ, hqz])
    · by_contra ht
      have hηz : η z.2 = 0 := by
        by_contra hne
        exact ht (subset_tsupport η (Function.mem_support.mpr hne))
      exact hφz (by simp [φ, hηz])
  have hProductCompact : IsCompact (tsupport q ×ˢ tsupport η) :=
    hqc.isCompact.prod hηc.isCompact
  have hSupportClosed : IsClosed (tsupport q ×ˢ tsupport η) :=
    hProductCompact.isClosed
  have hφsupport : tsupport φ ⊆ tsupport q ×ˢ tsupport η :=
    closure_minimal hSupport hSupportClosed
  have hφc : HasCompactSupport φ :=
    hProductCompact.of_isClosed_subset (isClosed_tsupport (f := φ)) hφsupport
  have hφI : tsupport φ ⊆ Set.univ ×ˢ Ioi (0 : ℝ) := by
    exact hφsupport.trans (Set.prod_mono (Set.subset_univ _) hηI)
  change φ ∈ spaceTimeTestFunction (V := ℝ) Set.univ (Ioi (0 : ℝ))
  exact ⟨hφd, hφc, hφI⟩

/-- Slice energy, finite total dissipation, and almost every positive-time H¹
slice follow from the R5 identity in `lem:reg-tails`. The gradient is extended
measurably from positive time before applying the global energy estimate. -/
theorem regTails_energy_bounds
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (u : ParabolicPoint → Vec3)
    (D : ParabolicPoint → Fin 3 → Vec3)
    (hR5 : ∀ t, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
        2 * regUniformDissipation u D t =
      eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a))
        2 volume ^ (2 : ℕ))
    (ha : MemLp a 2 volume)
    (hDcont : ∀ i j, ContinuousOn (fun z : ParabolicPoint => D z i j)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi (0 : ℝ))))
    (hU : ∀ t, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hSpatialC1 : ∀ t, 0 < t → ∀ i : Fin 3,
      ContDiff ℝ (1 : ℕ∞) (fun x : Vec3 => u (x, t) i))
    (hDerivative : ∀ t, 0 < t → ∀ x i j,
      (fderiv ℝ (fun y : Vec3 => u (y, t) i) x) (basisVec j) =
        D (x, t) i j) :
    (∀ t, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) ≤
        eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ)) ∧
    2 * (∫⁻ z, ENNReal.ofReal (spatialGradientSq u D z)
      ∂regUniformPositiveTimeMeasure) ≤
      eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ) ∧
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∃ h : ∀ _i : Fin 3, CKN.H1Function (Set.univ : Set Vec3),
        (∀ i x, (h i).toFun x = u (x, t) i) ∧
        (∀ i x j, (h i).grad x j = D (x, t) i j) := by
  classical
  let S : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)
  let Dplus : ParabolicPoint → Fin 3 → Vec3 := S.piecewise D 0
  have hSopen : IsOpen S := by
    simpa [S] using isOpen_spaceTimeSet (Set.univ : Set Vec3) (Ioi (0 : ℝ))
      isOpen_univ isOpen_Ioi
  have hSmeas : MeasurableSet S := hSopen.measurableSet
  have hDplusMeas : Measurable Dplus := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    have hzero : ContinuousOn (fun _ : ParabolicPoint => (0 : ℝ)) Sᶜ :=
      continuousOn_const
    have hm := lerayLimit_measurableOn_extension S hSmeas
      (fun z : ParabolicPoint => D z i j) (fun _ => 0) (hDcont i j) hzero
    have hcoord : (fun z : ParabolicPoint => Dplus z i j) =
        S.piecewise (fun z => D z i j) (fun _ => 0) := by
      funext z
      by_cases hz : z ∈ S <;> simp [Dplus, hz]
    rw [hcoord]
    exact hm
  have hDplusEq (z : ParabolicPoint) (hz : z ∈ S) : Dplus z = D z := by
    simp [Dplus, hz]
  have hR5plus : ∀ t, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
        2 * regUniformDissipation u Dplus t =
      eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a))
        2 volume ^ (2 : ℕ) := by
    intro t ht
    have hEq : (fun z : ParabolicPoint =>
        if (parabolicHomeomorph z).2 < t then
          ENNReal.ofReal (spatialGradientSq u Dplus z) else 0) =ᵐ[
          regUniformPositiveTimeMeasure]
      (fun z : ParabolicPoint =>
          if (parabolicHomeomorph z).2 < t then
            ENNReal.ofReal (spatialGradientSq u D z) else 0) := by
      filter_upwards [ae_restrict_mem hSmeas] with z hz
      have hsp : spatialGradientSq u Dplus z = spatialGradientSq u D z := by
        unfold spatialGradientSq
        simp only [hDplusEq z hz]
      rw [hsp]
    have hDiss : regUniformDissipation u Dplus t =
        regUniformDissipation u D t := by
      unfold regUniformDissipation
      exact lintegral_congr_ae hEq
    simpa [hDiss] using hR5 t ht
  have haField : MemLp (regUniformSpatialField a) 2 volume :=
    regTails_spatialField_memLp ha
  have hEnergyPlus := regUniform_energy_bounds ρ ε hε a u Dplus
    haField hR5plus hDplusMeas
  have hEnergyEq : (fun z : ParabolicPoint =>
      ENNReal.ofReal (spatialGradientSq u Dplus z)) =ᵐ[
        regUniformPositiveTimeMeasure]
      (fun z : ParabolicPoint =>
        ENNReal.ofReal (spatialGradientSq u D z)) := by
    filter_upwards [ae_restrict_mem hSmeas] with z hz
    have hsp : spatialGradientSq u Dplus z = spatialGradientSq u D z := by
      unfold spatialGradientSq
      simp only [hDplusEq z hz]
    rw [hsp]
  have hEnergyOrig : 2 * (∫⁻ z, ENNReal.ofReal
      (spatialGradientSq u D z) ∂regUniformPositiveTimeMeasure) ≤
      eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ) := by
    simpa only [lintegral_congr_ae hEnergyEq] using hEnergyPlus.2
  have hDensity : Measurable (fun z : ParabolicPoint => ENNReal.ofReal
      (spatialGradientSq u Dplus z)) := by
    apply ENNReal.measurable_ofReal.comp
    unfold spatialGradientSq
    fun_prop
  let μt : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hMeasure : regUniformPositiveTimeMeasure =
      (volume : Measure Vec3).prod μt := by
    unfold regUniformPositiveTimeMeasure
    change ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (Set.univ ×ˢ Ioi (0 : ℝ)) = _
    rw [← Measure.prod_restrict (μ := (volume : Measure Vec3))
      (ν := (volume : Measure ℝ)) Set.univ (Ioi (0 : ℝ))]
    simp [μt, Measure.restrict_univ]
  have hProductDensity : AEMeasurable
      (fun z : Vec3 × ℝ => ENNReal.ofReal
        (spatialGradientSq u Dplus z))
      ((volume : Measure Vec3).prod μt) := by
    exact hDensity.aemeasurable
  have hUncurriedDensity : AEMeasurable
      (Function.uncurry (fun x t => ENNReal.ofReal
        (spatialGradientSq u Dplus ((x, t) : ParabolicPoint))))
      ((volume : Measure Vec3).prod μt) := by
    have hEq : (fun z : Vec3 × ℝ => ENNReal.ofReal
        (spatialGradientSq u Dplus z)) =
        Function.uncurry (fun x t => ENNReal.ofReal
          (spatialGradientSq u Dplus ((x, t) : ParabolicPoint))) := by
      funext z
      rcases z with ⟨x, t⟩
      rfl
    exact hProductDensity.congr
      (Filter.Eventually.of_forall fun z => congrFun hEq z)
  have hNestedEq : (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Vec3,
      ENNReal.ofReal (spatialGradientSq u Dplus (x, t)) ∂volume ∂volume) =
      ∫⁻ z, ENNReal.ofReal (spatialGradientSq u Dplus z)
        ∂regUniformPositiveTimeMeasure := by
    calc
      _ = ∫⁻ t : ℝ, ∫⁻ x : Vec3,
          ENNReal.ofReal (spatialGradientSq u Dplus (x, t)) ∂volume ∂μt := by
        rfl
      _ = ∫⁻ x : Vec3, ∫⁻ t : ℝ,
          ENNReal.ofReal (spatialGradientSq u Dplus (x, t)) ∂μt ∂volume :=
        (MeasureTheory.lintegral_lintegral_swap
          (μ := (volume : Measure Vec3)) (ν := μt)
          (f := fun x t => ENNReal.ofReal
            (spatialGradientSq u Dplus ((x, t) : ParabolicPoint)))
          hUncurriedDensity).symm
      _ = ∫⁻ z, ENNReal.ofReal (spatialGradientSq u Dplus z)
          ∂regUniformPositiveTimeMeasure := by
        rw [hMeasure]
        exact (MeasureTheory.lintegral_prod _ hProductDensity).symm
  have hFieldMem : MemLp (regUniformSpatialField a) 2 volume :=
    regTails_spatialField_memLp ha
  have hEnergyRhsFinite :
      eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ) < ⊤ := by
    exact ENNReal.pow_lt_top hFieldMem.eLpNorm_lt_top
  have hGradientFinite :
      (∫⁻ z, ENNReal.ofReal (spatialGradientSq u Dplus z)
        ∂regUniformPositiveTimeMeasure) < ⊤ := by
    by_contra hnot
    have htop : (∫⁻ z, ENNReal.ofReal (spatialGradientSq u Dplus z)
        ∂regUniformPositiveTimeMeasure) = ⊤ := top_unique (not_lt.mp hnot)
    have hEnergyIneq := hEnergyPlus.2
    rw [htop] at hEnergyIneq
    have hRhsTop : eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ) = ⊤ :=
      top_unique (by simpa using hEnergyIneq)
    exact hEnergyRhsFinite.ne hRhsTop
  have hNestedFinite :
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Vec3,
        ENNReal.ofReal (spatialGradientSq u Dplus (x, t)) ∂volume ∂volume) < ⊤ := by
    rw [hNestedEq]
    exact hGradientFinite
  have hSlicesPlus := regUniform_velocity_h1_slices u Dplus hU
    hDplusMeas (by simpa [Measure.restrict_univ] using hNestedFinite)
    hSpatialC1 (by
      intro t ht x i j
      have hEq := hDplusEq (x, t) (by
        change (x, t) ∈ (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)
        exact ⟨Set.mem_univ _, ht⟩)
      exact (hDerivative t ht x i j).trans
        (congrFun (congrFun hEq.symm i) j))
  have hSlicesOrig : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∃ h : ∀ _i : Fin 3, CKN.H1Function (Set.univ : Set Vec3),
        (∀ i x, (h i).toFun x = u (x, t) i) ∧
        (∀ i x j, (h i).grad x j = D (x, t) i j) := by
    filter_upwards [hSlicesPlus, ae_restrict_mem measurableSet_Ioi]
      with t hH1 ht
    rcases hH1 with ⟨h, hvalue, hgradient⟩
    refine ⟨h, hvalue, ?_⟩
    intro i x j
    rw [hgradient i x j]
    have hEq := hDplusEq (x, t) (by
      change (x, t) ∈ (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)
      exact ⟨Set.mem_univ _, ht⟩)
    exact congrFun (congrFun hEq i) j
  exact ⟨hEnergyPlus.1, hEnergyOrig, hSlicesOrig⟩

end CKN.Leray

end
