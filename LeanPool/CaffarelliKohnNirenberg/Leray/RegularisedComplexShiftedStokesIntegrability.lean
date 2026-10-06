/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselShiftedStokesIntegrability
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Integrability of the translated complex physical Stokes term

The positive-time Stokes estimate controls the physical translated integrand by
an integrable Abel kernel on every bounded interval.
-/

public section

open MeasureTheory
open Filter
open scoped Interval ENNReal Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

local instance complexShiftedIntegrabilityMeasure :
    IsSeparable (volume : Measure L2Vec3) := by
  infer_instance

local instance complexShiftedIntegrabilityComplexSeparable :
    TopologicalSpace.SeparableSpace ComplexVec3 := by
  infer_instance

local instance complexShiftedIntegrabilityTwoFinite : Fact ((2 : ℝ≥0∞) ≠ ∞) :=
  ⟨by norm_num⟩

local instance complexShiftedIntegrabilityVectorSeparable :
    TopologicalSpace.SeparableSpace ComplexVectorL2 := by
  infer_instance

local instance complexShiftedIntegrabilityVectorSecondCountable :
    SecondCountableTopology ComplexVectorL2 := by
  exact UniformSpace.secondCountable_of_separable _

local instance complexShiftedIntegrabilityVectorMeasurableSpace :
    MeasurableSpace ComplexVectorL2 :=
  borel _

local instance complexShiftedIntegrabilityVectorBorelSpace :
    BorelSpace ComplexVectorL2 :=
  ⟨rfl⟩

/-- The complex physical Stokes kernel at elapsed time `τ`, truncated to the
causal interval of the observation time `t`. -/
@[expose]
def regularisedComplexShiftedStokesIntegrand
    (F : ℝ → ComplexTensorL2) (t τ : ℝ) : ComplexVectorL2 :=
  if h : 0 < τ ∧ τ < t then stokesL2Operator h.1 (F (t - τ)) else 0

/-- The translated physical Stokes integrand is integrable on every bounded
time interval under a uniform tensor bound. -/
theorem regularisedComplexShiftedStokesIntegrand_intervalIntegrable
    (F : ℝ → ComplexTensorL2)
    (hF : Continuous F) (C : ℝ) (hFC : ∀ s, ‖F s‖ ≤ C)
    (hC : 0 ≤ C) (T t : ℝ) (hT : 0 ≤ T) :
    IntervalIntegrable
      (regularisedComplexShiftedStokesIntegrand F t) volume 0 T := by
  let B : ℝ := C / Real.sqrt (2 * Real.exp 1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hAbel : IntervalIntegrable
      (fun τ : ℝ => τ ^ (-(2 : ℝ)⁻¹)) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hboundInt : IntervalIntegrable
      (fun τ : ℝ => B * τ ^ (-(2 : ℝ)⁻¹)) volume 0 T :=
    hAbel.const_mul B
  have hmeas : Measurable
      (regularisedComplexShiftedStokesIntegrand F t) := by
    have hposCont : Continuous
        (fun q : {x : ℝ // x ∈ Set.Ioi (0 : ℝ)} =>
          stokesL2Operator (Set.mem_Ioi.mp q.2) (F (t - q))) := by
      rw [continuous_iff_continuousAt]
      intro q
      let posTime : {x : ℝ // x ∈ Set.Ioi (0 : ℝ)} → {x : ℝ // 0 < x} :=
        fun r => ⟨r, Set.mem_Ioi.mp r.2⟩
      have hposTime : Continuous posTime :=
        continuous_subtype_val.subtype_mk (fun r => Set.mem_Ioi.mp r.2)
      have hG : ContinuousAt
          (fun r : {x : ℝ // 0 < x} => F (t - r)) (posTime q) := by
        exact hF.continuousAt.comp
          ((continuous_const.sub continuous_subtype_val).continuousAt)
      have ht : Tendsto posTime (𝓝 q) (𝓝 (posTime q)) :=
        hposTime.continuousAt.tendsto
      have hjoint := stokesL2Operator_continuousAt_apply
        (Set.mem_Ioi.mp q.2) (fun r => r) tendsto_id
        (fun r => F (t - r)) hG
      change Tendsto
        (fun x : {x : ℝ // x ∈ Set.Ioi (0 : ℝ)} =>
          stokesL2Operator (Set.mem_Ioi.mp x.2) (F (t - x)))
        (𝓝 q)
        (𝓝 (stokesL2Operator (Set.mem_Ioi.mp q.2) (F (t - q))) )
      exact hjoint.comp ht
    have hbase : ContinuousOn
        (fun τ : ℝ => if hτ : 0 < τ then
          stokesL2Operator hτ (F (t - τ)) else 0)
        {τ | τ ≠ 0} := by
      have hpos : ContinuousOn
          (fun τ : ℝ => if hτ : 0 < τ then
            stokesL2Operator hτ (F (t - τ)) else 0)
          (Set.Ioi 0) := by
        rw [continuousOn_iff_continuous_domRestrict]
        have hEq : (Set.Ioi (0 : ℝ)).domRestrict
            (fun τ : ℝ => if hτ : 0 < τ then
              stokesL2Operator hτ (F (t - τ)) else 0) =
            (fun q : {x : ℝ // x ∈ Set.Ioi (0 : ℝ)} =>
              stokesL2Operator (Set.mem_Ioi.mp q.2) (F (t - q))) := by
          funext q
          have hq : 0 < (q : ℝ) := Set.mem_Ioi.mp q.2
          simp [Set.domRestrict, hq]
        rw [hEq]
        exact hposCont
      have hneg : ContinuousOn
          (fun τ : ℝ => if hτ : 0 < τ then
            stokesL2Operator hτ (F (t - τ)) else 0)
          (Set.Iio 0) := by
        have hEq : ∀ τ ∈ Set.Iio (0 : ℝ),
            (if hτ : 0 < τ then
              stokesL2Operator hτ (F (t - τ)) else 0) =
              (0 : ComplexVectorL2) := by
          intro τ hτ
          have hτ' : τ < 0 := by simpa only [Set.mem_Iio] using hτ
          simp [not_lt_of_ge (le_of_lt hτ')]
        exact (continuousOn_congr hEq).2 continuousOn_const
      have hunion := hpos.union_of_isOpen hneg isOpen_Ioi isOpen_Iio
      convert hunion using 1
      ext τ
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Ioi, Set.mem_Iio]
      constructor
      · intro h
        by_cases hp : 0 < τ
        · exact Or.inl hp
        · right
          have hn : τ ≤ 0 := le_of_not_gt hp
          exact lt_of_le_of_ne hn h
      · rintro (h | h)
        · exact ne_of_gt h
        · exact ne_of_lt h
    have hbaseMeas : Measurable
        (fun τ : ℝ => if hτ : 0 < τ then
          stokesL2Operator hτ (F (t - τ)) else 0) :=
      hbase.measurable_of_countable_compl (by simp)
    have hset : MeasurableSet {τ : ℝ | τ < t} := measurableSet_Iio
    have hpiece : Measurable (fun τ : ℝ =>
        if τ < t then
          (if hτ : 0 < τ then
            stokesL2Operator hτ (F (t - τ)) else 0)
        else 0) :=
      Measurable.ite hset hbaseMeas measurable_const
    convert hpiece using 1
    funext τ
    by_cases hτ : 0 < τ
    · by_cases ht : τ < t <;>
        simp [regularisedComplexShiftedStokesIntegrand, hτ, ht]
    · simp [regularisedComplexShiftedStokesIntegrand, hτ]
  have hmeas' : AEStronglyMeasurable
      (regularisedComplexShiftedStokesIntegrand F t) volume :=
    hmeas.aestronglyMeasurable
  have hbound : ∀ᵐ τ ∂volume.restrict (Set.Ioc 0 T),
      ‖regularisedComplexShiftedStokesIntegrand F t τ‖ ≤
        B * τ ^ (-(2 : ℝ)⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
    have hτpos : 0 < τ := hτ.1
    by_cases h : 0 < τ ∧ τ < t
    · simp only [regularisedComplexShiftedStokesIntegrand, h, and_self, ↓reduceDIte,
      ge_iff_le]
      calc
        ‖stokesL2Operator h.1 (F (t - τ))‖ ≤
            (1 / Real.sqrt (2 * Real.exp 1 * τ)) * ‖F (t - τ)‖ :=
          stokesL2Operator_norm_le h.1 _
        _ ≤ (1 / Real.sqrt (2 * Real.exp 1 * τ)) * C :=
          mul_le_mul_of_nonneg_left (hFC _) (by positivity)
        _ = B * τ ^ (-(2 : ℝ)⁻¹) := by
          have hA : 0 ≤ 2 * Real.exp 1 := by positivity
          have hsqrtKernel : 1 / Real.sqrt (2 * Real.exp 1 * τ) =
              (1 / Real.sqrt (2 * Real.exp 1)) * τ ^ (-(2 : ℝ)⁻¹) := by
            rw [show 2 * Real.exp 1 * τ = (2 * Real.exp 1) * τ by ring,
              Real.sqrt_mul hA τ]
            have hsqrt : Real.sqrt τ = τ ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
            rw [hsqrt, Real.rpow_neg (le_of_lt h.1)]
            field_simp
          rw [hsqrtKernel]
          dsimp [B]
          ring
    · simp only [regularisedComplexShiftedStokesIntegrand, h, ↓reduceDIte, norm_zero,
      ge_iff_le]
      exact mul_nonneg hB (Real.rpow_nonneg hτpos.le _)
  have hmajorant : Integrable
      (fun τ : ℝ => B * τ ^ (-(2 : ℝ)⁻¹))
      (volume.restrict (Set.Ioc 0 T)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hboundInt
  have hintegrable : Integrable
      (regularisedComplexShiftedStokesIntegrand F t)
      (volume.restrict (Set.Ioc 0 T)) := by
    exact hmajorant.mono' (hmeas'.restrict) hbound
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr hintegrable

end CKN.Leray

end
