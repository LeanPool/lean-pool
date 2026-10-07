/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildPathContinuity
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Continuity and integrability of the mild Stokes term

The Abel singularity is kept at a fixed elapsed-time endpoint by translating
the time variable in the Stokes integral.
-/

public section

open MeasureTheory Filter
open scoped Interval ENNReal Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The Borel measurable structure used for the real vector-valued `L²` space. -/
local instance : MeasurableSpace RealVectorL2 := borel RealVectorL2
local instance : BorelSpace RealVectorL2 := ⟨rfl⟩
local instance : IsSeparable (volume : Measure L2Vec3) := by infer_instance
local instance : TopologicalSpace.SeparableSpace L2Vec3 := by infer_instance
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
local instance : SecondCountableTopology RealVectorL2 := by
  exact Lp.SecondCountableTopology

/-- The translated Stokes integrand, extended by zero outside `0 < τ < t`. -/
@[expose]
def mildShiftedStokesIntegrand (F : ℝ → RealTensorL2)
    (t τ : ℝ) : RealVectorL2 :=
  if h : 0 < τ ∧ τ < t then
    realStokesOperator h.1 (F (t - τ))
  else 0

private theorem mildShiftedStokesKernel_eq_of_pos {F : ℝ → RealTensorL2}
    {t τ : ℝ} (hτ : 0 < τ) :
    mildShiftedStokesIntegrand F t τ =
      if τ < t then realStokesOperator hτ (F (t - τ)) else 0 := by
  by_cases ht : τ < t <;> simp [mildShiftedStokesIntegrand, hτ, ht]

private theorem mildShiftedStokesIntegrand_measurable
    (F : ℝ → RealTensorL2) (hF : Continuous F) (t : ℝ) :
    Measurable (mildShiftedStokesIntegrand F t) := by
  have hposCont : Continuous
      (fun q : {x : ℝ // x ∈ Set.Ioi (0 : ℝ)} =>
        realStokesOperator (Set.mem_Ioi.mp q.2) (F (t - q))) := by
    rw [continuous_iff_continuousAt]
    intro q
    let posTime : {x : ℝ // x ∈ Set.Ioi (0 : ℝ)} → {x : ℝ // 0 < x} :=
      fun r => ⟨r, Set.mem_Ioi.mp r.2⟩
    have hposTime : Continuous posTime :=
      continuous_subtype_val.subtype_mk (fun r => Set.mem_Ioi.mp r.2)
    have hG : ContinuousAt (fun r : {x : ℝ // 0 < x} => F (t - r))
        (posTime q) := by
      exact hF.continuousAt.comp
        ((continuous_const.sub continuous_subtype_val).continuousAt)
    have ht : Tendsto posTime (𝓝 q) (𝓝 (posTime q)) :=
      hposTime.continuousAt.tendsto
    have hjoint := realStokesOperator_continuousAt_apply (Set.mem_Ioi.mp q.2)
      posTime ht (fun r => F (t - r)) hG
    change Tendsto
      (fun x : {x : ℝ // x ∈ Set.Ioi (0 : ℝ)} =>
        realStokesOperator (Set.mem_Ioi.mp x.2) (F (t - x)))
      (𝓝 q)
      (𝓝 (realStokesOperator (Set.mem_Ioi.mp q.2) (F (t - q))))
    exact hjoint
  have hbase : ContinuousOn
      (fun τ : ℝ => if hτ : 0 < τ then realStokesOperator hτ (F (t - τ)) else 0)
      {τ | τ ≠ 0} := by
    have hpos : ContinuousOn
        (fun τ : ℝ => if hτ : 0 < τ then realStokesOperator hτ (F (t - τ)) else 0)
      (Set.Ioi 0) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hEq : (Set.Ioi (0 : ℝ)).domRestrict
          (fun τ : ℝ => if hτ : 0 < τ then realStokesOperator hτ (F (t - τ)) else 0) =
          (fun q : {x : ℝ // x ∈ Set.Ioi (0 : ℝ)} =>
            realStokesOperator (Set.mem_Ioi.mp q.2) (F (t - q))) := by
        funext q
        have hq : 0 < (q : ℝ) := Set.mem_Ioi.mp q.2
        simp [Set.domRestrict, hq]
      rw [hEq]
      exact hposCont
    have hneg : ContinuousOn
        (fun τ : ℝ => if hτ : 0 < τ then realStokesOperator hτ (F (t - τ)) else 0)
        (Set.Iio 0) := by
      have hEq : ∀ τ ∈ Set.Iio (0 : ℝ),
          (if hτ : 0 < τ then realStokesOperator hτ (F (t - τ)) else 0) =
            (0 : RealVectorL2) := by
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
      (fun τ : ℝ => if hτ : 0 < τ then realStokesOperator hτ (F (t - τ)) else 0) :=
    hbase.measurable_of_countable_compl (by simp)
  have hset : MeasurableSet {τ : ℝ | τ < t} := measurableSet_Iio
  have hpiece : Measurable (fun τ : ℝ =>
      if τ < t then (if hτ : 0 < τ then realStokesOperator hτ (F (t - τ)) else 0) else 0) :=
    Measurable.ite hset hbaseMeas measurable_const
  convert hpiece using 1
  funext τ
  by_cases hτ : 0 < τ
  · by_cases ht : τ < t <;> simp [mildShiftedStokesIntegrand, hτ, ht]
  · simp [mildShiftedStokesIntegrand, hτ]

private theorem mildShiftedStokesIntegrand_continuousAt_time
    (F : ℝ → RealTensorL2) (hF : Continuous F) {t₀ τ : ℝ}
    (hτ : τ ≠ t₀) :
    ContinuousAt (fun t => mildShiftedStokesIntegrand F t τ) t₀ := by
  by_cases hpos : 0 < τ
  · by_cases hleft : τ < t₀
    · have hnear : ∀ᶠ t : ℝ in 𝓝 t₀, τ < t := Ioi_mem_nhds hleft
      have heq : (fun t => mildShiftedStokesIntegrand F t τ) =ᶠ[𝓝 t₀]
          fun t => realStokesOperator hpos (F (t - τ)) := by
        filter_upwards [hnear] with t ht
        simp [mildShiftedStokesIntegrand, hpos, ht]
      apply ContinuousAt.congr_of_eventuallyEq ?_ heq
      exact ((realStokesContinuousLinearMap hpos).continuous.continuousAt).comp
        (hF.continuousAt.comp (continuous_id.sub continuous_const).continuousAt)
    · have hgt : t₀ < τ := lt_of_le_of_ne (le_of_not_gt hleft) hτ.symm
      have hnear : ∀ᶠ t : ℝ in 𝓝 t₀, t < τ := Iio_mem_nhds hgt
      have heq : (fun t => mildShiftedStokesIntegrand F t τ) =ᶠ[𝓝 t₀]
          fun _ => (0 : RealVectorL2) := by
        filter_upwards [hnear] with t ht
        simp [mildShiftedStokesIntegrand, hpos, not_lt_of_ge ht.le]
      exact continuousAt_const.congr_of_eventuallyEq heq
  · have heq : (fun t => mildShiftedStokesIntegrand F t τ) =ᶠ[𝓝 t₀]
        fun _ => (0 : RealVectorL2) := by
      filter_upwards [] with t
      simp [mildShiftedStokesIntegrand, hpos]
    exact continuousAt_const.congr_of_eventuallyEq heq

private theorem mildStokesKernel_rpow_identity {τ : ℝ} (hτ : 0 < τ) :
    1 / Real.sqrt (2 * Real.exp 1 * τ) =
      (1 / Real.sqrt (2 * Real.exp 1)) * τ ^ (-(2 : ℝ)⁻¹) := by
  have hA : 0 ≤ 2 * Real.exp 1 := by positivity
  rw [show 2 * Real.exp 1 * τ = (2 * Real.exp 1) * τ by ring,
    Real.sqrt_mul hA τ]
  have hsqrt : Real.sqrt τ = τ ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  rw [hsqrt, Real.rpow_neg (le_of_lt hτ)]
  field_simp

private theorem mildAbelBound_intervalIntegrable (T : ℝ) :
    IntervalIntegrable (fun τ : ℝ => τ ^ (-(2 : ℝ)⁻¹)) volume 0 T := by
  exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)

/-- The fixed-upper-limit translated Stokes integral is continuous in its
evaluation time. -/
theorem mildShiftedStokesIntegral_continuousAt
    (F : ℝ → RealTensorL2) (hF : Continuous F) (C : ℝ)
    (hFC : ∀ t, ‖F t‖ ≤ C) (hC : 0 ≤ C) (T : ℝ) (hT : 0 ≤ T) {t₀ : ℝ} :
    ContinuousAt (fun t => ∫ τ in (0 : ℝ)..T,
      mildShiftedStokesIntegrand F t τ) t₀ := by
  borelize (↥RealVectorL2)
  let B : ℝ := C / Real.sqrt (2 * Real.exp 1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hboundInt : IntervalIntegrable
      (fun τ : ℝ => B * τ ^ (-(2 : ℝ)⁻¹)) volume 0 T :=
    (mildAbelBound_intervalIntegrable T).const_mul B
  apply intervalIntegral.continuousAt_of_dominated_interval
    (F := fun t τ => mildShiftedStokesIntegrand F t τ) (bound := fun τ => B * τ ^ (-(2 : ℝ)⁻¹))
  · exact Filter.Eventually.of_forall fun t =>
      (mildShiftedStokesIntegrand_measurable F hF t).aestronglyMeasurable.restrict
  · filter_upwards [] with t
    filter_upwards [] with τ
    intro hτ
    by_cases h : 0 < τ ∧ τ < t
    · simp only [mildShiftedStokesIntegrand, h, and_self, ↓reduceDIte]
      have hkernel := realStokesOperator_norm_le h.1 (F (t - τ))
      calc
        ‖realStokesOperator h.1 (F (t - τ))‖ ≤
            (1 / Real.sqrt (2 * Real.exp 1 * τ)) * ‖F (t - τ)‖ := hkernel
        _ ≤ (1 / Real.sqrt (2 * Real.exp 1 * τ)) * C :=
          mul_le_mul_of_nonneg_left (hFC _) (by positivity)
        _ = B * τ ^ (-(2 : ℝ)⁻¹) := by
          rw [mildStokesKernel_rpow_identity h.1]
          dsimp [B]
          ring
    · simp only [mildShiftedStokesIntegrand, h, ↓reduceDIte, norm_zero]
      rw [Set.uIoc_of_le hT] at hτ
      simpa [norm_zero] using (mul_nonneg hB (Real.rpow_nonneg hτ.1.le _))
  · exact hboundInt
  · have hne : ∀ᵐ τ : ℝ ∂volume, τ ≠ t₀ := by
      exact ae_iff.2 (by simp)
    filter_upwards [hne] with τ hτ
    intro hmem
    exact mildShiftedStokesIntegrand_continuousAt_time F hF hτ

/-- The fixed-upper-limit translated Stokes integral is a continuous
trajectory. -/
theorem mildShiftedStokesIntegral_continuous
    (F : ℝ → RealTensorL2) (hF : Continuous F) (C : ℝ)
    (hFC : ∀ t, ‖F t‖ ≤ C) (hC : 0 ≤ C) (T : ℝ) (hT : 0 ≤ T) :
    Continuous fun t => ∫ τ in (0 : ℝ)..T,
      mildShiftedStokesIntegrand F t τ := by
  rw [continuous_iff_continuousAt]
  intro t
  exact mildShiftedStokesIntegral_continuousAt F hF C hFC hC T hT

/-- The translated Stokes integrand is integrable on every bounded time
interval under a uniform tensor bound. -/
theorem mildShiftedStokesIntegrand_intervalIntegrable
    (F : ℝ → RealTensorL2) (hF : Continuous F) (C : ℝ)
    (hFC : ∀ s, ‖F s‖ ≤ C) (hC : 0 ≤ C) (T t : ℝ) (hT : 0 ≤ T) :
    IntervalIntegrable (mildShiftedStokesIntegrand F t) volume 0 T := by
  let B : ℝ := C / Real.sqrt (2 * Real.exp 1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hboundInt : IntervalIntegrable
      (fun τ : ℝ => B * τ ^ (-(2 : ℝ)⁻¹)) volume 0 T :=
    (mildAbelBound_intervalIntegrable T).const_mul B
  have hmeas : AEStronglyMeasurable (mildShiftedStokesIntegrand F t) volume :=
    (mildShiftedStokesIntegrand_measurable F hF t).aestronglyMeasurable
  have hbound : ∀ᵐ τ ∂volume.restrict (Set.Ioc 0 T),
      ‖mildShiftedStokesIntegrand F t τ‖ ≤ B * τ ^ (-(2 : ℝ)⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
    have hτpos : 0 < τ := hτ.1
    by_cases h : 0 < τ ∧ τ < t
    · simp only [mildShiftedStokesIntegrand, h, ge_iff_le]
      calc
        ‖realStokesOperator h.1 (F (t - τ))‖ ≤
            (1 / Real.sqrt (2 * Real.exp 1 * τ)) * ‖F (t - τ)‖ :=
          realStokesOperator_norm_le h.1 _
        _ ≤ (1 / Real.sqrt (2 * Real.exp 1 * τ)) * C :=
          mul_le_mul_of_nonneg_left (hFC _) (by positivity)
        _ = B * τ ^ (-(2 : ℝ)⁻¹) := by
          rw [mildStokesKernel_rpow_identity hτpos]
          dsimp [B]
          ring
    · simp only [mildShiftedStokesIntegrand, h, ↓reduceDIte, norm_zero,
        ge_iff_le]
      exact mul_nonneg hB (Real.rpow_nonneg hτpos.le _)
  have hg : Integrable (fun τ : ℝ => B * τ ^ (-(2 : ℝ)⁻¹))
      (volume.restrict (Set.Ioc 0 T)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hboundInt
  have hh : Integrable (mildShiftedStokesIntegrand F t)
      (volume.restrict (Set.Ioc 0 T)) := by
    apply hg.mono' (hmeas.restrict)
    filter_upwards [hbound] with τ hτ
    exact hτ
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr hh

/-- Translation of the time variable turns the singularity into a fixed
integrable Abel kernel. -/
theorem regularizedMildStokesIntegral_eq_shifted {F : ℝ → RealTensorL2}
    (T t : ℝ) (hT : 0 ≤ T) (ht : 0 ≤ t) (htT : t ≤ T)
    (hF : Continuous F) (C : ℝ) (hFC : ∀ s, ‖F s‖ ≤ C) (hC : 0 ≤ C) :
    regularizedMildStokesIntegral F t =
      ∫ τ in (0 : ℝ)..T, mildShiftedStokesIntegrand F t τ := by
  have hI0 := mildShiftedStokesIntegrand_intervalIntegrable F hF C hFC hC T t hT
  have hzeroMem : (0 : ℝ) ∈ Set.uIcc 0 T := Set.left_mem_uIcc
  have htMem : t ∈ Set.uIcc 0 T := Set.mem_uIcc_of_le ht htT
  have hTMem : T ∈ Set.uIcc 0 T := Set.right_mem_uIcc
  have hIt : IntervalIntegrable (mildShiftedStokesIntegrand F t) volume 0 t :=
    hI0.mono_set (Set.uIcc_subset_uIcc hzeroMem htMem)
  have hTt : IntervalIntegrable (mildShiftedStokesIntegrand F t) volume t T :=
    hI0.mono_set (Set.uIcc_subset_uIcc htMem hTMem)
  have hzeroEq : ∫ τ in t..T, mildShiftedStokesIntegrand F t τ = 0 := by
    have hEq : (∫ τ in t..T, mildShiftedStokesIntegrand F t τ) =
        ∫ τ in t..T, (0 : RealVectorL2) := by
      apply intervalIntegral.integral_congr_Ioo_of_le htT
      intro τ hτ
      have hnot : ¬ τ < t := not_lt_of_ge (le_of_lt hτ.1)
      simp [mildShiftedStokesIntegrand, hnot]
    rw [hEq]
    simp
  calc
    regularizedMildStokesIntegral F t =
        ∫ s in (0 : ℝ)..t, regularizedMildStokesIntegrand F t s := by
      simp [regularizedMildStokesIntegral, integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le ht]
    _ = ∫ s in (0 : ℝ)..t, mildShiftedStokesIntegrand F t (t - s) := by
      apply intervalIntegral.integral_congr_Ioo_of_le ht
      intro s hs
      have hspos : 0 < s := hs.1
      have hst : s < t := hs.2
      simp [regularizedMildStokesIntegrand, mildShiftedStokesIntegrand,
        hspos, hst, sub_pos.mpr hst]
    _ = ∫ τ in (0 : ℝ)..t, mildShiftedStokesIntegrand F t τ := by
      simp [sub_self]
    _ = (∫ τ in (0 : ℝ)..t, mildShiftedStokesIntegrand F t τ) +
          ∫ τ in t..T, mildShiftedStokesIntegrand F t τ := by
      rw [hzeroEq]
      simp
    _ = ∫ τ in (0 : ℝ)..T, mildShiftedStokesIntegrand F t τ :=
      intervalIntegral.integral_add_adjacent_intervals hIt hTt

end CKN.Leray

end
