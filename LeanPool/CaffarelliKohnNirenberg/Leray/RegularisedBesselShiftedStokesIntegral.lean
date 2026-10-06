/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselMildContinuity
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Continuity of the shifted complete Sobolev Stokes integral

The time translation fixes the Abel singularity at the left endpoint of the
integration interval, giving a common integrable bound for every evaluation
time.
-/

public section

open MeasureTheory Filter
open scoped Interval ENNReal Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

local instance shiftedBesselMeasure : IsSeparable (volume : Measure L2Vec3) := by
  infer_instance

local instance shiftedBesselComplexVecSeparable :
    TopologicalSpace.SeparableSpace ComplexVec3 := by
  infer_instance

local instance shiftedBesselTwoFinite : Fact ((2 : ℝ≥0∞) ≠ ∞) :=
  ⟨by norm_num⟩

local instance shiftedBesselVectorSeparable (k : ℕ) :
    TopologicalSpace.SeparableSpace
      (BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) := by
  let e := BesselPotentialSpace.toLpₗᵢ L2Vec3 ComplexVec3
    ((2 * k : ℕ) : ℝ) 2
  exact e.toContinuousLinearEquiv.isOpenMap.separableSpace_of_injective e.injective

local instance shiftedBesselVectorSecondCountable (k : ℕ) :
    SecondCountableTopology
      (BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) := by
  exact UniformSpace.secondCountable_of_separable _

local instance shiftedBesselVectorMeasurableSpace (k : ℕ) :
    MeasurableSpace
      (BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) :=
  borel _

local instance shiftedBesselVectorBorelSpace (k : ℕ) :
    BorelSpace
      (BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) :=
  ⟨rfl⟩

/-- The translated complete Sobolev Stokes integrand, set to zero outside
the interval where its elapsed-time parameter is positive. -/
@[expose]
def regularisedBesselShiftedStokesIntegrand
    (k : ℕ)
    (F : ℝ → BesselPotentialSpace L2Vec3 ComplexTensor3 ((2 * k : ℕ) : ℝ) 2)
    (t τ : ℝ) : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2 :=
  if h : 0 < τ ∧ τ < t then
    regularisedBesselStokesOperator h.1 k (F (t - τ)) else 0

private theorem regularisedBesselShiftedStokesKernel_eq_of_pos
    {k : ℕ} {F : ℝ → BesselPotentialSpace L2Vec3 ComplexTensor3
      ((2 * k : ℕ) : ℝ) 2} {t τ : ℝ} (hτ : 0 < τ) :
    regularisedBesselShiftedStokesIntegrand k F t τ =
      if τ < t then regularisedBesselStokesOperator hτ k (F (t - τ)) else 0 := by
  by_cases ht : τ < t <;> simp [regularisedBesselShiftedStokesIntegrand, hτ, ht]

private theorem regularisedBesselShiftedStokesIntegrand_measurable
    (k : ℕ)
    (F : ℝ → BesselPotentialSpace L2Vec3 ComplexTensor3 ((2 * k : ℕ) : ℝ) 2)
    (hF : Continuous F) (t : ℝ) :
    Measurable (regularisedBesselShiftedStokesIntegrand k F t) := by
  have hposCont : Continuous
      (fun q : {x : ℝ // x ∈ Set.Ioi (0 : ℝ)} =>
        regularisedBesselStokesOperator (Set.mem_Ioi.mp q.2) k (F (t - q))) := by
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
    have hjoint := regularisedBesselStokesOperator_continuousAt_apply
      (Set.mem_Ioi.mp q.2) k (fun r => F (t - r)) hG
    change Tendsto
      (fun x : {x : ℝ // x ∈ Set.Ioi (0 : ℝ)} =>
        regularisedBesselStokesOperator (Set.mem_Ioi.mp x.2) k (F (t - x)))
      (𝓝 q)
      (𝓝 (regularisedBesselStokesOperator (Set.mem_Ioi.mp q.2) k (F (t - q))))
    exact Filter.Tendsto.comp (f := posTime) hjoint.tendsto ht
  have hbase : ContinuousOn
      (fun τ : ℝ => if hτ : 0 < τ then
        regularisedBesselStokesOperator hτ k (F (t - τ)) else 0)
      {τ | τ ≠ 0} := by
    have hpos : ContinuousOn
        (fun τ : ℝ => if hτ : 0 < τ then
          regularisedBesselStokesOperator hτ k (F (t - τ)) else 0)
        (Set.Ioi 0) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hEq : (Set.Ioi (0 : ℝ)).domRestrict
          (fun τ : ℝ => if hτ : 0 < τ then
            regularisedBesselStokesOperator hτ k (F (t - τ)) else 0) =
          (fun q : {x : ℝ // x ∈ Set.Ioi (0 : ℝ)} =>
            regularisedBesselStokesOperator (Set.mem_Ioi.mp q.2) k (F (t - q))) := by
        funext q
        have hq : 0 < (q : ℝ) := Set.mem_Ioi.mp q.2
        simp [Set.domRestrict, hq]
      rw [hEq]
      exact hposCont
    have hneg : ContinuousOn
        (fun τ : ℝ => if hτ : 0 < τ then
          regularisedBesselStokesOperator hτ k (F (t - τ)) else 0)
        (Set.Iio 0) := by
      have hEq : ∀ τ ∈ Set.Iio (0 : ℝ),
          (if hτ : 0 < τ then
            regularisedBesselStokesOperator hτ k (F (t - τ)) else 0) =
            (0 : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) := by
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
        regularisedBesselStokesOperator hτ k (F (t - τ)) else 0) :=
    hbase.measurable_of_countable_compl (by simp)
  have hset : MeasurableSet {τ : ℝ | τ < t} := measurableSet_Iio
  have hpiece : Measurable (fun τ : ℝ =>
      if τ < t then
        (if hτ : 0 < τ then regularisedBesselStokesOperator hτ k (F (t - τ)) else 0)
      else 0) :=
    Measurable.ite hset hbaseMeas measurable_const
  convert hpiece using 1
  funext τ
  by_cases hτ : 0 < τ
  · by_cases ht : τ < t <;>
      simp [regularisedBesselShiftedStokesIntegrand, hτ, ht]
  · simp [regularisedBesselShiftedStokesIntegrand, hτ]

private theorem regularisedBesselShiftedStokesIntegrand_continuousAt_time
    (k : ℕ)
    (F : ℝ → BesselPotentialSpace L2Vec3 ComplexTensor3 ((2 * k : ℕ) : ℝ) 2)
    (hF : Continuous F) {t₀ τ : ℝ} (hτ : τ ≠ t₀) :
    ContinuousAt (fun t => regularisedBesselShiftedStokesIntegrand k F t τ) t₀ := by
  by_cases hpos : 0 < τ
  · by_cases hleft : τ < t₀
    · have hnear : ∀ᶠ t : ℝ in 𝓝 t₀, τ < t := Ioi_mem_nhds hleft
      have heq : (fun t => regularisedBesselShiftedStokesIntegrand k F t τ) =ᶠ[𝓝 t₀]
          fun t => regularisedBesselStokesOperator hpos k (F (t - τ)) := by
        filter_upwards [hnear] with t ht
        simp [regularisedBesselShiftedStokesIntegrand, hpos, ht]
      apply ContinuousAt.congr_of_eventuallyEq ?_ heq
      exact ((regularisedBesselStokesOperator hpos k).continuous.continuousAt).comp
        (hF.continuousAt.comp (continuous_id.sub continuous_const).continuousAt)
    · have hgt : t₀ < τ := lt_of_le_of_ne (le_of_not_gt hleft) hτ.symm
      have hnear : ∀ᶠ t : ℝ in 𝓝 t₀, t < τ := Iio_mem_nhds hgt
      have heq : (fun t => regularisedBesselShiftedStokesIntegrand k F t τ) =ᶠ[𝓝 t₀]
          fun _ => (0 : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) := by
        filter_upwards [hnear] with t ht
        simp [regularisedBesselShiftedStokesIntegrand, hpos, not_lt_of_ge ht.le]
      exact continuousAt_const.congr_of_eventuallyEq heq
  · have heq : (fun t => regularisedBesselShiftedStokesIntegrand k F t τ) =ᶠ[𝓝 t₀]
        fun _ => (0 : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) := by
      filter_upwards [] with t
      simp [regularisedBesselShiftedStokesIntegrand, hpos]
    exact continuousAt_const.congr_of_eventuallyEq heq

private theorem regularisedBesselShiftedStokesIntegral_continuousAt
    (k : ℕ)
    (F : ℝ → BesselPotentialSpace L2Vec3 ComplexTensor3 ((2 * k : ℕ) : ℝ) 2)
    (hF : Continuous F) (C : ℝ) (hFC : ∀ s, ‖F s‖ ≤ C)
    (hC : 0 ≤ C) (T : ℝ) (hT : 0 ≤ T) {t₀ : ℝ} :
    ContinuousAt (fun t => ∫ τ in (0 : ℝ)..T,
      regularisedBesselShiftedStokesIntegrand k F t τ) t₀ := by
  let B : ℝ := C / Real.sqrt (2 * Real.exp 1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hboundInt : IntervalIntegrable
      (fun τ : ℝ => B * τ ^ (-(2 : ℝ)⁻¹)) volume 0 T := by
    have hkernel : IntervalIntegrable
        (fun τ : ℝ => τ ^ (-(2 : ℝ)⁻¹)) volume 0 T :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    exact hkernel.const_mul B
  apply intervalIntegral.continuousAt_of_dominated_interval
    (F := fun t τ => regularisedBesselShiftedStokesIntegrand k F t τ)
    (bound := fun τ => B * τ ^ (-(2 : ℝ)⁻¹))
  · exact Filter.Eventually.of_forall fun t =>
      ((regularisedBesselShiftedStokesIntegrand_measurable k F hF t).aestronglyMeasurable).restrict
  · filter_upwards [] with t
    filter_upwards [] with τ
    intro hτ
    by_cases h : 0 < τ ∧ τ < t
    · simp only [regularisedBesselShiftedStokesIntegrand, h, and_self, ↓reduceDIte]
      have hkernel := regularisedBesselStokesOperator_norm_le h.1 k (F (t - τ))
      calc
        ‖regularisedBesselStokesOperator h.1 k (F (t - τ))‖ ≤
            (1 / Real.sqrt (2 * Real.exp 1 * τ)) * ‖F (t - τ)‖ := hkernel
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
    · simp only [regularisedBesselShiftedStokesIntegrand, h, ↓reduceDIte, norm_zero]
      rw [Set.uIoc_of_le hT] at hτ
      simpa [norm_zero] using
        (mul_nonneg hB (Real.rpow_nonneg hτ.1.le _))
  · exact hboundInt
  · have hne : ∀ᵐ τ : ℝ ∂volume, τ ≠ t₀ := by
      exact ae_iff.2 (by simp)
    filter_upwards [hne] with τ hτ
    intro hmem
    exact regularisedBesselShiftedStokesIntegrand_continuousAt_time k F hF hτ

/-- The fixed-upper-limit translated Stokes integral is continuous on the
complete even-order Bessel potential space. -/
theorem regularisedBesselShiftedStokesIntegral_continuous
    (k : ℕ)
    (F : ℝ → BesselPotentialSpace L2Vec3 ComplexTensor3 ((2 * k : ℕ) : ℝ) 2)
    (hF : Continuous F) (C : ℝ) (hFC : ∀ s, ‖F s‖ ≤ C)
    (hC : 0 ≤ C) (T : ℝ) (hT : 0 ≤ T) :
    Continuous (fun t : ℝ => ∫ τ in (0 : ℝ)..T,
      regularisedBesselShiftedStokesIntegrand k F t τ) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact regularisedBesselShiftedStokesIntegral_continuousAt
    k F hF C hFC hC T hT

end CKN.Leray

end
