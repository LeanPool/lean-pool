/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Locality for measures and integrals
-/

@[expose] public section

open Set Filter MeasureTheory Metric
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.MeasureLocality

/-- A property that holds almost everywhere on a ball about each point of a set
holds almost everywhere on the set. -/
theorem ae_of_forall_ball {E : Type*} [PseudoMetricSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] {μ : Measure E} {U : Set E} {Q : E → Prop}
    (h : ∀ z ∈ U, ∃ r > 0, ∀ᵐ x ∂μ, x ∈ ball z r → Q x) :
    ∀ᵐ x ∂μ, x ∈ U → Q x := by
  classical
  choose! r hr hQ using h
  obtain ⟨S, hSc, hSU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun z : U ↦ ball (z : E) (r z)) (fun _ ↦ isOpen_ball)
  have hS : ∀ᵐ x ∂μ, ∀ z ∈ S,
      x ∈ ball ((z : U) : E) (r z) → Q x :=
    (ae_ball_iff hSc).mpr fun z _ ↦ hQ z z.2
  filter_upwards [hS] with x hx hxU
  have hx' : x ∈ ⋃ z : U, ball (z : E) (r z) :=
    mem_iUnion.mpr ⟨⟨x, hxU⟩, mem_ball_self (hr x hxU)⟩
  rw [← hSU] at hx'
  obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp hx'
  exact hx z hz hxz

/-- A continuous compactly supported function with support in a set on whose
compact subsets the measure is finite is integrable. -/
theorem integrable_of_tsupport_subset {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {Ω : Set X} {μ : Measure X}
    (hμ : ∀ K, IsCompact K → K ⊆ Ω → μ K < ⊤) {φ : X → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφΩ : tsupport φ ⊆ Ω) : Integrable φ μ := by
  obtain ⟨M, hM⟩ := hφc.exists_bound_of_continuous hφ
  rw [← integrableOn_iff_integrable_of_support_subset (subset_tsupport φ)]
  exact Measure.integrableOn_of_bounded (M := M) (hμ _ hφc hφΩ).ne
    hφ.aestronglyMeasurable (Eventually.of_forall hM)

/-- A continuous compactly supported function times an a.e. bounded density
is integrable if the measure is finite on the support. -/
theorem integrable_mul_of_ae_bounded_on_tsupport {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} {φ w : X → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hμ : μ (tsupport φ) < ⊤)
    (hw : AEStronglyMeasurable w μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ.restrict (tsupport φ), |w x| ≤ C) :
    Integrable (fun x => φ x * w x) μ := by
  obtain ⟨M, hM⟩ := hφc.exists_bound_of_continuous hφ
  have hsupp : Function.support (fun x => φ x * w x) ⊆ tsupport φ := fun x hx =>
    subset_tsupport φ (left_ne_zero_of_mul hx)
  refine (integrableOn_iff_integrable_of_support_subset hsupp).mp ?_
  refine Measure.integrableOn_of_bounded (M := M * C) hμ.ne
    (hφ.aestronglyMeasurable.mul hw) ?_
  filter_upwards [hC] with x hx
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul (hM x) hx (abs_nonneg _) ((norm_nonneg _).trans (hM x))

/-- A test supported in a set has the same integral against the restricted measure. -/
theorem integral_restrict_eq_of_tsupport_subset {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] {μ : Measure X} {s : Set X} {f : X → ℝ}
    (hs : tsupport f ⊆ s) :
    (∫ x, f x ∂(μ.restrict s)) = ∫ x, f x ∂μ :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun _ hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hs h)

/-- Finiteness on compact subsets of a domain passes to the restricted measure
on any smaller domain. -/
theorem finiteOnCompacts_restrict {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} {U V : Set X} (hμ : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤)
    (hVU : V ⊆ U) (K : Set X) (hK : IsCompact K) (hKV : K ⊆ V) :
    μ.restrict V K < ⊤ :=
  (Measure.restrict_le_self K).trans_lt (hμ K hK (hKV.trans hVU))

end SGPT.Foundations.Analysis.MeasureLocality
