/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.MongeAmpere
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GlobalPotentials
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.LocalPotentialIndependence
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.SmoothPshHessian
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.SmoothMeasureTests
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.HolomorphicPullback
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PositiveDistributionMeasure
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorExistence

/-!
# Pending local Monge–Ampère foundation

These first-pass obligations use the actual Hessian density and genuine PSH
approximations. They neither postulate a non-pluripolar product as input nor
construct the unbounded truncation product. All spaces, scalar structures,
Borel structures and volume normalizations are fixed by `ComplexModel n`.
No arbitrary Haar measure, unmentioned manifold structure, or global local
finiteness of a zero extension is implicit in these statements.

Sources: revised manuscript §2, Demailly CADG III.3 (especially construction
and positivity 3.2, compact mass estimate 3.3, decreasing continuity 3.7).
Demailly's operator is twice ours: pure degree-n measures are scaled by 2⁻ⁿ.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.MongeAmpere

open FirstPass FirstPass.MongeAmpere

variable {n : ℕ}

/-- Link the coordinate Hessian to the existing actual exterior derivative.
C² at the evaluation point suffices; `J` is multiplication by `i`. -/
theorem smoothDDC_apply_eq_realHessian {u : ComplexModel n → ℝ}
    {z : ComplexModel n} (hu : ContDiffAt ℝ 2 u z) (v w : ComplexModel n) :
    smoothDDC u z ![v, w] =
      (realHessian u z w (Complex.I • v) -
        realHessian u z v (Complex.I • w)) / (4 * Real.pi) := by
  exact FirstPass.smoothDDC_apply_eq_realHessian hu v w

/-- The redundant coordinate positivity certificate can be recovered from
genuine smooth PSH, rather than supplied by downstream callers. -/
theorem isSmoothPshOn_of_psh {U : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hs : ContDiffOn ℝ ∞ u U)
    (hp : PlurisubharmonicOn (fun z => (u z : EReal)) U) :
    IsSmoothPshOn U u := by
  exact FirstPass.MongeAmpere.isSmoothPshOn_of_psh hs hp

/-- Finiteness is only asserted on compact sets inside the domain. -/
theorem smoothMeasure_finiteOnCompacts {U : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsSmoothPshOn U u)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKU : K ⊆ U) :
    smoothMeasure U u hu K < ⊤ := by
  exact FirstPass.MongeAmpere.smoothMeasure_finiteOnCompacts hu hK hKU

/-- Compact continuous tests integrate against the actual nonnegative density.
This also rules out using the nonintegrable Bochner-integral fallback. -/
theorem smoothMeasure_test_integral {U : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsSmoothPshOn U u)
    (φ : ComplexModel n → ℝ) (hφ : Continuous φ) (hK : HasCompactSupport φ)
    (hU : tsupport φ ⊆ U) :
    Integrable φ (smoothMeasure U u hu) ∧
      Integrable (fun z => φ z * smoothDensity u z)
        (volume.restrict (U : Set (ComplexModel n))) ∧
      (∫ z, φ z ∂(smoothMeasure U u hu)) =
        ∫ z in U, φ z * smoothDensity u z := by
  exact FirstPass.MongeAmpere.smoothMeasure_test_integral hu φ hφ hK hU

/-- Pointwise decreasing regularization on a relatively compact subdomain.
There is no assumption of global PSH extension or smooth boundary. -/
theorem exists_decreasingApproximation {Ω U : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u)
    (hU : RelativelyCompactIn U Ω) :
    ∃ f, IsDecreasingApproximation U u f := by
  exact HolomorphicPullback.exists_decreasingMollifierApproximation hu hU

/-- Existence includes convergence for every admissible sequence, not merely
for one selected approximation. The measure is extended by zero outside Ω. -/
theorem exists_localBedfordTaylorMeasure {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u) :
    ∃ μ : Measure (ComplexModel n), IsLocalBedfordTaylorMeasure Ω u μ :=
  BedfordTaylor.exists_isLocalBedfordTaylorMeasure hu

open scoped Distributions in
/-- Agreeing against tests supported in relatively compact subdomains determines a measure
carried by the open domain and finite on its compact subsets. -/
theorem eq_of_testFunction_integral_eq_on_relativelyCompact {Ω : Opens (ComplexModel n)}
    {μ ν : Measure (ComplexModel n)}
    (hμc : μ (Ω : Set (ComplexModel n))ᶜ = 0) (hνc : ν (Ω : Set (ComplexModel n))ᶜ = 0)
    (hμf : ∀ K, IsCompact K → K ⊆ Ω → μ K < ⊤)
    (hνf : ∀ K, IsCompact K → K ⊆ Ω → ν K < ⊤)
    (heq : ∀ U, RelativelyCompactIn U Ω → ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ U →
      (∫ z, φ z ∂μ) = ∫ z, φ z ∂ν) : μ = ν := by
  have hint : ∀ φ : 𝓓(Ω, ℝ), (∫ z, φ z ∂μ) = ∫ z, φ z ∂ν := by
    intro φ
    obtain ⟨δ, hδ, hδΩ⟩ :=
      φ.hasCompactSupport.exists_cthickening_subset_open Ω.isOpen φ.tsupport_subset
    let U : Opens (ComplexModel n) :=
      ⟨Metric.thickening δ (tsupport φ), Metric.isOpen_thickening⟩
    have hclosure :
        closure (U : Set (ComplexModel n)) ⊆ Metric.cthickening δ (tsupport φ) :=
      Metric.closure_thickening_subset_cthickening δ (tsupport φ)
    have hU : RelativelyCompactIn U Ω :=
      ⟨(φ.hasCompactSupport.cthickening).of_isClosed_subset isClosed_closure hclosure,
        hclosure.trans hδΩ⟩
    have hφU : tsupport φ ⊆ (U : Set (ComplexModel n)) :=
      Metric.self_subset_thickening hδ (tsupport φ)
    exact heq U hU φ hφU
  have hμrestrict : μ.restrict (Ω : Set (ComplexModel n)) = μ :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hμc)
  have hνrestrict : ν.restrict (Ω : Set (ComplexModel n)) = ν :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hνc)
  exact hμrestrict.symm.trans
    ((BedfordTaylor.restrict_eq_of_testFunction_integral_eq hμf hνf hint).trans
      hνrestrict)

open scoped Distributions in
/-- Uniqueness must use measure separation inside Ω (or on smaller subdomains),
not an unjustified ambient Radon hypothesis for the zero extensions. -/
theorem localBedfordTaylorMeasure_unique {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} {μ ν : Measure (ComplexModel n)}
    (hμ : IsLocalBedfordTaylorMeasure Ω u μ)
    (hν : IsLocalBedfordTaylorMeasure Ω u ν) : μ = ν := by
  apply eq_of_testFunction_integral_eq_on_relativelyCompact hμ.2.1 hν.2.1 hμ.2.2.1 hν.2.2.1
  intro U hU φ hφU
  obtain ⟨f, hf⟩ := (hμ.2.2.2 U hU).1
  exact tendsto_nhds_unique ((hμ.2.2.2 U hU).2 f hf φ φ.continuous φ.hasCompactSupport hφU)
    ((hν.2.2.2 U hU).2 f hf φ φ.continuous φ.hasCompactSupport hφU)

/-- Actual sequence independence follows from the existence theorem;
the only input about the limit potential is that it is locally bounded PSH. -/
theorem decreasingApproximation_sequence_independent {Ω U : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u)
    (hU : RelativelyCompactIn U Ω) {f g : ℕ → ComplexModel n → ℝ}
    (hf : IsDecreasingApproximation U u f) (hg : IsDecreasingApproximation U u g) :
    ∃ μ : Measure (ComplexModel n), IsLocalBedfordTaylorMeasure Ω u μ ∧
      WeaklyTendsTo U f hf.1 μ ∧ WeaklyTendsTo U g hg.1 μ := by
  obtain ⟨μ, hμ⟩ := exists_localBedfordTaylorMeasure hu
  exact ⟨μ, hμ, hμ.sequence_independent hU hf hg⟩

/-- Ordinary-open locality, before the stronger plurifine locality needed for
the non-pluripolar truncation construction. -/
theorem localBedfordTaylorMeasure_restrict {Ω U : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} {μ : Measure (ComplexModel n)}
    (hμ : IsLocalBedfordTaylorMeasure Ω u μ) (hU : U ≤ Ω) :
    IsLocalBedfordTaylorMeasure U u (μ.restrict (U : Set (ComplexModel n))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨hμ.1.1.mono hU, ?_⟩
    intro z hz
    obtain ⟨V, hzV, hVΩ, C, hC⟩ := hμ.1.2 z (hU hz)
    exact ⟨V ⊓ U, ⟨hzV, hz⟩, inf_le_right,
      C, fun w hw ↦ hC w hw.1⟩
  · rw [Measure.restrict_apply U.isOpen.measurableSet.compl]
    simp
  · intro K hK hKU
    exact lt_of_le_of_lt (Measure.restrict_le_self K)
      (hμ.2.2.1 K hK (hKU.trans hU))
  · intro V hV
    have hVΩ : RelativelyCompactIn V Ω := ⟨hV.1, hV.2.trans hU⟩
    obtain ⟨⟨f, hf⟩, hconv⟩ := hμ.2.2.2 V hVΩ
    refine ⟨⟨f, hf⟩, fun g hg φ hφ hφc hφV ↦ ?_⟩
    have hφU : tsupport φ ⊆ (U : Set (ComplexModel n)) :=
      hφV.trans (subset_closure.trans hV.2)
    have hindicator : (U : Set (ComplexModel n)).indicator φ = φ := by
      funext z
      by_cases hz : z ∈ U
      · simp [hz]
      · have hzt : z ∉ tsupport φ := fun h ↦ hz (hφU h)
        simp [hz, image_eq_zero_of_notMem_tsupport hzt]
    have hintegral :
        (∫ z, φ z ∂(μ.restrict (U : Set (ComplexModel n)))) = ∫ z, φ z ∂μ := by
      rw [← integral_indicator U.isOpen.measurableSet, hindicator]
    simpa only [hintegral] using hconv g hg φ hφ hφc hφV

end SGPT.Foundations.Analysis.Pending.MongeAmpere
