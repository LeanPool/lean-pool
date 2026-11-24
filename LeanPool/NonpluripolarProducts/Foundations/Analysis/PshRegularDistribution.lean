/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.RegularDistribution
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PlurisubharmonicIntegrability
public import Mathlib.Topology.Bases

/-!
# Almost-everywhere representatives and PSH regular distributions

Local almost-everywhere statements are assembled using a countable open
subcover. No uncountable union of null exceptional sets is used.
For a nontrivial PSH potential on a preconnected domain, the proven local
integrability constructs its actual regular distribution. Positivity of its
distributional Levi operator is treated separately in `GermPshLeviPositivity`.
-/

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions

namespace SGPT.Foundations.Analysis

/-- A property holding almost everywhere on an open neighborhood of each
point holds almost everywhere on the whole set in a second-countable space.
Neither the set nor the predicate is required to be measurable. -/
theorem ae_restrict_of_open_neighborhood_ae {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] {μ : Measure X} {U : Set X}
    {P : X → Prop}
    (h : ∀ x ∈ U, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∀ᵐ y ∂μ.restrict V, P y) :
    ∀ᵐ x ∂μ.restrict U, P x := by
  classical
  choose V hVo hxV hVa using fun x : U => h x x.property
  obtain ⟨T, hT, hEq⟩ := TopologicalSpace.isOpen_iUnion_countable V hVo
  have hcover : U ⊆ ⋃ i ∈ T, V i := by
    rw [hEq]
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  exact ae_restrict_of_ae_restrict_of_subset hcover
    ((ae_restrict_biUnion_iff (μ := μ) V hT P).2 (fun i _ => hVa i))

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]

/-- Countably many good neighborhoods suffice to retain global a.e. finiteness. -/
theorem ae_finite_of_subset_pshIntegrabilityLocus [SecondCountableTopology E]
    {u : E → EReal} {μ : Measure E} {U : Set E}
    (hU : U ⊆ pshIntegrabilityLocus u μ) :
    ∀ᵐ x ∂μ.restrict U, u x ≠ ⊤ ∧ u x ≠ ⊥ := by
  apply ae_restrict_of_open_neighborhood_ae
  intro x hx
  obtain ⟨V, hV, hxV, hfin, _⟩ := hU hx
  exact ⟨V, hV, hxV, hfin⟩

section RegularLocality

variable [NormedSpace ℝ E] [OpensMeasurableSpace E] {Ω : Opens E}

/-- Equality of densities only on the test-function domain suffices. -/
theorem regularDistribution_congr_ae_on {μ : Measure E} {u w : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) (hw : LocallyIntegrableOn w Ω μ)
    (heq : u =ᵐ[μ.restrict Ω] w) :
    regularDistribution μ u hu = regularDistribution μ w hw := by
  ext φ
  rw [regularDistribution_apply, regularDistribution_apply]
  apply integral_congr_ae
  have heq' : ∀ᵐ x ∂μ, x ∈ Ω → u x = w x :=
    (ae_restrict_iff' Ω.isOpen.measurableSet).mp heq
  filter_upwards [heq'] with x hx
  by_cases hxΩ : x ∈ Ω
  · rw [hx hxΩ]
  · have hφx : φ x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hxΩ (φ.tsupport_subset h))
    simp [hφx]

end RegularLocality

section PSH

variable [BorelSpace E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
variable {u : E → EReal} {U : Set E}

/-- Nontrivial PSH germs on a preconnected set are finite a.e. on that set. -/
theorem PlurisubharmonicOn.ae_finite
    (hu : PlurisubharmonicOn u U) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hU : IsPreconnected U) (hne : ∃ a ∈ U, u a ≠ ⊥) :
    ∀ᵐ x ∂μ.restrict U, u x ≠ ⊤ ∧ u x ≠ ⊥ :=
  ae_finite_of_subset_pshIntegrabilityLocus (hu.subset_pshIntegrabilityLocus μ hU hne)

/-- The real density retains the actual PSH potential almost everywhere. -/
theorem PlurisubharmonicOn.ae_coe_toReal
    (hu : PlurisubharmonicOn u U) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hU : IsPreconnected U) (hne : ∃ a ∈ U, u a ≠ ⊥) :
    (fun x => ((u x).toReal : EReal)) =ᵐ[μ.restrict U] u :=
  (hu.ae_finite μ hU hne).mono (fun _ hx => EReal.coe_toReal hx.1 hx.2)

/-- The actual distribution induced by a nontrivial PSH potential. Local
integrability is proved from the PSH hypotheses, rather than assumed. -/
noncomputable def pshRegularDistribution {Ω : Opens E}
    (hu : PlurisubharmonicOn u Ω) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hΩ : IsPreconnected (Ω : Set E)) (hne : ∃ a ∈ Ω, u a ≠ ⊥) : 𝓓'(Ω, ℝ) :=
  regularDistribution μ (fun x => (u x).toReal) (hu.locallyIntegrableOn_toReal μ hΩ hne)

theorem pshRegularDistribution_apply {Ω : Opens E}
    (hu : PlurisubharmonicOn u Ω) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hΩ : IsPreconnected (Ω : Set E)) (hne : ∃ a ∈ Ω, u a ≠ ⊥) (φ : 𝓓(Ω, ℝ)) :
    pshRegularDistribution hu μ hΩ hne φ = ∫ x, φ x * (u x).toReal ∂μ :=
  regularDistribution_apply μ _ (hu.locallyIntegrableOn_toReal μ hΩ hne) φ

/-- Potentials equal a.e. on the open domain induce the same distribution. -/
theorem pshRegularDistribution_congr_ae_on {Ω : Opens E} {w : E → EReal}
    (hu : PlurisubharmonicOn u Ω) (hw : PlurisubharmonicOn w Ω)
    (μ : Measure E) [μ.IsAddHaarMeasure] (hΩ : IsPreconnected (Ω : Set E))
    (hnu : ∃ a ∈ Ω, u a ≠ ⊥) (hnw : ∃ a ∈ Ω, w a ≠ ⊥)
    (heq : u =ᵐ[μ.restrict Ω] w) :
    pshRegularDistribution hu μ hΩ hnu = pshRegularDistribution hw μ hΩ hnw := by
  apply regularDistribution_congr_ae_on
  exact heq.mono (fun _ hx => congrArg EReal.toReal hx)

end PSH

end SGPT.Foundations.Analysis
