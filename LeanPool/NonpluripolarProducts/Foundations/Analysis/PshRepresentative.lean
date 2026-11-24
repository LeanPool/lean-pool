/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PlurisubharmonicAE
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.GermPshLeviPositivity

/-!
# Genuine PSH representatives of distributions

The representative is an actual extended-real PSH function, finite almost
everywhere on its domain. Local integrability and equality with the specified
distribution are part of what it means to represent that distribution, not
assumptions about every distribution. Existence is a separate theorem.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
variable (μ : Measure E) {Ω : Opens E}

/-- A genuine PSH representative of a distribution on its open domain.
Almost-everywhere finiteness prevents confusing the `toReal` of `⊥` with zero. -/
def IsPshRepresentative (T : 𝓓'(Ω, ℝ)) (u : E → EReal) : Prop :=
  PlurisubharmonicOn u Ω ∧
  (∀ᵐ x ∂μ.restrict Ω, u x ≠ ⊤ ∧ u x ≠ ⊥) ∧
  ∃ hu : LocallyIntegrableOn (fun x => (u x).toReal) Ω μ,
    T = regularDistribution μ (fun x => (u x).toReal) hu

variable {μ} [μ.IsAddHaarMeasure] {T : 𝓓'(Ω, ℝ)} {u v : E → EReal}

/-- Genuine PSH representatives are unique on the open domain, without a
connectedness assumption. No uniqueness outside that domain is asserted. -/
theorem IsPshRepresentative.unique (hu : IsPshRepresentative μ T u)
    (hv : IsPshRepresentative μ T v) : EqOn u v Ω := by
  obtain ⟨huP, huF, huL, huT⟩ := hu
  obtain ⟨hvP, hvF, hvL, hvT⟩ := hv
  exact huP.eqOn_of_regularDistribution_eq hvP μ huL hvL
    (huF.mono (fun _ hx => EReal.coe_toReal hx.1 hx.2))
    (hvF.mono (fun _ hx => EReal.coe_toReal hx.1 hx.2))
    (huT.symm.trans hvT)

/-- Every genuinely represented PSH distribution has nonnegative Levi
derivatives. The converse must construct a representative rather than assume it. -/
theorem IsPshRepresentative.hasNonnegativeDistributionalLevi
    (hu : IsPshRepresentative μ T u) : HasNonnegativeDistributionalLevi T := by
  obtain ⟨huP, huF, huL, rfl⟩ := hu
  exact huP.hasNonnegativeDistributionalLevi_of_locallyIntegrable huL huF

end SGPT.Foundations.Analysis
