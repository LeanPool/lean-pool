/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.DistributionRestriction
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PshRepresentative

/-!
# Distribution restriction and decreasing smooth PSH approximation data

These definitions describe actual continuous test functionals and actual smooth
functions. They assert no existence of a regularization or PSH representative.
The first-pass existence and limit arguments live in the separate Pending layer.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions Topology ContDiff

namespace SGPT.Foundations.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω U : Opens E}

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] in
/-- Restricting a regular distribution gives the regular distribution of the
same density on the smaller open set. -/
theorem restrictDistribution_regularDistribution (μ : Measure E)
    {u : E → ℝ} (hu : LocallyIntegrableOn u Ω μ) (hUΩ : U ≤ Ω) :
    restrictDistribution (regularDistribution μ u hu) hUΩ =
      regularDistribution μ u (hu.mono_set hUΩ) := by
  ext φ
  rw [restrictDistribution_apply, regularDistribution_apply,
    regularDistribution_apply]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change (TestFunction.monoCLM ℝ φ : 𝓓(Ω, ℝ)) x * u x = φ x * u x
    rw [congrFun (testFunction_inclusion_coe hUΩ φ) x]

omit [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] in
/-- A genuine PSH representative remains a representative after restricting
both its distribution and its open domain. -/
theorem IsPshRepresentative.restrict (μ : Measure E) {T : 𝓓'(Ω, ℝ)}
    {u : E → EReal} (hu : IsPshRepresentative μ T u) (hUΩ : U ≤ Ω) :
    IsPshRepresentative μ (restrictDistribution T hUΩ) u := by
  obtain ⟨huPsh, huFinite, huLocal, huT⟩ := hu
  have huLocalU := huLocal.mono_set hUΩ
  refine ⟨huPsh.mono hUΩ,
    ae_restrict_of_ae_restrict_of_subset hUΩ huFinite, huLocalU, ?_⟩
  calc
    restrictDistribution T hUΩ =
        restrictDistribution (regularDistribution μ (fun x => (u x).toReal) huLocal) hUΩ :=
      congrArg (fun S : 𝓓'(Ω, ℝ) => restrictDistribution S hUΩ) huT
    _ = regularDistribution μ (fun x => (u x).toReal) huLocalU :=
      restrictDistribution_regularDistribution μ huLocal hUΩ

/-- A decreasing smooth PSH approximation to an actual distribution, with weak
convergence tested against every smooth compactly supported test function.
Smoothness is global, whereas PSH and monotonicity are asserted only on Ω. -/
def IsDecreasingSmoothPshApproximation (μ : Measure E) (T : 𝓓'(Ω, ℝ))
    (f : ℕ → E → ℝ) : Prop :=
  (∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n)) ∧
  (∀ n, DiscPshOn (fun x => (f n x : EReal)) Ω) ∧
  (∀ x ∈ Ω, Antitone (fun n => f n x)) ∧
  ∀ φ : 𝓓(Ω, ℝ),
    Tendsto (fun n => ∫ x, φ x * f n x ∂μ) atTop (𝓝 (T φ))

end SGPT.Foundations.Analysis
