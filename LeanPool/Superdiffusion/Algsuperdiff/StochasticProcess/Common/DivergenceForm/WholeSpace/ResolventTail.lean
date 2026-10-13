/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Process.Kernel.ResolventTailVariable
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.Conservativity
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.PositiveC0Resolvent
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Semigroup.ResolventDenseRange

/-!
# ResolventTail

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Resolvent tails for the whole-space analytic exhaustion

The process construction below consumes the library predicate
`Algsuperdiff.Process.SubMarkovKernelSemigroup.HasResolventTail` through an
explicit profile
package.  This keeps the probabilistic theorem independent of the analytic
route used to prove the tail.

The intended coefficient class is `a = nu I + k`, with `nu > 0` and `k`
continuous, skew, and of arbitrary size.  The small-contrast construction is
the first named input.  The stream-field construction instead uses its
split-skew localized bounds and a subexponential profile with finite cubic
layer-cake budget, without changing any process declaration.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory Set
open MarkovProcess MarkovProcess.Semigroup
open scoped ENNReal ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d]

/-- A shift-dependent exhaustion-metric resolvent-tail input.  The profile and the trivial cutting
radius may depend on the shift; only the cubic layer-cake budget and the growth of the cutting
radius are uniform. -/
structure WholeSpaceVariableExhaustionResolventTailInput
    (R : PositiveC0ContractiveResolvent (Vec d)) where
  rho : Vec d → ℝ
  continuous_rho : Continuous rho
  rho_pos : ∀ x, 0 < rho x
  lipschitz_rho : LipschitzWith 1 rho
  isCompact_superlevel : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x}
  rho_le_one : ∀ x, rho x ≤ 1
  phi : ℝ → ℝ → ℝ
  phi_nonneg : ∀ lam s, 0 ≤ phi lam s
  hasTail : ∀ mu : PositiveShift, 1 ≤ (mu : ℝ) →
    letI := OnePoint.exhaustionMetricSpace rho continuous_rho rho_pos lipschitz_rho
      isCompact_superlevel
    Algsuperdiff.Process.SubMarkovKernelSemigroup.HasResolventTail R.onePointKernelSemigroup (mu : ℝ)
      (phi (mu : ℝ))
  cutoff : ℝ → ℝ
  cutoff_nonneg : ∀ lam, 0 ≤ cutoff lam
  budget : ℝ
  budget_nonneg : 0 ≤ budget
  integral_le : ∀ mu : PositiveShift, 1 ≤ (mu : ℝ) →
    ∫⁻ s in Set.Ioi (cutoff (mu : ℝ)),
      ENNReal.ofReal (phi (mu : ℝ) s * s ^ 3) ≤ ENNReal.ofReal budget
  timeExponent : ℝ
  one_lt_timeExponent : 1 < timeExponent
  timeExponent_le_two : timeExponent ≤ 2
  cutoffGrowth : ℝ
  cutoffGrowth_nonneg : 0 ≤ cutoffGrowth
  cutoff_pow_le : ∀ mu : PositiveShift, 1 ≤ (mu : ℝ) →
    cutoff (mu : ℝ) ^ 4 ≤ cutoffGrowth * (mu : ℝ) ^ (2 - timeExponent)

namespace WholeSpaceVariableExhaustionResolventTailInput

variable {R : PositiveC0ContractiveResolvent (Vec d)}

/-- The shift-dependent exhaustion-tail package gives the one-point regularity
data used by the canonical process construction. -/
def toOnePointRegular (H : WholeSpaceVariableExhaustionResolventTailInput R) :
    R.OnePointRegular :=
  Algsuperdiff.Process.PositiveC0ContractiveResolvent.OnePointRegular.of_variableResolventTail R H.rho
    H.continuous_rho H.rho_pos H.lipschitz_rho H.isCompact_superlevel H.rho_le_one
    H.phi_nonneg H.hasTail H.cutoff_nonneg H.budget_nonneg H.integral_le
    H.one_lt_timeExponent H.timeExponent_le_two H.cutoffGrowth_nonneg H.cutoff_pow_le

end WholeSpaceVariableExhaustionResolventTailInput

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-- Identification of a process kernel resolvent with the analytic cubic
supremum on nonnegative observables bounded by one.  The minimal-resolvent
construction supplies this after identifying each transported cube
resolvent. -/
def KernelResolventIdentifiesAnalyticMinimal
    (R : PositiveC0ContractiveResolvent (Vec d)) : Prop :=
  ∀ (mu : PositiveShift) {f : Vec d → ℝ} (hf : Measurable f),
    (∀ x, 0 ≤ f x) → (hf1 : ∀ x, |f x| ≤ 1) → ∀ x,
      R.kernelSemigroup.kernelResolvent (mu : ℝ)
          (fun y ↦ ENNReal.ofReal (f y)) x =
        A.analyticMinimalResolvent mu f hf hf1 x

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
