/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Generated.Generator
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.WeightedGradient.Closure
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The heat semigroup of a log-concave law

This module specialises the abstract semigroup construction of `Analysis/Semigroup/` to the
repository's energy operator. For a full-dimensional compact-set
log-concave probability `ν` on a finite-dimensional Euclidean space `V`, a Haar measure `m` and a
weight `B : V →L[ℝ] V`, the closable weighted gradient
`T = hν.weightedOperator m B hi : L²(ν) →ₗ.[ℝ] L²(ν; V)`
(`KLS/LogConcave/WeightedGradient/Basic.lean`,
`g ↦ B ∘ ∇g` on Lipschitz tests) has a closure `Tbar`, closed and densely defined. Feeding `Tbar` to
`FunctionalInequalities.Analysis.Semigroup.Generated.operator` gives

`P_t = HeatSemigroup.operator hν m B hi ht : L²(ν) →L[ℝ] L²(ν)`, formally `exp (-t Tbar†Tbar)`,

and every abstract law transfers by one `exact`: contraction, symmetry, `P_0 = 1`,
`P_{t+u} = P_t P_u`, strong continuity on `[0, ∞)`, and the generator identity
`(P_t f - f)/t → -Tbar†Tbar f` on `D(Tbar†Tbar)`. The bridge to the energy is `inner_adjointComp_self_eq`:
`⟪Tbar†Tbar f, f⟫ = ‖Tbar f‖²`, which by `weighted_relaxation_of_mem` is the sequential relaxation of
`‖B ∇g‖²`, the repository's closed energy. The intrinsic version for an arbitrary log-concave law
on any finite-dimensional Euclidean space is `HeatSemigroup.intrinsic`.

## What this is not

This module constructs the symmetric contraction semigroup from the concrete closed energy operator.
It does not establish the Markov property (positivity, `P_t 1 = 1` or `L^∞` contraction),
Bakry–Émery `Γ`-calculus, a small-time heat estimate or Buser's inequality with constant `π`.
Nothing here uses log-concavity beyond the three
hypothesis lemmas that make the weighted gradient closable and densely defined.
-/

@[expose] public section

noncomputable section

open MeasureTheory FunctionalInequalities.Analysis.Semigroup

open scoped RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave

open Energy

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

section FullDimensional

variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)

namespace HeatSemigroup

/--
**The heat semigroup of `ν`**: `P_t = exp (-t Tbar†Tbar)` on `L²(ν)`, for `t ≥ 0`, obtained from the
abstract construction `FunctionalInequalities.Analysis.Semigroup.Generated.operator` applied to the
closed weighted gradient. -/
def operator (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {t : ℝ}
    (ht : 0 ≤ t) : Lp ℝ 2 (ν : Measure V) →L[ℝ] Lp ℝ 2 (ν : Measure V) :=
  FunctionalInequalities.Analysis.Semigroup.Generated.operator
    (hν.closedWeightedOperator m B hi) (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) ht

end HeatSemigroup

variable (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)

namespace HeatSemigroup

/--
`P_t f` is the abstract `FunctionalInequalities.Analysis.Semigroup.Generated.apply` of the closed
weighted gradient. -/
theorem apply {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 (ν : Measure V)) :
    HeatSemigroup.operator m B hν hi ht f =
      FunctionalInequalities.Analysis.Semigroup.Generated.apply
        (hν.closedWeightedOperator m B hi) (hν.closedWeightedOperator_isClosed m B hi)
        (hν.dense_domain_closedWeightedOperator m B hi) t f :=
  rfl

/-- `P_t` is a contraction of `L²(ν)`. -/
theorem norm_apply_le {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 (ν : Measure V)) :
    ‖HeatSemigroup.operator m B hν hi ht f‖ ≤ ‖f‖ :=
  FunctionalInequalities.Analysis.Semigroup.Generated.norm_apply_le
    (hν.closedWeightedOperator m B hi) (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) ht f

/-- `P_t` is symmetric on `L²(ν)`. -/
theorem symmetric {t : ℝ} (ht : 0 ≤ t) (f g : Lp ℝ 2 (ν : Measure V)) :
    ⟪HeatSemigroup.operator m B hν hi ht f, g⟫ = ⟪f, HeatSemigroup.operator m B hν hi ht g⟫ :=
  FunctionalInequalities.Analysis.Semigroup.Generated.symmetric
    (hν.closedWeightedOperator m B hi) (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) ht f g

/-- `P_0 = 1`. -/
theorem zero (f : Lp ℝ 2 (ν : Measure V)) : HeatSemigroup.operator m B hν hi le_rfl f = f :=
  FunctionalInequalities.Analysis.Semigroup.Generated.zero_time
    (hν.closedWeightedOperator m B hi) (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) f

/-- The semigroup law `P_{t+u} = P_t P_u`. -/
theorem add {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) (f : Lp ℝ 2 (ν : Measure V)) :
    HeatSemigroup.operator m B hν hi (add_nonneg ht hu) f =
      HeatSemigroup.operator m B hν hi ht (HeatSemigroup.operator m B hν hi hu f) :=
  FunctionalInequalities.Analysis.Semigroup.Generated.add_time
    (hν.closedWeightedOperator m B hi) (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) ht hu f

/-- Strong continuity: `t ↦ P_t f` is continuous on `[0, ∞)`, expressed through the underlying
`FunctionalInequalities.Analysis.Semigroup.Generated.apply` (which is defined for every real `t`).
-/
theorem continuousOn (f : Lp ℝ 2 (ν : Measure V)) :
    ContinuousOn
      (fun t : ℝ =>
        FunctionalInequalities.Analysis.Semigroup.Generated.apply
          (hν.closedWeightedOperator m B hi) (hν.closedWeightedOperator_isClosed m B hi)
          (hν.dense_domain_closedWeightedOperator m B hi) t f)
      (Set.Ici 0) :=
  FunctionalInequalities.Analysis.Semigroup.Generated.continuousOn
    (hν.closedWeightedOperator m B hi) (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) f

/-- The generator is `-Tbar†Tbar`: on `D(Tbar†Tbar)`, `(P_t f - f)/t → -Tbar†Tbar f` as `t ↓ 0`. -/
theorem generator_limit (f : (adjointComp (hν.closedWeightedOperator m B hi)).domain)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, ∀ ht : 0 < t, t < δ →
      ‖t⁻¹ • (HeatSemigroup.operator m B hν hi ht.le f - f) +
        adjointComp (hν.closedWeightedOperator m B hi) f‖ < ε := by
  obtain ⟨δ, hδ, h⟩ := FunctionalInequalities.Analysis.Semigroup.Generated.generator_limit
    (hν.closedWeightedOperator m B hi) (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) f hε
  exact ⟨δ, hδ, fun t ht htδ => h t ht htδ⟩

end HeatSemigroup

/-- **The Dirichlet form of the heat semigroup is the closed energy**: for `f ∈ D(Tbar†Tbar)`,
`⟪Tbar†Tbar f, f⟫ = ‖Tbar f‖²`, and by `weighted_relaxation_of_mem` the right-hand side is the sequential
relaxation of `‖B ∇g‖²` at `f`. -/
theorem inner_adjointComp_self_eq (f : (adjointComp (hν.closedWeightedOperator m B hi)).domain) :
    ⟪adjointComp (hν.closedWeightedOperator m B hi) f, (f : Lp ℝ 2 (ν : Measure V))⟫ =
      ‖hν.closedWeightedOperator m B hi ⟨f, f.2.2⟩‖ ^ 2 := by
  rw [inner_adjointComp (hν.dense_domain_closedWeightedOperator m B hi) f f.2.2,
    real_inner_self_eq_norm_sq]

end FullDimensional

section Intrinsic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  {μ : ProbabilityMeasure E} (m : Measure (Probability.affineSupport μ).direction)
  [m.IsAddHaarMeasure] (B : (Probability.affineSupport μ).direction →L[ℝ]
    (Probability.affineSupport μ).direction)

namespace HeatSemigroup

omit [CompleteSpace E] in
/-- The heat semigroup of the intrinsic law of an arbitrary log-concave law, on
`L²(intrinsicMeasure μ)`. Every theorem of the full-dimensional section applies to it verbatim,
since it is `HeatSemigroup.operator` of `hμ.intrinsicMeasure`. -/
def intrinsic (hμ : LogConcave μ) {t : ℝ} (ht : 0 ≤ t) :
    Lp ℝ 2 (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) →L[ℝ]
      Lp ℝ 2 (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) :=
  HeatSemigroup.operator m B hμ.intrinsicMeasure hμ.interior_intrinsic_support_nonempty ht

end HeatSemigroup

end Intrinsic

end FunctionalInequalities.KLS.LogConcave
