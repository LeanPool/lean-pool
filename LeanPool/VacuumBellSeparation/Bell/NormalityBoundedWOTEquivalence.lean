/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.NormalGNSBoundedWOT
public import LeanPool.VacuumBellSeparation.Bell.NormalPositiveConeClosure

/-!
Positive order-normality is equivalent to continuity on every actual bounded
WOT ball. The converse uses the original positive directed set as its own
index set, its actual strong supremum, and the ball of radius norm X.
No predual or ultraweak topology is defined by this equivalence.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open Filter
open scoped Topology ComplexOrder InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every positive directed supremum lies in one original bounded WOT ball.
Continuity there gives the exact real least-upper-bound normality predicate. -/
theorem isNormalFunctional_of_continuous_boundedWOT
    (M : VonNeumannAlgebra H) (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hc : ∀ R : ℝ, 0 ≤ R →
      Continuous (fun T : vnaWOTBall M R => φ (vnaWOTBallElement T))) :
    IsNormalFunctional M φ := by
  intro s hs hd hp X hX
  let : Nonempty s := hs.to_subtype
  let : IsDirectedOrder s := hd.isDirectedOrder
  let T : s → vnaWOTBall M ‖X‖ := fun i =>
    ⟨ContinuousLinearMapWOT.ofCLM (i.1 : H →L[ℂ] H), i.1.2,
      CStarAlgebra.norm_le_norm_of_le_of_nonneg (hX.1 i.2) (hp i.1 i.2)⟩
  let L : vnaWOTBall M ‖X‖ :=
    ⟨ContinuousLinearMapWOT.ofCLM (X : H →L[ℂ] H), X.2, le_rfl⟩
  have ht : Tendsto T atTop (𝓝 L) := by
    apply tendsto_subtype_rng.mpr
    apply ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr
    intro x y
    exact tendsto_const_nhds.inner (strong_tendsto_of_isLUB_positive M hs hd hp hX x)
  have he : Tendsto (fun i : s => (φ i.1).re) atTop (𝓝 (φ X).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp
      ((hc ‖X‖ (norm_nonneg X)).continuousAt.tendsto.comp ht)
  constructor
  · rintro _ ⟨Y, hY, rfl⟩
    exact (Complex.le_def.mp (φ.monotone' (hX.1 hY))).1
  · intro r hr
    apply le_of_tendsto he
    exact Filter.Eventually.of_forall fun i : s => hr ⟨i.1, i.2, rfl⟩

theorem isNormalFunctional_iff_continuous_boundedWOT
    (M : VonNeumannAlgebra H) (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) :
    IsNormalFunctional M φ ↔ ∀ R : ℝ, 0 ≤ R →
      Continuous (fun T : vnaWOTBall M R => φ (vnaWOTBallElement T)) :=
  ⟨fun hn R _ => continuous_vnaWOTBall_eval_of_positive_normal M R φ hn,
    isNormalFunctional_of_continuous_boundedWOT M φ⟩

/-- A norm limit of finite original-H coefficients is order-normal whenever
the limiting functional is positive. No positivity of the approximants is needed. -/
theorem isNormalFunctional_of_mem_closure_coefficients
    (M : VonNeumannAlgebra H) (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hc : (PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap ∈
      closure {f : StrongDual ℂ M.toStarSubalgebra | IsFiniteVectorCoefficient M f}) :
    IsNormalFunctional M φ := by
  apply isNormalFunctional_of_continuous_boundedWOT M φ
  intro R _
  exact continuous_vnaWOTBall_eval_of_mem_closure_coefficients M R
    (PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap hc

/-- The positive cone of the concrete coefficient norm closure is precisely
the original positive order-normal cone. This makes no global WOT assertion. -/
theorem isNormalFunctional_iff_mem_closure_coefficients
    (M : VonNeumannAlgebra H) (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) :
    IsNormalFunctional M φ ↔
      (PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap ∈
        closure {f : StrongDual ℂ M.toStarSubalgebra | IsFiniteVectorCoefficient M f} := by
  constructor
  · intro hn
    apply closure_mono ?_ (normalFunctional_mem_closure_finite_vector_sums M φ hn)
    rintro f ⟨n, ξ, rfl⟩
    refine ⟨n, ξ, ξ, fun _ => 1, ?_⟩
    intro a
    change finiteVectorFunctional M ξ a = ∑ i, (1 : ℂ) * ⟪ξ i, (a : H →L[ℂ] H) (ξ i)⟫_ℂ
    simpa only [one_mul] using finiteVectorFunctional_apply M ξ a
  · exact isNormalFunctional_of_mem_closure_coefficients M φ

end VacuumBellSeparation.Bipartite
