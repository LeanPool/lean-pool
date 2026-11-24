/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsSobolev
public import LeanPool.CutoffRigidity.PositiveResolventOperator

/-!
# The self-adjoint operator of the actual closed Gibbs energy

The bounded variational resolvent is constructed in `GibbsSobolev`. Its
inverse graph supplies a genuine densely defined nonnegative self-adjoint
operator. This does not assert essential self-adjointness of the initial
compact-test operator, spectral compactness, or spectral-gap attainment.
-/

public section

namespace CutoffRigidity

open MeasureTheory
open scoped LinearPMap

section Gibbs

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual variational Gibbs resolvent is injective. -/
theorem gibbsL2Resolvent_injective {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    Function.Injective (gibbsL2Resolvent hV hprob) :=
  self_comp_adjoint_injective_of_denseRange _ (gibbsSobolevInclusion_denseRange hV hprob)

/-- The variational resolvent has dense range in actual Gibbs L². -/
theorem gibbsL2Resolvent_denseRange {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    DenseRange (gibbsL2Resolvent hV hprob) :=
  denseRange_of_injective_symmetric _ (gibbsL2Resolvent_injective hV hprob)
    (gibbsL2Resolvent_symmetric hV hprob)

/-- The nonnegative self-adjoint L² operator of the genuine closed Gibbs
Dirichlet form. The diffusion generator has the opposite sign. -/
@[expose] noncomputable def gibbsPositiveGenerator {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    (E →₂[gibbsMeasure volume V] ℝ) →ₗ.[ℝ] (E →₂[gibbsMeasure volume V] ℝ) :=
  positiveResolventOperator (gibbsL2Resolvent hV hprob)

/-- The operator graph is characterized by the variational Gibbs resolvent. -/
theorem mem_gibbsPositiveGenerator_graph_iff_resolvent {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (u g : E →₂[gibbsMeasure volume V] ℝ) :
    (u, g) ∈ (gibbsPositiveGenerator hV hprob).graph ↔ gibbsL2Resolvent hV hprob (u + g) = u :=
  mem_positiveResolventOperator_graph_iff _ (gibbsL2Resolvent_injective hV hprob) u g

/-- Self-adjointness is derived from the actual variational construction. -/
theorem gibbsPositiveGenerator_selfAdjoint {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    IsSelfAdjoint (gibbsPositiveGenerator hV hprob) :=
  positiveResolventOperator_selfAdjoint _ (gibbsL2Resolvent_injective hV hprob)
    (gibbsL2Resolvent_symmetric hV hprob)

theorem gibbsPositiveGenerator_dense_domain {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    Dense ((gibbsPositiveGenerator hV hprob).domain : Set (E →₂[gibbsMeasure volume V] ℝ)) :=
  (gibbsPositiveGenerator_selfAdjoint hV hprob).dense_domain

theorem gibbsPositiveGenerator_isClosed {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    (gibbsPositiveGenerator hV hprob).IsClosed :=
  (gibbsPositiveGenerator_selfAdjoint hV hprob).isClosed

/-- The form operator is nonnegative; this follows from the proved energy
equation, rather than an assumption about its spectrum. -/
theorem gibbsPositiveGenerator_nonneg {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : (gibbsPositiveGenerator hV hprob).domain) :
    0 ≤ inner ℝ (gibbsPositiveGenerator hV hprob u) (u : E →₂[gibbsMeasure volume V] ℝ) := by
  let R := gibbsL2Resolvent hV hprob
  obtain ⟨f, hf⟩ := (positiveResolventOperator_mem_domain R
    (gibbsL2Resolvent_injective hV hprob) u).mp u.property
  have hA : gibbsPositiveGenerator hV hprob u = f - R f := by
    change positiveResolventOperator R u = f - R f
    calc
      positiveResolventOperator R u = positiveResolventOperator R ⟨R f, hf ▸ u.property⟩ :=
        congrArg (positiveResolventOperator R) (Subtype.ext hf.symm)
      _ = f - R f := positiveResolventOperator_apply R
        (gibbsL2Resolvent_injective hV hprob) f (hf ▸ u.property)
  rw [hA, ← hf, inner_sub_left]
  have henergy := gibbsWeakResolvent_equation hV hprob f (gibbsWeakResolvent hV hprob f)
  have hn := gibbsDirichletEnergy_nonneg hV hprob (gibbsWeakResolvent hV hprob f)
  change inner ℝ (R f) (R f) + _ = inner ℝ f (R f) at henergy
  linarith

end Gibbs

end CutoffRigidity
