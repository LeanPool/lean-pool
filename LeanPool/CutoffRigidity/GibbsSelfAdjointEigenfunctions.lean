/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsSelfAdjoint
public import LeanPool.CutoffRigidity.GibbsSobolevClassical

/-!
# Classical eigenfunctions in the actual self-adjoint Gibbs form operator

The implication is proved via the actual variational resolvent. The converse
requires elliptic regularity and is not asserted. Neither spectral-gap
attainment nor identification with the stochastic semigroup is assumed.
-/

public section

namespace CutoffRigidity

open MeasureTheory

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A genuine weak form equation determines the variational resolvent. -/
theorem gibbsL2Resolvent_of_weak_equation {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : gibbsSobolevGraph hV hprob) (g : E →₂[gibbsMeasure volume V] ℝ)
    (he : ∀ v : gibbsSobolevGraph hV hprob,
      gibbsDirichletEnergy hV hprob u v = inner ℝ g (gibbsSobolevInclusion hV hprob v)) :
    gibbsL2Resolvent hV hprob (gibbsSobolevInclusion hV hprob u + g) =
      gibbsSobolevInclusion hV hprob u := by
  let J := gibbsSobolevInclusion hV hprob
  have hsol : gibbsWeakResolvent hV hprob (J u + g) = u := by
    apply ext_inner_right ℝ
    intro v
    calc
      _ = inner ℝ (J u + g) (J v) :=
        (gibbsSobolev_inner hV hprob (gibbsWeakResolvent hV hprob (J u + g)) v).trans
          (gibbsWeakResolvent_equation hV hprob (J u + g) v)
      _ = inner ℝ (J u) (J v) + gibbsDirichletEnergy hV hprob u v := by
        rw [inner_add_left, he v]
      _ = inner ℝ u v := (gibbsSobolev_inner hV hprob u v).symm
  exact congrArg J hsol

/-- Every genuine weak form solution lies in the self-adjoint operator
 domain, with its weak right-hand side as the actual operator value. -/
theorem gibbsPositiveGenerator_of_weak_equation {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : gibbsSobolevGraph hV hprob) (g : E →₂[gibbsMeasure volume V] ℝ)
    (he : ∀ v : gibbsSobolevGraph hV hprob,
      gibbsDirichletEnergy hV hprob u v = inner ℝ g (gibbsSobolevInclusion hV hprob v)) :
    (gibbsSobolevInclusion hV hprob u, g) ∈ (gibbsPositiveGenerator hV hprob).graph := by
  change (gibbsSobolevInclusion hV hprob u, g) ∈
    (positiveResolventOperator (gibbsL2Resolvent hV hprob)).graph
  rw [positiveResolventOperator_graph _ (gibbsL2Resolvent_injective hV hprob),
    mem_positiveResolventGraph]
  refine ⟨gibbsSobolevInclusion hV hprob u + g, ?_, ?_⟩
  · exact gibbsL2Resolvent_of_weak_equation hV hprob u g he
  · rw [gibbsL2Resolvent_of_weak_equation hV hprob u g he]
    abel

/-- A classical eigenclass belongs to the genuine self-adjoint form
operator domain; it is not merely an eigenfunction of a formal expression. -/
theorem classicalEigen_mem_gibbsPositiveGenerator_domain {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (u : classicalL2Eigenspace V ρ) :
    (u : E →₂[gibbsMeasure volume V] ℝ) ∈ (gibbsPositiveGenerator hV hprob).domain := by
  apply (positiveResolventOperator_mem_domain _ (gibbsL2Resolvent_injective hV hprob) _).mpr
  exact ⟨(1 + ρ) • (u : E →₂[gibbsMeasure volume V] ℝ),
    gibbsL2Resolvent_classicalEigen hV hprob ρ hρ u⟩

/-- The actual nonnegative self-adjoint operator acts on every classical
L² eigenclass by the prescribed eigenvalue. -/
theorem gibbsPositiveGenerator_classicalEigen {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (u : classicalL2Eigenspace V ρ) :
    gibbsPositiveGenerator hV hprob
      ⟨u, classicalEigen_mem_gibbsPositiveGenerator_domain hV hprob ρ hρ u⟩ =
        ρ • (u : E →₂[gibbsMeasure volume V] ℝ) := by
  let R := gibbsL2Resolvent hV hprob
  let A := positiveResolventOperator R
  let f := (1 + ρ) • (u : E →₂[gibbsMeasure volume V] ℝ)
  have hf : R f = (u : E →₂[gibbsMeasure volume V] ℝ) :=
    gibbsL2Resolvent_classicalEigen hV hprob ρ hρ u
  have hx := classicalEigen_mem_gibbsPositiveGenerator_domain hV hprob ρ hρ u
  change A ⟨u, hx⟩ = _
  calc
    A ⟨u, hx⟩ = A ⟨R f, hf ▸ hx⟩ := congrArg A (Subtype.ext hf.symm)
    _ = f - R f := positiveResolventOperator_apply R (gibbsL2Resolvent_injective hV hprob) f _
    _ = ρ • (u : E →₂[gibbsMeasure volume V] ℝ) := by
      rw [hf]
      dsimp only [f]
      module

/-- The actual Hilbert eigenspace of the self-adjoint form operator, defined
by its graph. No pointwise representative or differentiability is required. -/
@[expose] noncomputable def gibbsOperatorEigenspace {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ) :
    Submodule ℝ (E →₂[gibbsMeasure volume V] ℝ) :=
  (gibbsPositiveGenerator hV hprob).graph.comap
    (LinearMap.id.prod (ρ • LinearMap.id))

theorem mem_gibbsOperatorEigenspace {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ)
    (u : E →₂[gibbsMeasure volume V] ℝ) :
    u ∈ gibbsOperatorEigenspace hV hprob ρ ↔
      (u, ρ • u) ∈ (gibbsPositiveGenerator hV hprob).graph := Iff.rfl

/-- Classical eigenfunctions embed into the actual operator eigenspace.
The reverse inclusion remains a regularity theorem to prove. -/
theorem classicalL2Eigenspace_le_gibbsOperatorEigenspace {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    classicalL2Eigenspace V ρ ≤ gibbsOperatorEigenspace hV hprob ρ := by
  intro u hu
  let v : classicalL2Eigenspace V ρ := ⟨u, hu⟩
  rw [mem_gibbsOperatorEigenspace]
  have hv := (gibbsPositiveGenerator hV hprob).mem_graph
    ⟨u, classicalEigen_mem_gibbsPositiveGenerator_domain hV hprob ρ hρ v⟩
  rwa [gibbsPositiveGenerator_classicalEigen hV hprob ρ hρ v] at hv

end CutoffRigidity
