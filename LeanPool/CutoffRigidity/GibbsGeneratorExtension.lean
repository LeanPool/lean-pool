/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsSelfAdjointEigenfunctions

/-!
# The canonical self-adjoint form operator extends the actual compact generator

The negative Langevin differential expression on genuine compact C² L²
tests is a restriction of the constructed nonnegative self-adjoint operator.
This proves an extension relation, not essential self-adjointness.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A compact-domain L² class defines an actual element of the closed energy domain. -/
@[expose] noncomputable def compactGibbsSobolevLift {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : compactGibbsGeneratorDomain V) : gibbsSobolevGraph hV hprob :=
  ⟨WithLp.toLp 2 (u, compactGibbsGradient hV.continuous hprob u),
    LinearPMap.le_graph_of_le (compactGibbsGradient hV.continuous hprob).le_closure
      ((compactGibbsGradient hV.continuous hprob).mem_graph u)⟩

theorem compactGibbsSobolevLift_inclusion {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (u : compactGibbsGeneratorDomain V) :
    gibbsSobolevInclusion hV hprob (compactGibbsSobolevLift hV hprob u) =
      (u : E →₂[gibbsMeasure volume V] ℝ) := rfl

theorem compactGibbsSobolevLift_derivative {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (u : compactGibbsGeneratorDomain V) :
    gibbsSobolevDerivative hV hprob (compactGibbsSobolevLift hV hprob u) =
      compactGibbsGradient hV.continuous hprob u := rfl

/-- Continuity extends a proved compact-test gradient pairing to the entire
actual closed Sobolev domain. -/
theorem gibbs_weak_equation_of_compact_pairing {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : gibbsSobolevGraph hV hprob) (g : E →₂[gibbsMeasure volume V] ℝ)
    (he : ∀ v : compactGibbsGeneratorDomain V,
      inner ℝ (gibbsSobolevDerivative hV hprob u) (compactGibbsGradient hV.continuous hprob v) =
        inner ℝ g (v : E →₂[gibbsMeasure volume V] ℝ))
    (v : gibbsSobolevGraph hV hprob) :
    gibbsDirichletEnergy hV hprob u v = inner ℝ g (gibbsSobolevInclusion hV hprob v) := by
  let G := compactGibbsGradient hV.continuous hprob
  let S : Set ((E →₂[gibbsMeasure volume V] ℝ) × (E →₂[gibbsMeasure volume V] E)) :=
    {p | inner ℝ (gibbsSobolevDerivative hV hprob u) p.2 = inner ℝ g p.1}
  have hS : IsClosed S := isClosed_eq (continuous_const.inner continuous_snd)
    (continuous_const.inner continuous_fst)
  have hinit : (G.graph : Set _) ⊆ S := by
    intro p hp
    obtain ⟨w, hwf, hwg⟩ := G.mem_graph_iff.mp hp
    change inner ℝ (gibbsSobolevDerivative hV hprob u) p.2 = inner ℝ g p.1
    rw [← hwf, ← hwg]
    exact he w
  have hmem : (gibbsSobolevInclusion hV hprob v, gibbsSobolevDerivative hV hprob v) ∈
      closure (G.graph : Set _) := by
    change (gibbsSobolevInclusion hV hprob v, gibbsSobolevDerivative hV hprob v) ∈
      (compactGibbsGradient hV.continuous hprob).graph.topologicalClosure
    rw [(compactGibbsGradient_isClosable hV hprob).graph_closure_eq_closure_graph]
    exact v.property
  exact closure_minimal hinit hS hmem

/-- Actual compact integration by parts is the weak equation for the
canonical positive generator, with every domain already proved. -/
theorem compactGibbsSobolevLift_weak_equation {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : compactGibbsGeneratorDomain V) (v : gibbsSobolevGraph hV hprob) :
    gibbsDirichletEnergy hV hprob (compactGibbsSobolevLift hV hprob u) v =
      inner ℝ (-compactGibbsGenerator hV hprob u) (gibbsSobolevInclusion hV hprob v) := by
  apply gibbs_weak_equation_of_compact_pairing hV hprob
  intro w
  rw [compactGibbsSobolevLift_derivative hV hprob u, compactGibbsGradient_energy_pairing hV hprob u
    w,
    inner_neg_right, inner_neg_left]
  exact congrArg Neg.neg (compactGibbsGenerator_isFormalAdjoint hV hprob u w).symm

/-- The actual compact generator is contained in the self-adjoint form
operator, with the sign dictated by the paper's `-L` convention. -/
theorem compactGibbsGenerator_graph_mem_positiveGenerator {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (u : compactGibbsGeneratorDomain V) :
    ((u : E →₂[gibbsMeasure volume V] ℝ), -compactGibbsGenerator hV hprob u) ∈
      (gibbsPositiveGenerator hV hprob).graph := by
  have he := gibbsPositiveGenerator_of_weak_equation hV hprob
    (compactGibbsSobolevLift hV hprob u) (-compactGibbsGenerator hV hprob u)
    (compactGibbsSobolevLift_weak_equation hV hprob u)
  simpa only [compactGibbsSobolevLift_inclusion] using he

/-- Restriction relation between the actual Hilbert operators. -/
theorem neg_compactGibbsGenerator_le_positiveGenerator {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    -compactGibbsGenerator hV hprob ≤ gibbsPositiveGenerator hV hprob := by
  apply LinearPMap.le_of_le_graph
  rintro ⟨x, y⟩ hp
  obtain ⟨u, huf, hug⟩ := (-compactGibbsGenerator hV hprob).mem_graph_iff.mp hp
  change (u : E →₂[gibbsMeasure volume V] ℝ) = x at huf
  change (-compactGibbsGenerator hV hprob) u = y at hug
  rw [← huf, ← hug]
  exact compactGibbsGenerator_graph_mem_positiveGenerator hV hprob u

end CutoffRigidity
