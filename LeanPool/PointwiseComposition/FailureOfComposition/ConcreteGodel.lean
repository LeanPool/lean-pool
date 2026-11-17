/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.SigmaOneRealization
public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteAdequacy
public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteIndexObstruction

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
The complete arithmetization for the production history evaluator, and the
independent second-incompleteness proof for theories with a Delta-one axiom
presentation. The realization field is proved by the formula compiler; no
arithmetization structure or realization premise is supplied by the caller.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

open CategoricalRiceShapiro.PartialRecursive

namespace FailureOfComposition
namespace ConcreteEvaluator

/-- The actual Mathlib numbering and production arithmetic graph satisfy all
of the arithmetization properties used in the manuscript. -/
noncomputable def arithmetization : ProgramIndices.Arithmetization
    where
  evaluation := Kleene.eval
  graph := eventualGraph
  compIndex := canonicalPartrecCompIndex
  compIndex_primrec := Kleene.compIndex_primrec
  adequate := eventualGraph_adequate
  functional := eventualGraph_functional
  composition := eventualGraph_composition
  realization := SigmaOneRealization.realize_graph

end ConcreteEvaluator
end FailureOfComposition

namespace FailureOfComposition
namespace ConcreteIndices

/-- The second-incompleteness witnesses are indices of the concrete evaluator.
This proof uses the proof predicate of the chosen Delta-one presentation. -/
theorem index_noncongruence_via_godel (T : ArithmeticTheory) [T.Δ₁] [Consistent T] [𝐏𝐀 ≼ T] :
    ∃ f i g : ℕ,
      PointwiseIndex T f i ∧
        ¬PointwiseIndex T (canonicalPartrecCompIndex f g) (canonicalPartrecCompIndex i g) :=
  ProgramIndices.index_noncongruence_of_graph_noncongruence ConcreteEvaluator.arithmetization T
    (graph_noncongruence_via_godel T)

/-- Concrete quotient composition fails by Gödel II, independently of the
productive-set proof. Only consistency and the displayed theory hypotheses
are assumed; realization is supplied by the concrete formula compiler. -/
theorem no_index_quotient_via_godel (T : ArithmeticTheory) [T.Δ₁] [Consistent T] [𝐏𝐀 ≼ T] :
    NoIndexQuotientComposition T :=
  ProgramIndices.no_index_quotient_via_godel ConcreteEvaluator.arithmetization T

theorem pa_no_index_quotient_via_godel : NoIndexQuotientComposition 𝐏𝐀 :=
  no_index_quotient_via_godel 𝐏𝐀

/-- Replacing a theory by a deductively equivalent Delta-one presentation
preserves the external pointwise relation and its failure of congruence. -/
theorem index_noncongruence_via_godel_of_equivalent_presentation (S T : ArithmeticTheory) [S.Δ₁]
    [Consistent T] [𝐏𝐀 ≼ T] (hST : S ≼ T) (hTS : T ≼ S) :
    ∃ f i g : ℕ,
      PointwiseIndex T f i ∧
        ¬PointwiseIndex T (canonicalPartrecCompIndex f g) (canonicalPartrecCompIndex i g) :=
  by
  let : S ≼ T := hST
  let : T ≼ S := hTS
  have : 𝐏𝐀 ≼ S := WeakerThan.trans (𝓣 := T) inferInstance hTS
  have : Consistent S :=
    consistent_iff_unprovable_bot.mpr fun h =>
      consistent_iff_unprovable_bot.mp (inferInstance : Consistent T) (WeakerThan.pbl h)
  obtain ⟨f, i, g, hfi, hcomp⟩ := index_noncongruence_via_godel S
  refine ⟨f, i, g, fun n => WeakerThan.pbl (hfi n), ?_⟩
  intro h
  exact hcomp (fun n => WeakerThan.pbl (h n))

theorem no_index_quotient_via_godel_of_equivalent_presentation (S T : ArithmeticTheory) [S.Δ₁]
    [Consistent T] [𝐏𝐀 ≼ T] (hST : S ≼ T) (hTS : T ≼ S) : NoIndexQuotientComposition T :=
  by
  obtain ⟨f, i, g, hfi, hcomp⟩ :=
    index_noncongruence_via_godel_of_equivalent_presentation S T hST hTS
  exact
    no_quotient_composition_of_noncongruence (indexSetoid T) canonicalPartrecCompIndex f i g hfi
      hcomp

end ConcreteIndices
end FailureOfComposition

end

end PointwiseComposition
