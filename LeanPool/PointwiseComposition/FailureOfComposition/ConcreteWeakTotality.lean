/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteIndexObstruction

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Concrete weak-totality witnesses for the manuscript's external pointwise
provability relation. The guard agrees pointwise with identity, but annihilates
a search program that is not provably empty. Consequently weak totality cannot
be assigned to the pointwise quotient independently of a representative.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

open CategoricalRiceShapiro.PartialRecursive

namespace FailureOfComposition
namespace ConcreteIndices

open ProofSearch ConcreteEvaluator HistoryWitnesses ProgramIndices

open ConcreteEmptyGraph

/-- The manuscript's weak-totality predicate on concrete program indices. -/
def WeaklyTotalIndex (T : ArithmeticTheory) (e : ℕ) : Prop :=
  ∀ d,
    PointwiseIndex T (canonicalPartrecCompIndex e d) concreteEmptyIndex →
      PointwiseIndex T d concreteEmptyIndex

/-- Identity is a left identity for the external pointwise index relation. -/
theorem identity_comp_pointwiseIndex (T : ArithmeticTheory) [𝐏𝐀 ≼ T] (e : ℕ) :
    PointwiseIndex T (canonicalPartrecCompIndex Kleene.identityIndex e) e :=
  by
  have hRefl : Uniform 𝐏𝐀 (eventualGraph e) (eventualGraph e) :=
    by
    apply complete.{0} 𝐏𝐀
    intro M _ _
    simp [models_iff, uniformSentence]
  have eqv := pointwise_equivalence T
  apply (pointwiseIndex_iff T _ _).mpr
  exact
    eqv.trans (uniform_to_pointwise T (eventualGraph_composition _ _))
      (eqv.trans (uniform_to_pointwise T (uniform_comp eventualGraph_identity hRefl))
        (uniform_to_pointwise T (identity_comp (eventualGraph e))))

/-- Every standard instance of the divergent guard agrees provably with identity. -/
theorem guardIndex_pointwise_identity (T : ArithmeticTheory) [𝐏𝐀 ≼ T] (d : ℕ)
    (hdiv : ¬diagonalHistoryFormula.Evalb ![d]) :
    PointwiseIndex T (guardIndex d) Kleene.identityIndex :=
  by
  have eqv := pointwise_equivalence T
  apply (pointwiseIndex_iff T _ _).mpr
  exact
    eqv.trans (uniform_to_pointwise T (guardIndex_realizes d))
      (eqv.trans (guard_pointwise_identity T d hdiv)
        (eqv.symm (uniform_to_pointwise T eventualGraph_identity)))

/-- The guard annihilates its associated least-success search in PA. -/
theorem guard_search_pointwise_empty (T : ArithmeticTheory) [𝐏𝐀 ≼ T] (d : ℕ) :
    PointwiseIndex T (canonicalPartrecCompIndex (guardIndex d) (searchIndex d))
      concreteEmptyIndex :=
  by
  have eqv := pointwise_equivalence T
  apply (pointwiseIndex_iff T _ _).mpr
  exact
    eqv.trans (uniform_to_pointwise T (eventualGraph_composition _ _))
      (eqv.trans
        (uniform_to_pointwise T (uniform_comp (guardIndex_realizes d) (searchIndex_realizes d)))
        (eqv.trans (uniform_to_pointwise T (HistoryWitnesses.guard_search_empty d))
          (eqv.symm (uniform_to_pointwise T eventualGraph_empty))))

/-- Proving the search empty would prove the chosen divergence sentence. -/
theorem searchIndex_not_pointwise_empty (T : ArithmeticTheory) [𝐏𝐀 ≼ T] (d : ℕ)
    (hnot : T ⊬ ∼diagonalHistoryFormula/[d]) :
    ¬PointwiseIndex T (searchIndex d) concreteEmptyIndex :=
  by
  intro h
  have eqv := pointwise_equivalence T
  have hs : Pointwise T (searchGraph d) empty :=
    eqv.trans (eqv.symm (uniform_to_pointwise T (searchIndex_realizes d)))
      (eqv.trans ((pointwiseIndex_iff T _ _).mp h) (uniform_to_pointwise T eventualGraph_empty))
  exact hnot (Entailment.mdp (WeakerThan.pbl (search_empty_implies_absence d)) (hs 0))

/-- All four concrete witnesses used for composition and weak-totality failure. -/
theorem index_four_witnesses_of_history_divergence (T : ArithmeticTheory) [𝐏𝐀 ≼ T] (d : ℕ)
    (hdiv : ¬diagonalHistoryFormula.Evalb ![d]) (hnot : T ⊬ ∼diagonalHistoryFormula/[d]) :
    PointwiseIndex T (guardIndex d) Kleene.identityIndex ∧
      PointwiseIndex T (canonicalPartrecCompIndex (guardIndex d) (searchIndex d))
          concreteEmptyIndex ∧
        PointwiseIndex T (canonicalPartrecCompIndex Kleene.identityIndex (searchIndex d))
            (searchIndex d) ∧
          ¬PointwiseIndex T (searchIndex d) concreteEmptyIndex :=
  ⟨guardIndex_pointwise_identity T d hdiv, guard_search_pointwise_empty T d,
    identity_comp_pointwiseIndex T (searchIndex d), searchIndex_not_pointwise_empty T d hnot⟩

/-- Identity is weakly total without any consistency or enumerability hypothesis. -/
theorem weaklyTotalIndex_identity (T : ArithmeticTheory) [𝐏𝐀 ≼ T] :
    WeaklyTotalIndex T Kleene.identityIndex :=
  weaklyTotal_identity (indexSetoid T) canonicalPartrecCompIndex Kleene.identityIndex
    concreteEmptyIndex (identity_comp_pointwiseIndex T)

/-- The search witness refutes weak totality of the guard. -/
theorem not_weaklyTotalIndex_guard (T : ArithmeticTheory) [𝐏𝐀 ≼ T] (d : ℕ)
    (hnot : T ⊬ ∼diagonalHistoryFormula/[d]) : ¬WeaklyTotalIndex T (guardIndex d) :=
  not_weaklyTotal_guard (indexSetoid T) canonicalPartrecCompIndex (guardIndex d) (searchIndex d)
    concreteEmptyIndex (guard_search_pointwise_empty T d)
    (searchIndex_not_pointwise_empty T d hnot)

/-- A true unprovable divergence gives equivalent indices of different weak totality. -/
theorem weak_totality_counterexample_of_history_divergence (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (d : ℕ) (hdiv : ¬diagonalHistoryFormula.Evalb ![d])
    (hnot : T ⊬ ∼diagonalHistoryFormula/[d]) :
    PointwiseIndex T (guardIndex d) Kleene.identityIndex ∧
      ¬WeaklyTotalIndex T (guardIndex d) ∧ WeaklyTotalIndex T Kleene.identityIndex :=
  ⟨guardIndex_pointwise_identity T d hdiv, not_weaklyTotalIndex_guard T d hnot,
    weaklyTotalIndex_identity T⟩

/-- Productiveness supplies a concrete counterexample for every consistent
extension of PA with recursively enumerable theorem codes. -/
theorem weak_totality_counterexample_via_productiveness (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    [Consistent T] (hT : REPred (TheoremCodes T)) :
    ∃ d,
      PointwiseIndex T (guardIndex d) Kleene.identityIndex ∧
        ¬WeaklyTotalIndex T (guardIndex d) ∧ WeaklyTotalIndex T Kleene.identityIndex :=
  by
  obtain ⟨d, hdiv, hnot⟩ := exists_true_unprovable_history_divergence_of_theorem_codes T hT
  exact ⟨d, weak_totality_counterexample_of_history_divergence T d hdiv hnot⟩

/-- The decidable axiom-presentation specialization. -/
theorem weak_totality_counterexample_of_delta_one (T : ArithmeticTheory) [T.Δ₁] [𝐏𝐀 ≼ T]
    [Consistent T] :
    ∃ d,
      PointwiseIndex T (guardIndex d) Kleene.identityIndex ∧
        ¬WeaklyTotalIndex T (guardIndex d) ∧ WeaklyTotalIndex T Kleene.identityIndex :=
  by
  obtain ⟨d, hdiv, hnot⟩ := exists_true_unprovable_history_divergence T
  exact ⟨d, weak_totality_counterexample_of_history_divergence T d hdiv hnot⟩

/-- Recursively enumerable axiom codes suffice for weak-totality failure. -/
theorem weak_totality_counterexample_of_re_axioms (T : ArithmeticTheory) [𝐏𝐀 ≼ T] [Consistent T]
    (hT : REPred (AxiomCodes T)) :
    ∃ d,
      PointwiseIndex T (guardIndex d) Kleene.identityIndex ∧
        ¬WeaklyTotalIndex T (guardIndex d) ∧ WeaklyTotalIndex T Kleene.identityIndex :=
  weak_totality_counterexample_via_productiveness T (theorem_codes_re_of_axiom_codes T hT)

/-- The explicit program enumeration of axioms used in the manuscript. -/
theorem weak_totality_counterexample_of_axiom_enumerator (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    [Consistent T] (a : ℕ) (ha : ∀ n : ℕ, AxiomCodes T n ↔ ∃ x : ℕ, n ∈ Kleene.eval a x) :
    ∃ d,
      PointwiseIndex T (guardIndex d) Kleene.identityIndex ∧
        ¬WeaklyTotalIndex T (guardIndex d) ∧ WeaklyTotalIndex T Kleene.identityIndex :=
  weak_totality_counterexample_of_re_axioms T (axiom_codes_re_of_program_enumerator T a ha)

/-- No predicate on the pointwise quotient represents weak totality of its indices. -/
theorem no_quotient_weak_totality_of_history_divergence (T : ArithmeticTheory) [𝐏𝐀 ≼ T] (d : ℕ)
    (hdiv : ¬diagonalHistoryFormula.Evalb ![d]) (hnot : T ⊬ ∼diagonalHistoryFormula/[d]) :
    ¬∃ P : Quotient (indexSetoid T) → Prop,
        ∀ e, P (Quotient.mk (indexSetoid T) e) ↔ WeaklyTotalIndex T e :=
  by
  rintro ⟨P, hP⟩
  apply not_weaklyTotalIndex_guard T d hnot
  apply (hP (guardIndex d)).mp
  have hEq :
    Quotient.mk (indexSetoid T) (guardIndex d) =
      Quotient.mk (indexSetoid T) Kleene.identityIndex :=
    Quotient.sound (guardIndex_pointwise_identity T d hdiv)
  rw [hEq]
  exact (hP Kleene.identityIndex).mpr (weaklyTotalIndex_identity T)

/-- Weak totality does not descend for any consistent recursively axiomatized
extension of PA. -/
theorem no_quotient_weak_totality_of_re_axioms (T : ArithmeticTheory) [𝐏𝐀 ≼ T] [Consistent T]
    (hT : REPred (AxiomCodes T)) :
    ¬∃ P : Quotient (indexSetoid T) → Prop,
        ∀ e, P (Quotient.mk (indexSetoid T) e) ↔ WeaklyTotalIndex T e :=
  by
  obtain ⟨d, hdiv, hnot⟩ :=
    exists_true_unprovable_history_divergence_of_theorem_codes T
      (theorem_codes_re_of_axiom_codes T hT)
  exact no_quotient_weak_totality_of_history_divergence T d hdiv hnot

end ConcreteIndices
end FailureOfComposition

end

end PointwiseComposition
