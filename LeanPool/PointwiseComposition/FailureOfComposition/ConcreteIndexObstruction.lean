/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.HistoryObstruction
public import LeanPool.PointwiseComposition.FailureOfComposition.ArithmeticCodeCompiler
public import LeanPool.PointwiseComposition.FailureOfComposition.ProgramIndices
public import LeanPool.PointwiseComposition.FailureOfComposition.AxiomEnumeration

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Concrete natural-number witnesses for the failure of quotient composition.
The graphs are the production history evaluator, and the guard/search indices
are obtained by the proved structural compiler, without an Arithmetization
parameter or a graph-realization hypothesis.
-/

@[expose] public section

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

open CategoricalRiceShapiro.PartialRecursive

namespace FailureOfComposition
namespace ConcreteIndices

open ProofSearch ConcreteEvaluator HistoryWitnesses ArithmeticCodeCompiler

open ProgramIndices

/-- The guard Index construction in `FailureOfComposition.ConcreteIndices`. -/
def guardIndex (d : ℕ) : ℕ :=
  encode (unaryCompile (guardCode d))

/-- The search Index construction in `FailureOfComposition.ConcreteIndices`. -/
def searchIndex (d : ℕ) : ℕ :=
  encode (unaryCompile (searchCode d))

theorem guardIndex_realizes (d : ℕ) :
    Uniform 𝐏𝐀 (eventualGraph (guardIndex d)) (guardGraph d) :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  exact (computes_unaryCompile (guardCode d) x y).trans (guardCode_eval d x y)

theorem searchIndex_realizes (d : ℕ) :
    Uniform 𝐏𝐀 (eventualGraph (searchIndex d)) (searchGraph d) :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  exact (computes_unaryCompile (searchCode d) x y).trans (searchCode_eval d x y)

/-- The external input quantifier of Montagna's relation. -/
def PointwiseIndex (T : ArithmeticTheory) (e f : ℕ) : Prop :=
  ∀ n : ℕ, T ⊢ kleeneEqAt (eventualGraph e) (eventualGraph f) n

theorem pointwiseIndex_iff (T : ArithmeticTheory) [𝐏𝐀 ≼ T] (e f : ℕ) :
    PointwiseIndex T e f ↔ Pointwise T (eventualGraph e) (eventualGraph f) :=
  by
  have h (n : ℕ) :
    T ⊢
      kleeneEqAt (eventualGraph e) (eventualGraph f) n ⇔ₗ
        eqAt (eventualGraph e) (eventualGraph f) n :=
    WeakerThan.pbl
      (kleeneEqAt_iff_eqAt _ _ (eventualGraph_functional e) (eventualGraph_functional f) n)
  constructor
  · intro he n
    have hn := he n
    cl_prover[h n, hn]
  · intro he n
    have hn := he n
    cl_prover[h n, hn]

/-- The index Setoid construction in `FailureOfComposition.ConcreteIndices`. -/
def indexSetoid (T : ArithmeticTheory) [𝐏𝐀 ≼ T] : Setoid ℕ
    where
  r := PointwiseIndex T
  iseqv :=
    { refl := fun e => (pointwiseIndex_iff T e e).mpr ((pointwise_equivalence T).refl _)
      symm := fun {e f} h =>
        (pointwiseIndex_iff T f e).mpr
          ((pointwise_equivalence T).symm ((pointwiseIndex_iff T e f).mp h))
      trans := fun {e f g} h₁ h₂ =>
        (pointwiseIndex_iff T e g).mpr
          ((pointwise_equivalence T).trans ((pointwiseIndex_iff T e f).mp h₁)
            ((pointwiseIndex_iff T f g).mp h₂)) }

/-- The No Index Quotient Composition construction in `FailureOfComposition.ConcreteIndices`. -/
def NoIndexQuotientComposition (T : ArithmeticTheory) [𝐏𝐀 ≼ T] : Prop :=
  ¬∃ C : Quotient (indexSetoid T) → Quotient (indexSetoid T) → Quotient (indexSetoid T),
      ∀ e f,
        C (Quotient.mk (indexSetoid T) e) (Quotient.mk (indexSetoid T) f) =
          Quotient.mk (indexSetoid T) (canonicalPartrecCompIndex e f)

theorem index_noncongruence_of_history_divergence (T : ArithmeticTheory) [𝐏𝐀 ≼ T] (d : ℕ)
    (hdiv : ¬diagonalHistoryFormula.Evalb ![d]) (hnot : T ⊬ ∼diagonalHistoryFormula/[d]) :
    PointwiseIndex T (guardIndex d) Kleene.identityIndex ∧
      ¬PointwiseIndex T (canonicalPartrecCompIndex (guardIndex d) (searchIndex d))
          (canonicalPartrecCompIndex Kleene.identityIndex (searchIndex d)) :=
  by
  obtain ⟨hfi, hn⟩ := graph_noncongruence_of_history_divergence T d hdiv hnot
  have eqv := pointwise_equivalence T
  have hf := uniform_to_pointwise T (guardIndex_realizes d)
  have hi := uniform_to_pointwise T eventualGraph_identity
  have hfg :
    Pointwise T (eventualGraph (canonicalPartrecCompIndex (guardIndex d) (searchIndex d)))
      (comp (guardGraph d) (searchGraph d)) :=
    eqv.trans (uniform_to_pointwise T (eventualGraph_composition _ _))
      (uniform_to_pointwise T (uniform_comp (guardIndex_realizes d) (searchIndex_realizes d)))
  have hig :
    Pointwise T (eventualGraph (canonicalPartrecCompIndex Kleene.identityIndex (searchIndex d)))
      (comp identity (searchGraph d)) :=
    eqv.trans (uniform_to_pointwise T (eventualGraph_composition _ _))
      (uniform_to_pointwise T (uniform_comp eventualGraph_identity (searchIndex_realizes d)))
  refine ⟨(pointwiseIndex_iff T _ _).mpr (eqv.trans hf (eqv.trans hfi (eqv.symm hi))), ?_⟩
  intro hc
  exact hn (eqv.trans (eqv.symm hfg) (eqv.trans ((pointwiseIndex_iff T _ _).mp hc) hig))

theorem no_index_quotient_of_history_divergence (T : ArithmeticTheory) [𝐏𝐀 ≼ T] (d : ℕ)
    (hdiv : ¬diagonalHistoryFormula.Evalb ![d]) (hnot : T ⊬ ∼diagonalHistoryFormula/[d]) :
    NoIndexQuotientComposition T :=
  by
  obtain ⟨hfi, hcomp⟩ := index_noncongruence_of_history_divergence T d hdiv hnot
  exact
    no_quotient_composition_of_noncongruence (indexSetoid T) canonicalPartrecCompIndex
      (guardIndex d) Kleene.identityIndex (searchIndex d) hfi hcomp

/-- Concrete obstruction, using only consistency and an r.e. theorem set. -/
theorem no_index_quotient_via_productiveness (T : ArithmeticTheory) [𝐏𝐀 ≼ T] [Consistent T]
    (hT : REPred (FailureOfComposition.TheoremCodes T)) : NoIndexQuotientComposition T :=
  by
  obtain ⟨d, hdiv, hnot⟩ := exists_true_unprovable_history_divergence_of_theorem_codes T hT
  exact no_index_quotient_of_history_divergence T d hdiv hnot

/-- The decidable axiom-presentation specialization. -/
theorem no_index_quotient_of_delta_one (T : ArithmeticTheory) [T.Δ₁] [𝐏𝐀 ≼ T] [Consistent T] :
    NoIndexQuotientComposition T :=
  by
  obtain ⟨d, hdiv, hnot⟩ := exists_true_unprovable_history_divergence T
  exact no_index_quotient_of_history_divergence T d hdiv hnot

/-- Every consistent extension of PA with recursively enumerable axiom codes
has this concrete program-index quotient obstruction. -/
theorem no_index_quotient_of_re_axioms (T : ArithmeticTheory) [𝐏𝐀 ≼ T] [Consistent T]
    (hT : REPred (FailureOfComposition.AxiomCodes T)) : NoIndexQuotientComposition T :=
  no_index_quotient_via_productiveness T (theorem_codes_re_of_axiom_codes T hT)

/-- The explicit partial-recursive axiom enumeration used in v36. -/
theorem no_index_quotient_of_axiom_enumerator (T : ArithmeticTheory) [𝐏𝐀 ≼ T] [Consistent T]
    (a : ℕ) (ha : ∀ n : ℕ, AxiomCodes T n ↔ ∃ x : ℕ, n ∈ Kleene.eval a x) :
    NoIndexQuotientComposition T :=
  no_index_quotient_of_re_axioms T (axiom_codes_re_of_program_enumerator T a ha)

end ConcreteIndices
end FailureOfComposition

namespace FailureOfComposition
namespace ProgramIndices

/-- The manuscript's arithmetization assumptions with its r.e. axiom
presentation; no separate theorem-code enumerability hypothesis remains. -/
theorem no_index_quotient_of_re_axioms (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    [Consistent T] (hT : REPred (FailureOfComposition.AxiomCodes T)) :
    NoIndexQuotientComposition A T :=
  no_index_quotient_via_productiveness A T (theorem_codes_re_of_axiom_codes T hT)

end ProgramIndices
end FailureOfComposition

end

end PointwiseComposition
