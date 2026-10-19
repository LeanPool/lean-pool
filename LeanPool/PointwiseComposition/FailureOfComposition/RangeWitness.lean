/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.RangeAssignment

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
A zero-output probe separates external pointwise equality from equality of
range partial identities. Every standard input may have its own PA proof of
divergence, while the range at input zero tests an internal existential over
all possible probe inputs. No passage from these individual proofs to a
universal proof is assumed.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace FailureOfComposition
namespace ConcreteIndices

open ProofSearch ConcreteEvaluator ProgramIndices ConcreteEmptyGraph

/-- The zero-output probe for a Sigma-one predicate on possible witnesses. -/
def probeGraph (P : Σ₁.Semisentence 1) : Graph :=
  .mkSigma (“p y. !P.val p ∧ y = 0”)

@[simp]
theorem probeGraph_eval {M : Type*} [ORingStructure M] (P : Σ₁.Semisentence 1) (v : Fin 2 → M) :
    (probeGraph P).val.Evalb v ↔ P.val.Evalb ![v 0] ∧ v 1 = 0 := by simp [probeGraph]

/-- A probe has at most one output, whether or not its predicate holds. -/
theorem probeGraph_functional (P : Σ₁.Semisentence 1) : Functional (probeGraph P) :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  rw [models_iff, functionalSentence_eval]
  intro x y z hy hz
  exact ((probeGraph_eval P _).mp hy).2.trans ((probeGraph_eval P _).mp hz).2.symm

/-- A concrete program index supplied by the proved Sigma-one realization theorem. -/
noncomputable def probeIndex (P : Σ₁.Semisentence 1) : ℕ :=
  Classical.choose (SigmaOneRealization.realize_graph (probeGraph P) (probeGraph_functional P))

theorem probeIndex_realizes (P : Σ₁.Semisentence 1) :
    Uniform 𝐏𝐀 (eventualGraph (probeIndex P)) (probeGraph P) :=
  Classical.choose_spec
    (SigmaOneRealization.realize_graph (probeGraph P) (probeGraph_functional P))

/-- The equation holds for all inputs of every PA model, including nonstandard ones. -/
theorem probeIndex_graph_equation {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀]
    (P : Σ₁.Semisentence 1) (x y : M) :
    (eventualGraph (probeIndex P)).val.Evalb ![x, y] ↔ P.val.Evalb ![x] ∧ y = 0 :=
  by
  have h := consequence_iff.mp (Theory.Proof.sound (probeIndex_realizes P)) M inferInstance
  simp only [models_iff, uniformSentence_eval] at h
  exact (h x y).trans (probeGraph_eval P _)

/-- The internal assertion that the probe predicate has no witness. -/
def absenceSentence (P : Σ₁.Semisentence 1) : ArithmeticSentence :=
  “∀ p, ¬!P.val p”

@[simp]
theorem absenceSentence_eval {M : Type*} [ORingStructure M] (P : Σ₁.Semisentence 1) :
    (absenceSentence P).Evalb (M := M) ![] ↔ ∀ p : M, ¬P.val.Evalb ![p] := by
  simp [absenceSentence]

/-- Separate numeralwise refutations suffice for external pointwise equality. -/
theorem probeGraph_pointwise_empty (T : ArithmeticTheory) [𝐏𝐀 ≼ T] (P : Σ₁.Semisentence 1)
    (href : ∀ n : ℕ, 𝐏𝐀 ⊢ ∼P.val/[n]) : Pointwise T (probeGraph P) empty :=
  by
  intro n
  have h : 𝐏𝐀 ⊢ ∼P.val/[n] ⇒ₗ eqAt (probeGraph P) empty n :=
    by
    apply complete.{0} 𝐏𝐀
    intro M _ _
    simp [models_iff, eqAt, probeGraph, empty, Semiformula.eval_substs]
  exact WeakerThan.pbl (Entailment.mdp h (href n))

theorem probeIndex_pointwise_empty (T : ArithmeticTheory) [𝐏𝐀 ≼ T] (P : Σ₁.Semisentence 1)
    (href : ∀ n : ℕ, 𝐏𝐀 ⊢ ∼P.val/[n]) : PointwiseIndex T (probeIndex P) concreteEmptyIndex :=
  by
  apply (pointwiseIndex_iff T _ _).mpr
  have eqv := pointwise_equivalence T
  exact
    eqv.trans (uniform_to_pointwise T (probeIndex_realizes P))
      (eqv.trans (probeGraph_pointwise_empty T P href)
        (eqv.symm (uniform_to_pointwise T eventualGraph_empty)))

/-- The range at zero records the internal existential over all probe inputs. -/
theorem range_probe_at_zero {M : Type*} [ORingStructure M] (P : Σ₁.Semisentence 1) :
    (rangeOfGraph (probeGraph P)).val.Evalb ![(0 : M), 0] ↔ ∃ p : M, P.val.Evalb ![p] := by
  simp [rangeOfGraph_eval]

/-- Equality of the probe's range with the empty graph at the one input zero
already implies the internally quantified absence sentence. -/
theorem range_probe_empty_implies_absence (P : Σ₁.Semisentence 1) :
    𝐏𝐀 ⊢ eqAt (rangeOfGraph (probeGraph P)) empty 0 ⇒ₗ absenceSentence P :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  simp only [models_iff, LogicalConnective.HomClass.map_imply, eqAt_eval, absenceSentence_eval]
  intro he p hp
  have hzero := (range_probe_at_zero P).mpr ⟨p, hp⟩
  exact (empty_eval _).mp ((he 0).mp hzero)

theorem range_probeIndex_not_pointwise_empty (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (P : Σ₁.Semisentence 1) (hnot : T ⊬ absenceSentence P) :
    ¬PointwiseIndex T (rangeIndex (probeIndex P)) (rangeIndex concreteEmptyIndex) :=
  by
  intro he
  have eqv := pointwise_equivalence T
  have hprobe :
    Pointwise T (eventualGraph (rangeIndex (probeIndex P))) (rangeOfGraph (probeGraph P)) :=
    eqv.trans (uniform_to_pointwise T (rangeIndex_realizes (probeIndex P)))
      (uniform_to_pointwise T (uniform_rangeOfGraph (probeIndex_realizes P)))
  have h : Pointwise T (rangeOfGraph (probeGraph P)) empty :=
    eqv.trans (eqv.symm hprobe)
      (eqv.trans ((pointwiseIndex_iff T _ _).mp he) (uniform_to_pointwise T rangeIndex_empty))
  exact hnot (Entailment.mdp (WeakerThan.pbl (range_probe_empty_implies_absence P)) (h 0))

/-- A concrete pair of equivalent program indices whose range indices differ. -/
theorem range_counterexample_of_instance_refutations (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (P : Σ₁.Semisentence 1) (href : ∀ n : ℕ, 𝐏𝐀 ⊢ ∼P.val/[n]) (hnot : T ⊬ absenceSentence P) :
    PointwiseIndex T (probeIndex P) concreteEmptyIndex ∧
      ¬PointwiseIndex T (rangeIndex (probeIndex P)) (rangeIndex concreteEmptyIndex) :=
  ⟨probeIndex_pointwise_empty T P href, range_probeIndex_not_pointwise_empty T P hnot⟩

/-- The selected range assignment has no operation on the pointwise quotient. -/
def NoIndexQuotientRange (T : ArithmeticTheory) [𝐏𝐀 ≼ T] : Prop :=
  ¬∃ R : Quotient (indexSetoid T) → Quotient (indexSetoid T),
      ∀ e, R (Quotient.mk (indexSetoid T) e) = Quotient.mk (indexSetoid T) (rangeIndex e)

/-- A pair of equivalent indices with distinct range classes prevents descent. -/
theorem no_index_quotient_range_of_counterexample (T : ArithmeticTheory) [𝐏𝐀 ≼ T] (u z : ℕ)
    (huz : PointwiseIndex T u z) (hr : ¬PointwiseIndex T (rangeIndex u) (rangeIndex z)) :
    NoIndexQuotientRange T := by
  rintro ⟨R, hR⟩
  apply hr
  apply Quotient.exact (s := indexSetoid T)
  calc
    Quotient.mk (indexSetoid T) (rangeIndex u) = R (Quotient.mk (indexSetoid T) u) :=
      (hR _).symm
    _ = R (Quotient.mk (indexSetoid T) z) := by rw [Quotient.sound huz]
    _ = Quotient.mk (indexSetoid T) (rangeIndex z) := hR _

/-- No operation on the pointwise quotient induces the chosen range assignment. -/
theorem no_quotient_range_of_instance_refutations (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (P : Σ₁.Semisentence 1) (href : ∀ n : ℕ, 𝐏𝐀 ⊢ ∼P.val/[n]) (hnot : T ⊬ absenceSentence P) :
    NoIndexQuotientRange T :=
  no_index_quotient_range_of_counterexample T (probeIndex P) concreteEmptyIndex
    (probeIndex_pointwise_empty T P href) (range_probeIndex_not_pointwise_empty T P hnot)

/-- Non-descent persists for every choice of PA-correct range indices. -/
theorem no_quotient_range_of_correct_assignment (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (h : NoIndexQuotientRange T) (ρ : ℕ → ℕ)
    (hρ : ∀ e, Uniform 𝐏𝐀 (eventualGraph (ρ e)) (rangeGraph e)) :
    ¬∃ R : Quotient (indexSetoid T) → Quotient (indexSetoid T),
        ∀ e, R (Quotient.mk (indexSetoid T) e) = Quotient.mk (indexSetoid T) (ρ e) :=
  by
  rintro ⟨R, hR⟩
  apply h
  refine ⟨R, fun e => ?_⟩
  exact (hR e).trans (Quotient.sound (rangeIndex_choice_independent T (hρ e)))

end ConcreteIndices
end FailureOfComposition

end

end PointwiseComposition
