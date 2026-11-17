/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalUncountableSentence.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ElementarySatisfaction
public import LeanPool.TuringConeRigidity.SetModels.InternalCountableFamily

/-!
# Internal Uncountable Sentence
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalUncountableSentence
open TransitiveNameModel BoundedSetTheory ElementaryModel

/-- Bounded formula asserting that a function graph maps omega onto the designated set. -/
def ontoMatrix (f ω A : ℕ) : Formula :=
  .conj (.functionGraph f ω A) (.allMem A (.existsMem (ω+1) (.pairMem 0 1 (f+2))))

theorem ontoMatrix_spec (f ω A : ℕ) (e : ℕ → ZFSet.{0}) :
    (ontoMatrix f ω A).Eval e ↔ FunctionGraph (e ω) (e A) (e f) ∧
      ∀ x ∈ e A, ∃ n ∈ e ω, ZFSet.pair n x ∈ e f := by
  simp only [ontoMatrix,Formula.Eval,Formula.eval_functionGraph,Formula.eval_allMem,
    Formula.eval_pairMem,FunctionGraph,cons_zero,cons_succ]

/-- A full formula asserting existence of a function graph from omega onto `A`. -/
noncomputable def countableSentence (A ω : ℕ) : SentenceForm :=
  .ex (fromBounded (ontoMatrix 0 (ω+1) (A+1)))

theorem countableSentence_spec (M : ZFSet.{0}) (hM : Transitive M) (A ω : ℕ)
    (e : ℕ → ZFSet.{0}) (he : ∀ i, e i ∈ M) (hω : e ω = ZFSet.omega) :
    (countableSentence A ω).Sat (M : Set ZFSet) e ↔ InternallyCountable M (e A) := by
  change (∃ f ∈ M, (fromBounded _).Sat _ (cons f e)) ↔ _
  unfold InternallyCountable
  apply exists_congr; intro f
  apply and_congr_right; intro hf
  rw [bounded_sat,Formula.absolute _ M hM _ (by
    intro i
    cases i
    · exact hf
    · exact he _),ontoMatrix_spec]
  simp only [cons_zero,cons_succ,hω]

/-- A full formula asserting that the parameter is a nonempty ordinal admitting no surjection
from omega. -/
noncomputable def uncountableOrdinalSentence : SentenceForm :=
  .conj (fromBounded (.conj (.transitive 0) (.allMem 0 (.transitive 0))))
    (.conj (.neg (fromBounded (.empty 0))) (.neg (countableSentence 0 1)))

theorem uncountableOrdinalSentence_spec (M : ZFSet.{0}) (hM : Transitive M)
    (e : ℕ → ZFSet.{0}) (he : ∀ i, e i ∈ M) (hω : e 1 = ZFSet.omega) :
    uncountableOrdinalSentence.Sat (M : Set ZFSet) e ↔
      (e 0).IsOrdinal ∧ ¬ (e 0 = ∅ ∨ InternallyCountable M (e 0)) := by
  change (fromBounded _).Sat _ e ∧ (¬ (fromBounded _).Sat _ e) ∧
    ¬ (countableSentence 0 1).Sat _ e ↔ _
  rw [bounded_sat,Formula.absolute _ M hM e he,bounded_sat,Formula.absolute _ M hM e he,
    countableSentence_spec M hM 0 1 e he hω]
  simp only [Formula.Eval,Formula.eval_transitive,Formula.eval_allMem,Formula.eval_empty,
    cons_zero,ZFSet.isOrdinal_iff_forall_mem_isTransitive,not_or]
  rfl

theorem no_surjection [Uncountable (Conditions (Ordinal.omega 1 : Ordinal.{0}).toZFSet)]
    (f : ZFSet.{0}) (hf : FunctionGraph ZFSet.omega (Ordinal.omega 1 : Ordinal.{0}).toZFSet f)
    (hs : ∀ x ∈ (Ordinal.omega 1 : Ordinal.{0}).toZFSet, ∃ n ∈ ZFSet.omega, ZFSet.pair n x ∈ f) :
      False := by
  classical
  obtain ⟨E,hE,hEf⟩ := InternalCountableFamily.sequence_of_graph _ f hf
  let t : ℕ → Conditions (Ordinal.omega 1 : Ordinal.{0}).toZFSet := fun n => equivShrink _ ⟨E n,hE
    n⟩
  have ht : Function.Surjective t := by
    intro x
    obtain ⟨n,hn,hnx⟩ := hs (label _ x) (label_mem _ x)
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    have heq := (orbitGraph_pair E n (label _ x)).mp (hEf.symm ▸ hnx)
    exact ⟨n,label_injective _ (by simpa only [t,label,Equiv.symm_apply_apply] using heq.symm)⟩
  exact not_countable ht.countable

theorem ambient_uncountable_ordinal :
    uncountableOrdinalSentence.Sat Set.univ
      (cons (Ordinal.omega 1 : Ordinal.{0}).toZFSet (fun _ => ZFSet.omega)) := by
  classical
  have hc : Cardinal.aleph0 < Cardinal.mk (Conditions (Ordinal.omega 1 : Ordinal.{0}).toZFSet) := by
    change Cardinal.aleph0 < ((Ordinal.omega 1 : Ordinal.{0}).toZFSet).card
    rw [Ordinal.card_toZFSet,Ordinal.card_omega]
    exact Cardinal.aleph0_lt_aleph_one
  have : Uncountable (Conditions (Ordinal.omega 1 : Ordinal.{0}).toZFSet) :=
    Cardinal.aleph0_lt_mk_iff.mp hc
  change (fromBounded _).Sat _ _ ∧ (¬ (fromBounded _).Sat _ _) ∧ ¬ (countableSentence 0 1).Sat _ _
  rw [bounded_univ,bounded_univ]
  constructor
  · simp only [Formula.Eval,Formula.eval_transitive,Formula.eval_allMem,cons_zero]
    exact (ZFSet.isOrdinal_iff_forall_mem_isTransitive.mp (ZFSet.isOrdinal_toZFSet (Ordinal.omega
      1 : Ordinal.{0})))
  constructor
  · simp only [Formula.eval_empty,cons_zero]
    intro he
    have hpos := Ordinal.omega_pos (1 : Ordinal.{0})
    have hr := congrArg ZFSet.rank he
    rw [Ordinal.rank_toZFSet,ZFSet.rank_empty] at hr
    exact hpos.ne' hr
  · rintro ⟨f,_,hf⟩
    have h := (ontoMatrix_spec 0 2 1 _).mp ((bounded_univ _ _).mp hf)
    exact no_surjection f h.1 h.2

end TuringRigidity.InternalUncountableSentence

end OAI
