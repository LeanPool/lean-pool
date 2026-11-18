/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ValidFirstUncountable.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalUncountableSentence
public import LeanPool.TuringConeRigidity.SetModels.InternalGraphEquiv
public import LeanPool.TuringConeRigidity.SetModels.ElementarySchemas
public import LeanPool.TuringConeRigidity.SetModels.InternalCountableOrdinals

/-!
# Valid First Uncountable
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ValidFirstUncountable
open TransitiveNameModel BoundedSetTheory ElementaryModel InternalCountableOrdinals
open InternalUncountableSentence InternalGraphEquiv

theorem card_le_of_graph (A B f : ZFSet.{0}) (hf : FunctionGraph A B f)
    (hs : ∀ y ∈ B, ∃ x ∈ A, ZFSet.pair x y ∈ f) : B.card ≤ A.card := by
  have hsurj : Function.Surjective (graphMap A B f hf) := by
    intro y
    obtain ⟨x,hx,hxy⟩ := hs (label B y) (label_mem B y)
    obtain ⟨x,rfl⟩ := label_surjective A hx
    exact ⟨x,label_injective B (hf.functional (label_mem A x) (graphMap_spec A B f hf x) hxy)⟩
  exact Cardinal.mk_le_of_surjective hsurj

theorem ambient_larger_ordinal (W : ZFSet.{0}) :
    ∃ K : ZFSet.{0}, K.IsOrdinal ∧ K ≠ ∅ ∧
      ¬ (∃ f, FunctionGraph W K f ∧ ∀ y ∈ K, ∃ x ∈ W, ZFSet.pair x y ∈ f) := by
  let K : ZFSet.{0} := (Order.succ W.card).ord.toZFSet
  have hcard : K.card = Order.succ W.card := by
    dsimp only [K]
    rw [Ordinal.card_toZFSet,Cardinal.card_ord]
  refine ⟨K,ZFSet.isOrdinal_toZFSet _,?_,?_⟩
  · intro he
    have hh := congrArg ZFSet.card he
    rw [hcard,ZFSet.card_empty] at hh
    exact Cardinal.succ_ne_zero W.card hh
  · rintro ⟨f,hf,hs⟩
    have hle := card_le_of_graph W K f hf hs
    rw [hcard] at hle
    exact (Order.lt_succ W.card).not_ge hle

theorem ambient_sentence (e : ℕ → ZFSet.{0}) :
    (SentenceForm.ex uncountableOrdinalSentence).Sat Set.univ e := by
  obtain ⟨K,hK,hne,hunc⟩ := ambient_larger_ordinal (e 0)
  refine ⟨K,Set.mem_univ _,?_⟩
  change (fromBounded _).Sat _ _ ∧ (¬ (fromBounded _).Sat _ _) ∧ ¬ (countableSentence 0 1).Sat _ _
  rw [bounded_univ,bounded_univ]
  constructor
  · simp only [Formula.Eval,Formula.eval_transitive,Formula.eval_allMem,cons_zero]
    exact ZFSet.isOrdinal_iff_forall_mem_isTransitive.mp hK
  constructor
  · simpa only [Formula.eval_empty,cons_zero] using hne
  · rintro ⟨f,_,hf⟩
    exact hunc ⟨f,(ontoMatrix_spec 0 2 1 _).mp ((bounded_univ _ _).mp hf)⟩

theorem firstUncountable_exists (M : ZFSet.{0}) (hM : Transitive M) (hV : Valid M)
    (hne : ∃ a, a ∈ M) : ∃ K, FirstUncountable M K := by
  have hT := hV.sourceT hM hne
  have hω := sourceT_omega_mem M hM hT
  have h := hV (.ex uncountableOrdinalSentence) ambient_sentence (fun _ => ZFSet.omega) (fun _ =>
    hω)
  obtain ⟨L,hL,hs⟩ := h
  have he : ∀ i, cons L (fun _ => ZFSet.omega) i ∈ M := by
    intro i
    cases i
    · exact hL
    · exact hω
  obtain ⟨hord,hunc⟩ := (uncountableOrdinalSentence_spec M hM _ he rfl).mp hs
  obtain ⟨K,hK,_⟩ := firstUncountable_below M L hM hL hord hunc
  exact ⟨K,hK⟩

theorem firstUncountable_unique_exists (M : ZFSet.{0}) (hM : Transitive M) (hV : Valid M)
    (hne : ∃ a, a ∈ M) : ∃! K, FirstUncountable M K := by
  obtain ⟨K,hK⟩ := firstUncountable_exists M hM hV hne
  exact ⟨K,hK,fun L hL => InternalCountableOrdinals.unique M L K hL hK⟩

end TuringRigidity.ValidFirstUncountable

end OAI
