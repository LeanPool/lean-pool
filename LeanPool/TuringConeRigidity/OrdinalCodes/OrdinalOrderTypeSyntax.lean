/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OrdinalOrderTypeSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalOrderType
public import LeanPool.TuringConeRigidity.Constructibility.RelativeModelSyntax
public import LeanPool.TuringConeRigidity.SetModels.ElementarySatisfaction

/-!
# Ordinal Order Type Syntax
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory ElementaryModel RelativeConstructible
universe u

/-- A collapse graph onto an ordinal, with every ordinal element in its range. -/
def OrderTypeCertificate (d r a f : ZFSet.{u}) : Prop :=
  a.IsOrdinal ∧ Graph d r d a f ∧
    ∀ z ∈ a, ∃ x ∈ d, ZFSet.pair x z ∈ f

theorem OrderTypeCertificate.exact {d r a f : ZFSet.{u}}
    (wf : WellFounded (Rel d r)) (ht : TransitiveOn d r)
    (hc : OrderTypeCertificate d r a f) : a = (orderType d r wf).toZFSet := by
  rw [orderType_toZFSet wf ht]
  apply ZFSet.ext; intro z
  rw [mem_ordinalRange]
  constructor
  · intro hz
    obtain ⟨x,hx,hxz⟩ := hc.2.2 z hz
    exact ⟨x,hx,hc.2.1.correct wf x hx z hz hxz⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨z,hz,hxz,_⟩ := hc.2.1.2.2.2.1 x hx
    exact hc.2.1.correct wf x hx z hz hxz ▸ hz

theorem orderTypeCertificate_exists (M d r : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hd : d ∈ M) (hr : r ∈ M)
    (wf : WellFounded (Rel d r)) (ht : TransitiveOn d r) :
    (orderType d r wf).toZFSet ∈ M ∧
      ∃ f ∈ M, OrderTypeCertificate d r (orderType d r wf).toZFSet f := by
  obtain ⟨ha,f,hf,hg,ho⟩ := orderType_internal M d r hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hd hr wf ht
  exact ⟨ha,f,hf,ZFSet.isOrdinal_toZFSet _,hg,ho⟩

/-- Bounded formula expressing an ordinal range and a surjective collapse graph. -/
def orderTypeMatrix (a d r f : ℕ) : Formula :=
  .conj (ordinalFormula a) (.conj (Code.graph d r d a f)
    (Formula.allMem a (.existsMem (d+1) (Formula.pairMem 0 1 (f+2)))))

theorem orderTypeMatrix_eval (a d r f : ℕ) (e : ℕ → ZFSet.{u}) :
    (orderTypeMatrix a d r f).Eval e ↔ OrderTypeCertificate (e d) (e r) (e a) (e f) := by
  simp only [orderTypeMatrix,OrderTypeCertificate,Formula.Eval,eval_ordinalFormula,
    Code.eval_graph,Formula.eval_allMem,Formula.eval_pairMem,cons_zero,cons_succ]

/-- A full formula asserting existence of a collapse graph onto the designated ordinal. -/
noncomputable def orderTypeSentence : SentenceForm :=
  .ex (fromBounded (orderTypeMatrix 1 2 3 0))

theorem orderTypeSentence_bound : orderTypeSentence.bound = 3 := by rfl

theorem orderTypeSentence_semantics (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A) :
    orderTypeSentence.Sat (A : Set ZFSet) e ↔
      ∃ f ∈ A, OrderTypeCertificate (e 1) (e 2) (e 0) f := by
  change (∃ f ∈ A, (fromBounded _).Sat _ (cons f e)) ↔ _
  apply exists_congr; intro f
  apply and_congr_right; intro hf
  rw [bounded_sat,Formula.absolute _ A hA _
    (by intro i; cases i <;> simp [cons,hf,he]),orderTypeMatrix_eval]
  rfl

theorem orderTypeSentence_sound (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A)
    (wf : WellFounded (Rel (e 1) (e 2))) (ht : TransitiveOn (e 1) (e 2)) :
    orderTypeSentence.Sat (A : Set ZFSet) e →
      e 0 = (orderType (e 1) (e 2) wf).toZFSet := by
  intro h
  obtain ⟨f,_,hf⟩ := (orderTypeSentence_semantics A hA e he).mp h
  exact hf.exact wf ht

theorem orderTypeSentence_spec_of_certificate (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A)
    (wf : WellFounded (Rel (e 1) (e 2))) (ht : TransitiveOn (e 1) (e 2))
    (hw : ∃ f ∈ A, OrderTypeCertificate (e 1) (e 2)
      (orderType (e 1) (e 2) wf).toZFSet f) :
    orderTypeSentence.Sat (A : Set ZFSet) e ↔
      e 0 = (orderType (e 1) (e 2) wf).toZFSet := by
  refine ⟨orderTypeSentence_sound A hA e he wf ht,?_⟩
  intro heq
  apply (orderTypeSentence_semantics A hA e he).mpr
  simpa only [heq] using hw

theorem orderTypeSentence_sourceT (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (wf : WellFounded (Rel (e 1) (e 2))) (ht : TransitiveOn (e 1) (e 2)) :
    orderTypeSentence.Sat (M : Set ZFSet) e ↔
      e 0 = (orderType (e 1) (e 2) wf).toZFSet :=
  orderTypeSentence_spec_of_certificate M hM e he wf ht
    (orderTypeCertificate_exists M _ _ hM hT (he 1) (he 2) wf ht).2

end TuringRigidity.RelationCollapse

end OAI
