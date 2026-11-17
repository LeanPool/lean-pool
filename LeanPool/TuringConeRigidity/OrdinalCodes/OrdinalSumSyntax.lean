/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OrdinalSumSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalSumPresentation

/-!
# Ordinal Sum Syntax
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel
universe u

def nodeMember (a t x : ℕ) : Formula :=
  .existsMem a (.orderedPair (x+1) (t+1) 0)

theorem nodeMember_eval (a t x : ℕ) (e : ℕ → ZFSet.{u}) :
    (nodeMember a t x).Eval e ↔ ∃ s ∈ e a, e x = ZFSet.pair (e t) s := by
  simp [nodeMember,Formula.Eval]

def sumDomainMatrix (d a b z o : ℕ) : Formula :=
  .conj (.allMem d (.disj (nodeMember (a+1) (z+1) 0) (nodeMember (b+1) (o+1) 0)))
    (.conj (.allMem a (.existsMem (d+1) (.orderedPair 0 (z+2) 1)))
      (.allMem b (.existsMem (d+1) (.orderedPair 0 (o+2) 1))))

theorem sumDomainMatrix_eval (d a b z o : ℕ) (e : ℕ → ZFSet.{u})
    (hz : e z = ∅) (ho : e o = {∅}) :
    (sumDomainMatrix d a b z o).Eval e ↔ e d = sumDomain (e a) (e b) := by
  simp only [sumDomainMatrix,Formula.Eval,Formula.eval_allMem,Formula.eval_disj,
    nodeMember_eval,Formula.eval_orderedPair,cons_zero,cons_succ,hz,ho]
  change ((∀ x ∈ e d, (∃ s ∈ e a, x = leftNode s) ∨ (∃ s ∈ e b, x = rightNode s)) ∧
    (∀ s ∈ e a, ∃ x ∈ e d, x = leftNode s) ∧
    (∀ s ∈ e b, ∃ x ∈ e d, x = rightNode s)) ↔ _
  constructor
  · rintro ⟨hd,ha,hb⟩
    apply ZFSet.ext; intro x
    rw [mem_sumDomain]
    refine ⟨hd x,?_⟩
    rintro (⟨s,hs,rfl⟩|⟨s,hs,rfl⟩)
    · obtain ⟨x,hx,rfl⟩ := ha s hs; exact hx
    · obtain ⟨x,hx,rfl⟩ := hb s hs; exact hx
  · intro heq
    rw [heq]
    exact ⟨fun x hx => (mem_sumDomain _ _ _).mp hx,
      fun s hs => ⟨leftNode s,(mem_sumDomain _ _ _).mpr (Or.inl ⟨s,hs,rfl⟩),rfl⟩,
      fun s hs => ⟨rightNode s,(mem_sumDomain _ _ _).mpr (Or.inr ⟨s,hs,rfl⟩),rfl⟩⟩

def sumRelationMatrix (r d a b z o : ℕ) : Formula :=
  .conj (.allMem r (.existsMem (d+1) (.existsMem (d+2)
    (.conj (.orderedPair 2 1 0) (sumLessFormula (a+3) (b+3) (z+3) (o+3) 1 0)))))
    (.allMem d (.allMem (d+1) (.imp (sumLessFormula (a+2) (b+2) (z+2) (o+2) 1 0)
      (.pairMem 1 0 (r+2)))))

theorem sumRelationMatrix_eval (r d a b z o : ℕ) (e : ℕ → ZFSet.{u})
    (hz : e z = ∅) (ho : e o = {∅}) (hd : e d = sumDomain (e a) (e b)) :
    (sumRelationMatrix r d a b z o).Eval e ↔ e r = sumRelation (e a) (e b) := by
  simp only [sumRelationMatrix,Formula.Eval,Formula.eval_allMem,Formula.eval_orderedPair,
    Formula.eval_imp,Formula.eval_pairMem,cons_zero,cons_succ]
  have h3 (x y p : ZFSet.{u}) := sumLessFormula_eval (a+3) (b+3) (z+3) (o+3) 1 0
    (cons y (cons x (cons p e))) (by simpa using hz) (by simpa using ho)
  have h2 (x y : ZFSet.{u}) := sumLessFormula_eval (a+2) (b+2) (z+2) (o+2) 1 0
    (cons y (cons x e)) (by simpa using hz) (by simpa using ho)
  simp only [h3,h2,cons_zero,cons_succ,hd]
  constructor
  · rintro ⟨hr,hall⟩
    apply ZFSet.ext; intro p
    constructor
    · intro hp
      obtain ⟨x,hx,y,hy,rfl,hxy⟩ := hr p hp
      exact (pair_mem_sumRelation _ _ _ _).mpr ⟨hx,hy,hxy⟩
    · intro hp
      obtain ⟨_,x,hx,y,hy,rfl,hxy⟩ := ZFSet.mem_sep.mp hp
      exact hall x hx y hy hxy
  · intro heq
    rw [heq]
    exact ⟨fun p hp => (ZFSet.mem_sep.mp hp).2,
      fun x hx y hy hxy => (pair_mem_sumRelation _ _ _ _).mpr ⟨hx,hy,hxy⟩⟩

def sumMatrix (c a b d r f z o : ℕ) : Formula :=
  .conj (.allMem z (.neg (.equal 0 0)))
    (.conj (.singleton o z) (.conj (sumDomainMatrix d a b z o)
      (.conj (sumRelationMatrix r d a b z o) (orderTypeMatrix c d r f))))

theorem sumMatrix_eval (c a b d r f z o : ℕ) (e : ℕ → ZFSet.{u}) :
    (sumMatrix c a b d r f z o).Eval e ↔
      e z = ∅ ∧ e o = {∅} ∧ e d = sumDomain (e a) (e b) ∧
      e r = sumRelation (e a) (e b) ∧
      OrderTypeCertificate (e d) (e r) (e c) (e f) := by
  have hempty : (Formula.allMem z (.neg (.equal 0 0))).Eval e ↔ e z = ∅ := by
    simp only [Formula.eval_allMem,Formula.Eval,not_true_eq_false,imp_false]
    exact ⟨fun h => ZFSet.ext (fun x => by simp [h x]),fun h x => h ▸ ZFSet.notMem_empty x⟩
  simp only [sumMatrix,Formula.Eval,hempty,Formula.eval_singleton]
  apply and_congr_right; intro hz
  rw [hz]
  apply and_congr_right; intro ho
  rw [sumDomainMatrix_eval d a b z o e hz ho]
  apply and_congr_right; intro hd
  rw [sumRelationMatrix_eval r d a b z o e hz ho hd,orderTypeMatrix_eval]

noncomputable def sumSentence : SentenceForm :=
  .ex (.ex (.ex (.ex (.ex (fromBounded (sumMatrix 5 6 7 4 3 2 1 0))))))

theorem sumSentence_bound : sumSentence.bound = 3 := by rfl

theorem sumSentence_semantics (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A) :
    sumSentence.Sat (A : Set ZFSet) e ↔
      ∃ d ∈ A, ∃ r ∈ A, ∃ f ∈ A, ∃ z ∈ A, ∃ o ∈ A,
        z = ∅ ∧ o = {∅} ∧ d = sumDomain (e 1) (e 2) ∧
        r = sumRelation (e 1) (e 2) ∧ OrderTypeCertificate d r (e 0) f := by
  change (∃ d ∈ A, ∃ r ∈ A, ∃ f ∈ A, ∃ z ∈ A, ∃ o ∈ A,
    (fromBounded _).Sat _ (cons o (cons z (cons f (cons r (cons d e)))))) ↔ _
  apply exists_congr; intro d
  apply and_congr_right; intro hd
  apply exists_congr; intro r
  apply and_congr_right; intro hr
  apply exists_congr; intro f
  apply and_congr_right; intro hf
  apply exists_congr; intro z
  apply and_congr_right; intro hz
  apply exists_congr; intro o
  apply and_congr_right; intro ho
  rw [bounded_sat,Formula.absolute _ A hA _ (by
    intro i; rcases i with _|_|_|_|_|i <;> simp [cons,he,hd,hr,hf,hz,ho]),sumMatrix_eval]
  rfl

theorem sumSentence_sound (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A) (a b : Ordinal.{u})
    (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet) :
    sumSentence.Sat (A : Set ZFSet) e → e 0 = (a+b).toZFSet := by
  intro h
  obtain ⟨d,_,r,_,f,_,z,_,o,_,_,_,hd,hr,hc⟩ := (sumSentence_semantics A hA e he).mp h
  rw [ha,hb] at hd hr
  rw [hd,hr] at hc
  exact (hc.exact (sumRelation_wellFounded a b) (sumRelation_transitive a b)).trans
    (congrArg Ordinal.toZFSet (sum_orderType a b))

theorem sumSentence_spec_of_certificate (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A) (a b : Ordinal.{u})
    (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet)
    (h0 : (∅ : ZFSet.{u}) ∈ A) (h1 : ({∅} : ZFSet.{u}) ∈ A)
    (hd : sumDomain a.toZFSet b.toZFSet ∈ A) (hr : sumRelation a.toZFSet b.toZFSet ∈ A)
    (hf : ∃ f ∈ A, OrderTypeCertificate (sumDomain a.toZFSet b.toZFSet)
      (sumRelation a.toZFSet b.toZFSet) (a + b).toZFSet f) :
    sumSentence.Sat (A : Set ZFSet) e ↔ e 0 = (a+b).toZFSet := by
  refine ⟨sumSentence_sound A hA e he a b ha hb,?_⟩
  intro hc
  obtain ⟨f,hf,hcert⟩ := hf
  apply (sumSentence_semantics A hA e he).mpr
  exact ⟨_,hd,_,hr,f,hf,∅,h0,{∅},h1,rfl,rfl,by rw [ha,hb],by rw [ha,hb],hc ▸ hcert⟩

theorem sumSentence_sourceT (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) (a b : Ordinal.{u})
    (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet) :
    sumSentence.Sat (M : Set ZFSet) e ↔ e 0 = (a+b).toZFSet := by
  have haM : a.toZFSet ∈ M := ha ▸ he 1
  have hbM : b.toZFSet ∈ M := hb ▸ he 2
  have h0 := hM _ (omega_mem M hM hT.separation.finitePrefix.bounded hT.infinity) _ ZFSet.omega_zero
  obtain ⟨_,f,hf,_,hc⟩ := ordinal_add_internal M hM hT a b haM hbM
  exact sumSentence_spec_of_certificate M hM e he a b ha hb h0
    (singleton_mem M hM hT.pairing h0)
    (sumDomain_mem M _ _ hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded h0
      haM hbM)
    (sumRelation_mem M _ _ hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
      h0 haM hbM)
    ⟨f,hf,hc⟩

end TuringRigidity.OrdinalArithmetic

end OAI
