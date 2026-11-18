/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OrdinalProductSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalProductPresentation

/-!
# Ordinal Product Syntax
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel
universe u

/-- Bounded formula asserting that `d` is exactly the designated product domain. -/
def productDomainMatrix (d a b : ℕ) : Formula :=
  .conj (.allMem d (.existsMem (b+1) (.existsMem (a+2) (.orderedPair 2 1 0))))
    (.allMem b (.allMem (a+1) (.pairMem 1 0 (d+2))))

theorem productDomainMatrix_eval (d a b : ℕ) (e : ℕ → ZFSet.{u}) :
    (productDomainMatrix d a b).Eval e ↔ e d = ZFSet.prod (e b) (e a) := by
  simp only [productDomainMatrix,Formula.Eval,Formula.eval_allMem,
    Formula.eval_orderedPair,Formula.eval_pairMem,cons_zero,cons_succ]
  constructor
  · rintro ⟨hsub,hsup⟩
    apply ZFSet.ext; intro x
    constructor
    · intro hx; exact ZFSet.mem_prod.mpr (hsub x hx)
    · intro hx
      obtain ⟨s,hs,t,ht,rfl⟩ := ZFSet.mem_prod.mp hx
      exact hsup s hs t ht
  · intro heq
    rw [heq]
    exact ⟨fun x hx => ZFSet.mem_prod.mp hx,
      fun s hs t ht => ZFSet.mem_prod.mpr ⟨s,hs,t,ht,rfl⟩⟩

/-- Bounded formula asserting that `r` is exactly the designated lexicographic product
relation. -/
def productRelationMatrix (r d a b : ℕ) : Formula :=
  .conj (.allMem r (.existsMem (d+1) (.existsMem (d+2)
    (.conj (.orderedPair 2 1 0) (productLessFormula (a+3) (b+3) 1 0)))))
    (.allMem d (.allMem (d+1) (.imp (productLessFormula (a+2) (b+2) 1 0)
      (.pairMem 1 0 (r+2)))))

theorem productRelationMatrix_eval (r d a b : ℕ) (e : ℕ → ZFSet.{u})
    (hd : e d = ZFSet.prod (e b) (e a)) :
    (productRelationMatrix r d a b).Eval e ↔ e r = productRelation (e a) (e b) := by
  simp only [productRelationMatrix,Formula.Eval,Formula.eval_allMem,Formula.eval_orderedPair,
    Formula.eval_imp,Formula.eval_pairMem,cons_zero,cons_succ]
  have h3 (x y p : ZFSet.{u}) := productLessFormula_eval (a+3) (b+3) 1 0
    (cons y (cons x (cons p e)))
  have h2 (x y : ZFSet.{u}) := productLessFormula_eval (a+2) (b+2) 1 0
    (cons y (cons x e))
  simp only [h3,h2,cons_zero,cons_succ,hd]
  constructor
  · rintro ⟨hr,hall⟩
    apply ZFSet.ext; intro p
    constructor
    · intro hp
      obtain ⟨x,hx,y,hy,rfl,hxy⟩ := hr p hp
      exact (pair_mem_productRelation _ _ _ _).mpr ⟨hx,hy,hxy⟩
    · intro hp
      obtain ⟨_,x,hx,y,hy,rfl,hxy⟩ := ZFSet.mem_sep.mp hp
      exact hall x hx y hy hxy
  · intro heq
    rw [heq]
    exact ⟨fun p hp => (ZFSet.mem_sep.mp hp).2,
      fun x hx y hy hxy => (pair_mem_productRelation _ _ _ _).mpr ⟨hx,hy,hxy⟩⟩

/-- Bounded formula combining the product domain, product relation, and ordinal order-type
certificate. -/
def productMatrix (c a b d r f : ℕ) : Formula :=
  .conj (productDomainMatrix d a b)
    (.conj (productRelationMatrix r d a b) (orderTypeMatrix c d r f))

theorem productMatrix_eval (c a b d r f : ℕ) (e : ℕ → ZFSet.{u}) :
    (productMatrix c a b d r f).Eval e ↔
      e d = ZFSet.prod (e b) (e a) ∧ e r = productRelation (e a) (e b) ∧
      OrderTypeCertificate (e d) (e r) (e c) (e f) := by
  simp only [productMatrix,Formula.Eval,productDomainMatrix_eval]
  apply and_congr_right; intro hd
  rw [productRelationMatrix_eval r d a b e hd,orderTypeMatrix_eval]

/-- A full formula defining an ordinal product through its lexicographic order-type
presentation. -/
noncomputable def productSentence : SentenceForm :=
  .ex (.ex (.ex (fromBounded (productMatrix 3 4 5 2 1 0))))

theorem productSentence_bound : productSentence.bound = 3 := by rfl

theorem productSentence_semantics (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A) :
    productSentence.Sat (A : Set ZFSet) e ↔
      ∃ d ∈ A, ∃ r ∈ A, ∃ f ∈ A,
        d = ZFSet.prod (e 2) (e 1) ∧ r = productRelation (e 1) (e 2) ∧
          OrderTypeCertificate d r (e 0) f := by
  change (∃ d ∈ A, ∃ r ∈ A, ∃ f ∈ A,
    (fromBounded _).Sat _ (cons f (cons r (cons d e)))) ↔ _
  apply exists_congr; intro d
  apply and_congr_right; intro hd
  apply exists_congr; intro r
  apply and_congr_right; intro hr
  apply exists_congr; intro f
  apply and_congr_right; intro hf
  rw [bounded_sat,Formula.absolute _ A hA _ (by
    intro i; rcases i with _|_|_|i <;> simp [cons,he,hd,hr,hf]),productMatrix_eval]
  rfl

theorem productSentence_sound (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A) (a b : Ordinal.{u})
    (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet) :
    productSentence.Sat (A : Set ZFSet) e → e 0 = (a*b).toZFSet := by
  intro h
  obtain ⟨d,_,r,_,f,_,hd,hr,hc⟩ := (productSentence_semantics A hA e he).mp h
  rw [ha,hb] at hd hr
  rw [hd,hr] at hc
  exact (hc.exact (productRelation_wellFounded a b) (productRelation_transitive a b)).trans
    (congrArg Ordinal.toZFSet (product_orderType a b))

theorem productSentence_spec_of_certificate (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A) (a b : Ordinal.{u})
    (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet)
    (hd : ZFSet.prod b.toZFSet a.toZFSet ∈ A)
    (hr : productRelation a.toZFSet b.toZFSet ∈ A)
    (hf : ∃ f ∈ A, OrderTypeCertificate (ZFSet.prod b.toZFSet a.toZFSet)
      (productRelation a.toZFSet b.toZFSet) (a * b).toZFSet f) :
    productSentence.Sat (A : Set ZFSet) e ↔ e 0 = (a*b).toZFSet := by
  refine ⟨productSentence_sound A hA e he a b ha hb,?_⟩
  intro hc
  obtain ⟨f,hf,hcert⟩ := hf
  apply (productSentence_semantics A hA e he).mpr
  exact ⟨_,hd,_,hr,f,hf,by rw [ha,hb],by rw [ha,hb],hc ▸ hcert⟩

theorem productSentence_sourceT (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) (a b : Ordinal.{u})
    (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet) :
    productSentence.Sat (M : Set ZFSet) e ↔ e 0 = (a*b).toZFSet := by
  have haM : a.toZFSet ∈ M := ha ▸ he 1
  have hbM : b.toZFSet ∈ M := hb ▸ he 2
  obtain ⟨_,f,hf,_,hc⟩ := ordinal_mul_internal M hM hT a b haM hbM
  exact productSentence_spec_of_certificate M hM e he a b ha hb
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hbM haM)
    (productRelation_mem M _ _ hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded haM hbM)
    ⟨f,hf,hc⟩

end TuringRigidity.OrdinalArithmetic

end OAI
