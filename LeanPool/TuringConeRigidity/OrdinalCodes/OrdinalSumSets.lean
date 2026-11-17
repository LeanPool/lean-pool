/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OrdinalSumSets.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalOrderPresentation

/-!
# Ordinal Sum Sets
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse
universe u

def leftNode (x : ZFSet.{u}) : ZFSet.{u} := ZFSet.pair ∅ x
def rightNode (x : ZFSet.{u}) : ZFSet.{u} := ZFSet.pair {∅} x

theorem leftNode_inj {x y : ZFSet.{u}} : leftNode x = leftNode y ↔ x = y := by
  simp [leftNode, ZFSet.pair_inj]

theorem rightNode_inj {x y : ZFSet.{u}} : rightNode x = rightNode y ↔ x = y := by
  simp [rightNode, ZFSet.pair_inj]

theorem leftNode_ne_rightNode (x y : ZFSet.{u}) : leftNode x ≠ rightNode y := by
  intro h
  have hz := (ZFSet.pair_inj.mp h).1
  have hm : (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) := ZFSet.mem_singleton.mpr rfl
  rw [← hz] at hm
  exact ZFSet.notMem_empty _ hm

noncomputable def sumDomain (a b : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod {∅} a ∪ ZFSet.prod {{∅}} b

theorem mem_sumDomain (a b x : ZFSet.{u}) : x ∈ sumDomain a b ↔
    (∃ s ∈ a, x = leftNode s) ∨ (∃ t ∈ b, x = rightNode t) := by
  simp only [sumDomain, ZFSet.mem_union, ZFSet.mem_prod, ZFSet.mem_singleton,
    exists_eq_left, leftNode, rightNode]

def SumLess (a b x y : ZFSet.{u}) : Prop :=
  (∃ s ∈ a, ∃ t ∈ a, x = leftNode s ∧ y = leftNode t ∧ s ∈ t) ∨
  (∃ s ∈ a, ∃ t ∈ b, x = leftNode s ∧ y = rightNode t) ∨
  (∃ s ∈ b, ∃ t ∈ b, x = rightNode s ∧ y = rightNode t ∧ s ∈ t)

noncomputable def sumRelation (a b : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun p => ∃ x ∈ sumDomain a b, ∃ y ∈ sumDomain a b,
    p = ZFSet.pair x y ∧ SumLess a b x y) (ZFSet.prod (sumDomain a b) (sumDomain a b))

theorem sumRelation_on (a b : ZFSet.{u}) : On (sumDomain a b) (sumRelation a b) :=
  fun _ h => (ZFSet.mem_sep.mp h).1

theorem pair_mem_sumRelation (a b x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ sumRelation a b ↔
      x ∈ sumDomain a b ∧ y ∈ sumDomain a b ∧ SumLess a b x y := by
  rw [sumRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_,s,hs,t,ht,he,h⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hs,ht,h⟩
  · rintro ⟨hx,hy,h⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨x,hx,y,hy,rfl⟩,x,hx,y,hy,rfl,h⟩

def taggedClause (a b t v x y : ℕ) (cmp : Bool) : Formula :=
  .existsMem a (.existsMem (b+1)
    (.conj (.orderedPair (x+2) (t+2) 1)
      (.conj (.orderedPair (y+2) (v+2) 0)
        (if cmp then .member 1 0 else .equal 0 0))))

theorem taggedClause_eval (a b t v x y : ℕ) (cmp : Bool) (e : ℕ → ZFSet.{u}) :
    (taggedClause a b t v x y cmp).Eval e ↔
      ∃ s ∈ e a, ∃ q ∈ e b, e x = ZFSet.pair (e t) s ∧
        e y = ZFSet.pair (e v) q ∧ (if cmp then s ∈ q else True) := by
  cases cmp <;> simp [taggedClause, Formula.Eval]

def sumLessFormula (a b z o x y : ℕ) : Formula :=
  .disj (taggedClause a a z z x y true)
    (.disj (taggedClause a b z o x y false) (taggedClause b b o o x y true))

theorem sumLessFormula_eval (a b z o x y : ℕ) (e : ℕ → ZFSet.{u})
    (hz : e z = ∅) (ho : e o = {∅}) :
    (sumLessFormula a b z o x y).Eval e ↔ SumLess (e a) (e b) (e x) (e y) := by
  simp [sumLessFormula, taggedClause_eval, hz, ho, SumLess, leftNode, rightNode]

def sumRelationFormula : Formula :=
  .existsMem 1 (.existsMem 2 (.conj (.orderedPair 2 1 0)
    (sumLessFormula 4 5 6 7 1 0)))

theorem sumRelationFormula_eval (a b p : ZFSet.{u}) :
    sumRelationFormula.Eval
      (cons p (cons (sumDomain a b) (cons a (cons b (cons ∅ (fun _ => {∅})))))) ↔
      ∃ x ∈ sumDomain a b, ∃ y ∈ sumDomain a b,
        p = ZFSet.pair x y ∧ SumLess a b x y := by
  simp only [sumRelationFormula, Formula.Eval, Formula.eval_orderedPair,
    cons_zero, cons_succ]
  apply exists_congr; intro x
  apply and_congr_right; intro _
  apply exists_congr; intro y
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  exact sumLessFormula_eval _ _ _ _ _ _ _ rfl rfl

theorem sumDomain_mem (M a b : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (h0 : (∅ : ZFSet.{u}) ∈ M) (ha : a ∈ M) (hb : b ∈ M) :
    sumDomain a b ∈ M := by
  have h1 := singleton_mem M hM hP h0
  exact binary_union_mem M hM hP hU
    (product_mem M hM hP hU hPow hS h1 ha)
    (product_mem M hM hP hU hPow hS (singleton_mem M hM hP h1) hb)

theorem sumRelation_mem (M a b : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (h0 : (∅ : ZFSet.{u}) ∈ M) (ha : a ∈ M) (hb : b ∈ M) :
    sumRelation a b ∈ M := by
  have hd := sumDomain_mem M a b hM hP hU hPow hS h0 ha hb
  have h1 := singleton_mem M hM hP h0
  let e := cons (sumDomain a b) (cons a (cons b (cons ∅ (fun _ => {∅}))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hd
    rcases i with _ | i
    · exact ha
    rcases i with _ | i
    · exact hb
    rcases i with _ | i
    · exact h0
    exact h1
  have hs := sep_mem M hM hS sumRelationFormula e he
    (product_mem M hM hP hU hPow hS hd hd)
  have eq : ZFSet.sep (fun p => sumRelationFormula.Eval (cons p e))
      (ZFSet.prod (sumDomain a b) (sumDomain a b)) = sumRelation a b := by
    apply ZFSet.ext; intro p
    simp only [sumRelation, ZFSet.mem_sep, e, sumRelationFormula_eval]
  exact eq ▸ hs

end TuringRigidity.OrdinalArithmetic

end OAI
