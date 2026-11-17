/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OrdinalProductSets.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalOrderPresentation

/-!
# Ordinal Product Sets
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse
universe u

def ProductLess (a b x y : ZFSet.{u}) : Prop :=
  ∃ s ∈ b, ∃ t ∈ a, ∃ v ∈ b, ∃ w ∈ a,
    x = ZFSet.pair s t ∧ y = ZFSet.pair v w ∧ (s ∈ v ∨ (s = v ∧ t ∈ w))

noncomputable def productRelation (a b : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun p => ∃ x ∈ ZFSet.prod b a, ∃ y ∈ ZFSet.prod b a,
    p = ZFSet.pair x y ∧ ProductLess a b x y)
      (ZFSet.prod (ZFSet.prod b a) (ZFSet.prod b a))

theorem productRelation_on (a b : ZFSet.{u}) :
    On (ZFSet.prod b a) (productRelation a b) := fun _ h => (ZFSet.mem_sep.mp h).1

theorem pair_mem_productRelation (a b x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ productRelation a b ↔
      x ∈ ZFSet.prod b a ∧ y ∈ ZFSet.prod b a ∧ ProductLess a b x y := by
  rw [productRelation,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,s,hs,t,ht,he,h⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hs,ht,h⟩
  · rintro ⟨hx,hy,h⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨x,hx,y,hy,rfl⟩,x,hx,y,hy,rfl,h⟩

theorem productLess_pair (a b s t v w : ZFSet.{u}) :
    ProductLess a b (ZFSet.pair s t) (ZFSet.pair v w) ↔
      s ∈ b ∧ t ∈ a ∧ v ∈ b ∧ w ∈ a ∧ (s ∈ v ∨ (s = v ∧ t ∈ w)) := by
  simp only [ProductLess,ZFSet.pair_inj]
  constructor
  · rintro ⟨s',hs,t',ht,v',hv,w',hw,⟨rfl,rfl⟩,⟨rfl,rfl⟩,h⟩
    exact ⟨hs,ht,hv,hw,h⟩
  · rintro ⟨hs,ht,hv,hw,h⟩
    exact ⟨s,hs,t,ht,v,hv,w,hw,⟨rfl,rfl⟩,⟨rfl,rfl⟩,h⟩

def productLessFormula (a b x y : ℕ) : Formula :=
  .existsMem b (.existsMem (a+1) (.existsMem (b+2) (.existsMem (a+3)
    (.conj (.orderedPair (x+4) 3 2) (.conj (.orderedPair (y+4) 1 0)
      (.disj (.member 3 1) (.conj (.equal 3 1) (.member 2 0))))))))

theorem productLessFormula_eval (a b x y : ℕ) (e : ℕ → ZFSet.{u}) :
    (productLessFormula a b x y).Eval e ↔ ProductLess (e a) (e b) (e x) (e y) := by
  simp [productLessFormula,Formula.Eval,ProductLess]

def productRelationFormula : Formula :=
  .existsMem 1 (.existsMem 2 (.conj (.orderedPair 2 1 0)
    (productLessFormula 4 5 1 0)))

theorem productRelationFormula_eval (a b p : ZFSet.{u}) :
    productRelationFormula.Eval (cons p (cons (ZFSet.prod b a) (cons a (fun _ => b)))) ↔
      ∃ x ∈ ZFSet.prod b a, ∃ y ∈ ZFSet.prod b a,
        p = ZFSet.pair x y ∧ ProductLess a b x y := by
  simp [productRelationFormula,Formula.Eval,productLessFormula_eval]

theorem productRelation_mem (M a b : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (ha : a ∈ M) (hb : b ∈ M) : productRelation a b ∈ M := by
  have hd := product_mem M hM hP hU hPow hS hb ha
  let e := cons (ZFSet.prod b a) (cons a (fun _ => b))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    · exact hd
    · exact ha
    · exact hb
  have hs := sep_mem M hM hS productRelationFormula e he
    (product_mem M hM hP hU hPow hS hd hd)
  have eq : ZFSet.sep (fun p => productRelationFormula.Eval (cons p e))
      (ZFSet.prod (ZFSet.prod b a) (ZFSet.prod b a)) = productRelation a b := by
    apply ZFSet.ext; intro p
    simp only [productRelation,ZFSet.mem_sep,e,productRelationFormula_eval]
  exact eq ▸ hs

end TuringRigidity.OrdinalArithmetic

end OAI
