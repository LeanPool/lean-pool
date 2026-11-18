/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ModelProducts.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.BoundedSetTheory

/-!
# Model Products
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open Set TransitiveNameModel
universe u

theorem binary_union_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : Union M) {a b : ZFSet.{u}} (ha : a ∈ M) (hb : b ∈ M) :
    a ∪ b ∈ M := by
  simpa only [ZFSet.sUnion_pair] using union_mem M hM hU (pair_mem M hM hP ha hb)

theorem pair_bound (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : Union M) (hPow : PowerSet M)
    {a b : ZFSet.{u}} (ha : a ∈ M) (hb : b ∈ M) :
    ∃ c ∈ M, ∀ x ∈ a, ∀ y ∈ b, ZFSet.pair x y ∈ c := by
  obtain ⟨q,hq,hqdef⟩ := internal_power M hM hPow (binary_union_mem M hM hP hU ha hb)
  obtain ⟨r,hr,hrdef⟩ := internal_power M hM hPow hq
  refine ⟨r,hr,fun x hx y hy => ?_⟩
  have hxM := hM a ha x hx
  have hyM := hM b hb y hy
  apply (hrdef _).mpr
  refine ⟨orderedPair_mem M hM hP hxM hyM,?_⟩
  intro z hz
  change z ∈ ({({x} : ZFSet.{u}),({x,y} : ZFSet.{u})} : ZFSet.{u}) at hz
  rcases ZFSet.mem_pair.mp hz with rfl|rfl
  · apply (hqdef _).mpr
    refine ⟨singleton_mem M hM hP hxM,?_⟩
    intro t ht
    rw [ZFSet.mem_singleton] at ht
    exact ht ▸ ZFSet.mem_union.mpr (Or.inl hx)
  · apply (hqdef _).mpr
    refine ⟨pair_mem M hM hP hxM hyM,?_⟩
    intro t ht
    rcases ZFSet.mem_pair.mp ht with rfl|rfl
    · exact ZFSet.mem_union.mpr (Or.inl hx)
    · exact ZFSet.mem_union.mpr (Or.inr hy)

/-- Bounded formula describing membership in a Cartesian product through an ordered-pair
witness. -/
def productFormula : Formula := .existsMem 1 (.existsMem 3 (.orderedPair 2 1 0))

theorem eval_productFormula (z a b : ZFSet.{u}) (env : ℕ → ZFSet.{u}) :
    productFormula.Eval (cons z (cons a (cons b env))) ↔ z ∈ ZFSet.prod a b := by
  simp only [productFormula,Formula.Eval,cons_succ,cons_zero,Formula.eval_orderedPair]
  exact ZFSet.mem_prod.symm

theorem product_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : Union M) (hPow : PowerSet M) (hS : Separation M)
    {a b : ZFSet.{u}} (ha : a ∈ M) (hb : b ∈ M) : ZFSet.prod a b ∈ M := by
  obtain ⟨c,hc,hbound⟩ := pair_bound M hM hP hU hPow ha hb
  let env := cons a (cons b (fun _ => a))
  have he : ∀ i, env i ∈ M := by
    intro i
    cases i with
    | zero => exact ha
    | succ i => cases i <;> assumption
  have hs := sep_mem M hM hS productFormula env he hc
  have hprod : ZFSet.sep (fun z => productFormula.Eval (cons z env)) c = ZFSet.prod a b := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    change (z ∈ c ∧ productFormula.Eval (cons z (cons a (cons b (fun _ => a))))) ↔ _
    rw [eval_productFormula]
    constructor
    · exact And.right
    · intro hz
      obtain ⟨x,hx,y,hy,rfl⟩ := ZFSet.mem_prod.mp hz
      exact ⟨hbound x hx y hy,ZFSet.mem_prod.mpr ⟨x,hx,y,hy,rfl⟩⟩
  exact hprod ▸ hs

end TuringRigidity.BoundedSetTheory

end OAI
