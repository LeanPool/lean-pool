/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalMinimalSelector.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.SourceTheory

/-!
# Internal Minimal Selector
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace InternalWellOrder

/-- The element `x` belongs to `a` and has no predecessor in `a` under `r`. -/
def MinimalIn (r a x : ZFSet.{u}) : Prop := x ∈ a ∧ ∀ y ∈ a, ¬ ZFSet.pair y x ∈ r

/-- Every nonempty subset of `d` belonging to `M` has an `r`-minimal element. -/
def InternallyWellFounded (M d r : ZFSet.{u}) : Prop :=
  ∀ a ∈ M, a ⊆ d → (∃ x, x ∈ a) → ∃ x, MinimalIn r a x

/-- An `r`-minimal member of `a` chosen at the earliest index of the enumeration graph `F`. -/
def LeastMinimal (δ F r a x : ZFSet.{u}) : Prop := MinimalIn r a x ∧
  ∃ i ∈ δ, ZFSet.pair i x ∈ F ∧
    ∀ j ∈ i, ∀ y ∈ a, ZFSet.pair j y ∈ F → ¬ MinimalIn r a y

theorem leastMinimal_exists {δ d F r a : ZFSet.{u}} (hδ : δ.IsOrdinal)
    (honto : ∀ x ∈ d, ∃ i ∈ δ, ZFSet.pair i x ∈ F) (ha : a ⊆ d)
    (hm : ∃ x, MinimalIn r a x) : ∃ x, LeastMinimal δ F r a x := by
  classical
  have find (i : ZFSet.{u}) : i ∈ δ → (∃ x, MinimalIn r a x ∧ ZFSet.pair i x ∈ F) →
      ∃ x, LeastMinimal δ F r a x := by
    induction i using ZFSet.inductionOn with
    | h i ih =>
      intro hi hx
      by_cases he : ∃ j ∈ i, ∃ y, MinimalIn r a y ∧ ZFSet.pair j y ∈ F
      · obtain ⟨j,hji,hy⟩ := he
        exact ih j hji (hδ.subset_of_mem hi hji) hy
      · obtain ⟨x,hx,hix⟩ := hx
        exact ⟨x,hx,i,hi,hix,fun j hj y _ hjy hmy => he ⟨j,hj,y,hmy,hjy⟩⟩
  obtain ⟨x,hx⟩ := hm
  obtain ⟨i,hi,hix⟩ := honto x (ha hx.1)
  exact find i hi ⟨x,hx,hix⟩

theorem LeastMinimal.unique {δ d F r a x y : ZFSet.{u}} (hδ : δ.IsOrdinal)
    (hF : TransitiveNameModel.FunctionGraph δ d F)
    (hx : LeastMinimal δ F r a x) (hy : LeastMinimal δ F r a y) : x = y := by
  obtain ⟨hx,i,hi,hix,hleast⟩ := hx
  obtain ⟨hy,j,hj,hjy,hleast'⟩ := hy
  rcases (hδ.mem hi).mem_trichotomous (hδ.mem hj) with hij|he|hji
  · exact False.elim (hleast' i hij x hx.1 hix hx)
  · subst j; exact hF.functional hi hix hjy
  · exact False.elim (hleast j hji y hy.1 hjy hy)

open Formula

/-- Bounded formula expressing membership and relation-minimality inside `a`. -/
def minimalInFormula (r a x : ℕ) : Formula :=
  .conj (.member x a) (allMem a (.neg (pairMem 0 (x+1) (r+1))))

theorem eval_minimalInFormula (r a x : ℕ) (e : ℕ → ZFSet.{u}) :
    (minimalInFormula r a x).Eval e ↔ MinimalIn (e r) (e a) (e x) := by
  simp only [minimalInFormula,MinimalIn,Formula.Eval,eval_allMem,eval_pairMem,cons_zero,cons_succ]

/-- Bounded formula expressing the earliest enumerated relation-minimal member of a set. -/
def leastMinimalFormula (δ F r a x : ℕ) : Formula := .conj (minimalInFormula r a x)
  (.existsMem δ (.conj (pairMem 0 (x+1) (F+1))
    (allMem 0 (allMem (a+2) (imp (pairMem 1 0 (F+3))
      (.neg (minimalInFormula (r+3) (a+3) 0)))))))

theorem eval_leastMinimalFormula (δ F r a x : ℕ) (e : ℕ → ZFSet.{u}) :
    (leastMinimalFormula δ F r a x).Eval e ↔ LeastMinimal (e δ) (e F) (e r) (e a) (e x) := by
  simp only [leastMinimalFormula,LeastMinimal,Formula.Eval,eval_minimalInFormula,
    eval_pairMem,eval_allMem,eval_imp,cons_zero,cons_succ]

/-- Bounded formula describing the graph of the earliest-minimal-element selector. -/
def minimalSelectorFormula : Formula := .existsMem 1 (.existsMem 3
  (.conj (.orderedPair 2 1 0) (leastMinimalFormula 5 6 7 1 0)))

theorem internal_minimal_selector (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {d r : ZFSet.{u}} (hd : d ∈ M) (hr : r ∈ M) (hw : InternallyWellFounded M d r) :
    ∃ q ∈ M, ∃ s ∈ M, ChoiceGraph q s ∧
      (∀ a, a ∈ q ↔ a ∈ M ∧ a ⊆ d ∧ ∃ x, x ∈ a) ∧
      ∀ a x, ZFSet.pair a x ∈ s → MinimalIn r a x := by
  have hS := hT.separation.finitePrefix
  obtain ⟨q,hq,_,_,_,hqdef⟩ := internal_selector M hM hT.powerSet hS.bounded hT.choice hd
  obtain ⟨δ,hδM,hδ,F,hFM,hF,honto,_⟩ := internal_ordinal_enumeration M hM
    hT.pairing hT.union hT.powerSet hS hT.replacement.finitePrefix hT.infinity hT.choice hd
  let e := cons q (cons d (cons δ (cons F (fun _ => r))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hq
    rcases i with _ | i
    · exact hd
    rcases i with _ | i
    · exact hδM
    rcases i with _ | i
    · exact hFM
    exact hr
  let s := ZFSet.sep (fun z => minimalSelectorFormula.Eval (cons z e)) (ZFSet.prod q d)
  have hs : s ∈ M := sep_mem M hM hS.bounded _ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hS.bounded hq hd)
  have hmem (z : ZFSet.{u}) : z ∈ s ↔
      ∃ a ∈ q, ∃ x ∈ a, z = ZFSet.pair a x ∧ LeastMinimal δ F r a x := by
    simp only [s,ZFSet.mem_sep,minimalSelectorFormula,Formula.Eval,eval_orderedPair,
      eval_leastMinimalFormula,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨_,a,ha,x,_,hz,hm⟩; exact ⟨a,ha,x,hm.1.1,hz,hm⟩
    · rintro ⟨a,ha,x,hx,rfl,hm⟩
      have hxd := ((hqdef a).mp ha).2.1 hx
      exact ⟨ZFSet.mem_prod.mpr ⟨a,ha,x,hxd,rfl⟩,a,ha,x,hxd,rfl,hm⟩
  refine ⟨q,hq,s,hs,⟨?_,?_⟩,hqdef,?_⟩
  · intro z hz
    obtain ⟨a,ha,x,hx,hz,_⟩ := (hmem z).mp hz
    exact ⟨a,ha,x,hx,hz⟩
  · intro a ha
    obtain ⟨haM,had,hane⟩ := (hqdef a).mp ha
    obtain ⟨x,hx⟩ := leastMinimal_exists hδ honto had (hw a haM had hane)
    refine ⟨x,hx.1.1,(hmem _).mpr ⟨a,ha,x,hx.1.1,rfl,hx⟩,?_⟩
    intro y _ hy
    obtain ⟨a',_,y',_,heq,hy'⟩ := (hmem _).mp hy
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp heq
    exact hy'.unique hδ hF hx
  · intro a x hax
    obtain ⟨a',_,x',_,heq,hx⟩ := (hmem _).mp hax
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp heq
    exact hx.1

end InternalWellOrder
end TuringRigidity.BoundedSetTheory

end OAI
