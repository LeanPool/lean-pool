/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ChoiceFromOrdinalCover.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalOrdinalEnumeration

/-!
# Choice From Ordinal Cover
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace InternalWellOrder

def LeastValue (δ V F H x y : ZFSet.{u}) : Prop := y ∈ x ∧
  ∃ i ∈ δ, ∃ v ∈ V, ZFSet.pair i v ∈ F ∧ ZFSet.pair v y ∈ H ∧
    ∀ j ∈ i, ∀ w ∈ V, ∀ z ∈ x, ¬ (ZFSet.pair j w ∈ F ∧ ZFSet.pair w z ∈ H)

theorem leastValue_exists {δ V F H x : ZFSet.{u}} (hδ : δ.IsOrdinal)
    (hex : ∃ i ∈ δ, ∃ v ∈ V, ∃ y ∈ x, ZFSet.pair i v ∈ F ∧ ZFSet.pair v y ∈ H) :
    ∃ y ∈ x, LeastValue δ V F H x y := by
  classical
  have minimal (i : ZFSet.{u}) : i ∈ δ →
      (∃ v ∈ V, ∃ y ∈ x, ZFSet.pair i v ∈ F ∧ ZFSet.pair v y ∈ H) →
      ∃ y ∈ x, LeastValue δ V F H x y := by
    induction i using ZFSet.inductionOn with
    | h i ih =>
      intro hi hs
      by_cases hp : ∃ j ∈ i, ∃ w ∈ V, ∃ z ∈ x, ZFSet.pair j w ∈ F ∧ ZFSet.pair w z ∈ H
      · obtain ⟨j,hji,hw⟩ := hp
        exact ih j hji (hδ.subset_of_mem hi hji) hw
      · obtain ⟨v,hv,y,hy,hiv,hvy⟩ := hs
        exact ⟨y,hy,hy,i,hi,v,hv,hiv,hvy,fun j hj w hw z hz hp' => hp ⟨j,hj,w,hw,z,hz,hp'⟩⟩
  obtain ⟨i,hi,hs⟩ := hex
  exact minimal i hi hs

theorem LeastValue.unique {δ V F H x y z : ZFSet.{u}} (hδ : δ.IsOrdinal)
    (hF : TransitiveNameModel.FunctionGraph δ V F) (hH : FiniteTerm.Functional H)
    (hy : LeastValue δ V F H x y) (hz : LeastValue δ V F H x z) : y = z := by
  obtain ⟨hyx,i,hi,v,hv,hiv,hvy,hmin⟩ := hy
  obtain ⟨hzx,j,hj,w,hw,hjw,hwz,hmin'⟩ := hz
  rcases (hδ.mem hi).mem_trichotomous (hδ.mem hj) with hij|he|hji
  · exact False.elim (hmin' i hij v hv y hyx ⟨hiv,hvy⟩)
  · subst j
    have hvw := hF.functional hi hiv hjw
    subst w
    exact hH v y z hvy hwz
  · exact False.elim (hmin j hji w hw z hzx ⟨hjw,hwz⟩)

open Formula
def leastValueFormula (δ V F H x y : ℕ) : Formula := .conj (.member y x)
  (.existsMem δ (.existsMem (V+1) (.conj (.pairMem 1 0 (F+2))
    (.conj (.pairMem 0 (y+2) (H+2))
      (allMem 1 (allMem (V+3) (allMem (x+4)
        (.neg (.conj (.pairMem 2 1 (F+5)) (.pairMem 1 0 (H+5)))))))))))

theorem eval_leastValueFormula (δ V F H x y : ℕ) (e : ℕ → ZFSet.{u}) :
    (leastValueFormula δ V F H x y).Eval e ↔
      LeastValue (e δ) (e V) (e F) (e H) (e x) (e y) := by
  simp only [leastValueFormula,LeastValue,Formula.Eval,eval_pairMem,eval_allMem,cons_zero,cons_succ]

def selectionFormula : Formula := .existsMem 1 (.existsMem 3
  (.conj (.orderedPair 2 1 0) (leastValueFormula 5 6 7 8 1 0)))

theorem internal_choice_of_ordinal_cover (E : ZFSet.{u}) (hE : Transitive E)
    (hP : Pairing E) (hU : BoundedSetTheory.Union E) (hPow : PowerSet E) (hS : Separation E)
    {a δ V F H : ZFSet.{u}} (ha : a ∈ E) (hδE : δ ∈ E) (hV : V ∈ E) (hFE : F ∈ E) (hHE : H ∈ E)
    (hδ : δ.IsOrdinal) (hF : TransitiveNameModel.FunctionGraph δ V F) (hH : FiniteTerm.Functional H)
    (hcover : ∀ x ∈ a, ∃ i ∈ δ, ∃ v ∈ V, ∃ y ∈ x, ZFSet.pair i v ∈ F ∧ ZFSet.pair v y ∈ H) :
    ∃ f ∈ E, ChoiceGraph a f := by
  let u := ZFSet.sUnion a
  have hu : u ∈ E := union_mem E hE hU ha
  let e := cons a (cons u (cons δ (cons V (cons F (fun _ => H)))))
  have he : ∀ i, e i ∈ E := by
    intro i
    rcases i with _ | i
    · exact ha
    rcases i with _ | i
    · exact hu
    rcases i with _ | i
    · exact hδE
    rcases i with _ | i
    · exact hV
    rcases i with _ | i
    · exact hFE
    exact hHE
  let f := ZFSet.sep (fun z => selectionFormula.Eval (cons z e)) (ZFSet.prod a u)
  have hf : f ∈ E := sep_mem E hE hS selectionFormula e he (product_mem E hE hP hU hPow hS ha hu)
  have hmem (z : ZFSet.{u}) : z ∈ f ↔
      ∃ x ∈ a, ∃ y ∈ x, z = ZFSet.pair x y ∧ LeastValue δ V F H x y := by
    simp only [f,ZFSet.mem_sep,selectionFormula,Formula.Eval,eval_orderedPair,
      eval_leastValueFormula,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨_,x,hx,y,_,hz,hmin⟩
      exact ⟨x,hx,y,hmin.1,hz,hmin⟩
    · rintro ⟨x,hx,y,hy,rfl,hmin⟩
      have hyu : y ∈ u := ZFSet.mem_sUnion.mpr ⟨x,hx,hy⟩
      exact ⟨ZFSet.mem_prod.mpr ⟨x,hx,y,hyu,rfl⟩,x,hx,y,hyu,rfl,hmin⟩
  refine ⟨f,hf,?_,?_⟩
  · intro z hz
    obtain ⟨x,hx,y,hy,hz,_⟩ := (hmem z).mp hz
    exact ⟨x,hx,y,hy,hz⟩
  · intro x hx
    obtain ⟨y,hy,hmin⟩ := leastValue_exists hδ (hcover x hx)
    refine ⟨y,hy,(hmem _).mpr ⟨x,hx,y,hy,rfl,hmin⟩,?_⟩
    intro z _ hz
    obtain ⟨x',_,z',_,heq,hmin'⟩ := (hmem _).mp hz
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp heq
    exact hmin'.unique hδ hF hH hmin

end InternalWellOrder
end TuringRigidity.BoundedSetTheory

end OAI
