/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ChoiceTraceFormula.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ChoiceTrace

/-!
# Choice Trace Formula
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace InternalWellOrder
open Formula

def remainingFormula (a f i r : ℕ) : Formula :=
  .conj (.subset r a) (.allMem a (.iff (.member 0 (r+1))
    (.neg (.existsMem (i+1) (.pairMem 0 1 (f+2))))))

theorem eval_remainingFormula (a f i r : ℕ) (e : ℕ → ZFSet.{u}) :
    (remainingFormula a f i r).Eval e ↔ Remaining (e a) (e f) (e i) (e r) := by
  simp only [remainingFormula,Remaining,Formula.Eval,eval_subset,eval_allMem,eval_iff,
    eval_pairMem,cons_zero,cons_succ]

def traceFormula (α a q s f : ℕ) : Formula := .conj
  (.allMem f (.existsMem (α+1) (.existsMem (a+2) (.orderedPair 2 1 0))))
  (.conj
    (.allMem α (.allMem (a+1) (.imp (.pairMem 1 0 (f+2))
      (.allMem 1 (.existsMem (a+3) (.pairMem 1 0 (f+4)))))))
    (.allMem α (.allMem (a+1) (.imp (.pairMem 1 0 (f+2))
      (.existsMem (q+2) (.conj (remainingFormula (a+3) (f+3) 2 0) (.pairMem 0 1 (s+3))))))))

theorem eval_traceFormula (α a q s f : ℕ) (e : ℕ → ZFSet.{u}) :
    (traceFormula α a q s f).Eval e ↔ Trace (e α) (e a) (e q) (e s) (e f) := by
  simp only [traceFormula,Formula.Eval,eval_allMem,eval_imp,eval_orderedPair,
    eval_pairMem,eval_remainingFormula,cons_zero,cons_succ]
  exact ⟨fun ⟨hshape,hinitial,hchoice⟩ => ⟨hshape,hinitial,hchoice⟩,
    fun h => ⟨h.shape,h.initial,h.choice⟩⟩

theorem Trace.subset {α a q s f : ZFSet.{u}} (hf : Trace α a q s f) : f ⊆ ZFSet.prod α a :=
  fun z hz => ZFSet.mem_prod.mpr (hf.shape z hz)

theorem internal_maximal_trace (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    {α a q s : ZFSet.{u}} (hαM : α ∈ M) (ha : a ∈ M) (hq : q ∈ M) (hsM : s ∈ M)
    (hα : Transitive α) (hs : ChoiceGraph q s) :
    ∃ F ∈ M, Trace α a q s F ∧ ∀ f ∈ M, Trace α a q s f → f ⊆ F := by
  have hp := product_mem M hM hP hU hPow hS hαM ha
  obtain ⟨P,hP0,hPdef⟩ := internal_power M hM hPow hp
  let e := cons α (cons a (cons q (fun _ => s)))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hαM
    rcases i with _ | i
    · exact ha
    rcases i with _ | i
    · exact hq
    exact hsM
  let C := ZFSet.sep (fun f => (traceFormula 1 2 3 4 0).Eval (cons f e)) P
  have hC : C ∈ M := sep_mem M hM hS (traceFormula 1 2 3 4 0) e he hP0
  have hCdef (f : ZFSet.{u}) : f ∈ C ↔ f ∈ M ∧ Trace α a q s f := by
    rw [ZFSet.mem_sep,hPdef,eval_traceFormula]
    constructor
    · rintro ⟨⟨hf,_⟩,ht⟩; exact ⟨hf,ht⟩
    · rintro ⟨hf,ht⟩; exact ⟨⟨hf,ht.subset⟩,ht⟩
  refine ⟨ZFSet.sUnion C,union_mem M hM hU hC,Trace.sUnion hα hs (fun f hf => ((hCdef f).mp
    hf).2),?_⟩
  intro f hf htrace z hz
  exact ZFSet.mem_sUnion.mpr ⟨f,(hCdef f).mpr ⟨hf,htrace⟩,hz⟩

noncomputable def residual (a f i : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => ¬ ∃ j ∈ i, ZFSet.pair j x ∈ f) a

theorem residual_remaining (a f i : ZFSet.{u}) : Remaining a f i (residual a f i) := by
  refine ⟨fun _ hx => (ZFSet.mem_sep.mp hx).1,?_⟩
  intro x hx
  exact ZFSet.mem_sep.trans (and_iff_right hx)

theorem residual_mem (M : ZFSet.{u}) (hM : Transitive M) (hS : Separation M)
    {a f i : ZFSet.{u}} (ha : a ∈ M) (hf : f ∈ M) (hi : i ∈ M) : residual a f i ∈ M := by
  simpa only [residual,Formula.Eval,eval_pairMem,cons_zero,cons_succ] using
    sep_mem M hM hS (.neg (.existsMem 2 (.pairMem 0 1 2))) (cons f (fun _ => i))
      (by intro j; cases j <;> assumption) ha

end InternalWellOrder
end TuringRigidity.BoundedSetTheory

end OAI
