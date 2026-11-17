/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalChoice.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.BoundedRelations

/-!
# Internal Choice
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

/-- A single-valued set-coded function choosing an element of every set in `a`. -/
def ChoiceGraph (a f : ZFSet.{u}) : Prop :=
  (∀ z ∈ f, ∃ x ∈ a, ∃ y ∈ x, z = ZFSet.pair x y) ∧
  (∀ x ∈ a, ∃ y ∈ x, ZFSet.pair x y ∈ f ∧
    ∀ z ∈ x, ZFSet.pair x z ∈ f → z = y)

/-- The model contains a choice graph for every family of nonempty sets belonging to it. -/
def Choice (M : ZFSet.{u}) : Prop :=
  ∀ a ∈ M, (∀ x ∈ a, ∃ y, y ∈ x) → ∃ f ∈ M, ChoiceGraph a f

namespace ChoiceCode
open Formula

/-- Bounded formula describing a single-valued choice graph. -/
def graph (a f : ℕ) : Formula :=
  .conj (allMem f (.existsMem (a+1) (.existsMem 0 (orderedPair 2 1 0))))
    (allMem a (.existsMem 0 (.conj (pairMem 1 0 (f+2))
      (allMem 1 (imp (pairMem 2 0 (f+3)) (.equal 0 1))))))

theorem eval_graph (a f : ℕ) (e : ℕ → ZFSet.{u}) :
    (graph a f).Eval e ↔ ChoiceGraph (e a) (e f) := by
  simp only [graph,ChoiceGraph,Formula.Eval,eval_allMem,eval_orderedPair,
    eval_pairMem,eval_imp,cons_zero,cons_succ]
end ChoiceCode

theorem internal_selector (M : ZFSet.{u}) (hM : Transitive M)
    (hPow : PowerSet M) (hS : Separation M) (hAC : Choice M)
    {t : ZFSet.{u}} (ht : t ∈ M) :
    ∃ a ∈ M, ∃ f ∈ M, ChoiceGraph a f ∧
      ∀ x, x ∈ a ↔ x ∈ M ∧ x ⊆ t ∧ ∃ y, y ∈ x := by
  obtain ⟨q,hq,hqdef⟩ := internal_power M hM hPow ht
  let a := ZFSet.sep (fun x => ∃ y, y ∈ x) q
  have ha : a ∈ M := by
    simpa only [Formula.Eval,cons_zero,iff_true,exists_prop,and_true,a] using
      sep_mem M hM hS (.existsMem 0 (.equal 0 0)) (fun _ => t) (fun _ => ht) hq
  have hadef (x : ZFSet.{u}) : x ∈ a ↔ x ∈ M ∧ x ⊆ t ∧ ∃ y, y ∈ x := by
    rw [ZFSet.mem_sep,hqdef]
    exact and_assoc
  obtain ⟨f,hf,hfg⟩ := hAC a ha (fun x hx => ((hadef x).mp hx).2.2)
  exact ⟨a,ha,f,hf,hfg,hadef⟩

theorem ChoiceGraph.functional {a f : ZFSet.{u}} (hf : ChoiceGraph a f)
    {x y z : ZFSet.{u}} (hxy : ZFSet.pair x y ∈ f) (hxz : ZFSet.pair x z ∈ f) : y = z := by
  obtain ⟨a',ha,b,hb,he⟩ := hf.1 _ hxy
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
  obtain ⟨a',_,b,hb',he⟩ := hf.1 _ hxz
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
  obtain ⟨v,_,hxv,hunique⟩ := hf.2 x ha
  exact (hunique y hb hxy).trans (hunique z hb' hxz).symm

end TuringRigidity.BoundedSetTheory

end OAI
