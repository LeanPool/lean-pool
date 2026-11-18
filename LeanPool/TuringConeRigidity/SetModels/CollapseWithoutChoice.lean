/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/CollapseWithoutChoice.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalCollapseConditions

/-!
# Collapse Without Choice
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory.InternalCollapse
open TransitiveNameModel CountableForcing
universe u
attribute [local instance] order

theorem append_mem_without_choice (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M) (hU :
  BoundedSetTheory.Union M)
    (hω : ZFSet.omega.{u} ∈ M)
    {p x : ZFSet.{u}} (hp : p ∈ M) (hx : x ∈ M) (n : ℕ) : append p n x ∈ M :=
  binary_union_mem M hM hP hU hp
    (singleton_mem M hM hP (orderedPair_mem M hM hP
      (hM _ (hω) _ ((mem_omega _).mpr ⟨n,rfl⟩)) hx))

theorem conditions_exist_without_choice (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M) (hU :
  BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hω : ZFSet.omega.{u} ∈ M)
    {A : ZFSet.{u}} (hA : A ∈ M) :
    ∃ c ∈ M, ∀ p, p ∈ c ↔ p ∈ M ∧ Prefix A p := by
  obtain ⟨Q,hQM,hQ⟩ := internal_power M hM hPow
    (product_mem M hM hP hU hPow hS hω hA)
  let e := cons ZFSet.omega (fun _ => A)
  have he : ∀ i, e i ∈ M := by intro i; cases i <;> assumption
  let c := ZFSet.sep (fun p => (prefixFormula 1 2 0).Eval (cons p e)) Q
  refine ⟨c,sep_mem M hM hS _ e he hQM,fun p => ?_⟩
  rw [ZFSet.mem_sep,eval_prefixFormula 1 2 0 (cons p e) rfl,hQ]
  exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,prefix_subset h.2⟩,h.2⟩⟩

theorem orderSet_mem_without_choice (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M) (hU :
  BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M)
    {c : ZFSet.{u}} (hc : c ∈ M) : orderSet c ∈ M := by
  let e : ℕ → ZFSet.{u} := fun _ => c
  simpa only
    [orderSet,Formula.Eval,Formula.eval_orderedPair,Formula.eval_subset,cons_zero,cons_succ,e]
    using
    sep_mem M hM hS
      (.existsMem 1 (.existsMem 2 (.conj (.orderedPair 2 1 0) (.subset 0 1)))) e (fun _ => hc)
      (product_mem M hM hP hU hPow hS hc hc)

end TuringRigidity.BoundedSetTheory.InternalCollapse

end OAI
