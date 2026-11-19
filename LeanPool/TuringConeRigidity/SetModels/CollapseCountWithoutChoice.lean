/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/CollapseCountWithoutChoice.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.CollapseDenseWithoutChoice
public import LeanPool.TuringConeRigidity.SetModels.InternalCollapseCounting

/-!
# Collapse Count Without Choice
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory.InternalCollapse
open TransitiveNameModel CountableForcing
universe u
attribute [local instance] order collapsePreorder

theorem unionGraph_total_without_choice (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M) (hU :
  BoundedSetTheory.Union M)
    (hS : Separation M) (hω : ZFSet.omega.{u} ∈ M)
    {A c : ZFSet.{u}} (hA : A ∈ M) (hcM : c ∈ M)
    (hc : ∀ p, p ∈ c ↔ p ∈ M ∧ Prefix A p) (hne : ∃ x, x ∈ A)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (n : ℕ) :
    ∃ x ∈ A, ZFSet.pair (natSet n) x ∈ unionGraph G := by
  obtain ⟨p,hp,hpn⟩ := hG (definedAt c A n) (definedAt_mem_without_choice M hM hS hω hcM hA n)
    (definedAt_dense_without_choice M hM hP hU hω hA hc hne n)
  obtain ⟨_,x,hx,hnx⟩ := ZFSet.mem_sep.mp hpn
  exact ⟨x,hx,(mem_unionGraph G _).mpr ⟨p,hp,hnx⟩⟩

theorem unionGraph_onto_without_choice (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M) (hU :
  BoundedSetTheory.Union M)
    (hS : Separation M) (hω : ZFSet.omega.{u} ∈ M)
    {A c : ZFSet.{u}} (hA : A ∈ M) (hcM : c ∈ M)
    (hc : ∀ p, p ∈ c ↔ p ∈ M ∧ Prefix A p)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    ∀ x ∈ A, ∃ n ∈ ZFSet.omega, ZFSet.pair n x ∈ unionGraph G := by
  intro x hx
  obtain ⟨p,hp,hpx⟩ := hG (covers c x) (covers_mem_without_choice M hM hS hω hcM (hM _ hA _ hx))
    (covers_dense_without_choice M hM hP hU hω hA hc hx)
  obtain ⟨_,n,hn,hnx⟩ := ZFSet.mem_sep.mp hpx
  exact ⟨n,hn,(mem_unionGraph G _).mpr ⟨p,hp,hnx⟩⟩

theorem unionGraph_function_without_choice (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
  (hU : BoundedSetTheory.Union M)
    (hS : Separation M) (hω : ZFSet.omega.{u} ∈ M)
    {A c : ZFSet.{u}} (hA : A ∈ M) (hcM : c ∈ M)
    (hc : ∀ p, p ∈ c ↔ p ∈ M ∧ Prefix A p) (hne : ∃ x, x ∈ A)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    TransitiveNameModel.FunctionGraph ZFSet.omega A (unionGraph G) := by
  have hcP : ∀ p ∈ c, Prefix A p := fun p hp => ((hc p).mp hp).2
  constructor
  · intro z hz
    obtain ⟨p,_,hzp⟩ := (mem_unionGraph G z).mp hz
    exact ZFSet.mem_prod.mp (prefix_subset (hcP _ (label_mem c p)) hzp)
  · intro i hi
    obtain ⟨n,rfl⟩ := (mem_omega i).mp hi
    obtain ⟨x,hx,hnx⟩ := unionGraph_total_without_choice M hM hP hU hS hω hA hcM hc hne G hG n
    exact ⟨x,hx,hnx,fun y _ hny => unionGraph_functional hcP G hny hnx⟩

end TuringRigidity.BoundedSetTheory.InternalCollapse

end OAI
