/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalCollapseDense.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalCollapseConditions

/-!
# Internal Collapse Dense
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory.InternalCollapse
open TransitiveNameModel CountableForcing
universe u
attribute [local instance] order collapsePreorder

theorem extend_length (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {A p : ZFSet.{u}} (hA : A ∈ M) (hpM : p ∈ M) (hp : Prefix A p)
    (hne : ∃ x, x ∈ A) (m : ℕ) :
    ∃ q ∈ M, ∃ k : ℕ, m ≤ k ∧ TransitiveNameModel.FunctionGraph (natSet k) A q ∧ p ⊆ q := by
  obtain ⟨x,hx⟩ := hne
  induction m with
  | zero =>
    obtain ⟨k,hk⟩ := hp
    exact ⟨p,hpM,k,Nat.zero_le _,hk,fun _ h => h⟩
  | succ m ih =>
    obtain ⟨q,hqM,k,hk,hq,hpq⟩ := ih
    by_cases hmk : m+1 ≤ k
    · exact ⟨q,hqM,k,hmk,hq,hpq⟩
    · refine ⟨append q k x,append_mem M hM hT hqM (hM _ hA _ hx) k,k+1,by omega,
        append_function hq hx,fun z hz => ?_⟩
      exact (mem_append _ _ _ _).mpr (Or.inl (hpq hz))

/-- The conditions assigning the specified value `x` at some natural-number index. -/
noncomputable def covers (c x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun p => ∃ n ∈ ZFSet.omega, ZFSet.pair n x ∈ p) c

/-- The conditions assigning some value in `A` at the specified natural-number index. -/
noncomputable def definedAt (c A : ZFSet.{u}) (n : ℕ) : ZFSet.{u} :=
  ZFSet.sep (fun p => ∃ x ∈ A, ZFSet.pair (natSet n) x ∈ p) c

theorem covers_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c x : ZFSet.{u}} (hc : c ∈ M) (hx : x ∈ M) : covers c x ∈ M := by
  let e := cons ZFSet.omega (fun _ => x)
  have he : ∀ i, e i ∈ M := by
    intro i; cases i <;> first | exact sourceT_omega_mem M hM hT | exact hx
  simpa only [covers,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.existsMem 1 (.pairMem 0 3 1)) e he hc

theorem definedAt_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c A : ZFSet.{u}} (hc : c ∈ M) (hA : A ∈ M) (n : ℕ) : definedAt c A n ∈ M := by
  let e := cons A (fun _ => natSet.{u} n)
  have he : ∀ i, e i ∈ M := by
    intro i; cases i
    · exact hA
    · exact hM _ (sourceT_omega_mem M hM hT) _ ((mem_omega _).mpr ⟨n,rfl⟩)
  simpa only [definedAt,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.existsMem 1 (.pairMem 3 0 1)) e he hc

theorem covers_dense (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {A c : ZFSet.{u}} (hA : A ∈ M) (hc : ∀ p, p ∈ c ↔ p ∈ M ∧ Prefix A p)
    {x : ZFSet.{u}} (hx : x ∈ A) : Dense {p : Conditions c | label c p ∈ covers c x} := by
  intro p
  obtain ⟨hpM,n,hp⟩ := (hc _).mp (label_mem c p)
  let q := append (label c p) n x
  have hq : q ∈ c := (hc q).mpr ⟨append_mem M hM hT hpM (hM _ hA _ hx) n,n+1,append_function hp hx⟩
  obtain ⟨r,hr⟩ := label_surjective c hq
  refine ⟨r,?_,?_⟩
  · change label c p ⊆ label c r
    rw [hr]
    exact fun z hz => (mem_append _ _ _ _).mpr (Or.inl hz)
  · change label c r ∈ covers c x
    rw [hr,covers,ZFSet.mem_sep]
    exact ⟨hq,natSet n,(mem_omega _).mpr ⟨n,rfl⟩,(mem_append _ _ _ _).mpr (Or.inr rfl)⟩

theorem definedAt_dense (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {A c : ZFSet.{u}} (hA : A ∈ M) (hc : ∀ p, p ∈ c ↔ p ∈ M ∧ Prefix A p)
    (hne : ∃ x, x ∈ A) (n : ℕ) : Dense {p : Conditions c | label c p ∈ definedAt c A n} := by
  intro p
  obtain ⟨hpM,hp⟩ := (hc _).mp (label_mem c p)
  obtain ⟨q,hqM,k,hnk,hq,hpq⟩ := extend_length M hM hT hA hpM hp hne (n+1)
  have hqc : q ∈ c := (hc q).mpr ⟨hqM,k,hq⟩
  obtain ⟨r,hr⟩ := label_surjective c hqc
  obtain ⟨x,hx,hnx,_⟩ := hq.2 (natSet n) ((natSet_mem_natSet n k).mpr (by omega))
  refine ⟨r,?_,?_⟩
  · change label c p ⊆ label c r
    rw [hr]; exact hpq
  · change label c r ∈ definedAt c A n
    rw [hr,definedAt,ZFSet.mem_sep]
    exact ⟨hqc,x,hx,hnx⟩

end TuringRigidity.BoundedSetTheory.InternalCollapse

end OAI
