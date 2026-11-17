/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalCountableEnumeration.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalRelationSelection

/-!
# Internal Countable Enumeration
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalCountableEnumeration
open TransitiveNameModel BoundedSetTheory InternalRelationSelection
open InternalCountableFiniteUnion InternalFiniteEnumeration

def Enumerates (E g : ZFSet.{0}) : Prop :=
  (E = ∅ ∧ g = ∅) ∨ (FunctionGraph ZFSet.omega E g ∧
    ∀ x ∈ E, ∃ n ∈ ZFSet.omega, ZFSet.pair n x ∈ g)

def enumeratesFormula (ω E g : ℕ) : Formula :=
  .disj (.conj (.empty E) (.empty g))
    (.conj (.functionGraph g ω E) (.allMem E (.existsMem (ω+1) (.pairMem 0 1 (g+2)))))

theorem enumeratesFormula_spec (ω E g : ℕ) (e : ℕ → ZFSet.{0})
    (hω : e ω = ZFSet.omega) :
    (enumeratesFormula ω E g).Eval e ↔ Enumerates (e E) (e g) := by
  simp only [enumeratesFormula,Enumerates,FunctionGraph,Formula.eval_disj,Formula.Eval,
    Formula.eval_empty,Formula.eval_functionGraph,Formula.eval_allMem,
    Formula.eval_pairMem,cons_zero,cons_succ,hω]

theorem enumerates_ranges (U E g : ZFSet.{0}) (hE : E ⊆ U) (hg : Enumerates E g) :
    Ranges U E g := by
  refine ⟨hE,fun x _ => ?_⟩
  rcases hg with ⟨rfl,rfl⟩|⟨hg,honto⟩
  · simp
  · refine ⟨fun hx => honto x hx,?_⟩
    rintro ⟨n,_,hn⟩
    obtain ⟨n',_,x',hx,hp⟩ := hg.1 _ hn
    exact (ZFSet.pair_inj.mp hp).2 ▸ hx

theorem enumerates_entry (U E g d k : ZFSet.{0}) (hE : E ⊆ U) (hg : Enumerates E g)
    (hd : d ∈ U) (hk : k ∈ ZFSet.omega) :
    ∃ x ∈ U, Entry U g d k x ∧ ∀ y ∈ U, Entry U g d k y → y = x := by
  rcases hg with ⟨_,rfl⟩|⟨hg,_⟩
  · exact ⟨d,hd,Or.inr ⟨rfl,fun y _ => ZFSet.notMem_empty _⟩,
      fun y _ hy => hy.elim (fun h => False.elim (ZFSet.notMem_empty _ h)) And.left⟩
  · obtain ⟨x,hx,hkx,_⟩ := hg.2 k hk
    refine ⟨x,hE hx,Or.inl hkx,?_⟩
    intro y _ hy
    rcases hy with hy|⟨_,hy⟩
    · exact hg.functional hk hy hkx
    · exact False.elim (hy x (hE hx) hkx)

theorem internal_countable_selector (M U S : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hU : U ∈ M) (hS : S ∈ M)
    (hsub : ∀ E ∈ S, E ⊆ U)
    (hct : ∀ E ∈ S, E = ∅ ∨ InternallyCountable M E) :
    ∃ C ∈ M, ∃ T ∈ M, FunctionGraph S C T ∧
      ∀ E ∈ S, ∀ g, ZFSet.pair E g ∈ T → Enumerates E g := by
  have hω := sourceT_omega_mem M hM hT
  have hp := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hω hU
  obtain ⟨C,hCM,hC⟩ := internal_power M hM hT.powerSet hp
  let e := cons S (cons C (fun _ => ZFSet.omega))
  let φ : Formula := .existsMem 1 (.existsMem 3
    (.conj (.orderedPair 2 1 0) (enumeratesFormula 5 1 0)))
  let R := (ZFSet.prod S C).sep (fun z => φ.Eval (cons z e))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    · exact hS
    · exact hCM
    · exact hω
  have hRM : R ∈ M := sep_mem M hM hT.separation.finitePrefix.bounded φ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hS hCM)
  have hr (E g : ZFSet.{0}) : ZFSet.pair E g ∈ R ↔ E ∈ S ∧ g ∈ C ∧ Enumerates E g := by
    have henum (domain graph pair : ZFSet.{0}) :
        (enumeratesFormula 5 1 0).Eval (cons graph (cons domain (cons pair e))) ↔
          Enumerates domain graph := enumeratesFormula_spec 5 1 0 _ rfl
    simp only [R,ZFSet.mem_sep,φ,Formula.Eval,Formula.eval_orderedPair,
      henum,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨_,E',hE,g',hg,hp,hEnum⟩
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
      exact ⟨hE,hg,hEnum⟩
    · rintro ⟨hE,hg,hEnum⟩
      exact ⟨ZFSet.mem_prod.mpr ⟨E,hE,g,hg,rfl⟩,E,hE,g,hg,rfl,hEnum⟩
  have htotal : ∀ E ∈ S, ∃ g ∈ C, ZFSet.pair E g ∈ R := by
    intro E hE
    rcases hct E hE with hempty|⟨g,hgM,hg,honto⟩
    · have hzero : (∅ : ZFSet.{0}) ∈ M := hempty ▸ hM S hS E hE
      have hgC := (hC ∅).mpr ⟨hzero,fun _ h => False.elim (ZFSet.notMem_empty _ h)⟩
      exact ⟨∅,hgC,(hr E ∅).mpr ⟨hE,hgC,Or.inl ⟨hempty,rfl⟩⟩⟩
    · have hgC := (hC g).mpr ⟨hgM,by
        intro z hz
        obtain ⟨n,hn,x,hx,hz⟩ := hg.1 z hz
        exact ZFSet.mem_prod.mpr ⟨n,hn,x,hsub E hE hx,hz⟩⟩
      exact ⟨g,hgC,(hr E g).mpr ⟨hE,hgC,Or.inr ⟨hg,honto⟩⟩⟩
  obtain ⟨T,hTM,hfun,hTR⟩ := select_relation M S C R hM hT hS hCM hRM htotal
  exact ⟨C,hCM,T,hTM,hfun,fun E _ g hEg => ((hr E g).mp (hTR hEg)).2.2⟩

end TuringRigidity.InternalCountableEnumeration

end OAI
