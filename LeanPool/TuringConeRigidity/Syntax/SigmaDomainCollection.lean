/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/SigmaDomainCollection.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.SigmaTransitiveWitness

/-!
# Sigma Domain Collection
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace SigmaFormula

def domainVars : ℕ → ℕ
  | 0 => 1
  | i+1 => i+3

def domainRequest (φ : SigmaFormula) : SigmaFormula := .bounded
  (.conj (.transitive 0) (.conj (.subset 2 0) (FiniteTuple.relativizeSigma 0 (φ.rename
    domainVars))))

theorem realize_domainRequest (φ : SigmaFormula) (M : ZFSet.{u}) (hM : Transitive M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) {d x t : ZFSet.{u}}
    (hd : d ∈ M) (hx : x ∈ M) (ht : t ∈ M) :
    φ.domainRequest.Realize M (cons d (cons x (cons t e))) ↔
      Transitive d ∧ t ⊆ d ∧ φ.Realize d (cons x e) := by
  have he' : ∀ i, cons d (cons x (cons t e)) i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hd
    rcases i with _ | i
    · exact hx
    rcases i with _ | i
    · exact ht
    exact he i
  rw [domainRequest,Realize,Formula.absolute _ M hM _ he']
  simp only
    [Formula.Eval,Formula.eval_transitive,Formula.eval_subset,FiniteTuple.eval_relativizeSigma,
    realize_rename,cons_zero,cons_succ]
  have eq : (fun i => cons d (cons x (cons t e)) (domainVars i)) = cons x e := by
    funext i; cases i <;> rfl
  rw [eq]

theorem internal_bounded_domain (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hC : SigmaCollection M)
    {a t : ZFSet.{u}} (ha : a ∈ M) (ht : t ∈ M) (htt : Transitive t) (hat : a ∈ t)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ t) (φ : SigmaFormula)
    (hφ : ∀ x ∈ a, φ.Realize M (cons x e)) :
    ∃ D ∈ M, Transitive D ∧ t ⊆ D ∧ ∀ x ∈ a, φ.Realize D (cons x e) := by
  have heM := fun i => hM t ht _ (he i)
  have hxe (x : ZFSet.{u}) (hx : x ∈ a) : ∀ i, cons x e i ∈ t := by
    intro i; cases i with
    | zero => exact htt a hat x hx
    | succ i => exact he i
  obtain ⟨B,hB,hbound⟩ := hC φ.domainRequest (cons t e)
    (by intro i; cases i <;> simp [cons,ht,heM]) a ha (by
      intro x hx
      obtain ⟨d,hd,hdt,htd,hdφ⟩ := internal_transitive_witness M hM hP hU hS hR hI ht
        (cons x e) (hxe x hx) φ (hφ x hx)
      exact ⟨d,hd,(realize_domainRequest φ M hM e heM hd (hM a ha x hx) ht).mpr ⟨hdt,htd,hdφ⟩⟩)
  let C := ZFSet.sep (fun d => Transitive d ∧ t ⊆ d) B
  have hCmem : C ∈ M := by
    simpa only [Formula.Eval,Formula.eval_transitive,Formula.eval_subset,cons_zero,cons_succ] using
      sep_mem M hM hS (.conj (.transitive 0) (.subset 1 0)) (fun _ => t) (fun _ => ht) hB
  let D := t ∪ ZFSet.sUnion C
  have hDM : D ∈ M := binary_union_mem M hM hP hU ht (union_mem M hM hU hCmem)
  have htD : t ⊆ D := fun _ hy => ZFSet.mem_union.mpr (Or.inl hy)
  have hDT : Transitive D := by
    intro x hx y hy
    rcases ZFSet.mem_union.mp hx with hx|hx
    · exact htD (htt x hx y hy)
    · obtain ⟨d,hd,hxd⟩ := ZFSet.mem_sUnion.mp hx
      have hdt := (ZFSet.mem_sep.mp hd).2.1
      exact ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_sUnion.mpr ⟨d,hd,hdt x hxd y hy⟩))
  refine ⟨D,hDM,hDT,htD,?_⟩
  intro x hx
  obtain ⟨d,hdB,hdφ⟩ := hbound x hx
  have hdM := hM B hB d hdB
  obtain ⟨hdt,htd,hdφ⟩ := (realize_domainRequest φ M hM e heM hdM (hM a ha x hx) ht).mp hdφ
  have hdC : d ∈ C := ZFSet.mem_sep.mpr ⟨hdB,hdt,htd⟩
  have hdD : d ⊆ D := fun y hy => ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_sUnion.mpr ⟨d,hdC,hy⟩))
  exact φ.transitive_upward hdt hDT hdD (cons x e) (fun i => htd (hxe x hx i)) hdφ
end SigmaFormula

end TuringRigidity.BoundedSetTheory

end OAI
