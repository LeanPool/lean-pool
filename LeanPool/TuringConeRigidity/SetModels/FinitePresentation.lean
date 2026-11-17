/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/FinitePresentation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.TrimmedPresentation

/-!
# Finite Presentation
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory ElementaryModel RelativeConstructible
universe u

theorem presentation_graph_at_successor_of_pairs (R : ZFSet.{u}) (γ : Ordinal.{u})
    (d r : ZFSet.{u}) (o : Ordinal.{u})
    (j : ZFSet.{u} → ZFSet.{u})
    (hpairs : ∀ x ∈ d, ZFSet.pair x (j x) ∈ level R γ)
    (hj : ∀ x ∈ d, j x ∈ o.toZFSet)
    (hs : ∀ z ∈ o.toZFSet, ∃ x ∈ d, j x = z)
    (he : ∀ x ∈ d, ∀ y ∈ d, ZFSet.pair x y ∈ r ↔ j x ∈ j y)
    (p : SentenceForm) (e : ℕ → ZFSet.{u}) (henv : ∀ i, e i ∈ level R γ)
    (hp : ∀ z ∈ level R γ, p.Sat (level R γ : Set ZFSet) (cons z e) ↔
      ∃ x ∈ d, z = ZFSet.pair x (j x)) :
    ∃ f ∈ level R (γ+1), OrderTypeCertificate d r o.toZFSet f := by
  let A := level R γ
  let f := A.sep (fun z => p.Sat (A : Set ZFSet) (cons z e))
  have hf : f ∈ level R (γ+1) := by
    rw [level_succ]
    exact separation_mem_definablePower A p e (fun i _ => henv i)
  have hexact (z : ZFSet.{u}) : z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (j x) := by
    change z ∈ A.sep _ ↔ _
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz,h⟩; exact (hp z hz).mp h
    · rintro ⟨x,hx,rfl⟩
      have hz := hpairs x hx
      exact ⟨hz,(hp _ hz).mpr ⟨x,hx,rfl⟩⟩
  exact ⟨f,hf,order_certificate_of_exact_pairs d r f o j hj hs he hexact⟩

end TuringRigidity.RelationCollapse

end OAI
