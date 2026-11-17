/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/TrimmedPresentation.lean.
Also incorporates shared proofs from the upstream
OAI/Computability/DegreeRigidity/SetModels/FinitePresentation.lean under the same Apache-2.0 terms.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.FiniteStageSetBounds
public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalOrderTypeSyntax

/-!
# Trimmed Presentation
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory ElementaryModel RelativeConstructible
universe u

theorem order_certificate_of_exact_pairs (d r f : ZFSet.{u}) (o : Ordinal.{u})
    (j : ZFSet.{u} → ZFSet.{u})
    (hj : ∀ x ∈ d, j x ∈ o.toZFSet)
    (hs : ∀ z ∈ o.toZFSet, ∃ x ∈ d, j x = z)
    (he : ∀ x ∈ d, ∀ y ∈ d, ZFSet.pair x y ∈ r ↔ j x ∈ j y)
    (hf : ∀ z, z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (j x)) :
    OrderTypeCertificate d r o.toZFSet f := by
  have pair (x : ZFSet.{u}) (hx : x ∈ d) := (hf _).mpr ⟨x,hx,rfl⟩
  have eq (x z : ZFSet.{u}) (h : ZFSet.pair x z ∈ f) : z = j x := by
    obtain ⟨y,_,hh⟩ := (hf _).mp h
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hh
    rfl
  refine ⟨ZFSet.isOrdinal_toZFSet _,⟨fun _ h => h,fun _ _ _ h _ => h,?_,?_,?_⟩,?_⟩
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := (hf z).mp hz
    exact ⟨x,hx,j x,hj x hx,rfl⟩
  · intro x hx
    exact ⟨j x,hj x hx,pair x hx,fun z _ hz => eq x z hz⟩
  · intro x hx v _ hxv
    rw [eq x v hxv]
    constructor
    · intro z hz
      obtain ⟨y,hy,rfl⟩ := hs z ((ZFSet.isOrdinal_toZFSet o).subset_of_mem (hj x hx) hz)
      exact ⟨y,hy,(he y hy x hx).mpr hz,pair y hy⟩
    · intro y hy hyx z _ hyz
      rw [eq y z hyz]
      exact (he y hy x hx).mp hyx
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := hs z hz
    exact ⟨x,hx,pair x hx⟩

/-- A definable exact-pairs presentation yields an order-type certificate in the successor level. -/
theorem presentation_graph_mem_successor_of_pairs (R : ZFSet.{u}) (γ : Ordinal.{u})
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

theorem presentation_graph_at_limit_successor (R : ZFSet.{u}) (γ : Ordinal.{u})
    (hγ : Order.IsSuccLimit γ) (d r : ZFSet.{u}) (o : Ordinal.{u})
    (j : ZFSet.{u} → ZFSet.{u}) (hd : d ⊆ level R γ)
    (hjA : ∀ x ∈ d, j x ∈ level R γ)
    (hj : ∀ x ∈ d, j x ∈ o.toZFSet)
    (hs : ∀ z ∈ o.toZFSet, ∃ x ∈ d, j x = z)
    (he : ∀ x ∈ d, ∀ y ∈ d, ZFSet.pair x y ∈ r ↔ j x ∈ j y)
    (p : SentenceForm) (e : ℕ → ZFSet.{u}) (henv : ∀ i, e i ∈ level R γ)
    (hp : ∀ z ∈ level R γ, p.Sat (level R γ : Set ZFSet) (cons z e) ↔
      ∃ x ∈ d, z = ZFSet.pair x (j x)) :
    ∃ f ∈ level R (γ+1), OrderTypeCertificate d r o.toZFSet f := by
  exact presentation_graph_mem_successor_of_pairs R γ d r o j
    (fun x hx => orderedPair_mem_level_limit R γ hγ (hd hx) (hjA x hx))
    hj hs he p e henv hp

end TuringRigidity.RelationCollapse

end OAI
