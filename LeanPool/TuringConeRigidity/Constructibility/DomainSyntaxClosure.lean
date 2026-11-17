/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/DomainSyntaxClosure.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.DomainParameterizedSyntax

/-!
# Domain Syntax Closure
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedDefinability
open ElementaryModel BoundedSetTheory TransitiveNameModel SetModelFunctions
universe u
variable {M : ZFSet.{u}} {P Q : ZFSet.{u} → (ℕ → ZFSet.{u}) → Prop}

theorem DomainDefinable.neg (h : DomainDefinable M P) :
    DomainDefinable M (fun N e => ¬ P N e) := by
  obtain ⟨p,d,k,hk,hd,hp⟩ := h
  exact ⟨.neg p,d,k,hk,hd,fun N hN hdN e he => not_congr (hp N hN hdN e he)⟩

theorem DomainDefinable.imp (hP : DomainDefinable M P) (hQ : DomainDefinable M Q) :
    DomainDefinable M (fun N e => P N e → Q N e) := by
  apply (hP.and hQ.neg).neg.congr
  intro N e
  classical
  tauto

theorem DomainDefinable.subst (h : DomainDefinable M P) (r : ℕ → ℕ) :
    DomainDefinable M (fun N e => P N (e ∘ r)) := by
  obtain ⟨p,d,k,hk,hd,hp⟩ := h
  refine ⟨p.rename (slotMap r id),d,k,hk,hd,?_⟩
  intro N hN hdN e he
  rw [SentenceForm.sat_rename]
  change p.Sat _ (mix e d ∘ slotMap r id) ↔ _
  rw [mix_slotMap,Function.comp_id]
  exact hp N hN hdN (e ∘ r) (fun i => he (r i))

theorem DomainDefinable.allMem (C : Context M) (h : DomainDefinable M P) (a : ℕ) :
    DomainDefinable M (fun N e => ∀ x ∈ e a, P N (cons x e)) := by
  obtain ⟨p,d,k,hk,hd,hp⟩ := ((member_definable C 0 (a+1)).toDomain.and h.neg).existsSet.neg
  refine ⟨p,d,k,hk,hd,?_⟩
  intro N hN hdN e he
  rw [hp N hN hdN e he]
  change (¬ ∃ x ∈ N, x ∈ e a ∧ ¬ P N (cons x e)) ↔ _
  classical
  constructor
  · intro h x hx
    by_contra hn
    exact h ⟨x,hN _ (he a) x hx,hx,hn⟩
  · intro h ⟨x,_,hx,hn⟩
    exact hn (h x hx)

end TuringRigidity.BoundedDefinability

end OAI
