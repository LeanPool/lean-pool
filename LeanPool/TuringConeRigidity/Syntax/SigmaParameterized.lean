/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/SigmaParameterized.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.BoundedDefinability

/-!
# Sigma Parameterized
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedDefinability
open BoundedSetTheory TransitiveNameModel SetModelFunctions
universe u

/-- A sigma formula defines the predicate on model-valued environments using fixed parameters
from `M`. -/
def SigmaDefinable (M : ZFSet.{u}) (P : (ℕ → ZFSet.{u}) → Prop) : Prop :=
  ∃ p : SigmaFormula, ∃ d : ℕ → ZFSet.{u}, (∀ i, d i ∈ M) ∧
    ∀ e, (∀ i, e i ∈ M) → (p.Realize M (mix e d) ↔ P e)

variable {M : ZFSet.{u}} {P Q : (ℕ → ZFSet.{u}) → Prop}

theorem Definable.toSigma (hM : Transitive M) (h : Definable M P) : SigmaDefinable M P := by
  obtain ⟨p,d,hd,hp⟩ := h
  refine ⟨.bounded p,d,hd,?_⟩
  intro e he
  exact (p.absolute M hM (mix e d) (by
    intro i; unfold mix; split <;> first | exact he _ | exact hd _)).trans (hp e)

theorem SigmaDefinable.existsSet (h : SigmaDefinable M P) :
    SigmaDefinable M (fun e => ∃ x ∈ M, P (cons x e)) := by
  obtain ⟨p,d,hd,hp⟩ := h
  refine ⟨.existsSet (p.rename bindSlots),d,hd,?_⟩
  intro e he
  simp only [SigmaFormula.Realize,SigmaFormula.realize_rename]
  apply exists_congr; intro x
  apply and_congr_right; intro hx
  have hh := bind_mix x e d
  change (p.Realize M (cons x (mix e d) ∘ bindSlots)) ↔ _
  rw [hh]
  exact hp (cons x e) (by
    intro i
    cases i
    · exact hx
    · exact he _)

theorem SigmaDefinable.congr (h : SigmaDefinable M P)
    (hPQ : ∀ e, (∀ i, e i ∈ M) → (P e ↔ Q e)) : SigmaDefinable M Q := by
  obtain ⟨p,d,hd,hp⟩ := h
  exact ⟨p,d,hd,fun e he => (hp e he).trans (hPQ e he)⟩

theorem SigmaDefinable.binary (F : ZFSet.{u} → ZFSet.{u})
    (h : SigmaDefinable M (fun e => e 0 = F (e 1))) :
    ∃ p : SigmaFormula, ∃ d : ℕ → ZFSet.{u}, (∀ i, d i ∈ M) ∧
      ∀ x ∈ M, ∀ y ∈ M, p.Realize M (cons y (cons x d)) ↔ y = F x := by
  obtain ⟨p,d,hd,hp⟩ := h
  let r : ℕ → ℕ := fun i => if i % 2 = 0 then (if i / 2 = 0 then 0 else 1) else i/2+2
  refine ⟨p.rename r,d,hd,?_⟩
  intro x hx y hy
  rw [SigmaFormula.realize_rename]
  have he : cons y (cons x d) ∘ r = mix (cons y (fun _ => x)) d := by
    apply parity_ext
    · intro n
      cases n with
      | zero => rfl
      | succ n => simp [r]
    · intro n; simp [r,Nat.add_div]
  change p.Realize M (cons y (cons x d) ∘ r) ↔ _
  rw [he]
  exact hp (cons y (fun _ => x)) (by
    intro i
    cases i
    · exact hy
    · exact hx)

end TuringRigidity.BoundedDefinability

end OAI
