/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/NumericDomain.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.NumericDefSystem
public import LeanPool.TuringConeRigidity.Constructibility.DomainSyntaxClosure

/-!
# Numeric Domain
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.NumericSyntax
open ElementaryModel BoundedSetTheory TransitiveNameModel BoundedDefinability
universe u

def Domain (P : ZFSet.{u} → (ℕ → ZFSet.{u}) → Prop) : Prop :=
  ∃ p : SentenceForm, ∀ B, Covers B → ∀ N : ZFSet.{u}, Transitive N →
    (∀ i, params B i ∈ N) → ∀ e, (∀ i, e i ∈ N) →
      (p.Sat (N : Set ZFSet) (mix e (params B)) ↔ P N e)

variable {P Q : ZFSet.{u} → (ℕ → ZFSet.{u}) → Prop}

theorem Numeric.toDomain {P : (ℕ → ZFSet.{u}) → Prop} (h : Numeric P) :
    Domain (fun _ e => P e) := by
  obtain ⟨p,hp⟩ := h
  refine ⟨fromBounded p,?_⟩
  intro B hB N hN hd e he
  rw [bounded_sat,Formula.absolute p N hN _ (by
    intro i; unfold mix; split <;> first | exact he _ | exact hd _)]
  exact hp B hB e

theorem Domain.congr (h : Domain P) (he : ∀ N e, P N e ↔ Q N e) : Domain Q := by
  obtain ⟨p,hp⟩ := h
  exact ⟨p,fun B hB N hN hd e he' => (hp B hB N hN hd e he').trans (he N e)⟩

theorem Domain.and (h : Domain P) (k : Domain Q) : Domain (fun N e => P N e ∧ Q N e) := by
  obtain ⟨p,hp⟩ := h; obtain ⟨q,hq⟩ := k
  exact ⟨.conj p q,fun B hB N hN hd e he =>
    and_congr (hp B hB N hN hd e he) (hq B hB N hN hd e he)⟩

theorem Domain.neg (h : Domain P) : Domain (fun N e => ¬ P N e) := by
  obtain ⟨p,hp⟩ := h
  exact ⟨.neg p,fun B hB N hN hd e he => not_congr (hp B hB N hN hd e he)⟩

theorem Domain.imp (h : Domain P) (k : Domain Q) : Domain (fun N e => P N e → Q N e) :=
  (h.and k.neg).neg.congr (fun _ _ => by tauto)

theorem Domain.subst (h : Domain P) (r : ℕ → ℕ) : Domain (fun N e => P N (e ∘ r)) := by
  obtain ⟨p,hp⟩ := h
  refine ⟨p.rename (slotMap r id),?_⟩
  intro B hB N hN hd e he
  rw [SentenceForm.sat_rename]
  change p.Sat _ (mix e (params B) ∘ slotMap r id) ↔ _
  rw [mix_slotMap,Function.comp_id]
  exact hp B hB N hN hd (e ∘ r) (fun i => he (r i))

theorem Domain.existsSet (h : Domain P) : Domain (fun N e => ∃ x ∈ N, P N (cons x e)) := by
  obtain ⟨p,hp⟩ := h
  refine ⟨.ex (p.rename bindSlots),?_⟩
  intro B hB N hN hd e he
  change (∃ x ∈ N, (p.rename bindSlots).Sat _ (cons x (mix e (params B)))) ↔ _
  apply exists_congr; intro x
  apply and_congr_right; intro hx
  rw [SentenceForm.sat_rename]
  change p.Sat _ (cons x (mix e (params B)) ∘ bindSlots) ↔ _
  rw [bind_mix]
  exact hp B hB N hN hd (cons x e) (by
    intro i
    cases i
    · exact hx
    · exact he _)

theorem Domain.allMem (h : Domain P) (a : ℕ) : Domain (fun N e => ∀ x ∈ e a, P N (cons x e)) := by
  obtain ⟨p,hp⟩ := ((member_definable 0 (a+1)).toDomain.and h.neg).existsSet.neg
  refine ⟨p,?_⟩
  intro B hB N hN hd e he
  rw [hp B hB N hN hd e he]
  change (¬ ∃ x ∈ N, x ∈ e a ∧ ¬ P N (cons x e)) ↔ _
  classical
  constructor
  · intro h x hx
    by_contra hn
    exact h ⟨x,hN _ (he a) x hx,hx,hn⟩
  · intro h ⟨x,_,hx,hn⟩
    exact hn (h x hx)

theorem powerBound_domain (a q : ℕ) : Domain (fun N e => RelativeConstructible.PowerBound N (e a)
  (e q)) := by
  refine ⟨FullSetForcing.ownPower (2*a) (2*q),?_⟩
  intro B hB N hN hd e he
  rw [FullSetForcing.ownPower_spec N hN _ _ _ (by
    intro i; unfold mix; split <;> first | exact he _ | exact hd _)]
  simp only [mix_even,RelativeConstructible.PowerBound]

end TuringRigidity.NumericSyntax

end OAI
