/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/UniformSigmaDefinability.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.SourceTheory
public import LeanPool.TuringConeRigidity.Syntax.BoundedDefinability

/-!
# Uniform Sigma Definability
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedDefinability
open BoundedSetTheory TransitiveNameModel SetModelFunctions
universe u

/-- A uniform sigma formula defines the predicate over transitive SourceT extensions
containing `M`. -/
def UniformSigmaDefinable (M : ZFSet.{u})
    (P : ZFSet.{u} → (ℕ → ZFSet.{u}) → Prop) : Prop :=
  ∃ p : SigmaFormula, ∃ d : ℕ → ZFSet.{u}, (∀ i, d i ∈ M) ∧
    ∀ E : ZFSet.{u}, Transitive E → SourceT E → M ⊆ E →
      ∀ e, (∀ i, e i ∈ E) → (p.Realize E (mix e d) ↔ P E e)

variable {M : ZFSet.{u}} {P Q : ZFSet.{u} → (ℕ → ZFSet.{u}) → Prop}

theorem Definable.toUniformSigma {R : (ℕ → ZFSet.{u}) → Prop} (h : Definable M R) :
    UniformSigmaDefinable M (fun _ e => R e) := by
  obtain ⟨p,d,hd,hp⟩ := h
  refine ⟨.bounded p,d,hd,?_⟩
  intro E hE _ hME e he
  exact (p.absolute E hE (mix e d) (by
    intro i; unfold mix; split <;> first | exact he _ | exact hME (hd _))).trans (hp e)

theorem UniformSigmaDefinable.existsSet (h : UniformSigmaDefinable M P) :
    UniformSigmaDefinable M (fun E e => ∃ x ∈ E, P E (cons x e)) := by
  obtain ⟨p,d,hd,hp⟩ := h
  refine ⟨.existsSet (p.rename bindSlots),d,hd,?_⟩
  intro E hE hTE hME e he
  simp only [SigmaFormula.Realize,SigmaFormula.realize_rename]
  apply exists_congr; intro x
  apply and_congr_right; intro hx
  change (p.Realize E (cons x (mix e d) ∘ bindSlots)) ↔ _
  rw [bind_mix]
  exact hp E hE hTE hME (cons x e) (by
    intro i
    cases i
    · exact hx
    · exact he _)

theorem UniformSigmaDefinable.congr (h : UniformSigmaDefinable M P)
    (hPQ : ∀ E : ZFSet.{u}, Transitive E → SourceT E → M ⊆ E →
      ∀ e, (∀ i, e i ∈ E) → (P E e ↔ Q E e)) : UniformSigmaDefinable M Q := by
  obtain ⟨p,d,hd,hp⟩ := h
  exact ⟨p,d,hd,fun E hE hTE hME e he =>
    (hp E hE hTE hME e he).trans (hPQ E hE hTE hME e he)⟩

theorem UniformSigmaDefinable.subst (h : UniformSigmaDefinable M P) (r : ℕ → ℕ) :
    UniformSigmaDefinable M (fun E e => P E (e ∘ r)) := by
  obtain ⟨p,d,hd,hp⟩ := h
  refine ⟨p.rename (slotMap r id),d,hd,?_⟩
  intro E hE hTE hME e he
  rw [SigmaFormula.realize_rename]
  change p.Realize E (mix e d ∘ slotMap r id) ↔ _
  simpa only [mix_slotMap,Function.comp_id] using
    hp E hE hTE hME (e ∘ r) (fun i => he (r i))

theorem UniformSigmaDefinable.and (hP : UniformSigmaDefinable M P)
    (hQ : UniformSigmaDefinable M Q) :
    UniformSigmaDefinable M (fun E e => P E e ∧ Q E e) := by
  obtain ⟨p,d,hd,hp⟩ := hP
  obtain ⟨q,c,hc,hq⟩ := hQ
  refine ⟨.conj (p.rename (slotMap id (fun i => 2*i)))
    (q.rename (slotMap id (fun i => 2*i+1))),mix d c,?_,?_⟩
  · intro i; unfold mix; split <;> first | exact hd _ | exact hc _
  · intro E hE hTE hME e he
    rw [SigmaFormula.realize_conj,SigmaFormula.realize_rename,SigmaFormula.realize_rename]
    have hd' : mix d c ∘ (fun i => 2*i) = d := by funext i; simp
    have hc' : mix d c ∘ (fun i => 2*i+1) = c := by funext i; simp
    change p.Realize E (mix e (mix d c) ∘ slotMap id (fun i => 2*i)) ∧
      q.Realize E (mix e (mix d c) ∘ slotMap id (fun i => 2*i+1)) ↔ _
    rw [mix_slotMap,mix_slotMap,Function.comp_id,hd',hc',
      hp E hE hTE hME e he,hq E hE hTE hME e he]

theorem UniformSigmaDefinable.or (h0 : (∅ : ZFSet.{u}) ∈ M)
    (hP : UniformSigmaDefinable M P) (hQ : UniformSigmaDefinable M Q) :
    UniformSigmaDefinable M (fun E e => P E e ∨ Q E e) := by
  obtain ⟨p,d,hd,hp⟩ := hP
  obtain ⟨q,c,hc,hq⟩ := hQ
  refine ⟨.disj (p.rename (slotMap id (fun i => 2*i)))
    (q.rename (slotMap id (fun i => 2*i+1))),mix d c,?_,?_⟩
  · intro i; unfold mix; split <;> first | exact hd _ | exact hc _
  · intro E hE hTE hME e he
    rw [SigmaFormula.realize_disj E (hME
      h0),SigmaFormula.realize_rename,SigmaFormula.realize_rename]
    have hd' : mix d c ∘ (fun i => 2*i) = d := by funext i; simp
    have hc' : mix d c ∘ (fun i => 2*i+1) = c := by funext i; simp
    change p.Realize E (mix e (mix d c) ∘ slotMap id (fun i => 2*i)) ∨
      q.Realize E (mix e (mix d c) ∘ slotMap id (fun i => 2*i+1)) ↔ _
    rw [mix_slotMap,mix_slotMap,Function.comp_id,hd',hc',
      hp E hE hTE hME e he,hq E hE hTE hME e he]

theorem UniformSigmaDefinable.impBounded (C : Context M)
    {R : (ℕ → ZFSet.{u}) → Prop} (hR : Definable M R) (hQ : UniformSigmaDefinable M Q) :
    UniformSigmaDefinable M (fun E e => R e → Q E e) := by
  apply (hR.neg.toUniformSigma.or (C.nat_mem 0) hQ).congr
  intro E _ _ _ e _
  classical
  tauto

theorem UniformSigmaDefinable.allMem (h : UniformSigmaDefinable M P) (a : ℕ) :
    UniformSigmaDefinable M (fun E e => ∀ x ∈ e a, P E (cons x e)) := by
  obtain ⟨p,d,hd,hp⟩ := h
  refine ⟨.allMem (2*a) (p.rename bindSlots),d,hd,?_⟩
  intro E hE hTE hME e he
  have hC := sigma_collection E hE hTE.pairing hTE.union hTE.powerSet
    hTE.separation.finitePrefix hTE.replacement.finitePrefix hTE.infinity hTE.choice
  rw [SigmaFormula.realize_allMem E hE hTE.pairing hTE.union hTE.separation.finitePrefix.bounded
    hTE.replacement.finitePrefix hTE.infinity hC _ _ _ (by
      intro i; unfold mix; split <;> first | exact he _ | exact hME (hd _)),mix_even]
  apply forall_congr'; intro x
  apply forall_congr'; intro hx
  rw [SigmaFormula.realize_rename]
  change p.Realize E (cons x (mix e d) ∘ bindSlots) ↔ _
  rw [bind_mix]
  exact hp E hE hTE hME (cons x e) (by
    intro i
    cases i
    · exact hE _ (he a) x hx
    · exact he _)

end TuringRigidity.BoundedDefinability

end OAI
