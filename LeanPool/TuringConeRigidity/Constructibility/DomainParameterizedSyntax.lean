/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/DomainParameterizedSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.HierarchyCertificatePower
public import LeanPool.TuringConeRigidity.Representation.AmbientDegreeSyntax

/-!
# Domain Parameterized Syntax
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedDefinability
open ElementaryModel BoundedSetTheory TransitiveNameModel SetModelFunctions RelativeConstructible
universe u

/-- A full formula with finitely many parameters from `M` defines the domain-dependent
predicate in every suitable transitive set. -/
def DomainDefinable (M : ZFSet.{u})
    (P : ZFSet.{u} → (ℕ → ZFSet.{u}) → Prop) : Prop :=
  ∃ p : SentenceForm, ∃ d : ℕ → ZFSet.{u}, ∃ k : ℕ,
    (∀ i, ∃ j, j < k ∧ d i = d j) ∧ (∀ i, d i ∈ M) ∧
    ∀ N : ZFSet.{u}, Transitive N → (∀ i, d i ∈ N) →
      ∀ e, (∀ i, e i ∈ N) → (p.Sat (N : Set ZFSet) (mix e d) ↔ P N e)

variable {M : ZFSet.{u}} {P Q : ZFSet.{u} → (ℕ → ZFSet.{u}) → Prop}

theorem Definable.toDomain {P : (ℕ → ZFSet.{u}) → Prop} (h : Definable M P) :
    DomainDefinable M (fun _ e => P e) := by
  obtain ⟨p,d,hd,hp⟩ := h
  let b := (fromBounded p).bound + 1
  let d' : ℕ → ZFSet.{u} := fun i => d (if i < b then i else 0)
  have hn (i : ℕ) : ∃ j, j < b ∧ d' i = d' j := by
    by_cases hi : i < b
    · exact ⟨i,hi,rfl⟩
    · exact ⟨0,by dsimp [b]; omega,by simp [d',hi,show 0 < b by dsimp [b]; omega]⟩
  have heq (e : ℕ → ZFSet.{u}) : p.Eval (mix e d') ↔ p.Eval (mix e d) := by
    rw [← bounded_univ,← bounded_univ]
    apply (fromBounded p).finite_support
    intro i hi
    unfold mix
    split
    · rfl
    · dsimp [d']
      rw [ite_eq_left (show i / 2 < b by dsimp [b]; omega)]
  refine ⟨fromBounded p,d',b,hn,fun i => hd _,?_⟩
  intro N hN hdN e he
  rw [bounded_sat,Formula.absolute p N hN _ (by
    intro i; unfold mix; split <;> first | exact he _ | exact hdN _)]
  exact (heq e).trans (hp e)

theorem DomainDefinable.congr (h : DomainDefinable M P)
    (heq : ∀ N e, P N e ↔ Q N e) : DomainDefinable M Q := by
  obtain ⟨p,d,k,hk,hd,hp⟩ := h
  exact ⟨p,d,k,hk,hd,fun N hN hdN e he => (hp N hN hdN e he).trans (heq N e)⟩

theorem DomainDefinable.and (hP : DomainDefinable M P) (hQ : DomainDefinable M Q) :
    DomainDefinable M (fun N e => P N e ∧ Q N e) := by
  obtain ⟨p,d,k,hk,hd,hp⟩ := hP
  obtain ⟨q,c,l,hl,hc,hq⟩ := hQ
  refine ⟨.conj (p.rename (slotMap id (fun i => 2*i)))
    (q.rename (slotMap id (fun i => 2*i+1))),mix d c,2 * max k l,?_,?_,?_⟩
  · intro i
    by_cases hi : i % 2 = 0
    · obtain ⟨j,hj,heq⟩ := hk (i/2)
      refine ⟨2*j,by omega,?_⟩
      rw [mix_even]
      simpa only [mix,ite_eq_left hi] using heq
    · obtain ⟨j,hj,heq⟩ := hl (i/2)
      refine ⟨2*j+1,by omega,?_⟩
      rw [mix_odd]
      simpa only [mix,ite_eq_right hi] using heq
  · intro i; unfold mix; split <;> first | exact hd _ | exact hc _
  · intro N hN hdc e he
    have hdN (i : ℕ) : d i ∈ N := by simpa only [mix_even] using hdc (2*i)
    have hcN (i : ℕ) : c i ∈ N := by simpa only [mix_odd] using hdc (2*i+1)
    have hd' : mix d c ∘ (fun i => 2*i) = d := by funext i; simp
    have hc' : mix d c ∘ (fun i => 2*i+1) = c := by funext i; simp
    change (p.rename _).Sat _ _ ∧ (q.rename _).Sat _ _ ↔ _
    simp only [SentenceForm.sat_rename]
    change p.Sat _ (mix e (mix d c) ∘ slotMap id (fun i => 2*i)) ∧
      q.Sat _ (mix e (mix d c) ∘ slotMap id (fun i => 2*i+1)) ↔ _
    rw [mix_slotMap,mix_slotMap,Function.comp_id,hd',hc',hp N hN hdN e he,hq N hN hcN e he]

theorem DomainDefinable.existsSet (h : DomainDefinable M P) :
    DomainDefinable M (fun N e => ∃ x ∈ N, P N (cons x e)) := by
  obtain ⟨p,d,k,hk,hd,hp⟩ := h
  refine ⟨.ex (p.rename bindSlots),d,k,hk,hd,?_⟩
  intro N hN hdN e he
  change (∃ x ∈ N, (p.rename bindSlots).Sat _ (cons x (mix e d))) ↔ _
  apply exists_congr; intro x
  apply and_congr_right; intro hx
  rw [SentenceForm.sat_rename]
  change p.Sat _ (cons x (mix e d) ∘ bindSlots) ↔ _
  rw [bind_mix]
  exact hp N hN hdN (cons x e) (by
    intro i
    cases i
    · exact hx
    · exact he _)

theorem powerBound_domainDefinable (C : Context M) (a q : ℕ) :
    DomainDefinable M (fun N e => PowerBound N (e a) (e q)) := by
  refine ⟨FullSetForcing.ownPower (2*a) (2*q),fun _ => ZFSet.omega,1,
    fun _ => ⟨0,by decide,rfl⟩,fun _ => C.omega_mem,?_⟩
  intro N hN hd e he
  rw [FullSetForcing.ownPower_spec N hN _ _ _ (by
    intro i; unfold mix; split <;> first | exact he _ | exact hd 0)]
  simp only [mix_even,PowerBound]

end TuringRigidity.BoundedDefinability

end OAI
