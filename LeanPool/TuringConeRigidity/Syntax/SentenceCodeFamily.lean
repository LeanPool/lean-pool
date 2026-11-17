/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/SentenceCodeFamily.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.SentenceCode
public import LeanPool.TuringConeRigidity.Syntax.FiniteSatisfactionCertificate

/-!
# Sentence Code Family
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.SentenceCoding
open ElementaryModel RelativeConstructible BoundedSetTheory TransitiveNameModel
universe u

noncomputable def family (p : SentenceForm) : ZFSet.{u} :=
  ZFSet.range (fun i : Fin (subformulas p).length =>
    natSet (Encodable.encode (subformulas p)[i]))

theorem mem_family (p : SentenceForm) (z : ZFSet.{u}) :
    z ∈ family p ↔ ∃ q ∈ subformulas p, z = natSet (Encodable.encode q) := by
  rw [family,ZFSet.mem_range]
  constructor
  · rintro ⟨i,rfl⟩; exact ⟨_,List.getElem_mem i.isLt,rfl⟩
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hq
    exact ⟨⟨i,hi⟩,rfl⟩

theorem code_mem_family (p q : SentenceForm) :
    natSet.{u} (Encodable.encode q) ∈ family p ↔ q ∈ subformulas p := by
  rw [mem_family]
  constructor
  · rintro ⟨r,hr,he⟩
    have h : q = r := Encodable.encode_injective (natSet_injective he)
    exact h ▸ hr
  · intro h; exact ⟨q,h,rfl⟩

theorem family_subset_omega (p : SentenceForm) : family p ⊆ ZFSet.omega.{u} := by
  intro z hz
  obtain ⟨q,_,rfl⟩ := (mem_family p z).mp hz
  exact (mem_omega _).mpr ⟨_,rfl⟩

theorem family_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    (hU : BoundedSetTheory.Union M) (hω : ZFSet.omega.{u} ∈ M) (p : SentenceForm) :
    family p ∈ M := by
  have hn (k : ℕ) : natSet.{u} k ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨k,rfl⟩)
  exact finite_range_mem M hM hP hU (hn 0) _ _ (fun _ => hn _)

theorem family_closed (p : SentenceForm) :
    Closed (fun n => natSet.{u} n ∈ family p) := by
  intro n hn
  obtain ⟨q,hq,he⟩ := (mem_family p _).mp hn
  have he' := natSet_injective he
  subst n
  rw [step_encode]
  have hc := subformulas_closed p q hq
  cases q with
  | equal i j => trivial
  | member i j => trivial
  | conj a b =>
    exact ⟨(code_mem_family p a).mpr (hc a (by simp [subformulas,self_mem_subformulas])),
      (code_mem_family p b).mpr (hc b (by simp [subformulas,self_mem_subformulas]))⟩
  | neg a => exact (code_mem_family p a).mpr (hc a (by simp [subformulas,self_mem_subformulas]))
  | ex a => exact (code_mem_family p a).mpr (hc a (by simp [subformulas,self_mem_subformulas]))

theorem Closed.subformulas {C : ℕ → Prop} (h : Closed C) (p : SentenceForm)
    (hp : C (Encodable.encode p)) : ∀ q ∈ subformulas p, C (Encodable.encode q) := by
  induction p with
  | equal i j => simpa [RelativeConstructible.subformulas] using hp
  | member i j => simpa [RelativeConstructible.subformulas] using hp
  | conj p r ihp ihr =>
    have hc := (step_encode C (.conj p r)).mp (h _ hp)
    intro q hq
    simp only [RelativeConstructible.subformulas,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|hq|hq
    · exact hp
    · exact ihp hc.1 q hq
    · exact ihr hc.2 q hq
  | neg p ih =>
    have hc := (step_encode C (.neg p)).mp (h _ hp)
    intro q hq
    simp only [RelativeConstructible.subformulas,List.mem_cons] at hq
    rcases hq with rfl|hq
    · exact hp
    · exact ih hc q hq
  | ex p ih =>
    have hc := (step_encode C (.ex p)).mp (h _ hp)
    intro q hq
    simp only [RelativeConstructible.subformulas,List.mem_cons] at hq
    rcases hq with rfl|hq
    · exact hp
    · exact ih hc q hq

def SetClosed (S : ZFSet.{u}) : Prop :=
  S ⊆ ZFSet.omega ∧ Closed (fun n => natSet n ∈ S)

theorem family_setClosed (p : SentenceForm) : SetClosed (family.{u} p) :=
  ⟨family_subset_omega p,family_closed p⟩

theorem family_least (p : SentenceForm) (S : ZFSet.{u}) (hS : SetClosed S)
    (hp : natSet (Encodable.encode p) ∈ S) : family p ⊆ S := by
  intro z hz
  obtain ⟨q,hq,rfl⟩ := (mem_family p z).mp hz
  exact hS.2.subformulas p hp q hq

def LeastFamily (Q c S : ZFSet.{u}) : Prop :=
  c ∈ S ∧ SetClosed S ∧
    ∀ T ∈ Q, c ∈ T → SetClosed T → S ⊆ T

theorem leastFamily_spec (Q S : ZFSet.{u}) (p : SentenceForm) (hQ : family p ∈ Q) :
    LeastFamily Q (natSet (Encodable.encode p)) S ↔ S = family p := by
  constructor
  · rintro ⟨hc,hs,hm⟩
    exact ZFSet.ext (fun z => ⟨fun hz => hm _ hQ
      ((code_mem_family p p).mpr (self_mem_subformulas p)) (family_setClosed p) hz,
      fun hz => family_least p S hs hc hz⟩)
  · rintro rfl
    exact ⟨(code_mem_family p p).mpr (self_mem_subformulas p),family_setClosed p,
      fun T _ hc hs => family_least p T hs hc⟩

theorem setClosed_valid (S : ZFSet.{u}) (hS : SetClosed S) (c : ZFSet.{u}) (hc : c ∈ S) :
    ∃ p : SentenceForm, c = natSet (Encodable.encode p) := by
  obtain ⟨n,rfl⟩ := (mem_omega c).mp (hS.1 hc)
  obtain ⟨p,rfl⟩ := hS.2.valid n hc
  exact ⟨p,rfl⟩

theorem internal_family_bound (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hω : ZFSet.omega.{u} ∈ M) :
    ∃ Q ∈ M, (∀ S, S ∈ Q ↔ S ∈ M ∧ S ⊆ ZFSet.omega) ∧
      ∀ p : SentenceForm, family p ∈ Q := by
  obtain ⟨Q,hQ,hdef⟩ := internal_power M hM hPow hω
  exact ⟨Q,hQ,hdef,fun p => (hdef _).mpr
    ⟨family_mem M hM hP hU hω p,family_subset_omega p⟩⟩

end TuringRigidity.SentenceCoding

end OAI
