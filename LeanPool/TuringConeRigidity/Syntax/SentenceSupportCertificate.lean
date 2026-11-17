/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/SentenceSupportCertificate.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.SentenceCodeFamily

/-!
# Sentence Support Certificate
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.SentenceCoding
open ElementaryModel RelativeConstructible BoundedSetTheory TransitiveNameModel
universe u

noncomputable def supportGraph (p : SentenceForm) : ZFSet.{u} :=
  ZFSet.range (fun i : Fin (subformulas p).length =>
    ZFSet.pair (natSet (Encodable.encode (subformulas p)[i])) (natSet (subformulas p)[i].bound))

theorem mem_supportGraph (p : SentenceForm) (z : ZFSet.{u}) :
    z ∈ supportGraph p ↔ ∃ q ∈ subformulas p,
      z = ZFSet.pair (natSet (Encodable.encode q)) (natSet q.bound) := by
  rw [supportGraph,ZFSet.mem_range]
  constructor
  · rintro ⟨i,rfl⟩; exact ⟨_,List.getElem_mem i.isLt,rfl⟩
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hq
    exact ⟨⟨i,hi⟩,rfl⟩

def HasBound (G : ZFSet.{u}) (p : SentenceForm) (n : ℕ) : Prop :=
  ZFSet.pair (natSet (Encodable.encode p)) (natSet n) ∈ G

theorem supportGraph_bound (p q : SentenceForm) (n : ℕ) :
    HasBound (supportGraph.{u} p) q n ↔ q ∈ subformulas p ∧ n = q.bound := by
  rw [HasBound,mem_supportGraph]
  constructor
  · rintro ⟨r,hr,he⟩
    obtain ⟨hc,hb⟩ := ZFSet.pair_inj.mp he
    have hqr : q = r := Encodable.encode_injective (natSet_injective hc)
    subst r
    exact ⟨hr,natSet_injective hb⟩
  · rintro ⟨hq,rfl⟩; exact ⟨q,hq,rfl⟩

def SupportStep (G : ZFSet.{u}) : SentenceForm → ℕ → Prop
  | .equal i j, b | .member i j, b => b = max i j + 1
  | .conj p q, b => ∃ i j, HasBound G p i ∧ HasBound G q j ∧ b = max i j
  | .neg p, b => HasBound G p b
  | .ex p, b => ∃ i, HasBound G p i ∧ b = i-1

def SupportRecursion (root : SentenceForm) (G : ZFSet.{u}) : Prop :=
  (∀ z ∈ G, ∃ p ∈ subformulas root, ∃ n : ℕ,
    z = ZFSet.pair (natSet (Encodable.encode p)) (natSet n)) ∧
  ∀ p ∈ subformulas root, ∀ n, HasBound G p n ↔ SupportStep G p n

theorem supportGraph_recursion (root : SentenceForm) : SupportRecursion root (supportGraph.{u}
  root) := by
  constructor
  · intro z hz
    obtain ⟨p,hp,rfl⟩ := (mem_supportGraph root z).mp hz
    exact ⟨p,hp,p.bound,rfl⟩
  · intro p hp n
    rw [supportGraph_bound, and_iff_right hp]
    have hc := subformulas_closed root p hp
    cases p with
    | equal i j => rfl
    | member i j => rfl
    | conj p q =>
      have hp' := hc p (by simp [subformulas,self_mem_subformulas])
      have hq' := hc q (by simp [subformulas,self_mem_subformulas])
      simp [SupportStep,supportGraph_bound,hp',hq',SentenceForm.bound]
    | neg p =>
      have hp' := hc p (by simp [subformulas,self_mem_subformulas])
      simp [SupportStep,supportGraph_bound,hp',SentenceForm.bound]
    | ex p =>
      have hp' := hc p (by simp [subformulas,self_mem_subformulas])
      simp [SupportStep,supportGraph_bound,hp',SentenceForm.bound]

theorem SupportRecursion.correct {root : SentenceForm} {G : ZFSet.{u}}
    (h : SupportRecursion root G) (p : SentenceForm) (hp : p ∈ subformulas root) (n : ℕ) :
    HasBound G p n ↔ n = p.bound := by
  induction p generalizing n with
  | equal i j => exact h.2 _ hp n
  | member i j => exact h.2 _ hp n
  | conj p q ihp ihq =>
    have hp' := subformulas_closed root _ hp p (by simp [subformulas,self_mem_subformulas])
    have hq' := subformulas_closed root _ hp q (by simp [subformulas,self_mem_subformulas])
    rw [h.2 _ hp n]
    simp [SupportStep,ihp hp',ihq hq',SentenceForm.bound]
  | neg p ih =>
    have hp' := subformulas_closed root _ hp p (by simp [subformulas,self_mem_subformulas])
    exact (h.2 _ hp n).trans (ih hp' n)
  | ex p ih =>
    have hp' := subformulas_closed root _ hp p (by simp [subformulas,self_mem_subformulas])
    rw [h.2 _ hp n]
    simp [SupportStep,ih hp',SentenceForm.bound]

theorem SupportRecursion.unique {root : SentenceForm} {G : ZFSet.{u}}
    (h : SupportRecursion root G) : G = supportGraph root := by
  apply ZFSet.ext; intro z
  constructor
  · intro hz
    obtain ⟨p,hp,n,rfl⟩ := h.1 z hz
    exact (supportGraph_bound root p n).mpr ⟨hp,(h.correct p hp n).mp hz⟩
  · intro hz
    obtain ⟨p,hp,rfl⟩ := (mem_supportGraph root z).mp hz
    exact (h.correct p hp p.bound).mpr rfl

theorem supportGraph_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    (hU : BoundedSetTheory.Union M) (hω : ZFSet.omega.{u} ∈ M) (p : SentenceForm) :
    supportGraph p ∈ M := by
  have hn (k : ℕ) : natSet.{u} k ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨k,rfl⟩)
  exact finite_range_mem M hM hP hU (hn 0) _ _
    (fun _ => orderedPair_mem M hM hP (hn _) (hn _))

theorem supportGraph_subset (p : SentenceForm) :
    supportGraph p ⊆ ZFSet.prod ZFSet.omega.{u} ZFSet.omega := by
  intro z hz
  obtain ⟨q,_,rfl⟩ := (mem_supportGraph p z).mp hz
  exact ZFSet.mem_prod.mpr ⟨_,(mem_omega _).mpr ⟨_,rfl⟩,_,(mem_omega _).mpr ⟨_,rfl⟩,rfl⟩

end TuringRigidity.SentenceCoding

end OAI
