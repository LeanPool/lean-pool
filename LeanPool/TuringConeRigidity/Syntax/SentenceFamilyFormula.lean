/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/SentenceFamilyFormula.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.SentenceCodeFamily
public import LeanPool.TuringConeRigidity.Syntax.SentenceCodeDefinability

/-!
# Sentence Family Formula
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.SentenceCoding
open ElementaryModel BoundedSetTheory TransitiveNameModel BoundedDefinability SetModelFunctions
universe u

variable {M : ZFSet.{u}}

/-- The set-coded form of the valid-constructor and child-closure step. -/
def SetStep (S c : ZFSet.{u}) : Prop :=
  (∃ x ∈ ZFSet.omega, ∃ y ∈ ZFSet.omega, BinaryGraph (fun i j => binary 0 (atom i) (atom j)) x y
    c) ∨
  (∃ x ∈ ZFSet.omega, ∃ y ∈ ZFSet.omega, BinaryGraph (fun i j => binary 1 (atom i) (atom j)) x y
    c) ∨
  (∃ x ∈ S, ∃ y ∈ S, BinaryGraph (binary 2) x y c) ∨
  (∃ x ∈ S, UnaryGraph (unary 3) x c) ∨
  (∃ x ∈ S, UnaryGraph (unary 4) x c)

theorem setStep_nat (S : ZFSet.{u}) (n : ℕ) :
    SetStep S (natSet n) ↔ Step (fun k => natSet k ∈ S) n := by
  simp only [SetStep,Step,BinaryGraph,UnaryGraph]
  have hn (a b : ℕ) : natSet.{u} a = natSet b ↔ a = b := natSet_injective.eq_iff
  simp only [hn]
  constructor
  · intro h
    rcases h with h|h|h|h|h
    · obtain ⟨x,_,y,_,i,j,_,_,he⟩ := h; exact Or.inl ⟨i,j,he⟩
    · obtain ⟨x,_,y,_,i,j,_,_,he⟩ := h; exact Or.inr (Or.inl ⟨i,j,he⟩)
    · obtain ⟨x,hx,y,hy,i,j,rfl,rfl,he⟩ := h
      exact Or.inr (Or.inr (Or.inl ⟨i,j,he,hx,hy⟩))
    · obtain ⟨x,hx,i,rfl,he⟩ := h
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i,he,hx⟩)))
    · obtain ⟨x,hx,i,rfl,he⟩ := h
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i,he,hx⟩)))
  · intro h
    have hw (k : ℕ) : natSet.{u} k ∈ ZFSet.omega := (mem_omega _).mpr ⟨k,rfl⟩
    rcases h with h|h|h|h|h
    · obtain ⟨i,j,he⟩ := h
      exact Or.inl ⟨_,hw i,_,hw j,i,j,rfl,rfl,he⟩
    · obtain ⟨i,j,he⟩ := h
      exact Or.inr (Or.inl ⟨_,hw i,_,hw j,i,j,rfl,rfl,he⟩)
    · obtain ⟨i,j,he,hi,hj⟩ := h
      exact Or.inr (Or.inr (Or.inl ⟨_,hi,_,hj,i,j,rfl,rfl,he⟩))
    · obtain ⟨i,he,hi⟩ := h
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_,hi,i,rfl,he⟩)))
    · obtain ⟨i,he,hi⟩ := h
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_,hi,i,rfl,he⟩)))

theorem setStep_definable (C : Context M) (s c : ℕ) :
    Definable M (fun e => SetStep (e s) (e c)) := by
  have he := ((binaryGraph_definable C _ (atomic_primrec 0) 1 0 (c+2)).existsParam
    C.omega_mem).existsParam C.omega_mem
  have hm := ((binaryGraph_definable C _ (atomic_primrec 1) 1 0 (c+2)).existsParam
    C.omega_mem).existsParam C.omega_mem
  have ha := ((binaryGraph_definable C _ (binary_primrec 2) 1 0 (c+2)).existsMem (s+1)).existsMem s
  have hn := (unaryGraph_definable C _ (unary_primrec 3) 0 (c+1)).existsMem s
  have hx := (unaryGraph_definable C _ (unary_primrec 4) 0 (c+1)).existsMem s
  exact defOr he (defOr hm (defOr ha (defOr hn hx)))

theorem setClosed_spec (S : ZFSet.{u}) :
    SetClosed S ↔ S ⊆ ZFSet.omega ∧ ∀ c ∈ S, SetStep S c := by
  constructor
  · rintro ⟨hs,hc⟩
    refine ⟨hs,fun c hm => ?_⟩
    obtain ⟨n,rfl⟩ := (mem_omega c).mp (hs hm)
    exact (setStep_nat S n).mpr (hc n hm)
  · rintro ⟨hs,hc⟩
    exact ⟨hs,fun n hn => (setStep_nat S n).mp (hc _ hn)⟩

theorem setClosed_definable (C : Context M) (s : ℕ) :
    Definable M (fun e => SetClosed (e s)) := by
  have hs := defAllMem (defMemberParam C.omega_mem 0) s
  have hc := defAllMem (setStep_definable C (s+1) 0) s
  exact (hs.and hc).congr (fun e => (setClosed_spec (e s)).symm)

theorem leastFamily_definable (C : Context M) (q c s : ℕ) :
    Definable M (fun e => LeastFamily (e q) (e c) (e s)) := by
  have hm := defAllMem (defImp (member_definable C (c+1) 0)
    (defImp (setClosed_definable C 0) (defSubset C (s+1) 0))) q
  exact (member_definable C c s).and ((setClosed_definable C s).and hm)

theorem uniform_family_definition (C : Context M) :
    ∃ Q ∈ M, ∃ p : Formula, ∃ d : ℕ → ZFSet.{u}, (∀ i, d i ∈ M) ∧
      ∀ c S, p.Eval (mix (cons c (fun _ => S)) d) ↔
        ∃ root : SentenceForm, c = natSet (Encodable.encode root) ∧ S = family root := by
  obtain ⟨Q,hQ,_,hf⟩ := internal_family_bound M C.transitive C.pairing C.union C.power C.omega_mem
  have hd : Definable M (fun e => LeastFamily Q (e 0) (e 1)) := by
    have hs : ({Q} : ZFSet.{u}) ∈ M := singleton_mem M C.transitive C.pairing hQ
    exact (((equal_param hQ 0).and (leastFamily_definable C 0 1 2)).existsParam hs).congr
      (fun e => by simp only [ZFSet.mem_singleton,cons_zero,cons_succ]; simp)
  obtain ⟨p,d,hd,hdef⟩ := hd
  refine ⟨Q,hQ,p,d,hd,?_⟩
  intro c S
  rw [hdef]
  change LeastFamily Q c S ↔ _
  constructor
  · intro h
    obtain ⟨root,hr⟩ := setClosed_valid S h.2.1 c h.1
    exact ⟨root,hr,(leastFamily_spec Q S root (hf root)).mp (hr ▸ h)⟩
  · rintro ⟨root,rfl,rfl⟩
    exact (leastFamily_spec Q (family root) root (hf root)).mpr rfl

end TuringRigidity.SentenceCoding

end OAI
