/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/SatisfactionRecursion.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.FiniteSatisfactionCertificate

/-!
# Satisfaction Recursion
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

def truthStep (A S : ZFSet.{u}) {n : ℕ} (v : Fin n → ZFSet.{u}) : SentenceForm → Prop
  | .equal i j => tupleEnv v i = tupleEnv v j
  | .member i j => tupleEnv v i ∈ tupleEnv v j
  | .conj p q => accepts S p v ∧ accepts S q v
  | .neg p => ¬ accepts S p v
  | .ex p => ∃ x ∈ A, accepts S p (Fin.cases x v)

def TruthRecursion (A : ZFSet.{u}) (root : SentenceForm) (S : ZFSet.{u}) : Prop :=
  (∀ z ∈ S, ∃ p ∈ subformulas root, ∃ (n : ℕ) (v : Fin n → ZFSet.{u}),
    (∀ i, v i ∈ A) ∧ p.bound ≤ n ∧ z = ZFSet.pair (natSet (Encodable.encode p)) (tupleCode v)) ∧
  ∀ p ∈ subformulas root, ∀ (n : ℕ) (v : Fin n → ZFSet.{u}),
    (∀ i, v i ∈ A) → p.bound ≤ n → (accepts S p v ↔ truthStep A S v p)

theorem finiteSatisfaction_recursion (A : ZFSet.{u}) (root : SentenceForm) :
    TruthRecursion A root (finiteSatisfaction A (subformulas root)) := by
  constructor
  · intro z hz
    obtain ⟨p,hp,t,ht,rfl⟩ := (mem_finiteSatisfaction A z _).mp hz
    obtain ⟨n,v,hv,rfl⟩ := (mem_tupleSpace A t).mp (ZFSet.mem_sep.mp ht).1
    exact ⟨p,hp,n,v,hv,((truthSlice_record A p v hv).mp ht).1,rfl⟩
  · intro p hp n v hv hb
    cases p with
    | equal i j => exact certificate_correct A root _ hp v hv hb
    | member i j => exact certificate_correct A root _ hp v hv hb
    | conj p q => exact certificate_conj A root p q hp v hv hb
    | neg p => exact certificate_neg A root p hp v hv hb
    | ex p => exact certificate_ex A root p hp v hv hb

theorem TruthRecursion.correct {A S : ZFSet.{u}} {root : SentenceForm}
    (h : TruthRecursion A root S) (p : SentenceForm) (hp : p ∈ subformulas root)
    {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A) (hb : p.bound ≤ n) :
    accepts S p v ↔ p.Sat (A : Set ZFSet) (tupleEnv v) := by
  induction p generalizing n with
  | equal i j => exact h.2 _ hp n v hv hb
  | member i j => exact h.2 _ hp n v hv hb
  | conj p q ihp ihq =>
    have hp' := subformulas_closed root _ hp p (by simp [subformulas,self_mem_subformulas])
    have hq' := subformulas_closed root _ hp q (by simp [subformulas,self_mem_subformulas])
    have hbp : p.bound ≤ n := by simp only [SentenceForm.bound] at hb; omega
    have hbq : q.bound ≤ n := by simp only [SentenceForm.bound] at hb; omega
    exact (h.2 _ hp n v hv hb).trans (and_congr (ihp hp' v hv hbp) (ihq hq' v hv hbq))
  | neg p ih =>
    have hp' := subformulas_closed root _ hp p (by simp [subformulas,self_mem_subformulas])
    exact (h.2 _ hp n v hv hb).trans (not_congr (ih hp' v hv hb))
  | ex p ih =>
    have hp' := subformulas_closed root _ hp p (by simp [subformulas,self_mem_subformulas])
    have hbp : p.bound ≤ n+1 := by simp only [SentenceForm.bound] at hb; omega
    refine (h.2 (.ex p) hp n v hv hb).trans ?_
    simp only [truthStep,SentenceForm.Sat]
    apply exists_congr; intro x
    apply and_congr_right; intro hx
    rw [ih hp' (Fin.cases x v) (fun i => Fin.cases hx hv i) hbp,tupleEnv_cons]

theorem TruthRecursion.unique {A S T : ZFSet.{u}} {root : SentenceForm}
    (hS : TruthRecursion A root S) (hT : TruthRecursion A root T) : S = T := by
  have sub {U V : ZFSet.{u}} (hU : TruthRecursion A root U) (hV : TruthRecursion A root V) : U ⊆ V
    := by
    intro z hz
    obtain ⟨p,hp,n,v,hv,hb,rfl⟩ := hU.1 z hz
    exact (hV.correct p hp v hv hb).mpr ((hU.correct p hp v hv hb).mp hz)
  exact ZFSet.ext (fun _ => ⟨fun hz => sub hS hT hz,fun hz => sub hT hS hz⟩)

theorem internal_truthRecursion (M A : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (p : SentenceForm) :
    ∃ S ∈ M, TruthRecursion A p S ∧ ∀ T, TruthRecursion A p T → T = S := by
  refine ⟨finiteSatisfaction A (subformulas p),finiteSatisfaction_mem M A hM hT hA _,
    finiteSatisfaction_recursion A p,?_⟩
  exact fun T h => h.unique (finiteSatisfaction_recursion A p)

theorem satisfaction_iff_internal_recursion (M A : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (p : SentenceForm)
    {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A) :
    accepts (satisfactionSet A) p v ↔
      ∃ S ∈ M, TruthRecursion A p S ∧ accepts S p v := by
  constructor
  · intro h
    exact ⟨finiteSatisfaction A (subformulas p),finiteSatisfaction_mem M A hM hT hA _,
      finiteSatisfaction_recursion A p,(finiteSatisfaction_covers A p v hv).mpr h⟩
  · rintro ⟨S,_,hS,hs⟩
    have he := hS.unique (finiteSatisfaction_recursion A p)
    rw [he] at hs
    exact (finiteSatisfaction_covers A p v hv).mp hs

end TuringRigidity.RelativeConstructible

end OAI
