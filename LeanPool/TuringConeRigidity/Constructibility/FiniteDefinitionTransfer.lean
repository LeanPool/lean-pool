/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/FiniteDefinitionTransfer.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.SentenceInlining

/-!
# Finite Definition Transfer
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem finite_real_tail (p : SentenceForm) (D : Set ZFSet.{u})
    (z P : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    p.Sat D (cons z (cons P (tupleEnv (fun i : Fin p.bound => e i)))) ↔
      p.Sat D (cons z (cons P e)) := by
  apply p.finite_support
  intro i hi
  rcases i with _|_|i
  · rfl
  · rfl
  · simp only [cons_succ,tupleEnv,dite_eq_left (show i < p.bound by omega)]

theorem definedSubset_of_membership (M V : ZFSet.{u}) (hM : Transitive M)
    (hV : V ∈ M) (p : SentenceForm) (e : ℕ → ZFSet.{u})
    (hp : ∀ z ∈ M, p.Sat (M : Set ZFSet) (cons z e) ↔ z ∈ V) :
    V = definedSubset M p (fun i : Fin p.bound => e i) := by
  apply ZFSet.ext; intro z
  rw [mem_definedSubset]
  have hs := p.finite_support (M : Set ZFSet) (cons z e)
    (cons z (tupleEnv (fun i : Fin p.bound => e i)))
    (by
      intro i hin
      cases i with
      | zero => rfl
      | succ i => simp only [cons_succ,tupleEnv,dite_eq_left (show i < p.bound by omega)])
  constructor
  · intro hz
    have hzM := hM V hV z hz
    exact ⟨hzM,hs.mp ((hp z hzM).mpr hz)⟩
  · rintro ⟨hzM,hz⟩
    exact (hp z hzM).mp (hs.mpr hz)

end TuringRigidity.RelativeConstructible

end OAI
