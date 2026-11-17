/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticFreeConstruction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.BindCanonicalArithmetic
public import LeanPool.TuringConeRigidity.Constructibility.SingleRealConstruction

/-!
# Arithmetic Free Construction
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SetModelArithmetic
universe u

/-- Reorder construction parameters into the slots expected by arithmetic binding. -/
def arithmeticSlots : ℕ → ℕ
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 2
  | 4 => 0
  | 5 => 1
  | i+6 => i+6

/-- Bind the arithmetic parameters in a construction's single-membership sentence. -/
noncomputable def Construction.arithmeticFreeMembership (t : Construction.{u}) : SentenceForm :=
  bindArithmetic (t.singleMembership.rename arithmeticSlots)

/-- The parameter environment for a construction with arithmetic and real parameters made
explicit. -/
noncomputable def Construction.arithmeticFreeInputs (t : Construction.{u}) (R : ZFSet.{u})
    (P : Oracle) : ℕ → ZFSet.{u} := cons R (cons (realCode P) (t.stageInputs R))

theorem Construction.arithmeticSlots_env (t : Construction.{u}) (R : ZFSet.{u})
    (P : Oracle) (z : ZFSet.{u}) :
    (fun i => cons additionSet (cons pairNumbers (cons ZFSet.omega
      (cons z (t.arithmeticFreeInputs R P)))) (arithmeticSlots i)) =
      cons z (t.singleInputs R P) := by
  funext i
  rcases i with _|_|_|_|_|_|i <;> rfl

theorem Construction.arithmeticFreeInputs_mem (t : Construction.{u}) (M R : ZFSet.{u})
    (P : Oracle) (he : ∀ i, t.singleInputs R P i ∈ M) :
    ∀ i, t.arithmeticFreeInputs R P i ∈ M := by
  intro i
  rcases i with _|_|i
  · exact he 0
  · exact he 1
  · exact he (i+5)

theorem Construction.arithmeticFreeMembership_spec (t : Construction.{u}) (M R : ZFSet.{u})
    (hM : Transitive M) (P : Oracle) (ht : t.Certified R P)
    (he : ∀ i, t.singleInputs R P i ∈ M) (hv : t.value R P ∈ M)
    (z : ZFSet.{u}) (hz : z ∈ M) :
    t.arithmeticFreeMembership.Sat (M : Set ZFSet) (cons z (t.arithmeticFreeInputs R P)) ↔
      z ∈ t.value R P := by
  rw [Construction.arithmeticFreeMembership,bindArithmetic_spec M hM (he 2) (he 4) (he 3) _ _
    (by
      intro i
      cases i
      · exact hz
      · exact t.arithmeticFreeInputs_mem M R P he _),
    SentenceForm.sat_rename,t.arithmeticSlots_env]
  exact t.singleMembership_of_inputs M R hM P ht he hv z hz

end TuringRigidity.RelativeConstructible

end OAI
