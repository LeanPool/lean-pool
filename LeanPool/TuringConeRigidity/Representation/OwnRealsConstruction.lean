/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/OwnRealsConstruction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.CanonicalRealsSyntax
public import LeanPool.TuringConeRigidity.Computability.ArithmeticFreeConstruction
public import LeanPool.TuringConeRigidity.Constructibility.FiniteStageDefinition

/-!
# Own Reals Construction
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

noncomputable def Construction.ownRealsSlots (t : Construction.{u}) : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | k+3 => match t.ordinalData k with | none => 0 | some _ => k+3

noncomputable def Construction.ownRealsMembership (t : Construction.{u}) : SentenceForm :=
  .ex (.conj (canonicalReals 0) (t.arithmeticFreeMembership.rename t.ownRealsSlots))

noncomputable def Construction.ownRealsInputs (t : Construction.{u}) (R : ZFSet.{u})
    (P : Oracle) : ℕ → ZFSet.{u} :=
  cons (realCode P) (fun k => match t.ordinalData k with
    | none => realCode P
    | some o => level R o)

theorem Construction.ownRealsSlots_env (t : Construction.{u}) (R : ZFSet.{u})
    (P : Oracle) (z : ZFSet.{u}) :
    (fun i => cons R (cons z (t.ownRealsInputs R P)) (t.ownRealsSlots i)) =
      cons z (t.arithmeticFreeInputs R P) := by
  funext i
  rcases i with _|_|_|i
  · rfl
  · rfl
  · rfl
  · change (cons R (cons z (t.ownRealsInputs R P)))
      (match t.ordinalData i with | none => 0 | some _ => i+3) = t.stageInputs R i
    rw [t.stageInputs_eq]
    cases hidx : t.ordinalData i <;> simp [Construction.ownRealsInputs,hidx,cons,stageParameter]

theorem Construction.ownRealsInputs_mem (t : Construction.{u}) (M R : ZFSet.{u})
    (P : Oracle) (he : ∀ i, t.singleInputs R P i ∈ M) : ∀ i, t.ownRealsInputs R P i ∈ M := by
  intro i
  cases i with
  | zero => exact he 1
  | succ k =>
    have hs : t.stageInputs R k ∈ M := he (k+5)
    rw [t.stageInputs_eq] at hs
    change (match t.ordinalData k with | none => realCode P | some o => level R o) ∈ M
    cases hidx : t.ordinalData k with
    | none => exact he 1
    | some o => simpa only [hidx,stageParameter] using hs

theorem Construction.ownRealsMembership_spec (t : Construction.{u}) (M R : ZFSet.{u})
    (hM : Transitive M) (hR : groundReals M = R) (P : Oracle) (ht : t.Certified R P)
    (he : ∀ i, t.singleInputs R P i ∈ M) (hv : t.value R P ∈ M)
    (z : ZFSet.{u}) (hz : z ∈ M) :
    t.ownRealsMembership.Sat (M : Set ZFSet) (cons z (t.ownRealsInputs R P)) ↔ z ∈ t.value R P := by
  let e := cons z (t.ownRealsInputs R P)
  have he' (i : ℕ) : e i ∈ M := by
    cases i
    · exact hz
    · exact t.ownRealsInputs_mem M R P he _
  have hf (r : ZFSet.{u}) (hr : r ∈ M) :
      (canonicalReals 0).Sat (M : Set ZFSet) (cons r e) ↔ r = R := by
    rw [canonicalReals_spec M hM (he 2) 0 _
      (by
        intro i
        cases i
        · exact hr
        · exact he' _),hR]
    rfl
  have hb : (t.arithmeticFreeMembership.rename t.ownRealsSlots).Sat (M : Set ZFSet) (cons R e) ↔
      z ∈ t.value R P := by
    rw [SentenceForm.sat_rename]
    change t.arithmeticFreeMembership.Sat (M : Set ZFSet)
      (fun i => cons R (cons z (t.ownRealsInputs R P)) (t.ownRealsSlots i)) ↔ _
    rw [t.ownRealsSlots_env]
    exact t.arithmeticFreeMembership_spec M R hM P ht he hv z hz
  change (∃ r ∈ M, (canonicalReals 0).Sat (M : Set ZFSet) (cons r e) ∧
    (t.arithmeticFreeMembership.rename t.ownRealsSlots).Sat (M : Set ZFSet) (cons r e)) ↔ _
  constructor
  · rintro ⟨r,hr,hrS,hp⟩
    obtain rfl := (hf r hr).mp hrS
    exact hb.mp hp
  · intro hp
    exact ⟨R,he 0,(hf R (he 0)).mpr rfl,hb.mpr hp⟩

end TuringRigidity.RelativeConstructible

end OAI
