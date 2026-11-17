/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OrdinalInputSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.OwnRealsConstruction

/-!
# Ordinal Input Syntax
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

/-- Bind the model's own real set before applying the renamed stage definition. -/
noncomputable def ownStageFormula (p : SentenceForm) : SentenceForm :=
  .ex (.conj (canonicalReals 0) (p.rename (fun i => match i with | 0 => 1 | 1 => 2 | _ => 0)))

theorem ownStageFormula_spec (p : SentenceForm) (N R x A : ZFSet.{u}) (hN : Transitive N)
    (hw : ZFSet.omega.{u} ∈ N) (hR : groundReals N = R) (hRN : R ∈ N)
    (hA : A ∈ N) (hx : x ∈ N) :
    (ownStageFormula p).Sat (N : Set ZFSet) (cons A (fun _ => x)) ↔
      p.Sat (N : Set ZFSet) (cons A (cons x (fun _ => R))) := by
  have hf (r : ZFSet.{u}) (hr : r ∈ N) :
      (canonicalReals 0).Sat (N : Set ZFSet) (cons r (cons A (fun _ => x))) ↔ r = R := by
    rw [canonicalReals_spec N hN hw 0 _
      (by
        intro i
        rcases i with _|_|i
        · exact hr
        · exact hA
        · exact hx),hR]
    rfl
  have he (r : ZFSet.{u}) :
      (fun i => cons r (cons A (fun _ => x)) (match i with | 0 => 1 | 1 => 2 | _ => 0)) =
        cons A (cons x (fun _ => r)) := by
    funext i; rcases i with _|_|i <;> rfl
  change (∃ r ∈ N, (canonicalReals 0).Sat _ (cons r (cons A (fun _ => x))) ∧
    (p.rename _).Sat _ (cons r (cons A (fun _ => x)))) ↔ _
  simp only [SentenceForm.sat_rename,he]
  constructor
  · rintro ⟨r,hr,h,hp⟩
    obtain rfl := (hf r hr).mp h
    exact hp
  · intro hp
    exact ⟨R,hRN,(hf R hRN).mpr rfl,hp⟩

/-- The real parameter and the ordinal set codes required by the construction. -/
noncomputable def Construction.ordinalInputs (t : Construction.{u}) (P : Oracle) : ℕ → ZFSet.{u} :=
  cons (realCode P) (fun k => if k < t.ownRealsMembership.bound then
    match t.ordinalData k with | none => realCode P | some o => o.toZFSet
    else realCode P)

/-- Define the selected ordinal input slot, or use the real parameter for a non-ordinal slot. -/
noncomputable def Construction.ordinalInputFormula (t : Construction.{u}) (p : SentenceForm) (k :
  ℕ) : SentenceForm :=
  match t.ordinalData k with
  | none => .equal 0 2
  | some _ => (ownStageFormula p).rename (fun i => if i = 0 then 0 else k+3)

/-- Variable placement for a construction body after its ordinal inputs have been bound. -/
def ordinalBodySlots (n : ℕ) : ℕ → ℕ
  | 0 => n
  | 1 => n+1
  | k+2 => if k < n then k else n+1

/-- Express construction membership after defining and binding its ordinal input values. -/
noncomputable def Construction.ordinalMembership (t : Construction.{u}) (p : SentenceForm) :
  SentenceForm :=
  bindComputed t.ownRealsMembership.bound (t.ordinalInputFormula p)
    (t.ownRealsMembership.rename (ordinalBodySlots t.ownRealsMembership.bound))

theorem ordinalBodySlots_spec (p : SentenceForm) (N : ZFSet.{u})
    (e w : ℕ → ZFSet.{u}) :
    (p.rename (ordinalBodySlots p.bound)).Sat (N : Set ZFSet) (prependValues w p.bound e) ↔
      p.Sat (N : Set ZFSet) (cons (e 0) (cons (e 1) w)) := by
  rw [SentenceForm.sat_rename]
  apply p.finite_support
  intro i hi
  rcases i with _|_|k
  · exact prependValues_tail w p.bound e 0
  · exact prependValues_tail w p.bound e 1
  · simp only [ordinalBodySlots,ite_eq_left (show k < p.bound by omega),cons_succ]
    exact prependValues_lt w p.bound e k (by omega)

theorem Construction.ordinalMembership_spec (t : Construction.{u}) (p : SentenceForm)
    (N R : ZFSet.{u}) (P : Oracle) (z : ZFSet.{u})
    (hw : ∀ k, k < t.ownRealsMembership.bound → t.ownRealsInputs R P (k + 1) ∈ N)
    (hf : ∀ k, k < t.ownRealsMembership.bound → ∀ A ∈ N,
      (t.ordinalInputFormula p k).Sat (N : Set ZFSet) (cons A (cons z (t.ordinalInputs P))) ↔
        A = t.ownRealsInputs R P (k + 1)) :
    (t.ordinalMembership p).Sat (N : Set ZFSet) (cons z (t.ordinalInputs P)) ↔
      t.ownRealsMembership.Sat (N : Set ZFSet) (cons z (t.ownRealsInputs R P)) := by
  rw [Construction.ordinalMembership,bindComputed_spec N _ _ _ _ _ hw hf,
    ordinalBodySlots_spec]
  rfl

end TuringRigidity.RelativeConstructible

end OAI
