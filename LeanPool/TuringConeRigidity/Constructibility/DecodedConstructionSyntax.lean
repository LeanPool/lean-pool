/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/DecodedConstructionSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.CofinalPaddedDecoder

/-!
# Decoded Construction Syntax
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel OrdinalCoding
universe u
attribute [local irreducible] Construction.ownRealsMembership SentenceForm.bound

noncomputable def Construction.ordinalVector (t : Construction.{u}) :
    Fin t.ownRealsMembership.bound → Ordinal.{u} := fun k => (t.ordinalData k).getD 0

theorem Construction.ordinalVector_internal (t : Construction.{u}) (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (hi : t.Indexed M) :
    ∀ k, (t.ordinalVector k).toZFSet ∈ M := by
  intro k
  cases ho : t.ordinalData k with
  | none => simpa only [Construction.ordinalVector,ho,Option.getD_none] using
    internal_ordinal_zero M hM hT
  | some o =>
    simpa only [Construction.ordinalVector, ho, Option.getD_some] using
      t.ordinalData_mem M hi k o ho

noncomputable def Construction.decodedOrdinalInput (t : Construction.{u}) (k : ℕ) : SentenceForm :=
  if hk : k < t.ownRealsMembership.bound then
    match t.ordinalData k with
    | none => .equal 0 2
    | some _ => largestPaddedEntrySentence t.ownRealsMembership.bound ⟨k,hk⟩
  else .equal 0 2

noncomputable def Construction.decodedOrdinalBody (t : Construction.{u}) (q : SentenceForm) :
  SentenceForm :=
  bindComputed t.ownRealsMembership.bound t.decodedOrdinalInput
    (q.rename (ordinalBodySlots t.ownRealsMembership.bound))

theorem bindComputed_bound (n m : ℕ) (f : ℕ → SentenceForm) (p : SentenceForm)
    (hp : p.bound ≤ n + m) (hf : ∀ i < n, (f i).bound ≤ m + 1) :
    (bindComputed n f p).bound ≤ m := by
  induction n generalizing m f with
  | zero => simpa only [bindComputed,zero_add] using hp
  | succ n ih =>
    have hinner := ih (m+1) (fun i => (f i).rename skipValue) (by omega) (by
      intro i hi
      apply code_rename_bound (f i) skipValue (m+2)
      intro j hj
      cases j with
      | zero => change 0 < m+2; omega
      | succ j => change j+2 < m+2; have h := hf i (by omega); omega)
    have hn := hf n (by omega)
    simpa only [bindComputed,SentenceForm.bound] using
      (show max (f n).bound (bindComputed n (fun i => (f i).rename skipValue) p).bound - 1 ≤ m by
        omega)

theorem Construction.decodedOrdinalBody_bound (t : Construction.{u}) (q : SentenceForm) :
    (t.decodedOrdinalBody q).bound ≤ 2 := by
  apply bindComputed_bound
  · apply code_rename_bound
    intro i _
    rcases i with _|_|i
    · change t.ownRealsMembership.bound < t.ownRealsMembership.bound+2; omega
    · change t.ownRealsMembership.bound+1 < t.ownRealsMembership.bound+2; omega
    · dsimp only [ordinalBodySlots]; split <;> omega
  · intro i _
    by_cases hi : i < t.ownRealsMembership.bound
    · rw [Construction.decodedOrdinalInput,dite_eq_left hi]
      cases t.ordinalData i with
      | none => simp only [SentenceForm.bound]; omega
      | some o => exact (largestPaddedEntrySentence_bound _ _).trans (by omega)
    · rw [Construction.decodedOrdinalInput,dite_eq_right hi]
      simp only [SentenceForm.bound]; omega

theorem Construction.decodedOrdinalBody_spec (t : Construction.{u}) (q : SentenceForm)
    (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) (P : Oracle)
    (β : Ordinal.{u}) (hoff : realSeedOffset ≤ β)
    (hcert : PaddedCodeCertificates
      (level (groundReals M) (heightDomainIndex (paddedCode t.ordinalVector β))) t.ordinalVector β)
    (he : ∀ i, t.ordinalInputs P i ∈
      level (groundReals M) (heightDomainIndex (paddedCode t.ordinalVector β)))
    (z : ZFSet.{u}) :
    (t.decodedOrdinalBody q).Sat
      (level (groundReals M) (heightDomainIndex (paddedCode t.ordinalVector β)) : Set ZFSet)
      (cons z (fun _ => realCode P)) ↔
    q.Sat (level (groundReals M) (heightDomainIndex (paddedCode t.ordinalVector β)) : Set ZFSet)
      (cons z (t.ordinalInputs P)) := by
  let n := t.ownRealsMembership.bound
  let w := fun k => t.ordinalInputs P (k+1)
  let A := level (groundReals M) (heightDomainIndex (paddedCode t.ordinalVector β))
  have hf (k : ℕ) (hk : k < n) (x : ZFSet.{u}) (hx : x ∈ A) :
      (t.decodedOrdinalInput k).Sat (A : Set ZFSet) (cons x (cons z (fun _ => realCode P))) ↔ x =
        w k := by
    have hk' : k < t.ownRealsMembership.bound := hk
    rw [Construction.decodedOrdinalInput,dite_eq_left hk']
    cases ho : t.ordinalData k with
    | none => simp only
      [SentenceForm.Sat,w,Construction.ordinalInputs,cons_succ,cons_zero,ite_eq_left hk',ho]
    | some o =>
      have h := largestPaddedEntrySentence_of_certificates M hM hT n ⟨k,hk⟩ t.ordinalVector β hoff
        (cons x (cons z (fun _ => realCode P))) hx hcert
      simpa only [cons_zero,w,Construction.ordinalInputs,cons_succ,ite_eq_left hk',
        Construction.ordinalVector,ho,Option.getD_some] using h
  rw [Construction.decodedOrdinalBody,bindComputed_spec A n t.decodedOrdinalInput _
    (cons z (fun _ => realCode P)) w (fun i _ => he (i+1)) hf,SentenceForm.sat_rename]
  have henv : (fun i => prependValues w n (cons z (fun _ => realCode P)) (ordinalBodySlots n i)) =
      cons z (t.ordinalInputs P) := by
    funext i
    rcases i with _|_|k
    · exact prependValues_tail w n _ 0
    · exact prependValues_tail w n _ 1
    · by_cases hk : k < n
      · simpa only [ordinalBodySlots,ite_eq_left hk,cons_succ,w] using prependValues_lt w n _ k hk
      · have hk' : ¬ k < t.ownRealsMembership.bound := hk
        simp only [ordinalBodySlots,ite_eq_right
          hk,cons_succ,Construction.ordinalInputs,ite_eq_right hk']
        exact prependValues_tail w n _ 1
  rw [henv]

end TuringRigidity.RelativeConstructible

end OAI
