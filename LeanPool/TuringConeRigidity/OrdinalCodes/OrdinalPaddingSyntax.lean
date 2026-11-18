/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OrdinalPaddingSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalVectorRecovery

/-!
# Ordinal Padding Syntax
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
  OrdinalArithmetic
universe u

/-- A full formula defining a padded ordinal-vector code through an ordinal-pair code. -/
noncomputable def paddedCodeSentence (n : ℕ) : SentenceForm :=
  .ex (.ex (.conj
    (pairCodeSentence.rename (fun i => if i = 0 then 2 else if i = 1 then 1 else 0))
    ((vectorCodeSentence n).rename vectorTailSlots)))

theorem paddedCodeSentence_bound (n : ℕ) : (paddedCodeSentence n).bound ≤ n+1 := by
  have hp := code_rename_bound pairCodeSentence
    (fun i => if i = 0 then 2 else if i = 1 then 1 else 0) 3 (by
      intro i _; split <;> (try split) <;> omega)
  have ht := code_rename_bound (vectorCodeSentence n) vectorTailSlots (n+3) (by
    intro i hi
    have hb := vectorCodeSentence_bound n
    cases i with
    | zero => simp [vectorTailSlots]
    | succ i => change i+3 < n+3; omega)
  change max _ _ - 1 - 1 ≤ n+1
  omega

theorem paddedCodeSentence_recovers (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (n : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (v : Fin n → Ordinal.{u}) (β : Ordinal.{u}) (hc : e 0 = (paddedCode v β).toZFSet)
    (hp : (paddedCodeSentence n).Sat (M : Set ZFSet) e) :
    ∀ i, e (i.val+1) = (v i).toZFSet := by
  obtain ⟨b,hb,t,ht,hpair,hvec⟩ := hp
  rw [SentenceForm.sat_rename] at hpair hvec
  have hrec := pairCodeSentence_recovers M hM hω
    (fun i => cons t (cons b e) (if i = 0 then 2 else if i = 1 then 1 else 0)) (fun i => by
      split
      · exact he 0
      split
      · exact hb
      exact ht) β (vectorCode v) hc hpair
  have htcode : t = (vectorCode v).toZFSet := hrec.2
  exact vectorCodeSentence_recovers M hM hω n
    (fun i => cons t (cons b e) (vectorTailSlots i))
    (fun i => by
      cases i
      · exact ht
      · exact he _) v htcode hvec

theorem paddedCodeSentence_recognition (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (n : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (v : Fin n → Ordinal.{u}) (β : Ordinal.{u}) (hc : e 0 = (paddedCode v β).toZFSet) :
    (paddedCodeSentence n).Sat (M : Set ZFSet) e ↔ ∀ i, e (i.val+1) = (v i).toZFSet := by
  have hω := omega_mem M hM hT.separation.finitePrefix.bounded hT.infinity
  refine ⟨paddedCodeSentence_recovers M hM hω n e he v β hc,?_⟩
  intro hv
  have hcode : (paddedCode v β).toZFSet ∈ M := hc ▸ he 0
  have hb := paddedCode_padding_mem M hM v β hcode
  have ht := paddedCode_body_mem M hM v β hcode
  refine ⟨β.toZFSet,hb,(vectorCode v).toZFSet,ht,?_,?_⟩
  · rw [SentenceForm.sat_rename]
    apply (pairCodeSentence_sourceT M hM hT _ (fun i => by
      split
      · exact he 0
      split
      · exact hb
      exact ht)).mpr
    exact ⟨ZFSet.isOrdinal_toZFSet _,ZFSet.isOrdinal_toZFSet _,by simpa [paddedCode] using hc⟩
  · rw [SentenceForm.sat_rename]
    exact (vectorCodeSentence_sourceT M hM hT n
      (fun i => cons (vectorCode v).toZFSet (cons β.toZFSet e) (vectorTailSlots i))
      (fun i => by
        cases i
        · exact ht
        · exact he _) v hv).mpr rfl

end TuringRigidity.OrdinalCoding

end OAI
