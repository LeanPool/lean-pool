/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/VectorCodeCertificates.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.CodeBranchCertificates
public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalDecoderDomains

/-!
# Vector Code Certificates
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
  OrdinalArithmetic
universe u

def VectorCodeCertificates (M : ZFSet.{u}) : {n : ℕ} → (Fin n → Ordinal.{u}) → Prop
  | 0, _ => True
  | _+1, v =>
    (vectorCode (fun i => v i.succ)).toZFSet ∈ M ∧
      PairCodeCertificates M (v 0) (vectorCode (fun i => v i.succ)) ∧
      VectorCodeCertificates M (fun i => v i.succ)

theorem VectorCodeCertificates.mono {M N : ZFSet.{u}} {n : ℕ} {v : Fin n → Ordinal.{u}}
    (h : VectorCodeCertificates M v) (hMN : M ⊆ N) : VectorCodeCertificates N v := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨hMN h.1,h.2.1.mono hMN,ih h.2.2⟩

theorem vectorCodeSentence_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (n : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (v : Fin n → Ordinal.{u}) (hv : ∀ i, e (i.val + 1) = (v i).toZFSet)
    (hcert : VectorCodeCertificates M v) (hc : e 0 = (vectorCode v).toZFSet) :
    (vectorCodeSentence n).Sat (M : Set ZFSet) e := by
  induction n generalizing e with
  | zero =>
    rw [vectorCodeSentence,bounded_sat,Formula.absolute _ M hM e he,ordinalOneMatrix_eval]
    exact hc
  | succ n ih =>
    obtain ⟨ht,hp,hs⟩ := hcert
    let t := (vectorCode (fun i => v i.succ)).toZFSet
    refine ⟨t,ht,?_,?_⟩
    · rw [SentenceForm.sat_rename]
      apply pairCodeSentence_of_certificates M hM hω
        (fun i => cons t e (if i = 0 then 1 else if i = 1 then 2 else 0)) (fun i => by
        split
        · exact he 0
        split
        · exact he 1
        exact ht) (v 0) (vectorCode (fun i => v i.succ)) (hv 0) rfl hp
      exact hc
    · rw [SentenceForm.sat_rename]
      exact ih _ (fun i => by
        cases i
        · exact ht
        · exact he _) _ (fun i => hv i.succ) hs rfl

def PaddedCodeCertificates (M : ZFSet.{u}) {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u}) :
  Prop :=
  β.toZFSet ∈ M ∧ (vectorCode v).toZFSet ∈ M ∧
    PairCodeCertificates M β (vectorCode v) ∧ VectorCodeCertificates M v

theorem PaddedCodeCertificates.mono {M N : ZFSet.{u}} {n : ℕ}
    {v : Fin n → Ordinal.{u}} {β : Ordinal.{u}}
    (h : PaddedCodeCertificates M v β) (hMN : M ⊆ N) : PaddedCodeCertificates N v β :=
  ⟨hMN h.1,hMN h.2.1,h.2.2.1.mono hMN,h.2.2.2.mono hMN⟩

theorem paddedCodeSentence_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (n : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (v : Fin n → Ordinal.{u}) (β : Ordinal.{u}) (hv : ∀ i, e (i.val + 1) = (v i).toZFSet)
    (hcert : PaddedCodeCertificates M v β) (hc : e 0 = (paddedCode v β).toZFSet) :
    (paddedCodeSentence n).Sat (M : Set ZFSet) e := by
  obtain ⟨hb,ht,hp,hs⟩ := hcert
  refine ⟨β.toZFSet,hb,(vectorCode v).toZFSet,ht,?_,?_⟩
  · rw [SentenceForm.sat_rename]
    exact pairCodeSentence_of_certificates M hM hω _ (fun i => by
      split
      · exact he 0
      split
      · exact hb
      exact ht) β (vectorCode v) rfl rfl hp hc
  · rw [SentenceForm.sat_rename]
    exact vectorCodeSentence_of_certificates M hM hω n _
      (fun i => by
        cases i
        · exact ht
        · exact he _) v hv hs rfl

theorem paddedEntrySentence_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (n : ℕ) (k : Fin n) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (v : Fin n → Ordinal.{u}) (β : Ordinal.{u}) (hc : e 1 = (paddedCode v β).toZFSet)
    (hcert : PaddedCodeCertificates M v β) (hy : e 0 = (v k).toZFSet) :
    (paddedEntrySentence n k).Sat (M : Set ZFSet) e := by
  let w : ℕ → ZFSet.{u} := fun i => if hi : i < n then (v ⟨i,hi⟩).toZFSet else e 0
  have hw (i : ℕ) : w i ∈ M := by
    dsimp [w]
    split
    · exact paddedCode_entries_mem M hM v β (hc ▸ he 1) _
    · exact he 0
  apply (paddedEntrySentence_semantics M n k e).mpr
  refine ⟨w,fun i _ => hw i,?_,?_⟩
  · simpa [w,k.isLt] using hy
  · exact paddedCodeSentence_of_certificates M hM hω n (cons (e 1) w)
      (fun i => by
        cases i
        · exact he 1
        · exact hw _) v β
      (fun i => by simp [w,i.isLt]) hcert hc

theorem largestPaddedEntrySentence_of_certificates (M : ZFSet.{u}) (hM : Transitive M) (hT :
  SourceT M)
    (n : ℕ) (k : Fin n) (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (hβ : realSeedOffset ≤ β) (e : ℕ → ZFSet.{u})
    (he : e 0 ∈ level (groundReals M) (heightDomainIndex (paddedCode v β)))
    (hcert : PaddedCodeCertificates (level (groundReals M) (heightDomainIndex (paddedCode v β))) v
      β) :
    (largestPaddedEntrySentence n k).Sat
      (level (groundReals M) (heightDomainIndex (paddedCode v β)) : Set ZFSet) e ↔
        e 0 = (v k).toZFSet := by
  refine ⟨largestPaddedEntrySentence_sound M hM hT n k v β hβ e he,?_⟩
  intro hy
  rw [largestPaddedEntrySentence,bindLargestOrdinal_ground_domain _ M hM hT _
    (hβ.trans (padding_lt_paddedCode v β).le),SentenceForm.sat_rename]
  have heq : (fun i => cons (paddedCode v β).toZFSet e (if i = 0 then 1 else 0)) =
      cons (e 0) (fun _ => (paddedCode v β).toZFSet) := by
    funext i; cases i <;> rfl
  rw [heq]
  exact paddedEntrySentence_of_certificates _ (level_transitive _ _) (ground_level_omega_mem M hM
    hT _)
    n k _ (fun i => by
      cases i
      · exact he
      · exact (padded_height_domain M hM hT v β hβ).1)
    v β rfl hcert hy

end TuringRigidity.OrdinalCoding

end OAI
