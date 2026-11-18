/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OrdinalEntryDecoder.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalEntryBinding

/-!
# Ordinal Entry Decoder
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
  OrdinalArithmetic
universe u

theorem paddedEntrySentence_sound (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (n : ℕ) (k : Fin n) (e : ℕ → ZFSet.{u})
    (he : ∀ i, e i ∈ M) (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (hc : e 1 = (paddedCode v β).toZFSet)
    (hp : (paddedEntrySentence n k).Sat (M : Set ZFSet) e) : e 0 = (v k).toZFSet := by
  obtain ⟨w,hw,hy,hp⟩ := (paddedEntrySentence_semantics M n k e).mp hp
  let w' : ℕ → ZFSet.{u} := fun i => if i < n then w i else e 0
  have hw' (i : ℕ) : w' i ∈ M := by
    dsimp [w']
    split
    · exact hw i ‹i < n›
    · exact he 0
  have hp' : (paddedCodeSentence n).Sat (M : Set ZFSet) (cons (e 1) w') := by
    apply ((paddedCodeSentence n).finite_support _ (cons (e 1) w) (cons (e 1) w') ?_).mp hp
    intro i hi
    have hb := paddedCodeSentence_bound n
    cases i with
    | zero => rfl
    | succ i => simp [w',show i < n by omega]
  have hv := paddedCodeSentence_recovers M hM hω n (cons (e 1) w')
    (fun i => by
      cases i
      · exact he 1
      · exact hw' _) v β hc hp'
  have hk := hv k
  simpa only [cons_succ,w',ite_eq_left k.isLt,← hy] using hk

theorem paddedEntrySentence_sourceT (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (n : ℕ) (k : Fin n) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (v : Fin n → Ordinal.{u}) (β : Ordinal.{u}) (hc : e 1 = (paddedCode v β).toZFSet) :
    (paddedEntrySentence n k).Sat (M : Set ZFSet) e ↔ e 0 = (v k).toZFSet := by
  have hω := omega_mem M hM hT.separation.finitePrefix.bounded hT.infinity
  refine ⟨paddedEntrySentence_sound M hM hω n k e he v β hc,?_⟩
  intro hy
  let w : ℕ → ZFSet.{u} := fun i => if hi : i < n then (v ⟨i,hi⟩).toZFSet else e 0
  have hw (i : ℕ) : w i ∈ M := by
    dsimp [w]
    split
    · exact paddedCode_entries_mem M hM v β (hc ▸ he 1) _
    · exact he 0
  apply (paddedEntrySentence_semantics M n k e).mpr
  refine ⟨w,fun i _ => hw i,?_,?_⟩
  · simpa [w,k.isLt] using hy
  · apply (paddedCodeSentence_recognition M hM hT n (cons (e 1) w)
      (fun i => by
        cases i
        · exact he 1
        · exact hw _) v β hc).mpr
    intro i
    simp [w,i.isLt]

theorem uniform_padded_entry_decoder (n : ℕ) (k : Fin n) :
    ∃ p : SentenceForm, p.bound ≤ 2 ∧ ∀ M : ZFSet.{u}, Transitive M → SourceT M →
      ∀ (v : Fin n → Ordinal.{u}) (β : Ordinal.{u}), (paddedCode v β).toZFSet ∈ M →
        ∀ z ∈ M, p.Sat (M : Set ZFSet) (cons z (fun _ => (paddedCode v β).toZFSet)) ↔
          z = (v k).toZFSet := by
  refine ⟨paddedEntrySentence n k,paddedEntrySentence_bound n k,?_⟩
  intro M hM hT v β hc z hz
  exact paddedEntrySentence_sourceT M hM hT n k _
    (fun i => by
      cases i
      · exact hz
      · exact hc) v β rfl

end TuringRigidity.OrdinalCoding

end OAI
