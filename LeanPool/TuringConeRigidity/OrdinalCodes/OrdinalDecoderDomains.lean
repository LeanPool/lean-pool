/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OrdinalDecoderDomains.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalEntryDecoder

/-!
# Ordinal Decoder Domains
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
  OrdinalArithmetic
universe u

theorem ground_level_omega_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (δ : Ordinal.{u}) : ZFSet.omega ∈ level (groundReals M) δ :=
  seed_subset_stage _ _ (parameter_subset_seed _ (omega_mem_groundReals M hM hT))

theorem padded_entry_height_sound (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (n : ℕ) (k : Fin n) (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (hβ : realSeedOffset ≤ β) (z : ZFSet.{u})
    (hz : z ∈ level (groundReals M) (heightDomainIndex (paddedCode v β))) :
    (paddedEntrySentence n k).Sat
      (level (groundReals M) (heightDomainIndex (paddedCode v β)) : Set ZFSet)
      (cons z (fun _ => (paddedCode v β).toZFSet)) → z = (v k).toZFSet := by
  have hc := (padded_height_domain M hM hT v β hβ).1
  exact paddedEntrySentence_sound _ (level_transitive _ _) (ground_level_omega_mem M hM hT _)
    n k _ (fun i => by
      cases i
      · exact hz
      · exact hc) v β rfl

/-- Decode a selected padded ordinal entry using a largest-ordinal parameter. -/
noncomputable def largestPaddedEntrySentence (n : ℕ) (k : Fin n) : SentenceForm :=
  bindLargestOrdinal ((paddedEntrySentence n k).rename (fun i => if i = 0 then 1 else 0))

theorem largestPaddedEntrySentence_bound (n : ℕ) (k : Fin n) :
    (largestPaddedEntrySentence n k).bound ≤ 1 := by
  have hb := code_rename_bound (paddedEntrySentence n k)
    (fun i => if i = 0 then 1 else 0) 2 (by intro i _; split <;> omega)
  rw [largestPaddedEntrySentence,bindLargestOrdinal_bound]
  omega

theorem largestPaddedEntrySentence_sound (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (n : ℕ) (k : Fin n) (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (hβ : realSeedOffset ≤ β) (e : ℕ → ZFSet.{u})
    (he : e 0 ∈ level (groundReals M) (heightDomainIndex (paddedCode v β))) :
    (largestPaddedEntrySentence n k).Sat
      (level (groundReals M) (heightDomainIndex (paddedCode v β)) : Set ZFSet) e →
        e 0 = (v k).toZFSet := by
  rw [largestPaddedEntrySentence,bindLargestOrdinal_ground_domain _ M hM hT _
    (hβ.trans (padding_lt_paddedCode v β).le),SentenceForm.sat_rename]
  have heq : (fun i => cons (paddedCode v β).toZFSet e (if i = 0 then 1 else 0)) =
      cons (e 0) (fun _ => (paddedCode v β).toZFSet) := by
    funext i; cases i <;> rfl
  rw [heq]
  exact padded_entry_height_sound M hM hT n k v β hβ (e 0) he

end TuringRigidity.OrdinalCoding

end OAI
