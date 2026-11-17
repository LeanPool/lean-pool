/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/CofinalPaddedDecoder.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ClosedPaddingCertificates

/-!
# Cofinal Padded Decoder
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
  OrdinalArithmetic
universe u

theorem cofinal_padded_code_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) {n : ℕ} (v : Fin n → Ordinal.{u})
    (hv : ∀ i, (v i).toZFSet ∈ M) (θ : Ordinal.{u}) (hθ : θ.toZFSet ∈ M) :
    ∃ β : Ordinal.{u}, β.toZFSet ∈ M ∧ θ < β ∧ realSeedOffset < β ∧
      (heightDomainIndex (paddedCode v β)).toZFSet ∈ M ∧
      PaddedCodeCertificates (level (groundReals M) (heightDomainIndex (paddedCode v β))) v β := by
  obtain ⟨τ,hτ,homega⟩ := internal_explicit_omega_threshold M hM hT
  obtain ⟨η,hη,hvec⟩ := vectorCode_certificates_at_levels M hM hT v hv
  have hk := vectorCode_internal M hM hT v hv
  have hoffM : realSeedOffset.toZFSet ∈ M := by
    rw [← ground_seed_offset M hM hT]
    exact ordinalHeight_mem_model M _ hM hT.separation.finitePrefix.bounded
      (seed_mem M _ hM hT (groundReals_mem M hM hT)) (seed_transitive _)
  let γ := max θ (max τ (max η (max realSeedOffset (vectorCode v))))
  have hγ : γ.toZFSet ∈ M := internal_ordinal_max M hθ
    (internal_ordinal_max M hτ (internal_ordinal_max M hη (internal_ordinal_max M hoffM hk)))
  obtain ⟨β,hβM,hγβ,hβ,hfix⟩ := cofinal_internal_omega_fixed_points M hM hT γ hγ
  have hθβ : θ < β := (le_max_left _ _).trans_lt hγβ
  have htail : max τ (max η (max realSeedOffset (vectorCode v))) < β :=
    (le_max_right _ _).trans_lt hγβ
  have hτβ : τ < β := (le_max_left _ _).trans_lt htail
  have htail' : max η (max realSeedOffset (vectorCode v)) < β := (le_max_right _ _).trans_lt htail
  have hηβ : η < β := (le_max_left _ _).trans_lt htail'
  have hlast : max realSeedOffset (vectorCode v) < β := (le_max_right _ _).trans_lt htail'
  have hoffβ : realSeedOffset < β := (le_max_left _ _).trans_lt hlast
  have hkβ : vectorCode v < β := (le_max_right _ _).trans_lt hlast
  have hoff : realSeedOffset+β=β := by
    have h := Ordinal.add_omega0_opow (a := realSeedOffset) (b := β) (by rw [hfix]; exact hoffβ)
    simpa only [hfix] using h
  have hpow := lower_omega_closure_of_fixed_point M τ β homega hβ hτβ hfix
  have hc := padded_certificates_of_lower_closure M hM hT v β hβ hoff hkβ
    (hvec β hηβ.le).2 hpow
  exact ⟨β,hβM,hθβ,hoffβ,padded_height_index_from_inputs M hM hT v β hv hβM,hc⟩

theorem cofinal_largest_entry_decoder (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) {n : ℕ} (v : Fin n → Ordinal.{u})
    (hv : ∀ i, (v i).toZFSet ∈ M) (θ : Ordinal.{u}) (hθ : θ.toZFSet ∈ M) :
    ∃ β : Ordinal.{u}, β.toZFSet ∈ M ∧ θ < β ∧ realSeedOffset < β ∧
      (heightDomainIndex (paddedCode v β)).toZFSet ∈ M ∧
      ∀ (k : Fin n) (e : ℕ → ZFSet.{u}),
        e 0 ∈ level (groundReals M) (heightDomainIndex (paddedCode v β)) →
        ((largestPaddedEntrySentence n k).Sat
          (level (groundReals M) (heightDomainIndex (paddedCode v β)) : Set ZFSet) e ↔
          e 0 = (v k).toZFSet) := by
  obtain ⟨β,hβ,hθβ,hoff,hidx,hcert⟩ := cofinal_padded_code_certificates M hM hT v hv θ hθ
  exact ⟨β,hβ,hθβ,hoff,hidx,fun k e he =>
    largestPaddedEntrySentence_of_certificates M hM hT n k v β hoff.le e he hcert⟩

end TuringRigidity.OrdinalCoding

end OAI
