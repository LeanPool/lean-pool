/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/VectorCodeLevels.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.CodeBranchLevels
public import LeanPool.TuringConeRigidity.OrdinalCodes.VectorCodeCertificates

/-!
# Vector Code Levels
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
  OrdinalArithmetic
universe u

theorem vectorCode_certificates_at_levels (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (hv : ∀ i, (v i).toZFSet ∈ M) :
    ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧ ∀ δ : Ordinal.{u}, γ ≤ δ →
      (vectorCode v).toZFSet ∈ level (groundReals M) δ ∧
      VectorCodeCertificates (level (groundReals M) δ) v := by
  induction n with
  | zero =>
    refine ⟨0,internal_ordinal_zero M hM hT,?_⟩
    intro δ _
    refine ⟨?_,trivial⟩
    change (1 : Ordinal.{u}).toZFSet ∈ _
    rw [← Nat.cast_one,toZFSet_nat]
    exact level_transitive _ δ _ (ground_level_omega_mem M hM hT δ) _ ((mem_omega _).mpr ⟨1,rfl⟩)
  | succ n ih =>
    obtain ⟨α,hα,hαL⟩ := ih (fun i => v i.succ) (fun i => hv i.succ)
    obtain ⟨β,hβ,hβL⟩ := pairCode_certificates_at_levels M hM hT (v 0)
      (vectorCode (fun i => v i.succ)) (hv 0)
      (vectorCode_internal M hM hT _ (fun i => hv i.succ))
    refine ⟨max α β,internal_ordinal_max M hα hβ,?_⟩
    intro δ hδ
    obtain ⟨ht,hs⟩ := hαL δ ((le_max_left α β).trans hδ)
    obtain ⟨_,_,hc,hp⟩ := hβL δ ((le_max_right α β).trans hδ)
    exact ⟨hc,ht,hp,hs⟩

theorem paddedCode_certificates_at_levels (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (hv : ∀ i, (v i).toZFSet ∈ M) (hβ : β.toZFSet ∈ M) :
    ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧ ∀ δ : Ordinal.{u}, γ ≤ δ →
      (paddedCode v β).toZFSet ∈ level (groundReals M) δ ∧
      PaddedCodeCertificates (level (groundReals M) δ) v β := by
  obtain ⟨α,hα,hαL⟩ := vectorCode_certificates_at_levels M hM hT v hv
  obtain ⟨κ,hκ,hκL⟩ := pairCode_certificates_at_levels M hM hT β (vectorCode v)
    hβ (vectorCode_internal M hM hT v hv)
  refine ⟨max α κ,internal_ordinal_max M hα hκ,?_⟩
  intro δ hδ
  obtain ⟨ht,hs⟩ := hαL δ ((le_max_left α κ).trans hδ)
  obtain ⟨hb,_,hc,hp⟩ := hκL δ ((le_max_right α κ).trans hδ)
  exact ⟨hc,hb,ht,hp,hs⟩

theorem paddedEntry_sentences_at_levels (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (hv : ∀ i, (v i).toZFSet ∈ M) (hβ : β.toZFSet ∈ M) :
    ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧ ∀ δ : Ordinal.{u}, γ ≤ δ →
      (paddedCode v β).toZFSet ∈ level (groundReals M) δ ∧
      PaddedCodeCertificates (level (groundReals M) δ) v β ∧
      ∀ (k : Fin n) z, z ∈ level (groundReals M) δ →
        ((paddedEntrySentence n k).Sat (level (groundReals M) δ : Set ZFSet)
          (cons z (fun _ => (paddedCode v β).toZFSet)) ↔ z = (v k).toZFSet) := by
  obtain ⟨γ,hγ,hL⟩ := paddedCode_certificates_at_levels M hM hT v β hv hβ
  refine ⟨γ,hγ,?_⟩
  intro δ hδ
  obtain ⟨hc,hcert⟩ := hL δ hδ
  refine ⟨hc,hcert,?_⟩
  intro k z hz
  have he : ∀ i, cons z (fun _ => (paddedCode v β).toZFSet) i ∈ level (groundReals M) δ := by
    intro i
    cases i
    · exact hz
    · exact hc
  exact ⟨paddedEntrySentence_sound _ (level_transitive _ _) (ground_level_omega_mem M hM hT δ)
    n k _ he v β rfl,
    paddedEntrySentence_of_certificates _ (level_transitive _ _) (ground_level_omega_mem M hM hT δ)
      n k _ he v β rfl hcert⟩

end TuringRigidity.OrdinalCoding

end OAI
