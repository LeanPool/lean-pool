/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/CodeBranchLevels.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.CodeBranchCertificates
public import LeanPool.TuringConeRigidity.OrdinalCodes.SumCertificateLevels
public import LeanPool.TuringConeRigidity.Constructibility.UniformOmegaLevels

/-!
# Code Branch Levels
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
  OrdinalArithmetic
universe u

theorem codeBranch_certificates_at_levels (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (twice : Bool) (a b : Ordinal.{u}) (ha : a.toZFSet ∈ M) (hb : b.toZFSet ∈ M) :
    ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧ ∀ δ : Ordinal.{u}, γ ≤ δ →
      a.toZFSet ∈ level (groundReals M) δ ∧ b.toZFSet ∈ level (groundReals M) δ ∧
      (codeBranchValue twice a b).toZFSet ∈ level (groundReals M) δ ∧
      CodeBranchCertificates (level (groundReals M) δ) twice a b := by
  have hk := internal_ordinal_succ M hM hT a ha
  have hu := ordinal_omega_opow_internal M hM hT (a+1) hk
  have hv := ordinal_omega_opow_internal M hM hT b hb
  have ht := codeScale_internal M hM hT twice _ hu
  obtain ⟨κ,hκ,hκL⟩ := omega_certificates_at_levels M hM hT (a+1) hk
  obtain ⟨ℓ,hℓ,hℓL⟩ := omega_certificates_at_levels M hM hT b hb
  obtain ⟨μ,hμ,hμL⟩ := sum_certificates_at_levels M hM hT _ _ hu hu
  obtain ⟨ν,hν,hνL⟩ := sum_certificates_at_levels M hM hT _ _ ht hv
  refine ⟨max (max κ ℓ) (max μ ν),
    internal_ordinal_max M (internal_ordinal_max M hκ hℓ) (internal_ordinal_max M hμ hν),?_⟩
  intro δ hδ
  have hkδ := (le_max_left κ ℓ).trans ((le_max_left (max κ ℓ) (max μ ν)).trans hδ)
  have hlδ := (le_max_right κ ℓ).trans ((le_max_left (max κ ℓ) (max μ ν)).trans hδ)
  have hmδ := (le_max_left μ ν).trans ((le_max_right (max κ ℓ) (max μ ν)).trans hδ)
  have hnδ := (le_max_right μ ν).trans ((le_max_right (max κ ℓ) (max μ ν)).trans hδ)
  obtain ⟨hkL,huL,hpc,_⟩ := hκL δ hkδ
  obtain ⟨hbL,hvL,hqc,_⟩ := hℓL δ hlδ
  obtain ⟨_,_,_,hdc⟩ := hμL δ hmδ
  obtain ⟨htL,_,hcL,hsc⟩ := hνL δ hnδ
  have haL := ordinal_le_internal (level_transitive _ _) hkL (lt_add_one a).le
  exact ⟨haL,hbL,hcL,hkL,huL,hvL,htL,hpc,hqc,fun _ => hdc,hsc⟩

theorem pairCode_certificates_at_levels (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a b : Ordinal.{u}) (ha : a.toZFSet ∈ M) (hb : b.toZFSet ∈ M) :
    ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧ ∀ δ : Ordinal.{u}, γ ≤ δ →
      a.toZFSet ∈ level (groundReals M) δ ∧ b.toZFSet ∈ level (groundReals M) δ ∧
      (pairCode a b).toZFSet ∈ level (groundReals M) δ ∧
      PairCodeCertificates (level (groundReals M) δ) a b := by
  by_cases hle : b ≤ a
  · obtain ⟨γ,hγ,hL⟩ := codeBranch_certificates_at_levels M hM hT false a b ha hb
    refine ⟨γ,hγ,?_⟩
    intro δ hδ
    simpa only [pairCode,ite_eq_left hle,PairCodeCertificates,codeBranchValue,codeScale,
      Bool.false_eq_true,↓reduceIte] using hL δ hδ
  · obtain ⟨γ,hγ,hL⟩ := codeBranch_certificates_at_levels M hM hT true b a hb ha
    refine ⟨γ,hγ,?_⟩
    intro δ hδ
    obtain ⟨hbL,haL,hc,hcert⟩ := hL δ hδ
    refine ⟨haL,hbL,?_,?_⟩
    · simpa only [pairCode,ite_eq_right hle,codeBranchValue,codeScale,↓reduceIte] using hc
    · simpa only [PairCodeCertificates,ite_eq_right hle] using hcert

end TuringRigidity.OrdinalCoding

end OAI
