/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ClosedPaddingCertificates.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.FiniteBlockProducts
public import LeanPool.TuringConeRigidity.OrdinalCodes.VectorCodeCertificates

/-!
# Closed Padding Certificates
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
  OrdinalArithmetic
universe u

theorem padded_certificates_of_lower_closure (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (hβ : Order.IsSuccLimit β) (hoff : realSeedOffset + β = β) (hv : vectorCode v < β)
    (hvec : VectorCodeCertificates (level (groundReals M) β) v)
    (hpow : ∀ c < β, (Ordinal.omega0 ^ c).toZFSet ∈ level (groundReals M) β ∧
      OmegaPowerCertificates (level (groundReals M) β) c.toZFSet) :
    PaddedCodeCertificates (level (groundReals M) (heightDomainIndex (paddedCode v β))) v β := by
  let R := groundReals M
  let c := paddedCode v β
  let δ := heightDomainIndex c
  have hβpos : 0 < β := hβ.bot_lt
  have hβc : β < c := padding_lt_paddedCode v β
  have hcodeabs := offset_absorbed_above realSeedOffset β c hoff hβc.le
  have hδ : δ=c+1 := heightDomainIndex_of_absorbed c hcodeabs
  have hβδ : β ≤ δ := hβc.le.trans (hδ ▸ le_self_add)
  have hcut : ordinalHeight (seed R)+c=c := by rw [ground_seed_offset M hM hT]; exact hcodeabs
  have hmem (a : Ordinal.{u}) (ha : a ≤ c) : a.toZFSet ∈ level R δ := by
    rw [hδ,ordinal_mem_level_iff,← add_assoc,hcut]
    exact Order.lt_add_one_iff.mpr ha
  have hb1 : β+1 ≤ c := Order.add_one_le_iff.mpr hβc
  have hu : Ordinal.omega0 ^ (β+1) < c := by
    change Ordinal.omega0 ^ (β+1) < pairCode β (vectorCode v)
    rw [pairCode,ite_eq_left hv.le]
    simpa only [add_zero] using (add_lt_add_iff_left (Ordinal.omega0 ^ (β+1))).mpr
      (Ordinal.opow_pos (vectorCode v) Ordinal.omega0_pos)
  have hvpow := level_mono R hβδ (hpow (vectorCode v) hv).1
  have hcβ := padded_omega_boundary_certificates M hM hT v β hβ hoff hv.le hpow
    (omega_boundary_product_without_offset M hM hT β hβpos)
  have hck := (hpow (vectorCode v) hv).2.mono (level_mono R hβδ)
  have hsum := padded_final_sum_certificates M hM hT v β hβpos hoff hv.le
  refine ⟨hmem β hβc.le,hmem (vectorCode v) (hv.trans hβc).le,?_,hvec.mono (level_mono R hβδ)⟩
  rw [PairCodeCertificates,ite_eq_left hv.le]
  exact ⟨hmem (β+1) hb1,hmem _ hu.le,hvpow,hmem _ hu.le,hcβ,hck,
    fun h => Bool.noConfusion h,hsum⟩

end TuringRigidity.OrdinalCoding

end OAI
