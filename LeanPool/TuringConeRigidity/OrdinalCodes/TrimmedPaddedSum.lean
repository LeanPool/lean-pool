/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/TrimmedPaddedSum.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.TrimmedBoundaryCertificates

/-!
# Trimmed Padded Sum
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
  OrdinalArithmetic
universe u

theorem padded_final_sum_of_smaller_certificates (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) {n : ℕ} (v : Fin n → Ordinal.{u})
    (β : Ordinal.{u}) (hβ : 0 < β) (hoff : realSeedOffset + β = β) (hv : vectorCode v ≤ β)
    (hs : ∀ t < Ordinal.omega0 ^ vectorCode v,
      SumCertificates (level (groundReals M) (paddedCode v β)) (Ordinal.omega0 ^ (β + 1)) t) :
    SumCertificates (level (groundReals M) (heightDomainIndex (paddedCode v β)))
      (Ordinal.omega0 ^ (β+1)) (Ordinal.omega0 ^ vectorCode v) := by
  let R := groundReals M
  let a := Ordinal.omega0 ^ (β+1)
  let b := Ordinal.omega0 ^ vectorCode v
  let c := paddedCode v β
  have hc : c = a+b := by change pairCode β (vectorCode v) = _; rw [pairCode,ite_eq_left hv]
  have hca : a < c := by
    rw [hc]
    simpa only [add_zero] using (add_lt_add_iff_left a).mpr (Ordinal.opow_pos (vectorCode v)
      Ordinal.omega0_pos)
  have hba : b < a := (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr
    (hv.trans_lt (lt_add_one β))
  have habs := offset_absorbed_above realSeedOffset β c hoff (padding_lt_paddedCode v β).le
  have hcut : ordinalHeight (seed R)+c=c := by rw [ground_seed_offset M hM hT]; exact habs
  have hmem (o : Ordinal.{u}) (ho : o < c) : o.toZFSet ∈ level R c := by
    rw [ordinal_mem_level_iff,hcut]; exact ho
  have hω := ground_level_omega_mem M hM hT c
  have h0 := level_transitive R c _ hω _ ZFSet.omega_zero
  have h1 : ({∅} : ZFSet.{u}) ∈ level R c := by
    have h := level_transitive R c _ hω _ ((mem_omega _).mpr ⟨1,rfl⟩)
    simpa [natSet] using h
  have hlim := paddedCode_isSuccLimit v β hβ
  have hresult := sum_certificates_at_exact_cut R a b (hc ▸ hlim)
    (by rw [← hc]; exact hcut) (by rw [← hc]; exact hω)
    (by rw [← hc]; exact hmem a hca) (by rw [← hc]; exact hmem b (hba.trans hca))
    (by rw [← hc]; exact h0) (by rw [← hc]; exact h1) (by rw [← hc]; exact hs)
  rw [heightDomainIndex_of_absorbed _ habs]
  simpa only [← hc] using hresult

end TuringRigidity.OrdinalCoding

end OAI
