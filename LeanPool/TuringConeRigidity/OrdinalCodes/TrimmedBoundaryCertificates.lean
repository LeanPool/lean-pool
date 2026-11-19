/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/TrimmedBoundaryCertificates.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.TrimmedProductGraph
public import LeanPool.TuringConeRigidity.OrdinalCodes.TrimmedSumGraph
public import LeanPool.TuringConeRigidity.OrdinalCodes.PaddedOmegaBoundary

/-!
# Trimmed Boundary Certificates
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
  OrdinalCoding
universe u

theorem product_certificates_at_exact_cut (R : ZFSet.{u}) (a b : Ordinal.{u})
    (ha0 : 0 < a) (hγ : Order.IsSuccLimit (a * b))
    (hcut : ordinalHeight (seed R) + a * b = a * b)
    (hω : ZFSet.omega.{u} ∈ level R (a * b))
    (ha : a.toZFSet ∈ level R (a * b)) (hb : b.toZFSet ∈ level R (a * b))
    (hp : ∀ s < b, ProductCertificates (level R (a * b)) a s)
    (hs : ∀ s < b, ∀ t < a, SumCertificates (level R (a * b)) (a * s) t) :
    ProductCertificates (level R (a*b+1)) a b := by
  apply product_certificates_at_limit_successor R (a*b) a b hγ hω ha hb
  intro s hsb
  have hmem (c : Ordinal.{u}) (hc : c < a*b) : c.toZFSet ∈ level R (a*b) := by
    rw [ordinal_mem_level_iff,hcut]; exact hc
  refine ⟨hmem _ (mul_lt_mul_of_pos_left hsb ha0),hp s hsb,?_⟩
  intro t hta
  exact ⟨hmem _ (Ordinal.lt_mul_iff.mpr ⟨s,hsb,t,hta,rfl⟩),hs s hsb t hta⟩

theorem sum_certificates_at_exact_cut (R : ZFSet.{u}) (a b : Ordinal.{u})
    (hγ : Order.IsSuccLimit (a + b)) (hcut : ordinalHeight (seed R) + (a + b) = a + b)
    (hω : ZFSet.omega.{u} ∈ level R (a + b))
    (ha : a.toZFSet ∈ level R (a + b)) (hb : b.toZFSet ∈ level R (a + b))
    (h0 : (∅ : ZFSet.{u}) ∈ level R (a + b)) (h1 : ({∅} : ZFSet.{u}) ∈ level R (a + b))
    (hs : ∀ t < b, SumCertificates (level R (a + b)) a t) :
    SumCertificates (level R (a+b+1)) a b := by
  apply sum_certificates_at_limit_successor R (a+b) a b hγ hω ha hb h0 h1
  intro t ht
  refine ⟨?_,hs t ht⟩
  rw [ordinal_mem_level_iff,hcut]
  exact (add_lt_add_iff_left a).mpr ht

theorem lower_omega_closure_fixed_point (R : ZFSet.{u}) (β : Ordinal.{u})
    (hβ : Order.IsSuccLimit β) (hoff : ordinalHeight (seed R) + β = β)
    (hpow : ∀ c < β, (Ordinal.omega0 ^ c).toZFSet ∈ level R β) :
    Ordinal.omega0 ^ β = β := by
  apply le_antisymm
  · apply (Ordinal.opow_le_of_isSuccLimit (ne_of_gt Ordinal.omega0_pos) hβ).mpr
    intro c hc
    have h := (ordinal_mem_level_iff R β (Ordinal.omega0 ^ c)).mp (hpow c hc)
    rw [hoff] at h
    exact h.le
  · exact Ordinal.right_le_opow β Ordinal.one_lt_omega0

theorem omega_boundary_product_of_smaller_certificates (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (β : Ordinal.{u})
    (hβ : 0 < β) (hoff : realSeedOffset + β = β)
    (hp : ∀ s < Ordinal.omega0,
      ProductCertificates (level (groundReals M) (Ordinal.omega0 ^ (β + 1)))
        (Ordinal.omega0 ^ β) s)
    (hs : ∀ s < Ordinal.omega0, ∀ t < Ordinal.omega0 ^ β,
      SumCertificates (level (groundReals M) (Ordinal.omega0 ^ (β + 1)))
        (Ordinal.omega0 ^ β * s) t) :
    ProductCertificates (level (groundReals M) (Ordinal.omega0 ^ (β+1)+1))
      (Ordinal.omega0 ^ β) Ordinal.omega0 := by
  let R := groundReals M
  let a := Ordinal.omega0 ^ β
  let b := Ordinal.omega0 ^ (β+1)
  have hab : a * Ordinal.omega0 = b := (Ordinal.opow_add_one Ordinal.omega0 β).symm
  have hβb : β < b := (lt_add_one β).trans_le (Ordinal.right_le_opow (β+1) Ordinal.one_lt_omega0)
  have hcut : ordinalHeight (seed R)+b=b := by
    rw [ground_seed_offset M hM hT]
    exact offset_absorbed_above _ β b hoff hβb.le
  have hmem (c : Ordinal.{u}) (hc : c < b) : c.toZFSet ∈ level R b := by
    rw [ordinal_mem_level_iff,hcut]; exact hc
  have ha : a.toZFSet ∈ level R b := hmem _
    ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (lt_add_one β))
  have hb : Ordinal.omega0.toZFSet ∈ level R b := hmem _ (by
    have hlt : (1 : Ordinal.{u}) < β + 1 := Order.lt_add_one_iff.mpr (by
      simpa only [zero_add] using (Order.add_one_le_iff.mpr hβ))
    have h := (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hlt
    simpa only [Ordinal.opow_one] using h)
  have hl : Order.IsSuccLimit b := Ordinal.isSuccLimit_opow_left
    Ordinal.isSuccLimit_omega0 (ne_of_gt (hβ.trans (lt_add_one β)))
  have result := product_certificates_at_exact_cut R a Ordinal.omega0
    (Ordinal.opow_pos β Ordinal.omega0_pos) (hab.symm ▸ hl) (by rw [hab]; exact hcut)
    (by rw [hab]; exact ground_level_omega_mem M hM hT b)
    (by rw [hab]; exact ha) (by rw [hab]; exact hb)
    (by rw [hab]; exact hp) (by rw [hab]; exact hs)
  simpa only [hab] using result

end TuringRigidity.OrdinalArithmetic

end OAI
