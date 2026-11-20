/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/FiniteBlockProducts.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.FiniteSumPowerBound

/-!
# Finite Block Products
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
  OrdinalCoding
universe u

theorem finite_block_product_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (β : Ordinal.{u}) (hβ : 0 < β) (n : ℕ) :
    ProductCertificates
      (level (groundReals M) (Ordinal.omega0 ^ β * (n+2)+1))
      (Ordinal.omega0 ^ β) n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    let R := groundReals M
    let a := Ordinal.omega0 ^ β
    let γ := a*(n+2)
    have ha0 : 0 < a := Ordinal.opow_pos β Ordinal.omega0_pos
    have haLim : Order.IsSuccLimit a := Ordinal.isSuccLimit_opow_left
      Ordinal.isSuccLimit_omega0 (ne_of_gt hβ)
    have hn2 : (0 : Ordinal.{u}) < n+2 := by exact_mod_cast (show 0 < n+2 by omega)
    have hγ : Order.IsSuccLimit γ := Ordinal.isSuccLimit_mul_left haLim hn2
    have haγ : a < γ := by
      have h : (1 : Ordinal.{u}) < n+2 := by exact_mod_cast (show 1 < n+2 by omega)
      simpa only [mul_one] using mul_lt_mul_of_pos_left h ha0
    have hmem (c : Ordinal.{u}) (hc : c < γ) : c.toZFSet ∈ level R γ := by
      rw [ordinal_mem_level_iff]
      exact hc.trans_le le_add_self
    apply product_certificates_at_limit_successor R γ a n hγ
      (ground_level_omega_mem M hM hT γ) (hmem a haγ)
      (hmem n ((Ordinal.natCast_lt_of_isSuccLimit haLim n).trans haγ))
    intro s hsn
    obtain ⟨m,rfl⟩ := Ordinal.lt_omega0.mp (hsn.trans (Ordinal.natCast_lt_omega0 n))
    have hmn : m < n := by exact_mod_cast hsn
    have hm2 : (m : Ordinal.{u})+2 < n+2 := by exact_mod_cast (show m+2 < n+2 by omega)
    have hpγ : a*(m+2) < γ := mul_lt_mul_of_pos_left hm2 ha0
    have hp : ProductCertificates (level R γ) a m :=
      (ih m hmn).mono (level_mono R (Order.add_one_le_iff.mpr hpγ))
    have hmγ : a*m < γ := mul_lt_mul_of_pos_left
      (hsn.trans (by exact_mod_cast (show n < n+2 by omega))) ha0
    refine ⟨hmem _ hmγ,hp,?_⟩
    intro t ht
    have htmargin := finite_sum_margin_lt_power β t hβ ht
    have hbound : a*m+8*t+8 < a*(m+1) := by
      rw [add_assoc,mul_add_one]
      exact (add_lt_add_iff_left (a*m)).mpr htmargin
    have hm1 : (m : Ordinal.{u})+1 ≤ n+2 := by exact_mod_cast (show m+1 ≤ n+2 by omega)
    have hboundγ := hbound.trans_le (mul_le_mul_right hm1 a)
    have hvγ : a*m+t < γ := by
      have hv : a*m+t < a*m+a := (add_lt_add_iff_left (a*m)).mpr ht
      rw [← mul_add_one] at hv
      exact hv.trans_le (mul_le_mul_right hm1 a)
    exact ⟨hmem _ hvγ,(sum_certificates_finite_bound M hM hT (a*m) t).mono
      (level_mono R hboundγ.le)⟩

theorem finite_products_below_omega_boundary (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (β : Ordinal.{u}) (hβ : 0 < β) :
    ∀ s < Ordinal.omega0, ProductCertificates
      (level (groundReals M) (Ordinal.omega0 ^ (β+1))) (Ordinal.omega0 ^ β) s := by
  intro s hs
  obtain ⟨n,rfl⟩ := Ordinal.lt_omega0.mp hs
  have h := finite_block_product_certificates M hM hT β hβ n
  apply h.mono (level_mono _ ?_)
  apply Order.add_one_le_iff.mpr
  rw [Ordinal.opow_add_one]
  apply mul_lt_mul_of_pos_left _ (Ordinal.opow_pos β Ordinal.omega0_pos)
  exact_mod_cast Ordinal.natCast_lt_omega0 (n+2)

theorem partial_sums_below_omega_boundary (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (β : Ordinal.{u}) (hβ : 0 < β) :
    ∀ s < Ordinal.omega0, ∀ t < Ordinal.omega0 ^ β, SumCertificates
      (level (groundReals M) (Ordinal.omega0 ^ (β+1))) (Ordinal.omega0 ^ β*s) t := by
  intro s hs t ht
  have hc := sum_certificates_below_power_cut M hM hT (Ordinal.omega0 ^ β*s) β t hβ ht
  apply hc.mono (level_mono _ ?_)
  rw [← mul_add_one,Ordinal.opow_add_one]
  exact mul_le_mul_right (Order.add_one_le_iff.mpr hs) _

theorem omega_boundary_product_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (β : Ordinal.{u}) (hβ : 0 < β)
    (hoff : realSeedOffset + β = β) :
    ProductCertificates
      (level (groundReals M) (Ordinal.omega0 ^ (β+1)+1)) (Ordinal.omega0 ^ β) Ordinal.omega0 :=
  omega_boundary_product_of_smaller_certificates M hM hT β hβ hoff
    (finite_products_below_omega_boundary M hM hT β hβ)
    (partial_sums_below_omega_boundary M hM hT β hβ)

theorem omega_boundary_product_without_offset (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (β : Ordinal.{u}) (hβ : 0 < β) :
    ProductCertificates
      (level (groundReals M) (Ordinal.omega0 ^ (β+1)+1)) (Ordinal.omega0 ^ β) Ordinal.omega0 := by
  let R := groundReals M
  let a := Ordinal.omega0 ^ β
  let b := Ordinal.omega0 ^ (β+1)
  have hab : a*Ordinal.omega0=b := (Ordinal.opow_add_one Ordinal.omega0 β).symm
  have ha0 : 0 < a := Ordinal.opow_pos β Ordinal.omega0_pos
  have hmem (c : Ordinal.{u}) (hc : c < b) : c.toZFSet ∈ level R b := by
    rw [ordinal_mem_level_iff]
    exact hc.trans_le le_add_self
  have hl : Order.IsSuccLimit b := Ordinal.isSuccLimit_opow_left
    Ordinal.isSuccLimit_omega0 (ne_of_gt (hβ.trans (lt_add_one β)))
  have hω := ground_level_omega_mem M hM hT b
  apply product_certificates_at_limit_successor R b a Ordinal.omega0 hl hω
    (hmem a ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (lt_add_one β)))
    (toZFSet_omega.symm ▸ hω)
  intro s hs
  have hv : a*s < b := hab ▸ mul_lt_mul_of_pos_left hs ha0
  refine ⟨hmem _ hv,finite_products_below_omega_boundary M hM hT β hβ s hs,?_⟩
  intro t ht
  have hv' : a*s+t < b := hab ▸ Ordinal.lt_mul_iff.mpr ⟨s,hs,t,ht,rfl⟩
  exact ⟨hmem _ hv',partial_sums_below_omega_boundary M hM hT β hβ s hs t ht⟩

end TuringRigidity.OrdinalArithmetic

end OAI
