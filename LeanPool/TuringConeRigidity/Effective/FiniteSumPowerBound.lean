/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/FiniteSumPowerBound.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.RecursiveSumBound
public import LeanPool.TuringConeRigidity.OrdinalCodes.TrimmedPaddedSum

/-!
# Finite Sum Power Bound
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
  OrdinalCoding
universe u

theorem finite_left_mul_omega_power (n : ℕ) (hn : 0 < n) (β : Ordinal.{u}) (hβ : 0 < β) :
    (n : Ordinal.{u}) * Ordinal.omega0 ^ β = Ordinal.omega0 ^ β := by
  have h1 : (1 : Ordinal.{u}) ≤ β := by simpa only [zero_add] using Order.add_one_le_iff.mpr hβ
  have hsplit : β = 1+(β-1) := (Ordinal.add_sub_cancel_of_le h1).symm
  have hp : Ordinal.omega0 ^ β = Ordinal.omega0 * Ordinal.omega0 ^ (β-1) := by
    conv_lhs => rw [hsplit,Ordinal.opow_add,Ordinal.opow_one]
  rw [hp,← mul_assoc,Ordinal.natCast_mul_omega0 hn]

theorem finite_sum_margin_lt_power (β t : Ordinal.{u}) (hβ : 0 < β)
    (ht : t < Ordinal.omega0 ^ β) : 8*t+8 < Ordinal.omega0 ^ β := by
  have hn : (0 : ℕ) < 8 := by decide
  have h8 : (0 : Ordinal.{u}) < 8 := by exact_mod_cast hn
  have hmul : 8*t < Ordinal.omega0 ^ β := by
    rw [← finite_left_mul_omega_power 8 hn β hβ]
    exact mul_lt_mul_of_pos_left ht h8
  have hω : Ordinal.omega0 ≤ Ordinal.omega0 ^ β := by
    have hβ1 : (1 : Ordinal.{u}) ≤ β := by
      simpa only [zero_add] using (Order.add_one_le_iff.mpr hβ)
    simpa only [Ordinal.opow_one] using
      Ordinal.opow_le_opow_right Ordinal.omega0_pos hβ1
  exact Ordinal.isPrincipal_add_omega0_opow β hmul
    ((Ordinal.natCast_lt_omega0 8).trans_le hω)

theorem sum_certificates_below_power_cut (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (a β t : Ordinal.{u}) (hβ : 0 < β)
    (ht : t < Ordinal.omega0 ^ β) :
    SumCertificates (level (groundReals M) (a+Ordinal.omega0 ^ β)) a t := by
  apply (sum_certificates_finite_bound M hM hT a t).mono (level_mono _ ?_)
  rw [add_assoc]
  exact ((add_lt_add_iff_left a).mpr (finite_sum_margin_lt_power β t hβ ht)).le

theorem padded_final_sum_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (hβ : 0 < β) (hoff : realSeedOffset + β = β) (hv : vectorCode v ≤ β) :
    SumCertificates (level (groundReals M) (heightDomainIndex (paddedCode v β)))
      (Ordinal.omega0 ^ (β+1)) (Ordinal.omega0 ^ vectorCode v) := by
  apply padded_final_sum_of_smaller_certificates M hM hT v β hβ hoff hv
  intro t ht
  have hc : paddedCode v β = Ordinal.omega0 ^ (β+1)+Ordinal.omega0 ^ vectorCode v := by
    change pairCode β (vectorCode v) = _
    rw [pairCode,ite_eq_left hv]
  rw [hc]
  exact sum_certificates_below_power_cut M hM hT _ _ t (vectorCode_pos v) ht

end TuringRigidity.OrdinalArithmetic

end OAI
