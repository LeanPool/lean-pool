/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/PaddedOmegaBoundary.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.LimitOmegaCertificates
public import LeanPool.TuringConeRigidity.OrdinalCodes.SuccessorOmegaCertificates
public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalDecoderDomains

/-!
# Padded Omega Boundary
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
  OrdinalArithmetic
universe u

theorem offset_absorbed_above (s a b : Ordinal.{u}) (ha : s + a = a) (hab : a ≤ b) : s+b=b := by
  calc
    s+b = s+(a+(b-a)) := by rw [Ordinal.add_sub_cancel_of_le hab]
    _ = b := by rw [← add_assoc,ha,Ordinal.add_sub_cancel_of_le hab]

theorem heightDomainIndex_of_absorbed (a : Ordinal.{u}) (ha : realSeedOffset + a = a) :
    heightDomainIndex a = a+1 := by
  rw [heightDomainIndex,Ordinal.sub_eq_of_add_eq ha]

theorem padded_omega_boundary_certificates (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (hβ : Order.IsSuccLimit β) (hoff : realSeedOffset + β = β) (hv : vectorCode v ≤ β)
    (hpow : ∀ c < β, (Ordinal.omega0 ^ c).toZFSet ∈ level (groundReals M) β ∧
      OmegaPowerCertificates (level (groundReals M) β) c.toZFSet)
    (hprod : ProductCertificates
      (level (groundReals M) (Ordinal.omega0 ^ (β + 1) + 1)) (Ordinal.omega0 ^ β) Ordinal.omega0) :
    OmegaPowerCertificates
      (level (groundReals M) (heightDomainIndex (paddedCode v β))) (β+1).toZFSet := by
  let R := groundReals M
  let b := Ordinal.omega0 ^ (β+1)
  have hβpos : 0 < β := Ordinal.natCast_lt_of_isSuccLimit hβ 0
  have hβb : β < b := (lt_add_one β).trans_le (Ordinal.right_le_opow (β+1) Ordinal.one_lt_omega0)
  have hbLimit : Order.IsSuccLimit b := Ordinal.isSuccLimit_opow_left
    Ordinal.isSuccLimit_omega0 (ne_of_gt (hβpos.trans (lt_add_one β)))
  have hβ3 : β+3 < b := by
    have h := hbLimit.succ_lt (hbLimit.succ_lt (hbLimit.succ_lt hβb))
    simpa only [Order.succ_eq_add_one,add_assoc,one_add_one_eq_two,
      show (2 : Ordinal.{u})+1=3 by norm_num] using h
  have hheight : ordinalHeight (seed R)+β=β := by
    rw [ground_seed_offset M hM hT]; exact hoff
  have hc := omega_certificates_at_limit_add_three R β hβ hheight
    (ground_level_omega_mem M hM hT β) hpow
  have hbabs := offset_absorbed_above realSeedOffset β b hoff hβb.le
  have hbM : b.toZFSet ∈ level R (b+1) := by
    apply (ordinal_mem_level_iff R (b+1) b).mpr
    rw [ground_seed_offset M hM hT,← add_assoc,hbabs]
    exact lt_add_one b
  have hpM : (Ordinal.omega0 ^ β).toZFSet ∈ level R (b+1) :=
    internal_ordinal_downward _ (level_transitive R (b+1)) hbM
      (Ordinal.opow_le_opow_right Ordinal.omega0_pos (le_of_lt (lt_add_one β)))
  have hs := omega_certificates_successor_add_five R (b+1) β
    (hc.mono (level_mono R (hβ3.le.trans le_self_add))) hpM hbM hprod
  have hbcode : b < paddedCode v β := by
    change b < pairCode β (vectorCode v)
    rw [pairCode,ite_eq_left hv]
    simpa only [add_zero] using (add_lt_add_iff_left b).mpr
      (Ordinal.opow_pos (vectorCode v) Ordinal.omega0_pos)
  have hcodeabs := offset_absorbed_above realSeedOffset β (paddedCode v β) hoff
    (padding_lt_paddedCode v β).le
  rw [heightDomainIndex_of_absorbed _ hcodeabs]
  apply hs.mono (level_mono R ?_)
  have hmargin := finite_margin_lt_paddedCode v β b hβpos hbcode 6
  have hsum : b+1+5 = b+6 := by
    rw [add_assoc]; congr 1; norm_num
  rw [hsum]
  exact hmargin.le.trans le_self_add

end TuringRigidity.OrdinalCoding

end OAI
