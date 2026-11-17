/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/RecursiveSumBound.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.FiniteSumStep
public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalDecoderDomains

/-!
# Recursive Sum Bound
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
  OrdinalCoding
universe u

theorem sum_certificates_finite_bound (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (a b : Ordinal.{u}) :
    SumCertificates (level (groundReals M) (a+8*b+8)) a b := by
  induction b using WellFoundedLT.induction with
  | ind b ih =>
    let R := groundReals M
    let γ := a+8*b+1
    have hb8 : b ≤ 8*b := Ordinal.le_mul_right b (by exact_mod_cast (show (0 : ℕ) < 8 by decide) :
      (0 : Ordinal.{u}) < 8)
    have hsmall (t : Ordinal.{u}) (ht : t < b) : a+8*t+8 ≤ a+8*b := by
      rw [add_assoc,← mul_add_one]
      exact add_le_add le_rfl (mul_le_mul_right (Order.add_one_le_iff.mpr ht) 8)
    have hmem (c : Ordinal.{u}) (hc : c ≤ a+8*b) : c.toZFSet ∈ level R γ := by
      rw [ordinal_mem_level_iff]
      exact (hc.trans_lt (lt_add_one _)).trans_le le_add_self
    have ha := hmem a le_self_add
    have hb := hmem b (hb8.trans le_add_self)
    have hc (t : Ordinal.{u}) (ht : t < b) :
        (a+t).toZFSet ∈ level R γ ∧ SumCertificates (level R γ) a t := by
      refine ⟨hmem _ (add_le_add le_rfl (ht.le.trans hb8)),?_⟩
      exact (ih t ht).mono (level_mono R ((hsmall t ht).trans le_self_add))
    have result := sum_certificates_at_add_five R γ a b
      (ground_level_omega_mem M hM hT γ) ha hb hc
    apply result.mono (level_mono R ?_)
    dsimp [γ]
    rw [add_assoc]
    exact add_le_add le_rfl (by norm_num : (1 : Ordinal.{u})+5 ≤ 8)

end TuringRigidity.OrdinalArithmetic

end OAI
