/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/RecursiveOmegaBound.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.BoundedOmegaGraph
public import LeanPool.TuringConeRigidity.Effective.FiniteBlockProducts
public import LeanPool.TuringConeRigidity.Constructibility.UniformOmegaLevels

/-!
# Recursive Omega Bound
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
  OrdinalCoding
universe u

theorem omega_certificates_explicit_bound (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (θ : Ordinal.{u})
    (hbase : ∀ c ≤ (1 : Ordinal.{u}), OmegaPowerCertificates (level (groundReals M) θ) c.toZFSet)
    (a : Ordinal.{u}) :
    OmegaPowerCertificates (level (groundReals M) (θ+Ordinal.omega0 ^ (a+1))) a.toZFSet := by
  let R := groundReals M
  have hmem (γ c : Ordinal.{u}) (hc : c < γ) : c.toZFSet ∈ level R γ := by
    rw [ordinal_mem_level_iff]
    exact hc.trans_le le_add_self
  induction a using Ordinal.limitRecOn with
  | zero => exact (hbase 0 zero_le_one).mono (level_mono R le_self_add)
  | add_one a ih =>
    by_cases ha0 : a = 0
    · subst a
      simpa only [zero_add] using (hbase 1 le_rfl).mono
        (level_mono R (show θ ≤ θ+Ordinal.omega0 ^ ((1 : Ordinal.{u})+1) from le_self_add))
    have ha : 0 < a := pos_iff_ne_zero.mpr ha0
    let b := Ordinal.omega0 ^ (a+1)
    let γ := θ+b+1
    have hiγ : θ+b ≤ γ := le_self_add
    have hbγ : b < γ := (show b ≤ θ+b from le_add_self).trans_lt (lt_add_one _)
    have haγ : Ordinal.omega0 ^ a < γ :=
      ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (lt_add_one a)).trans hbγ
    have hp := omega_boundary_product_without_offset M hM hT a ha
    have hpγ := hp.mono (level_mono R (show b+1 ≤ γ from add_le_add le_add_self le_rfl))
    have hc := omega_certificates_successor_add_five R γ a
      (ih.mono (level_mono R hiγ)) (hmem γ _ haγ) (hmem γ b hbγ) hpγ
    apply hc.mono (level_mono R ?_)
    have hbnext : b < Ordinal.omega0 ^ (a+1+1) :=
      (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (lt_add_one (a+1))
    have hlim : Order.IsSuccLimit (Ordinal.omega0 ^ (a+1+1)) :=
      Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt (by positivity))
    have hmargin := hlim.add_natCast_lt hbnext 6
    dsimp [γ]
    rw [add_assoc θ b 1,add_assoc θ (b+1) 5,add_assoc b 1 5]
    have h15 : (1 : Ordinal.{u}) + 5 = 6 := by norm_num
    exact add_le_add le_rfl (by simpa only [Nat.cast_ofNat, h15] using hmargin.le)
  | limit a ha ih =>
    let b := Ordinal.omega0 ^ a
    let γ := θ+b+1
    have haγ : a < γ :=
      ((Ordinal.right_le_opow a Ordinal.one_lt_omega0).trans le_add_self).trans_lt (lt_add_one _)
    have hlocal (c : Ordinal.{u}) (hc : c < a) :
        (Ordinal.omega0 ^ c).toZFSet ∈ level R γ ∧ OmegaPowerCertificates (level R γ) c.toZFSet :=
          by
      have hv : Ordinal.omega0 ^ c < b :=
        (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hc
      have hstage : θ+Ordinal.omega0 ^ (c+1) ≤ γ :=
        (add_le_add le_rfl (Ordinal.opow_le_opow_right Ordinal.omega0_pos (ha.succ_lt
          hc).le)).trans le_self_add
      exact ⟨hmem γ _ ((hv.trans_le le_add_self).trans (lt_add_one _)),
        (ih c hc).mono (level_mono R hstage)⟩
    have result := omega_limit_certificates_at_add_five R γ a ha (hmem γ a haγ)
      (ground_level_omega_mem M hM hT γ) hlocal
    apply result.mono (level_mono R ?_)
    have hbnext : b < Ordinal.omega0 ^ (a+1) :=
      (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (lt_add_one a)
    have hlim : Order.IsSuccLimit (Ordinal.omega0 ^ (a+1)) :=
      Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt (by positivity))
    have hmargin := hlim.add_natCast_lt hbnext 6
    dsimp [γ]
    rw [add_assoc θ b 1,add_assoc θ (b+1) 5,add_assoc b 1 5]
    have h15 : (1 : Ordinal.{u}) + 5 = 6 := by norm_num
    exact add_le_add le_rfl (by simpa only [Nat.cast_ofNat, h15] using hmargin.le)

theorem internal_explicit_omega_threshold (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) : ∃ θ : Ordinal.{u}, θ.toZFSet ∈ M ∧
      ∀ a : Ordinal.{u}, OmegaPowerCertificates
        (level (groundReals M) (θ+Ordinal.omega0 ^ (a+1))) a.toZFSet := by
  have h1 : (1 : Ordinal.{u}).toZFSet ∈ M := by
    simpa only [zero_add] using internal_ordinal_succ M hM hT 0 (internal_ordinal_zero M hM hT)
  obtain ⟨θ,hθ,hbound⟩ := uniform_omega_certificates_at_levels M hM hT 1 h1
  exact ⟨θ,hθ,omega_certificates_explicit_bound M hM hT θ
    (fun c hc => (hbound θ le_rfl c hc).2.2.1)⟩

theorem lower_omega_closure_of_fixed_point (M : ZFSet.{u}) (θ β : Ordinal.{u})
    (hbound : ∀ a : Ordinal.{u}, OmegaPowerCertificates
      (level (groundReals M) (θ+Ordinal.omega0 ^ (a+1))) a.toZFSet)
    (hβ : Order.IsSuccLimit β) (hθ : θ < β) (hfix : Ordinal.omega0 ^ β = β) :
    ∀ c < β, (Ordinal.omega0 ^ c).toZFSet ∈ level (groundReals M) β ∧
      OmegaPowerCertificates (level (groundReals M) β) c.toZFSet := by
  intro c hc
  have hv : Ordinal.omega0 ^ c < β := hfix ▸
    (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hc
  have hs : Ordinal.omega0 ^ (c+1) < β := hfix ▸
    (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (hβ.succ_lt hc)
  have hsum : θ+Ordinal.omega0 ^ (c+1) < β := by
    rw [← hfix] at hθ hs ⊢
    exact Ordinal.isPrincipal_add_omega0_opow β hθ hs
  refine ⟨?_,(hbound c).mono (level_mono _ hsum.le)⟩
  rw [ordinal_mem_level_iff]
  exact hv.trans_le le_add_self

end TuringRigidity.OrdinalArithmetic

end OAI
