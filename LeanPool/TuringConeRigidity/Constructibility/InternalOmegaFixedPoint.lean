/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/InternalOmegaFixedPoint.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalSigmaSequence
public import LeanPool.TuringConeRigidity.OrdinalCodes.OmegaPowerDefinability

/-!
# Internal Omega Fixed Point
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory BoundedDefinability RelationCollapse ElementaryModel
  RelativeConstructible
universe u

theorem omega_fixed_point_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (θ : Ordinal.{u}) (hθ : θ.toZFSet ∈ M) :
    (Ordinal.nfp (fun a : Ordinal.{u} => Ordinal.omega0 ^ a) θ).toZFSet ∈ M := by
  let F : Ordinal.{u} → Ordinal.{u} := fun a => Ordinal.omega0 ^ a
  let s : ℕ → ZFSet.{u} := fun n => (F^[n] θ).toZFSet
  let S : ZFSet.{u} → ZFSet.{u} → Prop := fun x y =>
    x.IsOrdinal ∧ y = (Ordinal.omega0 ^ x.rank).toZFSet
  have hs (n : ℕ) : s n ∈ M := by
    induction n with
    | zero => exact hθ
    | succ n ih =>
      simpa only [s,Function.iterate_succ_apply',F] using
        ordinal_omega_opow_internal M hM hT (F^[n] θ) ih
  have hstep (n : ℕ) : S (s n) (s (n+1)) := by
    refine ⟨ZFSet.isOrdinal_toZFSet _,?_⟩
    simp only [s,Function.iterate_succ_apply',F,Ordinal.rank_toZFSet]
  have hu (n : ℕ) (y : ZFSet.{u}) (h : S (s n) y) : y = s (n+1) := by
    simpa only [s,Function.iterate_succ_apply',F,Ordinal.rank_toZFSet] using h.2
  obtain ⟨B,hB,hdef⟩ := sigma_sequence_range_internal M hM hT S
    (omegaPower_sigmaDefinable M hM hT) s hs hstep hu
  have heq : (Ordinal.nfp F θ).toZFSet = ZFSet.sUnion B := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sUnion]
    constructor
    · intro hz
      obtain ⟨a,ha,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hz
      obtain ⟨n,hn⟩ := Ordinal.lt_nfp_iff.mp ha
      exact ⟨s n,(hdef _).mpr ⟨n,rfl⟩,Ordinal.toZFSet_mem_toZFSet_iff.mpr hn⟩
    · rintro ⟨t,ht,hz⟩
      obtain ⟨n,rfl⟩ := (hdef t).mp ht
      exact Ordinal.toZFSet_monotone (Ordinal.iterate_le_nfp F θ n) hz
  rw [heq]
  exact union_mem M hM hT.union hB

theorem cofinal_internal_omega_fixed_points (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (θ : Ordinal.{u}) (hθ : θ.toZFSet ∈ M) :
    ∃ β : Ordinal.{u}, β.toZFSet ∈ M ∧ θ < β ∧ Order.IsSuccLimit β ∧ Ordinal.omega0 ^ β = β := by
  let F : Ordinal.{u} → Ordinal.{u} := fun a => Ordinal.omega0 ^ a
  let β := Ordinal.nfp F (θ+1)
  have hb : θ < β := (lt_add_one θ).trans_le (Ordinal.le_nfp F (θ+1))
  have hfix : Ordinal.omega0 ^ β = β := Ordinal.nfp_fp (Ordinal.isNormal_opow
    Ordinal.one_lt_omega0) (θ+1)
  refine ⟨β,omega_fixed_point_internal M hM hT (θ+1) (internal_ordinal_succ M hM hT θ
    hθ),hb,?_,hfix⟩
  rw [← hfix]
  exact Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt (lt_of_le_of_lt zero_le
    hb))

end TuringRigidity.OrdinalArithmetic

end OAI
