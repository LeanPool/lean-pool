/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/SuccessorOmegaCertificates.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ExactOmegaGraph
public import LeanPool.TuringConeRigidity.Constructibility.FiniteStageSetBounds
public import LeanPool.TuringConeRigidity.OrdinalCodes.OmegaPowerCertificates

/-!
# Successor Omega Certificates
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

theorem omega_certificates_successor_add_five (R : ZFSet.{u}) (γ a : Ordinal.{u})
    (hc : OmegaPowerCertificates (level R γ) a.toZFSet)
    (ha : (Ordinal.omega0 ^ a).toZFSet ∈ level R γ)
    (hs : (Ordinal.omega0 ^ (a + 1)).toZFSet ∈ level R γ)
    (hp : ProductCertificates (level R γ) (Ordinal.omega0 ^ a) Ordinal.omega0) :
    OmegaPowerCertificates (level R (γ+5)) (a+1).toZFSet := by
  obtain ⟨hd,f,hf,r,hr,hg,hprod⟩ := hc
  have h02 : γ ≤ γ+2 := le_self_add
  have h05 : γ ≤ γ+5 := le_self_add
  have h15 : γ+1 ≤ γ+5 := add_le_add le_rfl (by norm_num)
  have h35 : γ+3 ≤ γ+5 := add_le_add le_rfl (by exact_mod_cast (by decide : (3 : ℕ) ≤ 5))
  let g := insert (ZFSet.pair a.toZFSet (omegaNext a.toZFSet)) f
  have hy : omegaNext a.toZFSet ∈ level R γ := by
    simpa only [omegaNext,Ordinal.rank_toZFSet] using hs
  have hgM : g ∈ level R (γ+3) := by
    have h := insert_mem_level_succ R (γ+2)
      (orderedPair_mem_level_add_two R γ hd hy) (level_mono R h02 hf)
    simpa only [add_assoc,show (2 : Ordinal.{u})+1=3 by norm_num] using h
  have hexact (z : ZFSet.{u}) : z ∈ g ↔
      ∃ x ∈ (a+1).toZFSet, z = ZFSet.pair x (omegaNext x) := by
    rw [Ordinal.toZFSet_add_one]
    change z ∈ insert _ f ↔ _
    rw [ZFSet.mem_insert_iff,hg.mem_iff]
    constructor
    · rintro (hz|⟨x,hx,hz⟩)
      · exact ⟨a.toZFSet,ZFSet.mem_insert _ _,hz⟩
      · exact ⟨x,ZFSet.mem_insert_of_mem _ hx,hz⟩
    · rintro ⟨x,hx,hz⟩
      rcases ZFSet.mem_insert_iff.mp hx with rfl|hx
      · exact Or.inl hz
      · exact Or.inr ⟨x,hx,hz⟩
  have hdom : (a+1).toZFSet ∈ level R (γ+5) := by
    rw [Ordinal.toZFSet_add_one]
    exact level_mono R h15 (insert_mem_level_succ R γ hd hd)
  have hrange : iterUnion 2 g ∈ level R (γ+5) := by
    simpa only [Nat.cast_ofNat,add_assoc,show (3 : Ordinal.{u})+2=5 by norm_num] using
      iterUnion_mem_level_add R (γ+3) hgM 2
  refine ⟨hdom,g,level_mono R h35 hgM,_,hrange,
    omegaGraph_of_exact_pairs _ _ g (ZFSet.isOrdinal_toZFSet _) hexact ?_,?_⟩
  · intro x hx
    rw [Ordinal.toZFSet_add_one] at hx
    rcases ZFSet.mem_insert_iff.mp hx with rfl|hx
    · simpa only [Ordinal.rank_toZFSet] using level_mono R h05 ha
    · exact level_mono R h05 (hg.union_value_mem hx)
  · intro x hx
    rw [Ordinal.toZFSet_add_one] at hx
    rcases ZFSet.mem_insert_iff.mp hx with rfl|hx
    · simpa only [Ordinal.rank_toZFSet] using hp.mono (level_mono R h05)
    · exact (hprod x hx).mono (level_mono R h05)

end TuringRigidity.OrdinalArithmetic

end OAI
