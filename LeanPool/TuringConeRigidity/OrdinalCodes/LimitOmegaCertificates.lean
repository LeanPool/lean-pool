/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/LimitOmegaCertificates.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.LimitOmegaGraphSyntax
public import LeanPool.TuringConeRigidity.SetModels.ExactOmegaGraph
public import LeanPool.TuringConeRigidity.Constructibility.FiniteStageSetBounds
public import LeanPool.TuringConeRigidity.OrdinalCodes.LevelOrdinalHeight

/-!
# Limit Omega Certificates
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

theorem omega_graph_at_limit_successor (R : ZFSet.{u}) (a : Ordinal.{u})
    (ha : Order.IsSuccLimit a) (hheight : ordinalHeight (seed R) + a = a)
    (hω : ZFSet.omega.{u} ∈ level R a)
    (hpow : ∀ c < a, (Ordinal.omega0 ^ c).toZFSet ∈ level R a ∧
      OmegaPowerCertificates (level R a) c.toZFSet) :
    ∃ f ∈ level R (a+1), ∀ z, z ∈ f ↔
      ∃ x ∈ a.toZFSet, z = ZFSet.pair x (omegaNext x) := by
  let A := level R a
  have hcut (c : Ordinal.{u}) : c.toZFSet ∈ A ↔ c < a := by
    rw [ordinal_mem_level_iff,hheight]
  let f := A.sep (fun z => omegaNextPairSentence.Sat (A : Set ZFSet)
    (cons z (fun _ => ZFSet.omega)))
  have hf : f ∈ level R (a+1) := by
    rw [level_succ]
    exact separation_mem_definablePower A omegaNextPairSentence (fun _ => ZFSet.omega)
      (fun _ _ => hω)
  refine ⟨f,hf,?_⟩
  intro z
  change z ∈ A.sep _ ↔ _
  rw [ZFSet.mem_sep]
  constructor
  · rintro ⟨hz,hzspec⟩
    obtain ⟨c,hc,hz⟩ := (omegaNextPairSentence_at_cut A (level_transitive R a) hω a ha hcut hpow
      _ (fun i => by
        cases i
        · exact hz
        · exact hω)).mp hzspec
    exact ⟨c.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr hc,hz⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hx
    have hy : omegaNext c.toZFSet ∈ A := by
      simpa only [omegaNext,Ordinal.rank_toZFSet] using (hpow (c+1) (ha.succ_lt hc)).1
    have hz := orderedPair_mem_level_limit R a ha ((hcut c).mpr hc) hy
    refine ⟨hz,(omegaNextPairSentence_at_cut A (level_transitive R a) hω a ha hcut hpow
      _ (fun i => by
        cases i
        · exact hz
        · exact hω)).mpr ⟨c,hc,rfl⟩⟩

theorem omega_certificates_at_limit_add_three (R : ZFSet.{u}) (a : Ordinal.{u})
    (ha : Order.IsSuccLimit a) (hheight : ordinalHeight (seed R) + a = a)
    (hω : ZFSet.omega.{u} ∈ level R a)
    (hpow : ∀ c < a, (Ordinal.omega0 ^ c).toZFSet ∈ level R a ∧
      OmegaPowerCertificates (level R a) c.toZFSet) :
    OmegaPowerCertificates (level R (a+3)) a.toZFSet := by
  obtain ⟨f,hf,hexact⟩ := omega_graph_at_limit_successor R a ha hheight hω hpow
  have h01 : a ≤ a+1 := le_self_add
  have h13 : a+1 ≤ a+3 := add_le_add le_rfl (by norm_num : (1 : Ordinal.{u}) ≤ 3)
  have h03 := h01.trans h13
  have hd : a.toZFSet ∈ level R (a+3) := by
    apply level_mono R h13
    apply (ordinal_mem_level_iff R (a+1) a).mpr
    rw [← add_assoc,hheight]
    exact lt_add_one a
  have hr : iterUnion 2 f ∈ level R (a+3) := by
    simpa only [Nat.cast_ofNat,add_assoc,show (1 : Ordinal.{u})+2=3 by norm_num] using
      iterUnion_mem_level_add R (a+1) hf 2
  refine ⟨hd,f,level_mono R h13 hf,_,hr,
    omegaGraph_of_exact_pairs _ _ f (ZFSet.isOrdinal_toZFSet a) hexact ?_,?_⟩
  · intro x hx
    obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hx
    rw [Ordinal.rank_toZFSet]
    exact level_mono R h03 (hpow c hc).1
  · intro x hx
    obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hx
    obtain ⟨_,g,hg,r,hr,hgraph,hprod⟩ := (hpow (c+1) (ha.succ_lt hc)).2
    exact (hprod c.toZFSet (Ordinal.toZFSet_mem_toZFSet_iff.mpr (lt_add_one c))).mono
      (level_mono R h03)

end TuringRigidity.OrdinalArithmetic

end OAI
