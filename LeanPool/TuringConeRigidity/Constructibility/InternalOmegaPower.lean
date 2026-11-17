/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/InternalOmegaPower.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OmegaPowerGraph

/-!
# Internal Omega Power
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions
universe u

theorem internal_omegaGraph (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (x : ZFSet.{u}) (hxM : x ∈ M) (hxo : x.IsOrdinal) :
    ∃ f ∈ M, OmegaGraph M (insert x x) (iterUnion 2 f) f := by
  have h1 : (1 : Ordinal.{u}).toZFSet ∈ M := by
    rw [← Nat.cast_one,toZFSet_nat]
    exact hM _ (omega_mem M hM hT.separation.finitePrefix.bounded hT.infinity) _ ((mem_omega
      _).mpr ⟨1,rfl⟩)
  obtain ⟨p,e,he,hp⟩ := uniform_omega_certificate M hM hT
  induction x using ZFSet.inductionOn with
  | h x ih =>
    have cert (y f : ZFSet.{u}) (hy : y ∈ x) (hf : f ∈ M) := hp y (hM x hxM y hy) f hf
    obtain ⟨b,hb,hbdef⟩ := hT.replacement.finitePrefix p e he x hxM (by
      intro y hy
      obtain ⟨f,hf,hfg⟩ := ih y hy (hM x hxM y hy) (hxo.mem hy)
      refine ⟨f,hf,(cert y f hy hf).mpr
        ⟨_,iterUnion_mem M hM hT.union hf 2,hfg⟩,?_⟩
      intro g hg hcg
      obtain ⟨r,_,hgg⟩ := (cert y g hy hg).mp hcg
      exact hgg.unique hfg)
    have hbg (f : ZFSet.{u}) : f ∈ b ↔
        ∃ y ∈ x, ∃ r ∈ M, OmegaGraph M (insert y y) r f := by
      constructor
      · intro hf
        have hfM := hM b hb f hf
        obtain ⟨y,hy,hc⟩ := (hbdef f hfM).mp hf
        exact ⟨y,hy,(cert y f hy hfM).mp hc⟩
      · rintro ⟨y,hy,r,hr,hg⟩
        obtain ⟨f',hf',hg'⟩ := ih y hy (hM x hxM y hy) (hxo.mem hy)
        have heq := hg.unique hg'
        have hfM : f ∈ M := heq ▸ hf'
        exact (hbdef f hfM).mpr ⟨y,hy,(cert y f hy hfM).mpr ⟨r,hr,hg⟩⟩
    let g := ZFSet.sUnion b
    have hgM : g ∈ M := union_mem M hM hT.union hb
    have hg (z : ZFSet.{u}) : z ∈ g ↔ ∃ y ∈ x, z = ZFSet.pair y (omegaNext y) := by
      constructor
      · intro hz
        obtain ⟨f,hf,hzf⟩ := ZFSet.mem_sUnion.mp hz
        obtain ⟨y,hy,r,_,hfg⟩ := (hbg f).mp hf
        obtain ⟨w,hw,hz⟩ := (hfg.mem_iff z).mp hzf
        rcases ZFSet.mem_insert_iff.mp hw with rfl|hw
        · exact ⟨w,hy,hz⟩
        · exact ⟨w,hxo.subset_of_mem hy hw,hz⟩
      · rintro ⟨y,hy,hz⟩
        obtain ⟨f,hf,hfg⟩ := ih y hy (hM x hxM y hy) (hxo.mem hy)
        exact ZFSet.mem_sUnion.mpr ⟨f,(hbg f).mpr
          ⟨y,hy,_,iterUnion_mem M hM hT.union hf 2,hfg⟩,
          (hfg.mem_iff z).mpr ⟨y,ZFSet.mem_insert_iff.mpr (Or.inl rfl),hz⟩⟩
    have hvalue : stageImage (1 : Ordinal.{u}).toZFSet x g =
        (Ordinal.omega0 ^ x.rank).toZFSet := by
      apply ZFSet.ext; intro z
      rw [mem_stageImage,omegaPower_members,hxo.toZFSet_rank_eq]
      apply or_congr_right
      constructor
      · rintro ⟨y,hy,w,hfw,hz⟩
        obtain ⟨v,_,hp⟩ := (hg _).mp hfw
        obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
        exact ⟨y,hy,hz⟩
      · rintro ⟨y,hy,hz⟩
        exact ⟨y,hy,_,(hg _).mpr ⟨y,hy,rfl⟩,hz⟩
    have hpow : (Ordinal.omega0 ^ x.rank).toZFSet ∈ M :=
      hvalue ▸ stageImage_mem M hM hT h1 hxM hgM
    have hvM : omegaNext x ∈ M := by
      rw [omegaNext,Ordinal.opow_add_one]
      exact ordinal_mul_omega_internal M hM hT _ hpow
    let f := g ∪ ({ZFSet.pair x (omegaNext x)} : ZFSet.{u})
    have hfM : f ∈ M := binary_union_mem M hM hT.pairing hT.union hgM
      (singleton_mem M hM hT.pairing (orderedPair_mem M hM hT.pairing hxM hvM))
    have hsucc : (insert x x).IsOrdinal := by
      rw [← hxo.toZFSet_rank_eq,← Ordinal.toZFSet_add_one]
      exact ZFSet.isOrdinal_toZFSet _
    refine ⟨f,hfM,omegaGraph_of_mem_iff M _ f hM hT
      (insert_self_mem M hM hT.pairing hT.union hxM) hfM hsucc ?_⟩
    intro z
    change z ∈ g ∪ ({ZFSet.pair x (omegaNext x)} : ZFSet.{u}) ↔ _
    rw [ZFSet.mem_union,ZFSet.mem_singleton,hg]
    constructor
    · rintro (⟨y,hy,hz⟩|hz)
      · exact ⟨y,ZFSet.mem_insert_of_mem _ hy,hz⟩
      · exact ⟨x,ZFSet.mem_insert_iff.mpr (Or.inl rfl),hz⟩
    · rintro ⟨y,hy,hz⟩
      rcases ZFSet.mem_insert_iff.mp hy with rfl|hy
      · exact Or.inr hz
      · exact Or.inl ⟨y,hy,hz⟩

theorem ordinal_omega_opow_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) : (Ordinal.omega0 ^ a).toZFSet ∈ M := by
  obtain ⟨f,hf,hg⟩ := internal_omegaGraph M hM hT a.toZFSet ha (ZFSet.isOrdinal_toZFSet a)
  have h1 : (1 : Ordinal.{u}).toZFSet ∈ M := by
    rw [← Nat.cast_one,toZFSet_nat]
    exact hM _ (omega_mem M hM hT.separation.finitePrefix.bounded hT.infinity) _ ((mem_omega
      _).mpr ⟨1,rfl⟩)
  have hv := omegaStageImage _ f a.toZFSet hg.1 (ZFSet.mem_insert_iff.mpr (Or.inl rfl)) hg.mem_iff
  rw [Ordinal.rank_toZFSet] at hv
  exact hv ▸ stageImage_mem M hM hT h1 ha hf

end TuringRigidity.OrdinalArithmetic

end OAI
