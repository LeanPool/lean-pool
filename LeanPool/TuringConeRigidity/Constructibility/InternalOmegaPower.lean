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
The schema recursion proofs are shared from upstream
SetModels/RestrictedOmegaRecursion.lean.
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

/-- Replacement and collection construct the internal successor omega graph. -/
theorem internal_omegaGraph_of_schemas (M : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement M)
  (hColl : SigmaCollection M)
    (x : ZFSet.{u}) (hxM : x ∈ M) (hxo : x.IsOrdinal) :
    ∃ f ∈ M, OmegaGraph M (insert x x) (iterUnion 2 f) f := by
  have h1 : (1 : Ordinal.{u}).toZFSet ∈ M := by
    rw [← Nat.cast_one,toZFSet_nat]
    exact C.transitive _ (omega_mem M C.transitive C.separation C.infinity) _ ((mem_omega _).mpr
      ⟨1,rfl⟩)
  obtain ⟨p,e,he,hp⟩ := uniform_omega_certificate_of_schemas M C hRep hColl
  induction x using ZFSet.inductionOn with
  | h x ih =>
    have cert (y f : ZFSet.{u}) (hy : y ∈ x) (hf : f ∈ M) := hp y (C.transitive x hxM y hy) f hf
    obtain ⟨b,hb,hbdef⟩ := hRep p e he x hxM (by
      intro y hy
      obtain ⟨f,hf,hfg⟩ := ih y hy (C.transitive x hxM y hy) (hxo.mem hy)
      refine ⟨f,hf,(cert y f hy hf).mpr
        ⟨_,iterUnion_mem M C.transitive C.union hf 2,hfg⟩,?_⟩
      intro g hg hcg
      obtain ⟨r,_,hgg⟩ := (cert y g hy hg).mp hcg
      exact hgg.unique hfg)
    have hbg (f : ZFSet.{u}) : f ∈ b ↔
        ∃ y ∈ x, ∃ r ∈ M, OmegaGraph M (insert y y) r f := by
      constructor
      · intro hf
        have hfM := C.transitive b hb f hf
        obtain ⟨y,hy,hc⟩ := (hbdef f hfM).mp hf
        exact ⟨y,hy,(cert y f hy hfM).mp hc⟩
      · rintro ⟨y,hy,r,hr,hg⟩
        obtain ⟨f',hf',hg'⟩ := ih y hy (C.transitive x hxM y hy) (hxo.mem hy)
        have heq := hg.unique hg'
        have hfM : f ∈ M := heq ▸ hf'
        exact (hbdef f hfM).mpr ⟨y,hy,(cert y f hy hfM).mpr ⟨r,hr,hg⟩⟩
    let g := ZFSet.sUnion b
    have hgM : g ∈ M := union_mem M C.transitive C.union hb
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
        obtain ⟨f,hf,hfg⟩ := ih y hy (C.transitive x hxM y hy) (hxo.mem hy)
        exact ZFSet.mem_sUnion.mpr ⟨f,(hbg f).mpr
          ⟨y,hy,_,iterUnion_mem M C.transitive C.union hf 2,hfg⟩,
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
      hvalue ▸ stageImage_mem_of_context M C h1 hxM hgM
    have hvM : omegaNext x ∈ M := by
      rw [omegaNext,Ordinal.opow_add_one]
      exact (ordinal_mul_internal_schemas M C.transitive C.pairing C.union C.power C.separation
        hRep _ Ordinal.omega0 hpow (toZFSet_omega.symm ▸ C.omega_mem)).1
    let f := g ∪ ({ZFSet.pair x (omegaNext x)} : ZFSet.{u})
    have hfM : f ∈ M := binary_union_mem M C.transitive C.pairing C.union hgM
      (singleton_mem M C.transitive C.pairing (orderedPair_mem M C.transitive C.pairing hxM hvM))
    have hsucc : (insert x x).IsOrdinal := by
      rw [← hxo.toZFSet_rank_eq,← Ordinal.toZFSet_add_one]
      exact ZFSet.isOrdinal_toZFSet _
    refine ⟨f,hfM,omegaGraph_of_mem_iff_of_context M _ f C
      (insert_self_mem M C.transitive C.pairing C.union hxM) hfM hsucc ?_⟩
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

/-- Internal omega exponentiation follows from the explicit recursion schemas. -/
theorem ordinal_omega_opow_of_schemas (M : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement M)
  (hColl : SigmaCollection M)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) : (Ordinal.omega0 ^ a).toZFSet ∈ M := by
  obtain ⟨f,hf,hg⟩ := internal_omegaGraph_of_schemas M C hRep hColl a.toZFSet ha
    (ZFSet.isOrdinal_toZFSet a)
  have h1 : (1 : Ordinal.{u}).toZFSet ∈ M := by
    rw [← Nat.cast_one,toZFSet_nat]
    exact C.transitive _ (omega_mem M C.transitive C.separation C.infinity) _ ((mem_omega _).mpr
      ⟨1,rfl⟩)
  have hv := omegaStageImage _ f a.toZFSet hg.1 (ZFSet.mem_insert_iff.mpr (Or.inl rfl)) hg.mem_iff
  rw [Ordinal.rank_toZFSet] at hv
  exact hv ▸ stageImage_mem_of_context M C h1 ha hf

theorem internal_omegaGraph (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (x : ZFSet.{u}) (hxM : x ∈ M) (hxo : x.IsOrdinal) :
    ∃ f ∈ M, OmegaGraph M (insert x x) (iterUnion 2 f) f := by
  let C : Context M :=
    ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  have hColl := sigma_collection M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix hT.replacement.finitePrefix hT.infinity hT.choice
  exact internal_omegaGraph_of_schemas M C hT.replacement.finitePrefix hColl x hxM hxo

theorem ordinal_omega_opow_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) : (Ordinal.omega0 ^ a).toZFSet ∈ M := by
  let C : Context M :=
    ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  have hColl := sigma_collection M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix hT.replacement.finitePrefix hT.infinity hT.choice
  exact ordinal_omega_opow_of_schemas M C hT.replacement.finitePrefix hColl a ha

end TuringRigidity.OrdinalArithmetic

end OAI
