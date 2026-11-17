/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/InternalHierarchyRecursion.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
The common recursion adapts upstream Constructibility/CollectionHierarchyRecursion.lean.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.HierarchySyntax

/-!
# Internal Hierarchy Recursion
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

/-- Construct the hierarchy graph using explicit replacement and collection. -/
theorem internal_hierarchyGraph_context (M R d q : ZFSet.{u}) (C : Context M) (hRep :
  SigmaReplacement M) (hColl : SigmaCollection M)
    (hs : seed R ∈ M) (hdM : d ∈ M) (hqM : q ∈ M) (hd : Transitive d)
    (hq : ∀ c, c ∈ q ↔ c ∈ M ∧ c ⊆ d) (x : ZFSet.{u}) (hx : x ∈ d) :
    ∃ f ∈ M, HierarchyGraph M (seed R) (hull d q x) (iterUnion 2 f) f := by
  let hP := C.pairing
  let hU := C.union
  let hS := C.separation
  let hR := hRep
  obtain ⟨p,e,he,hp⟩ := uniform_hierarchy_certificate_context M R d q C hRep hColl hs hdM hqM
    hd hq
  induction x using ZFSet.inductionOn with
  | h x ih =>
    have hxM := C.transitive d hdM x hx
    have cert (y f : ZFSet.{u}) (hy : y ∈ x) (hf : f ∈ M) :
        p.Realize M (cons f (cons y e)) ↔
          ∃ r ∈ M, HierarchyGraph M (seed R) (hull d q y) r f :=
      hp y (hd x hx y hy) f hf
    obtain ⟨b,hb,hbdef⟩ := hR p e he x hxM (by
      intro y hy
      obtain ⟨f,hf,hfg⟩ := ih y hy (hd x hx y hy)
      refine ⟨f,hf,(cert y f hy hf).mpr
        ⟨_,iterUnion_mem M C.transitive hU hf 2,hfg⟩,?_⟩
      intro g hg hcg
      obtain ⟨r,_,hgg⟩ := (cert y g hy hg).mp hcg
      exact hgg.unique hfg)
    have hbg (f : ZFSet.{u}) : f ∈ b ↔
        ∃ y ∈ x, ∃ r ∈ M, HierarchyGraph M (seed R) (hull d q y) r f := by
      constructor
      · intro hf
        have hfM := C.transitive b hb f hf
        obtain ⟨y,hy,hc⟩ := (hbdef f hfM).mp hf
        exact ⟨y,hy,(cert y f hy hfM).mp hc⟩
      · rintro ⟨y,hy,r,hr,hg⟩
        obtain ⟨f',hf',hg'⟩ := ih y hy (hd x hx y hy)
        have heq := hg.unique hg'
        have hfM : f ∈ M := heq ▸ hf'
        exact (hbdef f hfM).mpr ⟨y,hy,(cert y f hy hfM).mpr ⟨r,hr,hg⟩⟩
    let g := ZFSet.sUnion b
    have hgM : g ∈ M := union_mem M C.transitive hU hb
    have hg (z : ZFSet.{u}) : z ∈ g ↔
        ∃ y ∈ x, ∃ w ∈ hull d q y, z = ZFSet.pair w (definablePower (stage R w)) := by
      constructor
      · intro hz
        obtain ⟨f,hf,hzf⟩ := ZFSet.mem_sUnion.mp hz
        obtain ⟨y,hy,r,_,hfg⟩ := (hbg f).mp hf
        exact ⟨y,hy,(hfg.mem_iff z).mp hzf⟩
      · rintro ⟨y,hy,w,hw,hz⟩
        obtain ⟨f,hf,hfg⟩ := ih y hy (hd x hx y hy)
        exact ZFSet.mem_sUnion.mpr ⟨f,(hbg f).mpr
          ⟨y,hy,_,iterUnion_mem M C.transitive hU hf 2,hfg⟩,(hfg.mem_iff z).mpr ⟨w,hw,hz⟩⟩
    have hvalue : stageImage (seed R) x g = stage R x := by
      apply ZFSet.ext; intro z
      rw [mem_stageImage,mem_stage]
      apply or_congr_right
      constructor
      · rintro ⟨y,hy,w,hw,hz⟩
        obtain ⟨a,_,v,_,hp⟩ := (hg _).mp hw
        obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
        exact ⟨y,hy,hz⟩
      · rintro ⟨y,hy,hz⟩
        exact ⟨y,hy,_,(hg _).mpr
          ⟨y,hy,y,self_mem_hull d q (hd x hx y hy),rfl⟩,hz⟩
    have hvM : definablePower (stage R x) ∈ M := definablePower_mem_of_context M _ C
      (hvalue ▸ stageImage_mem_of_context M C hs hxM hgM)
    let f := g ∪ ({ZFSet.pair x (definablePower (stage R x))} : ZFSet.{u})
    have hfM : f ∈ M := binary_union_mem M C.transitive hP hU hgM
      (singleton_mem M C.transitive hP (orderedPair_mem M C.transitive hP hxM hvM))
    refine ⟨f,hfM,hierarchyGraph_of_mem_iff_of_context M R _ f C hs
      (hull_mem M d q C.transitive hS hdM hqM hxM) hfM (hull_transitive d q x hd) ?_⟩
    intro z
    change z ∈ g ∪ ({ZFSet.pair x (definablePower (stage R x))} : ZFSet.{u}) ↔ _
    rw [ZFSet.mem_union,ZFSet.mem_singleton,hg]
    constructor
    · rintro (⟨y,hy,w,hw,hz⟩|hz)
      · exact ⟨w,(hull_unfold M d q C.transitive hP hU hS hR hdM hqM hd hq hx w).mpr
          (Or.inr ⟨y,hy,hw⟩),hz⟩
      · exact ⟨x,self_mem_hull d q hx,hz⟩
    · rintro ⟨w,hw,hz⟩
      rcases (hull_unfold M d q C.transitive hP hU hS hR hdM hqM hd hq hx w).mp hw with
        rfl|⟨y,hy,hw⟩
      · exact Or.inr hz
      · exact Or.inl ⟨y,hy,w,hw,hz⟩

theorem internal_hierarchyGraph (M R d q : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hs : seed R ∈ M) (hdM : d ∈ M) (hqM : q ∈ M) (hd : Transitive d)
    (hq : ∀ c, c ∈ q ↔ c ∈ M ∧ c ⊆ d) (x : ZFSet.{u}) (hx : x ∈ d) :
    ∃ f ∈ M, HierarchyGraph M (seed R) (hull d q x) (iterUnion 2 f) f := by
  let C : Context M :=
    ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  have hColl := sigma_collection M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix hT.replacement.finitePrefix hT.infinity hT.choice
  exact internal_hierarchyGraph_context M R d q C hT.replacement.finitePrefix hColl
    hs hdM hqM hd hq x hx

end TuringRigidity.RelativeConstructible

end OAI
