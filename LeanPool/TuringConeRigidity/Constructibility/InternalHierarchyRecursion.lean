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
Only certificate collection, graph union, and domain extension are shared through
SetModels/CertifiedGraphAssembly.lean; semantic recursion and value closure remain here.
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
    obtain ⟨g,hgM,hg⟩ := CertifiedGraphAssembly.certified_union M (x)
      C.transitive hU hR hxM p e he
      (fun y f => ∃ r ∈ M, HierarchyGraph M (seed R) (hull d q y) r f)
      (fun y z => ∃ w ∈ (hull d q) y, z = ZFSet.pair w ((fun w => definablePower (stage R w)) w))
      (fun y hy f hf => cert y f hy hf) (by
        intro y hy
        obtain ⟨f,hf,hfg⟩ := ih y hy (hd x hx y hy)
        exact ⟨f,hf,_,iterUnion_mem M C.transitive hU hf 2,hfg⟩) (by
        intro _ _ f g hf hg
        obtain ⟨_,_,hf⟩ := hf
        obtain ⟨_,_,hg⟩ := hg
        exact hf.unique hg) (by
        intro _ _ _ hf z
        obtain ⟨_,_,hf⟩ := hf
        exact hf.mem_iff z)
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
    exact CertifiedGraphAssembly.singleton_graph_extension (x) x
      (hull d q) (fun w => definablePower (stage R w)) (hull d q x) g
      (hull_unfold M d q C.transitive hP hU hS hR hdM hqM hd hq hx) hg

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
