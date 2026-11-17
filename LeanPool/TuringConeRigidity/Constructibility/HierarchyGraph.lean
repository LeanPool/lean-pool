/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/HierarchyGraph.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.ConstructibleStages
public import LeanPool.TuringConeRigidity.Syntax.SentenceSupportFormula

/-!
# Hierarchy Graph
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

/-- The stage base `s` together with all members of hierarchy values at predecessor indices in
`x`. -/
def StageStep (s f r x A : ZFSet.{u}) : Prop :=
  s ⊆ A ∧
  (∀ z ∈ A, z ∈ s ∨ ∃ y ∈ x, ∃ w ∈ r, ZFSet.pair y w ∈ f ∧ z ∈ w) ∧
  ∀ y ∈ x, ∀ w ∈ r, ZFSet.pair y w ∈ f → w ⊆ A

/-- A function graph on a transitive domain whose values are the definable powers of the
prescribed stage bases. -/
def HierarchyGraph (M s d r f : ZFSet.{u}) : Prop :=
  Transitive d ∧ FunctionGraph d r f ∧
  ∀ x ∈ d, ∀ v ∈ r, ZFSet.pair x v ∈ f →
    ∃ A ∈ M, StageStep s f r x A ∧ v = definablePower A

theorem HierarchyGraph.correct {M R d r f : ZFSet.{u}}
    (h : HierarchyGraph M (seed R) d r f) (x : ZFSet.{u}) (hx : x ∈ d)
    (v : ZFSet.{u}) (hv : v ∈ r) (hfv : ZFSet.pair x v ∈ f) :
    v = definablePower (stage R x) := by
  induction x using ZFSet.inductionOn generalizing v with
  | h x ih =>
    obtain ⟨A,_,hs,rfl⟩ := h.2.2 x hx v hv hfv
    congr 1
    apply ZFSet.ext; intro z
    rw [mem_stage]
    constructor
    · intro hz
      rcases hs.2.1 z hz with hz|⟨y,hy,w,hw,hfw,hz⟩
      · exact Or.inl hz
      · rw [ih y hy (h.1 x hx y hy) w hw hfw] at hz
        exact Or.inr ⟨y,hy,hz⟩
    · rintro (hz|⟨y,hy,hz⟩)
      · exact hs.1 hz
      · obtain ⟨w,hw,hfw,_⟩ := h.2.1.2 y (h.1 x hx y hy)
        rw [← ih y hy (h.1 x hx y hy) w hw hfw] at hz
        exact hs.2.2 y hy w hw hfw hz

theorem HierarchyGraph.mem_iff {M R d r f : ZFSet.{u}}
    (h : HierarchyGraph M (seed R) d r f) (z : ZFSet.{u}) :
    z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (definablePower (stage R x)) := by
  constructor
  · intro hz
    obtain ⟨x,hx,v,hv,rfl⟩ := h.2.1.1 z hz
    exact ⟨x,hx,by rw [h.correct x hx v hv hz]⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨v,hv,hfv,_⟩ := h.2.1.2 x hx
    rw [← h.correct x hx v hv hfv]
    exact hfv

theorem HierarchyGraph.unique {M N R d r t f g : ZFSet.{u}}
    (hf : HierarchyGraph M (seed R) d r f) (hg : HierarchyGraph N (seed R) d t g) : f = g := by
  apply ZFSet.ext; intro z
  exact (hf.mem_iff z).trans (hg.mem_iff z).symm

/-- Union the seed with the members of hierarchy values at indices in `x`. -/
noncomputable def stageImage (s x f : ZFSet.{u}) : ZFSet.{u} :=
  s ∪ (ZFSet.sUnion (iterUnion 2 f)).sep
    (fun z => ∃ y ∈ x, ∃ w ∈ iterUnion 2 f, ZFSet.pair y w ∈ f ∧ z ∈ w)

theorem mem_stageImage (s x f z : ZFSet.{u}) :
    z ∈ stageImage s x f ↔ z ∈ s ∨ ∃ y ∈ x, ∃ w, ZFSet.pair y w ∈ f ∧ z ∈ w := by
  rw [stageImage,ZFSet.mem_union,ZFSet.mem_sep]
  apply or_congr_right
  constructor
  · rintro ⟨_,y,hy,w,_,hf,hz⟩; exact ⟨y,hy,w,hf,hz⟩
  · rintro ⟨y,hy,w,hf,hz⟩
    have hw := second_mem_doubleUnion hf
    exact ⟨ZFSet.mem_sUnion.mpr ⟨w,hw,hz⟩,y,hy,w,hw,hf,hz⟩

theorem stageImage_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {s x f : ZFSet.{u}} (hs : s ∈ M) (hx : x ∈ M) (hf : f ∈ M) : stageImage s x f ∈ M := by
  let C : Context M :=
    ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  have hr := iterUnion_mem M hM hT.union hf 2
  have hd := (((defPairMem C 1 0 4).and (member_definable C 2 0)).existsMem 4).existsMem 1
  let e := cons x (cons f (fun _ => iterUnion 2 f))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|i
    · exact hx
    · exact hf
    · exact hr
  exact binary_union_mem M hM hT.pairing hT.union hs
    (hd.sep_mem C e he (union_mem M hM hT.union hr))

theorem hierarchyGraph_of_mem_iff (M R d f : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hs : seed R ∈ M) (hdM : d ∈ M) (hfM : f ∈ M) (hd : Transitive d)
    (hf : ∀ z, z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (definablePower (stage R x))) :
    HierarchyGraph M (seed R) d (iterUnion 2 f) f := by
  have hpair (x v : ZFSet.{u}) : ZFSet.pair x v ∈ f ↔ x ∈ d ∧ v = definablePower (stage R x) := by
    rw [hf]
    constructor
    · rintro ⟨y,hy,he⟩
      obtain ⟨rfl,hv⟩ := ZFSet.pair_inj.mp he
      exact ⟨hy,hv⟩
    · rintro ⟨hx,rfl⟩; exact ⟨x,hx,rfl⟩
  refine ⟨hd,⟨?_,?_⟩,?_⟩
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := (hf z).mp hz
    exact ⟨x,hx,_,second_mem_doubleUnion hz,rfl⟩
  · intro x hx
    have hp := (hpair x _).mpr ⟨hx,rfl⟩
    exact ⟨_,second_mem_doubleUnion hp,hp,fun v _ hv => (hpair x v).mp hv |>.2⟩
  · intro x hx v _ hv
    have he := (hpair x v).mp hv |>.2
    subst v
    have hA : stageImage (seed R) x f = stage R x := by
      apply ZFSet.ext; intro z
      rw [mem_stageImage,mem_stage]
      apply or_congr_right
      constructor
      · rintro ⟨y,hy,w,hw,hz⟩
        rw [(hpair y w).mp hw |>.2] at hz
        exact ⟨y,hy,hz⟩
      · rintro ⟨y,hy,hz⟩
        exact ⟨y,hy,_,(hpair y _).mpr ⟨hd x hx y hy,rfl⟩,hz⟩
    refine ⟨stage R x,hA ▸ stageImage_mem M hM hT hs (hM d hdM x hx) hfM,?_,rfl⟩
    refine ⟨seed_subset_stage R x,?_,?_⟩
    · intro z hz
      rcases (mem_stage R x z).mp hz with hz|⟨y,hy,hz⟩
      · exact Or.inl hz
      · have hp := (hpair y _).mpr ⟨hd x hx y hy,rfl⟩
        exact Or.inr ⟨y,hy,_,second_mem_doubleUnion hp,hp,hz⟩
    · intro y hy w _ hw
      rw [(hpair y w).mp hw |>.2]
      exact definablePower_subset_stage R hy

end TuringRigidity.RelativeConstructible

end OAI
