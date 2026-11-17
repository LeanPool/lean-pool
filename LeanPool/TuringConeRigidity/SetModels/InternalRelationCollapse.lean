/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalRelationCollapse.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.RelationCollapse

/-!
# Internal Relation Collapse
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory
universe u

noncomputable def nextValue (d r x f : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ y ∈ d, ZFSet.pair y x ∈ r ∧ ZFSet.pair y z ∈ f) (iterUnion 2 f)

theorem mem_nextValue (d r x f z : ZFSet.{u}) :
    z ∈ nextValue d r x f ↔ ∃ y ∈ d, ZFSet.pair y x ∈ r ∧ ZFSet.pair y z ∈ f := by
  rw [nextValue,ZFSet.mem_sep]
  constructor
  · exact And.right
  · intro h
    obtain ⟨y,hy,hyx,hyz⟩ := h
    exact ⟨second_mem_doubleUnion hyz,y,hy,hyx,hyz⟩

def nextFormula : Formula := .existsMem 1 (.conj (.pairMem 0 3 4) (.pairMem 0 1 5))

theorem nextValue_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hU : BoundedSetTheory.Union M) (hS : Separation M)
    {d r x f : ZFSet.{u}} (hd : d ∈ M) (hr : r ∈ M) (hx : x ∈ M) (hf : f ∈ M) :
    nextValue d r x f ∈ M := by
  let e := cons d (cons x (cons r (cons f (fun _ => d))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hd
    rcases i with _ | i
    · exact hx
    rcases i with _ | i
    · exact hr
    rcases i with _ | i
    · exact hf
    exact hd
  simpa only [nextFormula,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e,nextValue] using
    sep_mem M hM hS nextFormula e he (iterUnion_mem M hM hU hf 2)

def certificate : SigmaFormula := .existsSet (.existsSet (.bounded
  (.conj (RelationHull.Code.isHull 1 3 4 5 6) (Code.graph 5 6 1 0 2))))

theorem realize_certificate (M d r q : ZFSet.{u}) (hM : Transitive M)
    (hS : Separation M) (hd : d ∈ M) (hr : r ∈ M) (hqM : q ∈ M)
    (hq : ∀ a, a ∈ q ↔ a ∈ M ∧ a ⊆ d)
    {x f : ZFSet.{u}} (hx : x ∈ d) (hf : f ∈ M) :
    certificate.Realize M (cons f (cons x (cons q (cons d (cons r (fun _ => d)))))) ↔
      ∃ b ∈ M, Graph d r (RelationHull.hull d r q x) b f := by
  have hxM := hM d hd x hx
  have matrix (a b : ZFSet.{u}) (ha : a ∈ M) (hb : b ∈ M) :
      (Formula.conj (RelationHull.Code.isHull 1 3 4 5 6) (Code.graph 5 6 1 0 2)).Realize M
        (cons b (cons a (cons f (cons x (cons q (cons d (cons r (fun _ => d)))))))) ↔
      a = RelationHull.hull d r q x ∧ Graph d r a b f := by
    rw [Formula.absolute _ M hM _ (by
      intro i
      rcases i with _ | i
      · exact hb
      rcases i with _ | i
      · exact ha
      rcases i with _ | i
      · exact hf
      rcases i with _ | i
      · exact hxM
      rcases i with _ | i
      · exact hqM
      rcases i with _ | i
      · exact hd
      rcases i with _ | i
      · exact hr
      exact hd)]
    simp only [Formula.Eval,RelationHull.Code.eval_isHull,Code.eval_graph,cons_zero,cons_succ]
    exact and_congr (RelationHull.isHull_iff M d r q hM hS hd hr hqM hq hx) Iff.rfl
  change (∃ a ∈ M, ∃ b ∈ M, _) ↔ _
  constructor
  · rintro ⟨a,ha,b,hb,h⟩
    obtain ⟨rfl,hg⟩ := (matrix a b ha hb).mp h
    exact ⟨b,hb,hg⟩
  · rintro ⟨b,hb,hg⟩
    have ha := RelationHull.hull_mem M d r q hM hS hd hr hqM hxM
    exact ⟨_,ha,b,hb,(matrix _ b ha hb).mpr ⟨rfl,hg⟩⟩

theorem internal_hull_graph (M d r q : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hS : Separation M) (hR : SigmaReplacement M)
    (hd : d ∈ M) (hr : r ∈ M) (hqM : q ∈ M)
    (hq : ∀ a, a ∈ q ↔ a ∈ M ∧ a ⊆ d)
    (wf : WellFounded (Rel d r)) (x : ZFSet.{u}) (hx : x ∈ d) :
    ∃ f ∈ M, Graph d r (RelationHull.hull d r q x) (iterUnion 2 f) f := by
  induction x using wf.induction with
  | h x ih =>
    have hxM := hM d hd x hx
    let e := cons q (cons d (cons r (fun _ => d)))
    have he : ∀ i, e i ∈ M := by
      intro i
      rcases i with _ | i
      · exact hqM
      rcases i with _ | i
      · exact hd
      rcases i with _ | i
      · exact hr
      exact hd
    have cert (y f : ZFSet.{u}) (hy : y ∈ RelationHull.predecessors d r x) (hf : f ∈ M) :
        certificate.Realize M (cons f (cons y e)) ↔
          ∃ b ∈ M, Graph d r (RelationHull.hull d r q y) b f :=
      realize_certificate M d r q hM hS hd hr hqM hq
        ((RelationHull.mem_predecessors _ _ _ _).mp hy).1 hf
    have predM := RelationHull.predecessors_mem M hM hS hd hr hxM
    obtain ⟨B,hB,hBdef⟩ := hR certificate e he _ predM (by
      intro y hy
      have hyr := (RelationHull.mem_predecessors _ _ _ _).mp hy
      obtain ⟨f,hf,hfg⟩ := ih y hyr hyr.1
      refine ⟨f,hf,(cert y f hy hf).mpr ⟨_,iterUnion_mem M hM hU hf 2,hfg⟩,?_⟩
      intro g hg hcg
      obtain ⟨b,_,hgg⟩ := (cert y g hy hg).mp hcg
      exact hgg.unique wf hfg)
    have hBg (f : ZFSet.{u}) : f ∈ B ↔
        ∃ y ∈ RelationHull.predecessors d r x, ∃ b ∈ M,
          Graph d r (RelationHull.hull d r q y) b f := by
      constructor
      · intro hf
        have hfM := hM B hB f hf
        obtain ⟨y,hy,hc⟩ := (hBdef f hfM).mp hf
        exact ⟨y,hy,(cert y f hy hfM).mp hc⟩
      · rintro ⟨y,hy,b,hb,hg⟩
        have hyr := (RelationHull.mem_predecessors _ _ _ _).mp hy
        obtain ⟨f',hf',hg'⟩ := ih y hyr hyr.1
        have hfM : f ∈ M := hg.unique wf hg' ▸ hf'
        exact (hBdef f hfM).mpr ⟨y,hy,(cert y f hy hfM).mpr ⟨b,hb,hg⟩⟩
    let g := ZFSet.sUnion B
    have hgM : g ∈ M := union_mem M hM hU hB
    have hg (z : ZFSet.{u}) : z ∈ g ↔
        ∃ y ∈ RelationHull.predecessors d r x, ∃ w ∈ RelationHull.hull d r q y,
          z = ZFSet.pair w (value d r wf w) := by
      constructor
      · intro hz
        obtain ⟨f,hf,hzf⟩ := ZFSet.mem_sUnion.mp hz
        obtain ⟨y,hy,b,_,hfg⟩ := (hBg f).mp hf
        exact ⟨y,hy,(hfg.mem_iff wf z).mp hzf⟩
      · rintro ⟨y,hy,w,hw,hz⟩
        have hyr := (RelationHull.mem_predecessors _ _ _ _).mp hy
        obtain ⟨f,hf,hfg⟩ := ih y hyr hyr.1
        exact ZFSet.mem_sUnion.mpr ⟨f,(hBg f).mpr
          ⟨y,hy,_,iterUnion_mem M hM hU hf 2,hfg⟩,(hfg.mem_iff wf z).mpr ⟨w,hw,hz⟩⟩
    have hvalue : nextValue d r x g = value d r wf x := by
      apply ZFSet.ext
      intro z
      rw [mem_nextValue,mem_value]
      constructor
      · rintro ⟨y,hyd,hyx,hyz⟩
        obtain ⟨a,_,w,_,heq⟩ := (hg _).mp hyz
        obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp heq
        exact ⟨y,hyd,hyx,rfl⟩
      · rintro ⟨y,hyd,hyx,rfl⟩
        exact ⟨y,hyd,hyx,(hg _).mpr
          ⟨y,(RelationHull.mem_predecessors _ _ _ _).mpr ⟨hyd,hyx⟩,
            y,RelationHull.self_mem d r q hyd,rfl⟩⟩
    have hvM : value d r wf x ∈ M := hvalue ▸ nextValue_mem M hM hU hS hd hr hxM hgM
    let f := g ∪ ({ZFSet.pair x (value d r wf x)} : ZFSet.{u})
    have hfM : f ∈ M := binary_union_mem M hM hP hU hgM
      (singleton_mem M hM hP (orderedPair_mem M hM hP hxM hvM))
    refine ⟨f,hfM,graph_of_mem_iff d r _ f wf (RelationHull.hull_subset d r q x)
      (RelationHull.hull_closed d r q x) ?_⟩
    intro z
    change z ∈ g ∪ ({ZFSet.pair x (value d r wf x)} : ZFSet.{u}) ↔ _
    rw [ZFSet.mem_union,ZFSet.mem_singleton,hg]
    constructor
    · rintro (⟨y,hy,w,hw,hz⟩|hz)
      · exact ⟨w,(RelationHull.hull_unfold M d r q hM hP hU hS hR hd hr hqM hq hx w).mpr
          (Or.inr ⟨y,hy,hw⟩),hz⟩
      · exact ⟨x,RelationHull.self_mem d r q hx,hz⟩
    · rintro ⟨w,hw,hz⟩
      rcases (RelationHull.hull_unfold M d r q hM hP hU hS hR hd hr hqM hq hx w).mp hw with
        rfl|⟨y,hy,hw⟩
      · exact Or.inr hz
      · exact Or.inl ⟨y,hy,w,hw,hz⟩

end TuringRigidity.RelationCollapse

end OAI
