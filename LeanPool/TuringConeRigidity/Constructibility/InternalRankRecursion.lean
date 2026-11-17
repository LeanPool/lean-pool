/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/InternalRankRecursion.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalHull
public import LeanPool.TuringConeRigidity.OrdinalCodes.RankGraphConstruction

/-!
# Internal Rank Recursion
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.InternalRank
open TransitiveNameModel BoundedSetTheory
universe u

/-- A sigma formula requesting a hull and an internal rank graph certificate. -/
def rankCertificate : SigmaFormula := .existsSet (.existsSet (.bounded
  (.conj (.isHull 1 3 4 5) (Code.graph 1 0 2))))

theorem realize_rankCertificate (M d q : ZFSet.{u}) (hM : Transitive M)
    (hS : Separation M) (hdM : d ∈ M) (hqM : q ∈ M)
    (hd : Transitive d) (hq : ∀ c, c ∈ q ↔ c ∈ M ∧ c ⊆ d)
    {x f : ZFSet.{u}} (hx : x ∈ d) (hf : f ∈ M) :
    rankCertificate.Realize M (cons f (cons x (cons d (cons q (fun _ => d))))) ↔
      ∃ r ∈ M, Graph (hull d q x) r f := by
  have hxM := hM d hdM x hx
  have matrix (c r : ZFSet.{u}) (hc : c ∈ M) (hr : r ∈ M) :
      (Formula.conj (.isHull 1 3 4 5) (Code.graph 1 0 2)).Realize M
        (cons r (cons c (cons f (cons x (cons d (cons q (fun _ => d))))))) ↔
      c = hull d q x ∧ Graph c r f := by
    have he : ∀ i, (cons r (cons c (cons f (cons x
        (cons d (cons q (fun _ => d))))))) i ∈ M := by
      intro i
      rcases i with _ | i
      · exact hr
      rcases i with _ | i
      · exact hc
      rcases i with _ | i
      · exact hf
      rcases i with _ | i
      · exact hxM
      rcases i with _ | i
      · exact hdM
      rcases i with _ | i
      · exact hqM
      exact hdM
    rw [Formula.absolute _ M hM _ he]
    simp only [Formula.Eval,Formula.eval_isHull,Code.eval_graph,cons_zero,cons_succ]
    exact and_congr (isHull_iff M d q hM hS hdM hqM hd hq hx hc) Iff.rfl
  change (∃ c ∈ M, ∃ r ∈ M, _) ↔ _
  constructor
  · rintro ⟨c,hc,r,hr,h⟩
    obtain ⟨rfl,hg⟩ := (matrix c r hc hr).mp h
    exact ⟨r,hr,hg⟩
  · rintro ⟨r,hr,hg⟩
    have hc := hull_mem M d q hM hS hdM hqM hxM
    exact ⟨_,hc,r,hr,(matrix _ r hc hr).mpr ⟨rfl,hg⟩⟩

theorem internal_rankGraph (M d q : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hS : Separation M) (hR : SigmaReplacement M)
    (hdM : d ∈ M) (hqM : q ∈ M) (hd : Transitive d)
    (hq : ∀ c, c ∈ q ↔ c ∈ M ∧ c ⊆ d) (x : ZFSet.{u}) (hx : x ∈ d) :
    ∃ f ∈ M, Graph (hull d q x) (iterUnion 2 f) f := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    have hxM := hM d hdM x hx
    let e := cons d (cons q (fun _ => d))
    have he : ∀ i, e i ∈ M := by
      intro i
      rcases i with _ | i
      · exact hdM
      rcases i with _ | i
      · exact hqM
      exact hdM
    have cert (y f : ZFSet.{u}) (hy : y ∈ x) (hf : f ∈ M) :
        rankCertificate.Realize M (cons f (cons y e)) ↔
          ∃ r ∈ M, Graph (hull d q y) r f :=
      realize_rankCertificate M d q hM hS hdM hqM hd hq (hd x hx y hy) hf
    obtain ⟨b,hb,hbdef⟩ := hR rankCertificate e he x hxM (by
      intro y hy
      obtain ⟨f,hf,hfg⟩ := ih y hy (hd x hx y hy)
      refine ⟨f,hf,(cert y f hy hf).mpr
        ⟨_,iterUnion_mem M hM hU hf 2,hfg⟩,?_⟩
      intro g hg hcg
      obtain ⟨r,_,hgg⟩ := (cert y g hy hg).mp hcg
      exact hgg.unique hfg)
    have hbg (f : ZFSet.{u}) : f ∈ b ↔
        ∃ y ∈ x, ∃ r ∈ M, Graph (hull d q y) r f := by
      constructor
      · intro hf
        have hfM := hM b hb f hf
        obtain ⟨y,hy,hc⟩ := (hbdef f hfM).mp hf
        exact ⟨y,hy,(cert y f hy hfM).mp hc⟩
      · rintro ⟨y,hy,r,hr,hg⟩
        obtain ⟨f',hf',hg'⟩ := ih y hy (hd x hx y hy)
        have heq := hg.unique hg'
        have hfM : f ∈ M := heq ▸ hf'
        exact (hbdef f hfM).mpr ⟨y,hy,(cert y f hy hfM).mpr ⟨r,hr,hg⟩⟩
    let g := ZFSet.sUnion b
    have hgM : g ∈ M := union_mem M hM hU hb
    have hg (z : ZFSet.{u}) : z ∈ g ↔
        ∃ y ∈ x, ∃ w ∈ hull d q y, z = ZFSet.pair w (rankSet w) := by
      constructor
      · intro hz
        obtain ⟨f,hf,hzf⟩ := ZFSet.mem_sUnion.mp hz
        obtain ⟨y,hy,r,_,hfg⟩ := (hbg f).mp hf
        exact ⟨y,hy,(hfg.mem_iff z).mp hzf⟩
      · rintro ⟨y,hy,w,hw,hz⟩
        obtain ⟨f,hf,hfg⟩ := ih y hy (hd x hx y hy)
        exact ZFSet.mem_sUnion.mpr ⟨f,(hbg f).mpr
          ⟨y,hy,_,iterUnion_mem M hM hU hf 2,hfg⟩,(hfg.mem_iff z).mpr ⟨w,hw,hz⟩⟩
    have hvalue : rankImage x g = rankSet x := by
      apply ZFSet.ext
      intro z
      rw [mem_rankImage,mem_rankSet]
      constructor
      · rintro ⟨y,hy,w,hw,hz⟩
        obtain ⟨a,_,v,_,hp⟩ := (hg _).mp hw
        obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
        exact ⟨y,hy,hz⟩
      · rintro ⟨y,hy,hz⟩
        exact ⟨y,hy,_,(hg _).mpr
          ⟨y,hy,y,self_mem_hull d q (hd x hx y hy),rfl⟩,hz⟩
    have hvM : rankSet x ∈ M := hvalue ▸
      rankImage_mem M hM hP hU hS hxM hgM
    let f := g ∪ ({ZFSet.pair x (rankSet x)} : ZFSet.{u})
    have hfM : f ∈ M := binary_union_mem M hM hP hU hgM
      (singleton_mem M hM hP (orderedPair_mem M hM hP hxM hvM))
    refine ⟨f,hfM,graph_of_mem_iff _ f (hull_transitive d q x hd) ?_⟩
    intro z
    change z ∈ g ∪ ({ZFSet.pair x (rankSet x)} : ZFSet.{u}) ↔ _
    rw [ZFSet.mem_union,ZFSet.mem_singleton,hg]
    constructor
    · rintro (⟨y,hy,w,hw,hz⟩|hz)
      · exact ⟨w,(hull_unfold M d q hM hP hU hS hR hdM hqM hd hq hx w).mpr
          (Or.inr ⟨y,hy,hw⟩),hz⟩
      · exact ⟨x,self_mem_hull d q hx,hz⟩
    · rintro ⟨w,hw,hz⟩
      rcases (hull_unfold M d q hM hP hU hS hR hdM hqM hd hq hx w).mp hw with rfl|⟨y,hy,hw⟩
      · exact Or.inr hz
      · exact Or.inl ⟨y,hy,w,hw,hz⟩

theorem rankSet_mem_of_container (M d : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M)
    (hdM : d ∈ M) (hd : Transitive d)
    {x : ZFSet.{u}} (hx : x ∈ d) : rankSet x ∈ M := by
  obtain ⟨q,hqM,hq⟩ := internal_power M hM hPow hdM
  obtain ⟨f,hf,hfg⟩ := internal_rankGraph M d q hM hP hU hS hR
    hdM hqM hd hq x hx
  obtain ⟨v,hv,hfv,_⟩ := hfg.2.2.1 x (self_mem_hull d q hx)
  rw [←hfg.correct x (self_mem_hull d q hx) v hv hfv]
  exact hM _ (iterUnion_mem M hM hU hf 2) v hv

end TuringRigidity.InternalRank

end OAI
