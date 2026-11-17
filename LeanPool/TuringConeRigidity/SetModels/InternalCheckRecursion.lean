/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalCheckRecursion.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
Only certificate collection, graph union, and domain extension are shared through
SetModels/CertifiedGraphAssembly.lean; semantic recursion and value closure remain here.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.CertifiedGraphAssembly
public import LeanPool.TuringConeRigidity.SetModels.InternalHull
public import LeanPool.TuringConeRigidity.Syntax.CheckGraphConstruction

/-!
# Internal Check Recursion
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.TransitiveNameModel
open RecursiveNames BoundedSetTheory
universe u

/-- A sigma formula requesting a hull and a checked-name graph certificate. -/
def checkCertificate : SigmaFormula := .existsSet (.existsSet (.bounded
  (.conj (.isHull 1 3 4 5) (CheckFormula.graph 1 0 2 6))))

theorem realize_checkCertificate (M d q t : ZFSet.{u}) (hM : Transitive M)
    (hS : Separation M) (hdM : d ∈ M) (hqM : q ∈ M) (htM : t ∈ M)
    (hd : Transitive d) (hq : ∀ c, c ∈ q ↔ c ∈ M ∧ c ⊆ d)
    {x f : ZFSet.{u}} (hx : x ∈ d) (hf : f ∈ M) :
    checkCertificate.Realize M (cons f (cons x (cons d (cons q (cons t (fun _ => d)))))) ↔
      ∃ r ∈ M, CheckGraph (hull d q x) r f t := by
  have hxM := hM d hdM x hx
  have matrix (c r : ZFSet.{u}) (hc : c ∈ M) (hr : r ∈ M) :
      (Formula.conj (.isHull 1 3 4 5) (CheckFormula.graph 1 0 2 6)).Realize M
        (cons r (cons c (cons f (cons x (cons d (cons q (cons t (fun _ => d)))))))) ↔
      c = hull d q x ∧ CheckGraph c r f t := by
    have he : ∀ i, (cons r (cons c (cons f (cons x
        (cons d (cons q (cons t (fun _ => d)))))))) i ∈ M := by
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
      rcases i with _ | i
      · exact htM
      exact hdM
    rw [Formula.absolute _ M hM _ he]
    simp only [Formula.Eval,Formula.eval_isHull,CheckFormula.eval_graph,cons_zero,cons_succ]
    exact and_congr (isHull_iff M d q hM hS hdM hqM hd hq hx hc) Iff.rfl
  change (∃ c ∈ M, ∃ r ∈ M, _) ↔ _
  constructor
  · rintro ⟨c,hc,r,hr,h⟩
    obtain ⟨rfl,hg⟩ := (matrix c r hc hr).mp h
    exact ⟨r,hr,hg⟩
  · rintro ⟨r,hr,hg⟩
    have hc := hull_mem M d q hM hS hdM hqM hxM
    exact ⟨_,hc,r,hr,(matrix _ r hc hr).mpr ⟨rfl,hg⟩⟩

theorem internal_checkGraph (M d q t : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M)
    (hdM : d ∈ M) (hqM : q ∈ M) (htM : t ∈ M) (hd : Transitive d)
    (hq : ∀ c, c ∈ q ↔ c ∈ M ∧ c ⊆ d) (x : ZFSet.{u}) (hx : x ∈ d) :
    ∃ f ∈ M, CheckGraph (hull d q x) (iterUnion 2 f) f t := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    have hxM := hM d hdM x hx
    let e := cons d (cons q (cons t (fun _ => d)))
    have he : ∀ i, e i ∈ M := by
      intro i
      rcases i with _ | i
      · exact hdM
      rcases i with _ | i
      · exact hqM
      rcases i with _ | i
      · exact htM
      exact hdM
    have cert (y f : ZFSet.{u}) (hy : y ∈ x) (hf : f ∈ M) :
        checkCertificate.Realize M (cons f (cons y e)) ↔
          ∃ r ∈ M, CheckGraph (hull d q y) r f t :=
      realize_checkCertificate M d q t hM hS hdM hqM htM hd hq (hd x hx y hy) hf
    obtain ⟨g,hgM,hg⟩ := CertifiedGraphAssembly.certified_union M (x)
      hM hU hR hxM checkCertificate e he
      (fun y f => ∃ r ∈ M, CheckGraph (hull d q y) r f t)
      (fun y z => ∃ w ∈ (hull d q) y, z = ZFSet.pair w ((checkedCode t) w))
      (fun y hy f hf => cert y f hy hf) (by
        intro y hy
        obtain ⟨f,hf,hfg⟩ := ih y hy (hd x hx y hy)
        exact ⟨f,hf,_,iterUnion_mem M hM hU hf 2,hfg⟩) (by
        intro _ _ f g hf hg
        obtain ⟨_,_,hf⟩ := hf
        obtain ⟨_,_,hg⟩ := hg
        exact hf.unique hg) (by
        intro _ _ _ hf z
        obtain ⟨_,_,hf⟩ := hf
        exact hf.mem_iff z)
    have hvalue : taggedImage x g t = checkedCode t x := by
      apply ZFSet.ext
      intro z
      rw [mem_taggedImage,mem_checkedCode]
      constructor
      · rintro ⟨y,hy,w,hw,hz⟩
        obtain ⟨a,_,v,_,hp⟩ := (hg _).mp hw
        obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
        exact ⟨y,hy,hz⟩
      · rintro ⟨y,hy,hz⟩
        exact ⟨y,hy,_,(hg _).mpr
          ⟨y,hy,y,self_mem_hull d q (hd x hx y hy),rfl⟩,hz⟩
    have hvM : checkedCode t x ∈ M := hvalue ▸
      taggedImage_mem M hM hP hU hPow hS hxM hgM htM
    let f := g ∪ ({ZFSet.pair x (checkedCode t x)} : ZFSet.{u})
    have hfM : f ∈ M := binary_union_mem M hM hP hU hgM
      (singleton_mem M hM hP (orderedPair_mem M hM hP hxM hvM))
    refine ⟨f,hfM,checkGraph_of_mem_iff _ f t (hull_transitive d q x hd) ?_⟩
    exact CertifiedGraphAssembly.singleton_graph_extension (x) x
      (hull d q) (checkedCode t) (hull d q x) g
      (hull_unfold M d q hM hP hU hS hR hdM hqM hd hq hx) hg

theorem checkedCode_mem_of_container (M d t : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M)
    (hdM : d ∈ M) (htM : t ∈ M) (hd : Transitive d)
    {x : ZFSet.{u}} (hx : x ∈ d) : checkedCode t x ∈ M := by
  obtain ⟨q,hqM,hq⟩ := internal_power M hM hPow hdM
  obtain ⟨f,hf,hfg⟩ := internal_checkGraph M d q t hM hP hU hPow hS hR
    hdM hqM htM hd hq x hx
  obtain ⟨v,hv,hfv,_⟩ := hfg.2.2.1 x (self_mem_hull d q hx)
  rw [←hfg.correct x (self_mem_hull d q hx) v hv hfv]
  exact hM _ (iterUnion_mem M hM hU hf 2) v hv

theorem encoded_check_mem_of_container (M p d : ZFSet.{u}) [Top (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hR : SigmaReplacement M)
    (hpM : p ∈ M) (hdM : d ∈ M) (hd : Transitive d)
    {x : ZFSet.{u}} (hx : x ∈ d) : (Name.check x).encode (label p) ∈ M := by
  rw [encode_check]
  exact checkedCode_mem_of_container M d _ hM hP hU hPow hS hR hdM
    (hM p hpM _ (label_mem p ⊤)) hd hx

end TuringRigidity.TransitiveNameModel

end OAI
