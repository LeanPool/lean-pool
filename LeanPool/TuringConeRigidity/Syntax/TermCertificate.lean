/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/TermCertificate.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.FiniteTerm

/-!
# Term Certificate
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace FiniteTerm

theorem Certificate.union {A B L O K D f g : ZFSet.{u}}
    (hf : Certificate A B L O K D f) (hg : Certificate A B L O K D g) :
    Certificate A B L O K D (f ∪ g) := by
  intro z hz
  rcases ZFSet.mem_union.mp hz with hz|hz
  · obtain ⟨c,hc,v,hv,rfl,hs⟩ := hf z hz
    exact ⟨c,hc,v,hv,rfl,hs.mono (fun _ hx => ZFSet.mem_union.mpr (Or.inl hx))⟩
  · obtain ⟨c,hc,v,hv,rfl,hs⟩ := hg z hz
    exact ⟨c,hc,v,hv,rfl,hs.mono (fun _ hx => ZFSet.mem_union.mpr (Or.inr hx))⟩

theorem Certificate.adjoin {A B L O K D f c v : ZFSet.{u}}
    (hf : Certificate A B L O K D f) (hc : c ∈ K) (hv : v ∈ D)
    (hs : Step A B L O K D (f ∪ ({ZFSet.pair c v} : ZFSet.{u})) c v) :
    Certificate A B L O K D (f ∪ ({ZFSet.pair c v} : ZFSet.{u})) := by
  intro z hz
  rcases ZFSet.mem_union.mp hz with hz|hz
  · obtain ⟨a,ha,x,hx,rfl,hax⟩ := hf z hz
    exact ⟨a,ha,x,hx,rfl,hax.mono (fun _ hx => ZFSet.mem_union.mpr (Or.inl hx))⟩
  · obtain rfl := ZFSet.mem_singleton.mp hz
    exact ⟨c,hc,v,hv,rfl,hs⟩

theorem internal_certificate (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    {A B L O K D : ZFSet.{u}} (hK : K ∈ M) (hD : D ∈ M)
    (hcode : ∀ c v, Eval A B L O D c v → c ∈ K)
    {c v : ZFSet.{u}} (h : Eval A B L O D c v) :
    ∃ f ∈ M, Certificate A B L O K D f ∧ ZFSet.pair c v ∈ f := by
  induction h with
  | @leaf a x ha hx hax =>
    have ev : Eval A B L O D (tag 0 a) x := .leaf ha hx hax
    have hc := hcode _ _ ev
    let f := ({ZFSet.pair (tag 0 a) x} : ZFSet.{u})
    have hf : f ∈ M := singleton_mem M hM hP
      (orderedPair_mem M hM hP (hM K hK _ hc) (hM D hD _ hx))
    refine ⟨f,hf,?_,ZFSet.mem_singleton.mpr rfl⟩
    intro z hz; obtain rfl := ZFSet.mem_singleton.mp hz
    exact ⟨_,hc,x,hx,rfl,Or.inl ⟨a,ha,rfl,hax⟩⟩
  | @app o a x y ho ev hy hoy ih =>
    obtain ⟨f,hf,hfc,hax⟩ := ih
    have hc := hcode _ _ (Eval.app ho ev hy hoy)
    have hroot : ZFSet.pair (tag 1 (ZFSet.pair o a)) y ∈ M :=
      orderedPair_mem M hM hP (hM K hK _ hc) (hM D hD _ hy)
    refine ⟨f ∪ {ZFSet.pair (tag 1 (ZFSet.pair o a)) y},
      binary_union_mem M hM hP hU hf (singleton_mem M hM hP hroot),?_,
      ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_singleton.mpr rfl))⟩
    apply hfc.adjoin hc hy
    exact Or.inr (Or.inl ⟨o,ho,a,hcode _ _ ev,x,ev.value_mem,rfl,
      ZFSet.mem_union.mpr (Or.inl hax),hoy⟩)
  | @pair a b x y eva evb hxy iha ihb =>
    obtain ⟨f,hf,hfc,hax⟩ := iha
    obtain ⟨g,hg,hgc,hby⟩ := ihb
    have hc := hcode _ _ (Eval.pair eva evb hxy)
    have hroot : ZFSet.pair (tag 2 (ZFSet.pair a b)) (ZFSet.pair x y) ∈ M :=
      orderedPair_mem M hM hP (hM K hK _ hc) (hM D hD _ hxy)
    refine ⟨(f ∪ g) ∪ {ZFSet.pair (tag 2 (ZFSet.pair a b)) (ZFSet.pair x y)},
      binary_union_mem M hM hP hU (binary_union_mem M hM hP hU hf hg)
        (singleton_mem M hM hP hroot),?_,
      ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_singleton.mpr rfl))⟩
    apply (hfc.union hgc).adjoin hc hxy
    exact Or.inr (Or.inr ⟨a,hcode _ _ eva,b,hcode _ _ evb,x,eva.value_mem,y,evb.value_mem,rfl,
      ZFSet.mem_union.mpr (Or.inl (ZFSet.mem_union.mpr (Or.inl hax))),
      ZFSet.mem_union.mpr (Or.inl (ZFSet.mem_union.mpr (Or.inr hby))),rfl⟩)

end FiniteTerm
end TuringRigidity.BoundedSetTheory

end OAI
