/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/TermFunctionality.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.TermEvaluationGraph

/-!
# Term Functionality
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace FiniteTerm

def Functional (f : ZFSet.{u}) : Prop :=
  ∀ a x y, ZFSet.pair a x ∈ f → ZFSet.pair a y ∈ f → x = y

theorem Eval.unfold (A B L O D c v : ZFSet.{u}) : Eval A B L O D c v ↔
    (∃ a ∈ A, v ∈ D ∧ c = tag 0 a ∧ ZFSet.pair a v ∈ L) ∨
    (∃ o ∈ B, ∃ a x, Eval A B L O D a x ∧ v ∈ D ∧
      c = tag 1 (ZFSet.pair o a) ∧ ZFSet.pair (ZFSet.pair o x) v ∈ O) ∨
    (∃ a b x y, Eval A B L O D a x ∧ Eval A B L O D b y ∧ v ∈ D ∧
      c = tag 2 (ZFSet.pair a b) ∧ v = ZFSet.pair x y) := by
  constructor
  · intro h; cases h with
    | @leaf a x ha hx hax => exact Or.inl ⟨a,ha,hx,rfl,hax⟩
    | @app o c x y ho hx hy hox => exact Or.inr (Or.inl ⟨o,ho,c,x,hx,hy,rfl,hox⟩)
    | @pair a b x y ha hb hxy => exact Or.inr (Or.inr ⟨a,b,x,y,ha,hb,hxy,rfl,rfl⟩)
  · rintro (⟨a,ha,hv,rfl,hav⟩|⟨o,ho,a,x,hax,hv,rfl,hov⟩|⟨a,b,x,y,hax,hby,hv,rfl,rfl⟩)
    · exact .leaf ha hv hav
    · exact .app ho hax hv hov
    · exact .pair hax hby hv

theorem Eval.functional {A B L O D c x y : ZFSet.{u}} (hL : Functional L) (hO : Functional O)
    (hx : Eval A B L O D c x) (hy : Eval A B L O D c y) : x = y := by
  induction hx generalizing y with
  | @leaf a x ha hx hax =>
    rcases (Eval.unfold _ _ _ _ _ _ _).mp hy with h|h|h
    · obtain ⟨a',_,_,he,hav⟩ := h
      obtain ⟨_,rfl⟩ := (tag_inj _ _ _ _).mp he
      exact hL _ _ _ hax hav
    · obtain ⟨o,_,b,v,_,_,he,_⟩ := h
      have hh := ((tag_inj _ _ _ _).mp he).1
      omega
    · obtain ⟨b,c,v,w,_,_,_,he,_⟩ := h
      have hh := ((tag_inj _ _ _ _).mp he).1
      omega
  | @app o a x v ho hax hv hov ih =>
    rcases (Eval.unfold _ _ _ _ _ _ _).mp hy with h|h|h
    · obtain ⟨b,_,_,he,_⟩ := h
      have hh := ((tag_inj _ _ _ _).mp he).1
      omega
    · obtain ⟨o',_,a',x',hax',_,he,hov'⟩ := h
      have hp := ((tag_inj _ _ _ _).mp he).2
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
      obtain rfl := ih hax'
      exact hO _ _ _ hov hov'
    · obtain ⟨b,c,w,z,_,_,_,he,_⟩ := h
      have hh := ((tag_inj _ _ _ _).mp he).1
      omega
  | @pair a b x v hax hbv hxv iha ihb =>
    rcases (Eval.unfold _ _ _ _ _ _ _).mp hy with h|h|h
    · obtain ⟨c,_,_,he,_⟩ := h
      have hh := ((tag_inj _ _ _ _).mp he).1
      omega
    · obtain ⟨o,_,c,w,_,_,he,_⟩ := h
      have hh := ((tag_inj _ _ _ _).mp he).1
      omega
    · obtain ⟨a',b',x',v',hax',hbv',_,he,rfl⟩ := h
      have hp := ((tag_inj _ _ _ _).mp he).2
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
      obtain rfl := iha hax'
      obtain rfl := ihb hbv'
      rfl

theorem evaluation_graph_functional {A B L O D E : ZFSet.{u}}
    (hL : Functional L) (hO : Functional O)
    (hE : ∀ c v, ZFSet.pair c v ∈ E ↔ Eval A B L O D c v) : Functional E :=
  fun c x y hx hy => ((hE c x).mp hx).functional hL hO ((hE c y).mp hy)

end FiniteTerm
end TuringRigidity.BoundedSetTheory

end OAI
