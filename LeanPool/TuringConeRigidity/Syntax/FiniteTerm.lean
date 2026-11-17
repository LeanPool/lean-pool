/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/FiniteTerm.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.FiniteCodeBound
public import Mathlib.SetTheory.ZFC.Rank

/-!
# Finite Term
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace FiniteTerm

noncomputable def tag (n : ℕ) (x : ZFSet.{u}) : ZFSet.{u} := ZFSet.pair (natSet n) x

theorem tag_inj (n m : ℕ) (x y : ZFSet.{u}) : tag n x = tag m y ↔ n = m ∧ x = y := by
  rw [tag,tag,ZFSet.pair_inj]
  exact and_congr ⟨fun h => natSet_injective h,fun h => congrArg natSet h⟩ Iff.rfl

inductive Eval (A B L O D : ZFSet.{u}) : ZFSet.{u} → ZFSet.{u} → Prop
  | leaf {a x : ZFSet.{u}} : a ∈ A → x ∈ D → ZFSet.pair a x ∈ L → Eval A B L O D (tag 0 a) x
  | app {o c x y : ZFSet.{u}} : o ∈ B → Eval A B L O D c x → y ∈ D →
      ZFSet.pair (ZFSet.pair o x) y ∈ O → Eval A B L O D (tag 1 (ZFSet.pair o c)) y
  | pair {a b x y : ZFSet.{u}} : Eval A B L O D a x → Eval A B L O D b y →
      ZFSet.pair x y ∈ D → Eval A B L O D (tag 2 (ZFSet.pair a b)) (ZFSet.pair x y)

theorem Eval.value_mem {A B L O D c x : ZFSet.{u}} (h : Eval A B L O D c x) : x ∈ D := by
  cases h with
  | leaf _ hx _ => exact hx
  | app _ _ hx _ => exact hx
  | pair _ _ hx => exact hx

theorem Eval.code_finite {A B L O D t c x : ZFSet.{u}}
    (hA : A ⊆ t) (hB : B ⊆ t) (hn : ∀ n, natSet.{u} n ∈ t)
    (h : Eval A B L O D c x) : FiniteTuple.FiniteCode t c := by
  induction h with
  | leaf ha _ _ => exact (FiniteTuple.FiniteCode.atom _ (hn 0)).orderedPair (.atom _ (hA ha))
  | app ho _ _ _ ih =>
    exact (FiniteTuple.FiniteCode.atom _ (hn 1)).orderedPair
      ((FiniteTuple.FiniteCode.atom _ (hB ho)).orderedPair ih)
  | pair _ _ _ iha ihb =>
    exact (FiniteTuple.FiniteCode.atom _ (hn 2)).orderedPair (iha.orderedPair ihb)

def Step (A B L O K D f c v : ZFSet.{u}) : Prop :=
  (∃ a ∈ A, c = tag 0 a ∧ ZFSet.pair a v ∈ L) ∨
  (∃ o ∈ B, ∃ a ∈ K, ∃ x ∈ D, c = tag 1 (ZFSet.pair o a) ∧
    ZFSet.pair a x ∈ f ∧ ZFSet.pair (ZFSet.pair o x) v ∈ O) ∨
  (∃ a ∈ K, ∃ b ∈ K, ∃ x ∈ D, ∃ y ∈ D, c = tag 2 (ZFSet.pair a b) ∧
    ZFSet.pair a x ∈ f ∧ ZFSet.pair b y ∈ f ∧ v = ZFSet.pair x y)

def Certificate (A B L O K D f : ZFSet.{u}) : Prop :=
  ∀ z ∈ f, ∃ c ∈ K, ∃ v ∈ D, z = ZFSet.pair c v ∧ Step A B L O K D f c v

theorem Step.mono {A B L O K D f g c v : ZFSet.{u}} (hfg : f ⊆ g)
    (h : Step A B L O K D f c v) : Step A B L O K D g c v := by
  rcases h with h|h|h
  · exact Or.inl h
  · obtain ⟨o,ho,a,ha,x,hx,hc,hax,hox⟩ := h
    exact Or.inr (Or.inl ⟨o,ho,a,ha,x,hx,hc,hfg hax,hox⟩)
  · obtain ⟨a,ha,b,hb,x,hx,y,hy,hc,hax,hby,hv⟩ := h
    exact Or.inr (Or.inr ⟨a,ha,b,hb,x,hx,y,hy,hc,hfg hax,hfg hby,hv⟩)

theorem Certificate.subset {A B L O K D f : ZFSet.{u}} (hf : Certificate A B L O K D f) :
    f ⊆ ZFSet.prod K D := by
  intro z hz
  obtain ⟨c,hc,v,hv,hz,_⟩ := hf z hz
  exact ZFSet.mem_prod.mpr ⟨c,hc,v,hv,hz⟩

theorem Certificate.step {A B L O K D f c v : ZFSet.{u}}
    (hf : Certificate A B L O K D f) (hp : ZFSet.pair c v ∈ f) :
    c ∈ K ∧ v ∈ D ∧ Step A B L O K D f c v := by
  obtain ⟨c',hc,v',hv,he,hs⟩ := hf _ hp
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
  exact ⟨hc,hv,hs⟩

theorem pair_rank_left (x y : ZFSet.{u}) : ZFSet.rank x < ZFSet.rank (ZFSet.pair x y) := by
  have ha : x ∈ ({x,y} : ZFSet.{u}) := ZFSet.mem_pair.mpr (Or.inl rfl)
  have hb : ({x,y} : ZFSet.{u}) ∈ ZFSet.pair x y := ZFSet.mem_pair.mpr (Or.inr rfl)
  exact (ZFSet.rank_lt_of_mem ha).trans (ZFSet.rank_lt_of_mem hb)

theorem pair_rank_right (x y : ZFSet.{u}) : ZFSet.rank y < ZFSet.rank (ZFSet.pair x y) := by
  have ha : y ∈ ({x,y} : ZFSet.{u}) := ZFSet.mem_pair.mpr (Or.inr rfl)
  have hb : ({x,y} : ZFSet.{u}) ∈ ZFSet.pair x y := ZFSet.mem_pair.mpr (Or.inr rfl)
  exact (ZFSet.rank_lt_of_mem ha).trans (ZFSet.rank_lt_of_mem hb)

theorem Certificate.sound {A B L O K D f : ZFSet.{u}}
    (hf : Certificate A B L O K D f) (c v : ZFSet.{u})
    (hp : ZFSet.pair c v ∈ f) : Eval A B L O D c v := by
  have wf : WellFounded (fun a b : ZFSet.{u} => ZFSet.rank a < ZFSet.rank b) :=
    InvImage.wf ZFSet.rank Ordinal.lt_wf
  induction c using wf.induction generalizing v with
  | h c ih =>
    have hv := (hf.step hp).2.1
    rcases (hf.step hp).2.2 with h|h|h
    · obtain ⟨a,ha,rfl,hav⟩ := h
      exact .leaf ha hv hav
    · obtain ⟨o,ho,a,_,x,_,rfl,hax,hov⟩ := h
      have hlt := (pair_rank_right o a).trans (pair_rank_right (natSet 1) (ZFSet.pair o a))
      exact .app ho (ih a hlt x hax) hv hov
    · obtain ⟨a,_,b,_,x,_,y,_,rfl,hax,hby,rfl⟩ := h
      have ha := (pair_rank_left a b).trans (pair_rank_right (natSet 2) (ZFSet.pair a b))
      have hb := (pair_rank_right a b).trans (pair_rank_right (natSet 2) (ZFSet.pair a b))
      exact .pair (ih a ha x hax) (ih b hb y hby) hv

end FiniteTerm
end TuringRigidity.BoundedSetTheory

end OAI
