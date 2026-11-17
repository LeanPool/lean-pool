/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/RelationHull.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalHull

/-!
# Relation Hull
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelationHull
open TransitiveNameModel BoundedSetTheory
universe u

def Closed (d r b : ZFSet.{u}) : Prop :=
  ∀ x ∈ b, ∀ y ∈ d, ZFSet.pair y x ∈ r → y ∈ b

namespace Code
open Formula

def closed (d r b : ℕ) : Formula :=
  allMem b (allMem (d+1) (imp (pairMem 0 1 (r+2)) (.member 0 (b+2))))

theorem eval_closed (d r b : ℕ) (e : ℕ → ZFSet.{u}) :
    (closed d r b).Eval e ↔ Closed (e d) (e r) (e b) := by
  simp only [closed,Closed,eval_allMem,eval_imp,eval_pairMem,Formula.Eval,cons_zero,cons_succ]

def member : Formula := allMem 2
  (imp (.conj (closed 4 5 0) (.member 2 0)) (.member 1 0))

theorem eval_member (z x q d r : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    member.Eval (cons z (cons x (cons q (cons d (cons r e))))) ↔
      ∀ b ∈ q, Closed d r b → x ∈ b → z ∈ b := by
  simp only [member,eval_allMem,eval_imp,Formula.Eval,eval_closed,cons_zero,cons_succ]
  exact forall_congr' (fun b => forall_congr' (fun _ => and_imp))

def isHull (b x q d r : ℕ) : Formula :=
  .conj (.member b q) (.conj (closed d r b) (.conj (.member x b)
    (allMem q (imp (.conj (closed (d+1) (r+1) 0) (.member (x+1) 0)) (subset (b+1) 0)))))

theorem eval_isHull (b x q d r : ℕ) (e : ℕ → ZFSet.{u}) :
    (isHull b x q d r).Eval e ↔ e b ∈ e q ∧ Closed (e d) (e r) (e b) ∧ e x ∈ e b ∧
      ∀ a ∈ e q, Closed (e d) (e r) a → e x ∈ a → e b ⊆ a := by
  simp only [isHull,Formula.Eval,eval_closed,eval_allMem,eval_imp,eval_subset,cons_zero,cons_succ]
  simp only [and_imp]
end Code

noncomputable def hull (d r q x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∀ b ∈ q, Closed d r b → x ∈ b → z ∈ b) d

theorem mem_hull (d r q x z : ZFSet.{u}) :
    z ∈ hull d r q x ↔ z ∈ d ∧ ∀ b ∈ q, Closed d r b → x ∈ b → z ∈ b := ZFSet.mem_sep

theorem hull_subset (d r q x : ZFSet.{u}) : hull d r q x ⊆ d :=
  fun _ h => (mem_hull _ _ _ _ _).mp h |>.1

theorem self_mem (d r q : ZFSet.{u}) {x : ZFSet.{u}} (hx : x ∈ d) :
    x ∈ hull d r q x := (mem_hull _ _ _ _ _).mpr ⟨hx,fun _ _ _ h => h⟩

theorem hull_closed (d r q x : ZFSet.{u}) : Closed d r (hull d r q x) := by
  intro y hy z hz hzy
  exact (mem_hull _ _ _ _ _).mpr ⟨hz,fun b hb hbc hxb =>
    hbc y (((mem_hull _ _ _ _ _).mp hy).2 b hb hbc hxb) z hz hzy⟩

theorem hull_least (d r q x b : ZFSet.{u}) (hb : b ∈ q)
    (hc : Closed d r b) (hx : x ∈ b) : hull d r q x ⊆ b :=
  fun _ hz => (mem_hull _ _ _ _ _).mp hz |>.2 b hb hc hx

theorem hull_mem (M d r q : ZFSet.{u}) (hM : Transitive M) (hS : Separation M)
    (hd : d ∈ M) (hr : r ∈ M) (hq : q ∈ M) {x : ZFSet.{u}} (hx : x ∈ M) :
    hull d r q x ∈ M := by
  let e := cons x (cons q (cons d (cons r (fun _ => r))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hx
    rcases i with _ | i
    · exact hq
    rcases i with _ | i
    · exact hd
    cases i <;> exact hr
  have hs := sep_mem M hM hS Code.member e he hd
  have eq : ZFSet.sep (fun z => Code.member.Eval (cons z e)) d = hull d r q x := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep,mem_hull]
    apply and_congr Iff.rfl
    simpa only [e,cons] using Code.eval_member z x q d r (fun _ => r)
  exact eq ▸ hs

theorem isHull_iff (M d r q : ZFSet.{u}) (hM : Transitive M) (hS : Separation M)
    (hd : d ∈ M) (hr : r ∈ M) (hqM : q ∈ M)
    (hq : ∀ b, b ∈ q ↔ b ∈ M ∧ b ⊆ d) {x b : ZFSet.{u}} (hx : x ∈ d) :
    (b ∈ q ∧ Closed d r b ∧ x ∈ b ∧
      ∀ a ∈ q, Closed d r a → x ∈ a → b ⊆ a) ↔ b = hull d r q x := by
  have hh := hull_mem M d r q hM hS hd hr hqM (hM d hd x hx)
  have hhq := (hq _).mpr ⟨hh,hull_subset d r q x⟩
  constructor
  · rintro ⟨hb,hc,hxb,hmin⟩
    apply ZFSet.ext
    intro z
    exact ⟨fun hz => hmin _ hhq (hull_closed d r q x) (self_mem d r q hx) hz,
      fun hz => hull_least d r q x b hb hc hxb hz⟩
  · rintro rfl
    exact ⟨hhq,hull_closed d r q x,self_mem d r q hx,
      fun a ha hc hx => hull_least d r q x a ha hc hx⟩

noncomputable def predecessors (d r x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun y => ZFSet.pair y x ∈ r) d

theorem mem_predecessors (d r x y : ZFSet.{u}) :
    y ∈ predecessors d r x ↔ y ∈ d ∧ ZFSet.pair y x ∈ r := ZFSet.mem_sep

theorem predecessors_mem (M : ZFSet.{u}) (hM : Transitive M) (hS : Separation M)
    {d r x : ZFSet.{u}} (hd : d ∈ M) (hr : r ∈ M) (hx : x ∈ M) :
    predecessors d r x ∈ M := by
  simpa only [Formula.eval_pairMem,cons_zero,cons_succ,predecessors] using
    sep_mem M hM hS (.pairMem 0 1 2) (cons x (fun _ => r))
    (by intro i; cases i <;> assumption) hd

theorem collect_hulls (M d r q : ZFSet.{u}) (hM : Transitive M)
    (hS : Separation M) (hR : SigmaReplacement M)
    (hd : d ∈ M) (hr : r ∈ M) (hqM : q ∈ M)
    (hq : ∀ b, b ∈ q ↔ b ∈ M ∧ b ⊆ d) {x : ZFSet.{u}} (hx : x ∈ d) :
    ∃ b ∈ M, ∀ z, z ∈ b ↔ ∃ y ∈ predecessors d r x, hull d r q y = z := by
  let e := cons q (cons d (fun _ => r))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hqM
    rcases i with _ | i
    · exact hd
    exact hr
  apply replacement_image M hM hR (.bounded (Code.isHull 0 1 2 3 4)) e he
    (predecessors_mem M hM hS hd hr (hM d hd x hx)) (hull d r q)
  · intro y hy
    exact hull_mem M d r q hM hS hd hr hqM (hM d hd y ((mem_predecessors _ _ _ _).mp hy).1)
  · intro y hy b hb
    change (Code.isHull 0 1 2 3 4).Realize M (cons b (cons y e)) ↔ _
    rw [Formula.absolute _ M hM _ (by
      intro i
      rcases i with _ | i
      · exact hb
      rcases i with _ | i
      · exact hM d hd y ((mem_predecessors _ _ _ _).mp hy).1
      exact he i),Code.eval_isHull]
    exact isHull_iff M d r q hM hS hd hr hqM hq ((mem_predecessors _ _ _ _).mp hy).1

theorem hull_unfold (M d r q : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hS : Separation M) (hR : SigmaReplacement M)
    (hd : d ∈ M) (hr : r ∈ M) (hqM : q ∈ M)
    (hq : ∀ b, b ∈ q ↔ b ∈ M ∧ b ⊆ d) {x : ZFSet.{u}} (hx : x ∈ d) (z : ZFSet.{u}) :
    z ∈ hull d r q x ↔ z = x ∨ ∃ y ∈ predecessors d r x, z ∈ hull d r q y := by
  obtain ⟨b,hb,hbdef⟩ := collect_hulls M d r q hM hS hR hd hr hqM hq hx
  let a := ({x} : ZFSet.{u}) ∪ ZFSet.sUnion b
  have ha : a ∈ M := binary_union_mem M hM hP hU
    (singleton_mem M hM hP (hM d hd x hx)) (union_mem M hM hU hb)
  have ha_def (w : ZFSet.{u}) : w ∈ a ↔ w = x ∨ ∃ y ∈ predecessors d r x, w ∈ hull d r q y := by
    simp only [a,ZFSet.mem_union,ZFSet.mem_singleton,ZFSet.mem_sUnion]
    constructor
    · rintro (h|⟨v,hv,hw⟩)
      · exact Or.inl h
      · obtain ⟨y,hy,rfl⟩ := (hbdef v).mp hv
        exact Or.inr ⟨y,hy,hw⟩
    · rintro (h|⟨y,hy,hw⟩)
      · exact Or.inl h
      · exact Or.inr ⟨_,(hbdef _).mpr ⟨y,hy,rfl⟩,hw⟩
  have had : a ⊆ d := by
    intro w hw
    rcases (ha_def w).mp hw with rfl|⟨y,_,hw⟩
    · exact hx
    · exact hull_subset d r q y hw
  have hac : Closed d r a := by
    intro w hw v hv hvw
    apply (ha_def v).mpr
    rcases (ha_def w).mp hw with rfl|⟨y,hy,hw⟩
    · exact Or.inr ⟨v,(mem_predecessors _ _ _ _).mpr ⟨hv,hvw⟩,self_mem d r q hv⟩
    · exact Or.inr ⟨y,hy,hull_closed d r q y w hw v hv hvw⟩
  have hhq := (hq _).mpr ⟨hull_mem M d r q hM hS hd hr hqM (hM d hd x hx),hull_subset d r q x⟩
  constructor
  · intro hz
    exact (ha_def z).mp (hull_least d r q x a ((hq a).mpr ⟨ha,had⟩) hac
      ((ha_def x).mpr (Or.inl rfl)) hz)
  · rintro (rfl|⟨y,hy,hz⟩)
    · exact self_mem d r q hx
    · obtain ⟨hyd,hyx⟩ := (mem_predecessors _ _ _ _).mp hy
      exact hull_least d r q y _ hhq (hull_closed d r q x)
        (hull_closed d r q x x (self_mem d r q hx) y hyd hyx) hz

end TuringRigidity.RelationHull

end OAI
