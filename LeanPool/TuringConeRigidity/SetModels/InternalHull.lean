/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalHull.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.BoundedRelations
public import LeanPool.TuringConeRigidity.SetModels.ModelProducts

/-!
# Internal Hull
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

/-- The elements of `d` lying in every transitive member of `q` that contains `x`. -/
noncomputable def hull (d q x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∀ c ∈ q, Transitive c → x ∈ c → z ∈ c) d

theorem mem_hull (d q x z : ZFSet.{u}) :
    z ∈ hull d q x ↔ z ∈ d ∧ ∀ c ∈ q, Transitive c → x ∈ c → z ∈ c :=
  ZFSet.mem_sep

/-- Bounded formula expressing membership in every suitable transitive hull candidate. -/
def hullMemberFormula : Formula :=
  .allMem 2 (.imp (.conj (.transitive 0) (.member 2 0)) (.member 1 0))

theorem eval_hullMemberFormula (z x q : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    hullMemberFormula.Eval (cons z (cons x (cons q e))) ↔
      ∀ c ∈ q, Transitive c → x ∈ c → z ∈ c := by
  simp only [hullMemberFormula, Formula.eval_allMem, Formula.eval_imp,
    Formula.Eval, Formula.eval_transitive, cons_zero, cons_succ]
  exact forall_congr' (fun c => forall_congr' (fun _ => and_imp))

theorem hull_mem (M d q : ZFSet.{u}) (hM : Transitive M) (hS : Separation M)
    (hdM : d ∈ M) (hqM : q ∈ M) {x : ZFSet.{u}} (hxM : x ∈ M) :
    hull d q x ∈ M := by
  have he : ∀ i, cons x (cons q (fun _ => d)) i ∈ M := by
    intro i; cases i with
    | zero => exact hxM
    | succ i => cases i <;> assumption
  have hs := sep_mem M hM hS hullMemberFormula _ he hdM
  have heq : ZFSet.sep (fun z => hullMemberFormula.Eval
      (cons z (cons x (cons q (fun _ => d))))) d = hull d q x := by
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_sep, eval_hullMemberFormula, mem_hull]
  exact heq ▸ hs

theorem hull_subset (d q x : ZFSet.{u}) : hull d q x ⊆ d :=
  fun _ hz => (mem_hull _ _ _ _).mp hz |>.1

theorem self_mem_hull (d q : ZFSet.{u}) {x : ZFSet.{u}} (hx : x ∈ d) :
    x ∈ hull d q x := (mem_hull _ _ _ _).mpr ⟨hx,fun _ _ _ h => h⟩

theorem hull_transitive (d q x : ZFSet.{u}) (hd : Transitive d) :
    Transitive (hull d q x) := by
  intro y hy z hz
  obtain ⟨hyd,hyc⟩ := (mem_hull _ _ _ _).mp hy
  exact (mem_hull _ _ _ _).mpr
    ⟨hd y hyd z hz,fun c hc ht hx => ht y (hyc c hc ht hx) z hz⟩

theorem hull_least (d q x c : ZFSet.{u}) (hcq : c ∈ q)
    (hc : Transitive c) (hx : x ∈ c) : hull d q x ⊆ c :=
  fun _ hz => (mem_hull _ _ _ _).mp hz |>.2 c hcq hc hx

namespace Formula
/-- Bounded formula identifying a least transitive member of `q` containing `x`. -/
def isHull (c x _d q : ℕ) : Formula :=
  .conj (.member c q) (.conj (transitive c) (.conj (.member x c)
    (allMem q (imp (.conj (transitive 0) (.member (x+1) 0)) (subset (c+1) 0)))))

theorem eval_isHull (c x d q : ℕ) (e : ℕ → ZFSet.{u}) :
    (isHull c x d q).Eval e ↔ e c ∈ e q ∧ Transitive (e c) ∧ e x ∈ e c ∧
      ∀ b ∈ e q, Transitive b → e x ∈ b → e c ⊆ b := by
  simp only [isHull, Eval, eval_transitive, eval_allMem, eval_imp,
    eval_subset, cons_zero, cons_succ]
  simp only [and_imp]
end Formula

theorem isHull_iff (M d q : ZFSet.{u}) (hM : Transitive M)
    (hS : Separation M) (hdM : d ∈ M) (hqM : q ∈ M) (hd : Transitive d)
    (hq : ∀ c, c ∈ q ↔ c ∈ M ∧ c ⊆ d) {x c : ZFSet.{u}}
    (hx : x ∈ d) (hc : c ∈ M) :
    (c ∈ q ∧ Transitive c ∧ x ∈ c ∧
      ∀ b ∈ q, Transitive b → x ∈ b → c ⊆ b) ↔ c = hull d q x := by
  have hhM := hull_mem M d q hM hS hdM hqM (hM d hdM x hx)
  have hhq := (hq _).mpr ⟨hhM,hull_subset d q x⟩
  have hht := hull_transitive d q x hd
  have hhx := self_mem_hull d q hx
  constructor
  · rintro ⟨hcq,hct,hxc,hmin⟩
    apply ZFSet.ext
    intro z
    exact ⟨fun hz => hmin _ hhq hht hhx hz,fun hz => hull_least d q x c hcq hct hxc hz⟩
  · rintro rfl
    exact ⟨hhq,hht,hhx,fun b hb ht hx => hull_least d q x b hb ht hx⟩

theorem collect_hulls (M d q : ZFSet.{u}) (hM : Transitive M)
    (hS : Separation M) (hR : SigmaReplacement M)
    (hdM : d ∈ M) (hqM : q ∈ M) (hd : Transitive d)
    (hq : ∀ c, c ∈ q ↔ c ∈ M ∧ c ⊆ d) {x : ZFSet.{u}} (hx : x ∈ d) :
    ∃ b ∈ M, ∀ c, c ∈ b ↔ ∃ y ∈ x, hull d q y = c := by
  let e := cons d (cons q (fun _ => d))
  have he : ∀ i, e i ∈ M := by
    intro i; cases i with
    | zero => exact hdM
    | succ i => cases i <;> assumption
  apply replacement_image M hM hR (.bounded (.isHull 0 1 2 3)) e he
    (hM d hdM x hx) (hull d q)
  · intro y hy
    exact hull_mem M d q hM hS hdM hqM (hM _ (hM d hdM x hx) y hy)
  · intro y hy c hc
    change (Formula.isHull 0 1 2 3).Realize M (cons c (cons y e)) ↔ _
    have he' : ∀ i, cons c (cons y e) i ∈ M := by
      intro i; cases i with
      | zero => exact hc
      | succ i => cases i with
        | zero => exact hM _ (hM d hdM x hx) y hy
        | succ i => exact he i
    rw [Formula.absolute _ M hM _ he', Formula.eval_isHull]
    exact isHull_iff M d q hM hS hdM hqM hd hq (hd x hx y hy) hc

theorem hull_unfold (M d q : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : Union M) (hS : Separation M) (hR : SigmaReplacement M)
    (hdM : d ∈ M) (hqM : q ∈ M) (hd : Transitive d)
    (hq : ∀ c, c ∈ q ↔ c ∈ M ∧ c ⊆ d) {x : ZFSet.{u}} (hx : x ∈ d) :
    ∀ z, z ∈ hull d q x ↔ z = x ∨ ∃ y ∈ x, z ∈ hull d q y := by
  obtain ⟨b,hb,hbdef⟩ := collect_hulls M d q hM hS hR hdM hqM hd hq hx
  let a := ({x} : ZFSet.{u}) ∪ ZFSet.sUnion b
  have haM : a ∈ M := binary_union_mem M hM hP hU
    (singleton_mem M hM hP (hM d hdM x hx)) (union_mem M hM hU hb)
  have ha (z : ZFSet.{u}) : z ∈ a ↔ z = x ∨ ∃ y ∈ x, z ∈ hull d q y := by
    simp only [a,ZFSet.mem_union,ZFSet.mem_singleton,ZFSet.mem_sUnion]
    constructor
    · rintro (h|⟨c,hc,hzc⟩)
      · exact Or.inl h
      · obtain ⟨y,hy,rfl⟩ := (hbdef c).mp hc
        exact Or.inr ⟨y,hy,hzc⟩
    · rintro (h|⟨y,hy,hzy⟩)
      · exact Or.inl h
      · exact Or.inr ⟨_,(hbdef _).mpr ⟨y,hy,rfl⟩,hzy⟩
  have had : a ⊆ d := by
    intro z hz
    rcases (ha z).mp hz with rfl|⟨y,_,hzy⟩
    · exact hx
    · exact hull_subset d q y hzy
  have hat : Transitive a := by
    intro z hz w hw
    apply (ha w).mpr
    rcases (ha z).mp hz with rfl|⟨y,hy,hzy⟩
    · exact Or.inr ⟨w,hw,self_mem_hull d q (hd _ hx w hw)⟩
    · exact Or.inr ⟨y,hy,hull_transitive d q y hd z hzy w hw⟩
  have hhM := hull_mem M d q hM hS hdM hqM (hM d hdM x hx)
  have hhq := (hq _).mpr ⟨hhM,hull_subset d q x⟩
  intro z
  constructor
  · intro hz
    exact (ha z).mp (hull_least d q x a ((hq _).mpr ⟨haM,had⟩) hat
      ((ha x).mpr (Or.inl rfl)) hz)
  · rintro (rfl|⟨y,hy,hzy⟩)
    · exact self_mem_hull d q hx
    · exact hull_least d q y _ hhq (hull_transitive d q x hd)
        (hull_transitive d q x hd x (self_mem_hull d q hx) y hy) hzy

end TuringRigidity.BoundedSetTheory

end OAI
