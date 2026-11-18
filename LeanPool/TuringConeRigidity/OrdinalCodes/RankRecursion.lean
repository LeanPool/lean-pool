/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/RankRecursion.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.BoundedRelations

/-!
# Rank Recursion
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.InternalRank
open TransitiveNameModel BoundedSetTheory
universe u

/-- The set-valued rank obtained by recursively taking unions of successor ranks. -/
noncomputable def rankSet (x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sUnion (ZFSet.range (fun y : Shrink x =>
    insert (rankSet ((equivShrink x).symm y).val) (rankSet ((equivShrink x).symm y).val)))
termination_by x
decreasing_by exact ((equivShrink x).symm y).property

theorem mem_rankSet (x z : ZFSet.{u}) :
    z ∈ rankSet x ↔ ∃ y ∈ x, z = rankSet y ∨ z ∈ rankSet y := by
  rw [rankSet,ZFSet.mem_sUnion]
  constructor
  · rintro ⟨v,hv,hz⟩
    obtain ⟨y,rfl⟩ := ZFSet.mem_range.mp hv
    exact ⟨_,((equivShrink x).symm y).property,ZFSet.mem_insert_iff.mp hz⟩
  · rintro ⟨y,hy,hz⟩
    refine ⟨_,ZFSet.mem_range.mpr ⟨equivShrink x ⟨y,hy⟩,rfl⟩,?_⟩
    simpa using ZFSet.mem_insert_iff.mpr hz

theorem rankSet_mem {x y : ZFSet.{u}} (hy : y ∈ x) : rankSet y ∈ rankSet x :=
  (mem_rankSet x _).mpr ⟨y,hy,Or.inl rfl⟩

theorem rankSet_transitive (x : ZFSet.{u}) : Transitive (rankSet x) := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    intro z hz w hw
    obtain ⟨y,hy,rfl|hz⟩ := (mem_rankSet x z).mp hz
    · exact (mem_rankSet x w).mpr ⟨y,hy,Or.inr hw⟩
    · exact (mem_rankSet x w).mpr ⟨y,hy,Or.inr (ih y hy z hz w hw)⟩

/-- The value `v` is exactly the union of the successor values assigned to members of `x`. -/
def Step (f r x v : ZFSet.{u}) : Prop :=
  (∀ z ∈ v, ∃ y ∈ x, ∃ w ∈ r, ZFSet.pair y w ∈ f ∧ (z = w ∨ z ∈ w)) ∧
  (∀ y ∈ x, ∀ w ∈ r, ZFSet.pair y w ∈ f → w ∈ v ∧ w ⊆ v)

/-- A total single-valued rank-recursion graph on a transitive domain with values in `r`. -/
def Graph (d r f : ZFSet.{u}) : Prop :=
  Transitive d ∧
  (∀ z ∈ f, ∃ x ∈ d, ∃ y ∈ r, z = ZFSet.pair x y) ∧
  (∀ x ∈ d, ∃ y ∈ r, ZFSet.pair x y ∈ f ∧
    ∀ z ∈ r, ZFSet.pair x z ∈ f → z = y) ∧
  (∀ x ∈ d, ∀ y ∈ r, ZFSet.pair x y ∈ f → Step f r x y)

theorem Graph.correct {d r f : ZFSet.{u}} (h : Graph d r f)
    (x : ZFSet.{u}) (hx : x ∈ d) (v : ZFSet.{u}) (hv : v ∈ r)
    (hfv : ZFSet.pair x v ∈ f) : v = rankSet x := by
  induction x using ZFSet.inductionOn generalizing v with
  | h x ih =>
    have hs := h.2.2.2 x hx v hv hfv
    apply ZFSet.ext
    intro z
    rw [mem_rankSet]
    constructor
    · intro hz
      obtain ⟨y,hy,w,hw,hfw,hz⟩ := hs.1 z hz
      rw [ih y hy (h.1 x hx y hy) w hw hfw] at hz
      exact ⟨y,hy,hz⟩
    · rintro ⟨y,hy,hz⟩
      obtain ⟨w,hw,hfw,_⟩ := h.2.2.1 y (h.1 x hx y hy)
      rw [←ih y hy (h.1 x hx y hy) w hw hfw] at hz
      exact hz.elim (fun hzw => hzw ▸ (hs.2 y hy w hw hfw).1)
        (fun hz => (hs.2 y hy w hw hfw).2 hz)

theorem Graph.unique {d r s f g : ZFSet.{u}}
    (hf : Graph d r f) (hg : Graph d s g) : f = g := by
  apply ZFSet.ext
  intro z
  have forward {r s f g : ZFSet.{u}} (hf : Graph d r f)
      (hg : Graph d s g) (hz : z ∈ f) : z ∈ g := by
    obtain ⟨x,hx,y,hy,rfl⟩ := hf.2.1 z hz
    obtain ⟨v,hv,hgv,_⟩ := hg.2.2.1 x hx
    have he := (hf.correct x hx y hy hz).trans (hg.correct x hx v hv hgv).symm
    exact he ▸ hgv
  exact ⟨forward hf hg,forward hg hf⟩

namespace Code
open Formula

/-- Bounded formula expressing one internal rank-recursion step. -/
def step (f r x v : ℕ) : Formula :=
  .conj (allMem v (.existsMem (x+1) (.existsMem (r+2)
    (.conj (pairMem 1 0 (f+3)) (disj (.equal 2 0) (.member 2 0))))))
    (allMem x (allMem (r+1) (imp (pairMem 1 0 (f+2))
      (.conj (.member 0 (v+2)) (subset 0 (v+2))))))

theorem eval_step (f r x v : ℕ) (e : ℕ → ZFSet.{u}) :
    (step f r x v).Eval e ↔ Step (e f) (e r) (e x) (e v) := by
  simp only [step,Formula.Eval,eval_allMem,eval_pairMem,eval_disj,
    eval_imp,eval_subset,cons_zero,cons_succ,Step]

/-- Bounded formula expressing the transitive domain, function graph, and internal rank steps. -/
def graph (d r f : ℕ) : Formula :=
  .conj (transitive d) (.conj (functionGraph f d r)
    (allMem d (allMem (r+1) (imp (pairMem 1 0 (f+2)) (step (f+2) (r+2) 1 0)))))

theorem eval_graph (d r f : ℕ) (e : ℕ → ZFSet.{u}) :
    (graph d r f).Eval e ↔ Graph (e d) (e r) (e f) := by
  simp only [graph,Formula.Eval,eval_transitive,eval_functionGraph,
    eval_allMem,eval_imp,eval_pairMem,eval_step,cons_zero,cons_succ,Graph]
  exact and_congr_right (fun _ => and_assoc)
end Code

end TuringRigidity.InternalRank

end OAI
