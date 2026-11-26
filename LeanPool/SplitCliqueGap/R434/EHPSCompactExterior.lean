/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.EHPSProduct
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FinCases

/-! Six convex certificates for points outside the EHPS region. -/

@[expose] public section

namespace GapExtremal.R434.EHPS.CompactExterior

private def cell (ε : ℝ) (x : Point) (i : Fin 6) : Prop :=
  match i.val with
  | 0 => total x ≤ 2/3
  | 1 => x.1 < 1/2 ∧ total x < 7/6 + ε
  | 2 => 7/6 < total x ∧ total x < 7/6 + ε
  | 3 => 7/6 < total x ∧ 1/2 ≤ x.1 ∧ 1/2 ≤ x.2
  | 4 => x.1 < 1/2 ∧ 2*x.1 + x.2 < 3/2 + ε
  | _ => 17/12 < total x

private theorem covered {ε : ℝ} (he : 0 < ε) {x : Point} (hs : InSquare x) (hx : ¬Region ε x) :
    ∃ i, cell ε x i := by
  by_contra! h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  simp [cell,total] at h0 h1 h2 h3 h4 h5
  apply hx
  obtain ⟨ha,ha',hb,hb'⟩ := hs
  refine ⟨ha,ha',hb,hb',?_⟩
  unfold total
  grind

private theorem outside {ε : ℝ} (he : 0 < ε) {x : Point} {i : Fin 6}
    (hx : cell ε x i) : ¬Region ε x := by
  intro hr
  obtain ⟨_,_,_,_,hr⟩ := hr
  fin_cases i <;> simp [cell,total] at hx <;> unfold total at hr <;> grind

private theorem closed_mid {ε : ℝ} {x y : Point} {i : Fin 6}
    (hx : cell ε x i) (hy : cell ε y i) : cell ε (midpoint x y) i := by
  fin_cases i <;> simp [cell,total,midpoint] at * <;> grind

/-- A coordinate, an exterior class, and two parity bits. -/
abbrev Label (j : ℕ) := Fin j × Fin 6 × Fin 2 × Fin 2

theorem label_count (j : ℕ) : Fintype.card (Label j) = 24*j := by
  simp [Label]; omega

theorem product_colouring {m j : ℕ} [NeZero m] (hm : Odd m) {ε : ℝ} (he : 0 < ε) :
    ∃ χ : {a : ProductGrid m j // a ∉ productSupport ε m j} → Label j,
      ∀ u v, χ u = χ v → productHalf m j * (u.val + v.val) ∉ productSupport ε m j := by
  classical
  let E := {a : ProductGrid m j // a ∉ productSupport ε m j}
  have bad (a : E) : ∃ i, ¬Region ε (gridPoint m (a.val i)) :=
    not_forall.mp fun h => a.prop (mem_productSupport.mpr h)
  let idx (a : E) := (bad a).choose
  have witness (a : E) := covered he (grid_in_square (a.val (idx a))) (bad a).choose_spec
  let χ (a : E) : Label j := (idx a,(witness a).choose,
    ⟨(a.val (idx a)).1.val % 2, Nat.mod_lt _ (by decide)⟩,
    ⟨(a.val (idx a)).2.val % 2, Nat.mod_lt _ (by decide)⟩)
  refine ⟨χ, fun u v eq hs => ?_⟩
  have hi : idx u = idx v := congrArg Prod.fst eq
  have hc : (witness u).choose = (witness v).choose := congrArg (fun c : Label j => c.2.1) eq
  have hp := congrArg (fun c : Label j => c.2.2.1.val) eq
  have hq := congrArg (fun c : Label j => c.2.2.2.val) eq
  change (u.val (idx u)).1.val % 2 = (v.val (idx v)).1.val % 2 at hp
  change (u.val (idx u)).2.val % 2 = (v.val (idx v)).2.val % 2 at hq
  have hu := (witness u).choose_spec
  have hv := (witness v).choose_spec
  have hvSame := Eq.mp (congrArg₂ (fun i k => cell ε (gridPoint m (v.val i)) k) hi hc).symm hv
  rw [← hi] at hp hq
  have ht := (mem_productSupport.mp hs) (idx u)
  apply outside he (closed_mid hu hvSame)
  convert ht using 1
  exact (Prod.ext (grid_coord_mid hm _ _ hp) (grid_coord_mid hm _ _ hq)).symm

/-- Extend the exterior coloring to a total map. The extra label is used only
on the support. -/
noncomputable def colour {m j : ℕ} [NeZero m] {ε : ℝ} (hm : Odd m) (he : 0 < ε)
    (a : ProductGrid m j) : Option (Label j) := by
  classical
  exact if ha : a ∉ productSupport ε m j then
    some ((product_colouring hm he).choose ⟨a, ha⟩) else none

theorem mid_outside {m j : ℕ} [NeZero m] {ε : ℝ} (hm : Odd m) (he : 0 < ε)
    {a b : ProductGrid m j} (ha : a ∉ productSupport ε m j)
    (hb : b ∉ productSupport ε m j) (hc : colour hm he a = colour hm he b) :
    productHalf m j * (a + b) ∉ productSupport ε m j := by
  classical
  simp only [colour, dite_eq_left ha, dite_eq_left hb, Option.some.injEq] at hc
  exact (product_colouring hm he).choose_spec _ _ hc

end GapExtremal.R434.EHPS.CompactExterior
