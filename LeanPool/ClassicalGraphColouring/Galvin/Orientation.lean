/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.ClassicalGraphColouring.Galvin.GaleShapley
public import LeanPool.ClassicalGraphColouring.Galvin.Kernel
public import Mathlib.Combinatorics.SimpleGraph.LineGraph

/-!
# Galvin's orientation of the line graph of a bipartite graph

Fix a `2`-colouring `c` of `G` (sides `0` and `1`) and a proper edge colouring `φ` with colours
in `Fin Δ`. Every edge `e` has an endpoint `endA c e` on side `0` and `endB c e` on side `1`. For
edges sharing their side-`0` endpoint, the arc goes from the larger to the smaller colour; for
edges sharing their side-`1` endpoint, from the smaller to the larger colour. Every out-degree is
less than `Δ`, and every set of edges has a kernel (a stable matching).
-/

@[expose] public section

namespace Galvin

open Finset SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

theorem exists_ends (c : G.Coloring (Fin 2)) (e : G.edgeSet) :
    ∃ a b : V, (e : Sym2 V) = s(a, b) ∧ c a = 0 := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ x y =>
  have hne : c x ≠ c y := c.valid he
  by_cases hx : c x = 0
  · exact ⟨x, y, rfl, hx⟩
  · refine ⟨y, x, Sym2.eq_swap, ?_⟩
    revert hne hx
    generalize c x = i
    generalize c y = j
    revert i j
    decide

/-- The endpoint of an edge on side `0`. -/
noncomputable def endA (c : G.Coloring (Fin 2)) (e : G.edgeSet) : V :=
  (exists_ends c e).choose

/-- The endpoint of an edge on side `1`. -/
noncomputable def endB (c : G.Coloring (Fin 2)) (e : G.edgeSet) : V :=
  (exists_ends c e).choose_spec.choose

theorem edge_eq_ends (c : G.Coloring (Fin 2)) (e : G.edgeSet) :
    (e : Sym2 V) = s(endA c e, endB c e) :=
  (exists_ends c e).choose_spec.choose_spec.1

theorem colour_endA (c : G.Coloring (Fin 2)) (e : G.edgeSet) : c (endA c e) = 0 :=
  (exists_ends c e).choose_spec.choose_spec.2

theorem adj_ends (c : G.Coloring (Fin 2)) (e : G.edgeSet) : G.Adj (endA c e) (endB c e) := by
  have := e.2
  rw [edge_eq_ends c e] at this
  exact this

theorem colour_endB (c : G.Coloring (Fin 2)) (e : G.edgeSet) : c (endB c e) = 1 := by
  have h1 := c.valid (adj_ends c e)
  rw [colour_endA] at h1
  revert h1
  generalize c (endB c e) = i
  revert i
  decide

theorem eq_of_ends (c : G.Coloring (Fin 2)) {e f : G.edgeSet} (hA : endA c e = endA c f)
    (hB : endB c e = endB c f) : e = f := by
  apply Subtype.ext
  rw [edge_eq_ends c e, edge_eq_ends c f, hA, hB]

theorem mem_edge_iff (c : G.Coloring (Fin 2)) (e : G.edgeSet) (v : V) :
    v ∈ (e : Sym2 V) ↔ v = endA c e ∨ v = endB c e := by
  rw [edge_eq_ends c e, Sym2.mem_iff]

theorem lineGraph_adj_iff_ends (c : G.Coloring (Fin 2)) {e f : G.edgeSet} :
    G.lineGraph.Adj e f ↔ e ≠ f ∧ (endA c e = endA c f ∨ endB c e = endB c f) := by
  rw [lineGraph_adj_iff_exists]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨v, hve, hvf⟩
    rw [mem_edge_iff c] at hve hvf
    have hA := colour_endA c e
    have hA' := colour_endA c f
    have hB := colour_endB c e
    have hB' := colour_endB c f
    rcases hve with rfl | rfl <;> rcases hvf with h | h
    · exact Or.inl h
    · rw [h, hB'] at hA; exact absurd hA (by decide)
    · rw [h, hA'] at hB; exact absurd hB (by decide)
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨endA c e, (mem_edge_iff c e _).2 (Or.inl rfl), (mem_edge_iff c f _).2 (Or.inl h)⟩
    · exact ⟨endB c e, (mem_edge_iff c e _).2 (Or.inr rfl), (mem_edge_iff c f _).2 (Or.inr h)⟩

theorem eq_of_colour_eq (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    {e f : G.edgeSet} (hφ : φ e = φ f) (h : endA c e = endA c f ∨ endB c e = endB c f) :
    e = f := by
  by_contra hne
  exact φ.valid ((lineGraph_adj_iff_ends c).2 ⟨hne, h⟩) hφ

/-- Galvin's orientation of the line graph. -/
def arc (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    (e f : G.edgeSet) : Prop :=
  (endA c e = endA c f ∧ φ f < φ e) ∨ (endB c e = endB c f ∧ φ e < φ f)

/-- Every out-degree of Galvin's orientation is less than `Δ`. -/
theorem card_arc_lt [Fintype G.edgeSet] (c : G.Coloring (Fin 2)) {Δ : ℕ}
    (φ : G.lineGraph.Coloring (Fin Δ)) (e : G.edgeSet) [DecidablePred (arc c φ e)] :
    (univ.filter (arc c φ e)).card < Δ := by
  classical
  have hsub : univ.filter (arc c φ e) ⊆
      univ.filter (fun f => endA c e = endA c f ∧ φ f < φ e) ∪
        univ.filter (fun f => endB c e = endB c f ∧ φ e < φ f) := by
    intro f hf
    simp only [arc, mem_filter, mem_univ, true_and, mem_union] at hf ⊢
    exact hf
  have h1 : (univ.filter (fun f => endA c e = endA c f ∧ φ f < φ e)).card ≤
      (Iio (φ e)).card := by
    refine card_le_card_of_injOn (fun f => φ f) (fun f hf => ?_) (fun f hf f' hf' h => ?_)
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hf
      simpa using hf.2
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hf hf'
      exact eq_of_colour_eq c φ h (Or.inl (hf.1.symm.trans hf'.1))
  have h2 : (univ.filter (fun f => endB c e = endB c f ∧ φ e < φ f)).card ≤
      (Ioi (φ e)).card := by
    refine card_le_card_of_injOn (fun f => φ f) (fun f hf => ?_) (fun f hf f' hf' h => ?_)
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hf
      simpa using hf.2
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hf hf'
      exact eq_of_colour_eq c φ h (Or.inr (hf.1.symm.trans hf'.1))
  rw [Fin.card_Iio] at h1
  rw [Fin.card_Ioi] at h2
  have h3 := (card_le_card hsub).trans (card_union_le _ _)
  have h4 := (φ e).isLt
  omega

/-- Rank of `w` for the man `m`: the colour of the edge `mw` (smaller colours preferred). -/
noncomputable def rankA (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    (idx : V → ℕ) (m w : V) : ℕ :=
  open Classical in
  if h : ∃ e : G.edgeSet, endA c e = m ∧ endB c e = w then (φ h.choose : ℕ) else Δ + idx w

/-- Rank of `m` for the woman `w`: `Δ` minus the colour of the edge `mw` (larger colours
preferred). -/
noncomputable def rankB (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    (idx : V → ℕ) (w m : V) : ℕ :=
  open Classical in
  if h : ∃ e : G.edgeSet, endA c e = m ∧ endB c e = w then Δ - (φ h.choose : ℕ)
  else Δ + 1 + idx m

theorem choose_ends_eq (c : G.Coloring (Fin 2)) (e : G.edgeSet)
    (h : ∃ f : G.edgeSet, endA c f = endA c e ∧ endB c f = endB c e) : h.choose = e :=
  eq_of_ends c h.choose_spec.1 h.choose_spec.2

theorem rankA_ends (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    (idx : V → ℕ) (e : G.edgeSet) : rankA c φ idx (endA c e) (endB c e) = φ e := by
  have h : ∃ f : G.edgeSet, endA c f = endA c e ∧ endB c f = endB c e := ⟨e, rfl, rfl⟩
  rw [rankA]
  split_ifs
  rw [choose_ends_eq c e h]

theorem rankB_ends (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    (idx : V → ℕ) (e : G.edgeSet) : rankB c φ idx (endB c e) (endA c e) = Δ - φ e := by
  have h : ∃ f : G.edgeSet, endA c f = endA c e ∧ endB c f = endB c e := ⟨e, rfl, rfl⟩
  rw [rankB]
  split_ifs
  rw [choose_ends_eq c e h]

theorem rankA_injective (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    {idx : V → ℕ} (hidx : Function.Injective idx) (m : V) :
    Function.Injective (rankA c φ idx m) := by
  intro w w' hww
  unfold rankA at hww
  split_ifs at hww with h h'
  · have := eq_of_colour_eq c φ (Fin.ext hww)
      (Or.inl (h.choose_spec.1.trans h'.choose_spec.1.symm))
    rw [← h.choose_spec.2, ← h'.choose_spec.2, this]
  · have := (φ h.choose).isLt; omega
  · rename_i h₂; have := (φ h₂.choose).isLt; omega
  · exact hidx (by omega)

theorem rankB_injective (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    {idx : V → ℕ} (hidx : Function.Injective idx) (w : V) :
    Function.Injective (rankB c φ idx w) := by
  intro m m' hmm
  unfold rankB at hmm
  split_ifs at hmm with h h'
  · have h1 := (φ h.choose).isLt
    have h2 := (φ h'.choose).isLt
    have := eq_of_colour_eq c φ (Fin.ext (by omega))
      (Or.inr (h.choose_spec.2.trans h'.choose_spec.2.symm))
    rw [← h.choose_spec.1, ← h'.choose_spec.1, this]
  · omega
  · omega
  · exact hidx (by omega)

/-- Every set of edges has a kernel for Galvin's orientation: a stable matching. -/
theorem hasKernels_arc [Finite V] (c : G.Coloring (Fin 2)) {Δ : ℕ}
    (φ : G.lineGraph.Coloring (Fin Δ)) : HasKernels G.lineGraph (arc c φ) := by
  classical
  intro S
  obtain ⟨N, ⟨eqv⟩⟩ := Finite.exists_equiv_fin V
  let idx : V → ℕ := fun v => (eqv v : ℕ)
  have hidx : Function.Injective idx := fun a b h => eqv.injective (Fin.ext h)
  let E : V → V → Prop := fun m w => ∃ e ∈ S, endA c e = m ∧ endB c e = w
  obtain ⟨μ, hsub, hm, hw, hst⟩ := exists_isStable (rankA c φ idx) (rankB c φ idx)
    (rankA_injective c φ hidx) (rankB_injective c φ hidx) _ E rfl
  refine ⟨S.filter (fun e => μ (endA c e) (endB c e)), filter_subset _ _, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [mem_filter] at hx hy
    obtain ⟨hne, h | h⟩ := (lineGraph_adj_iff_ends c).1 hxy
    · rw [h] at hx
      exact hne (eq_of_ends c h (hm _ _ _ hx.2 hy.2))
    · rw [h] at hx
      exact hne (eq_of_ends c (hw _ _ _ hx.2 hy.2) h)
  · intro x hxS hxK
    simp only [mem_filter, hxS, true_and] at hxK
    rcases hst _ _ ⟨x, hxS, rfl, rfl⟩ hxK with ⟨w', hμ, hlt⟩ | ⟨m', hμ, hlt⟩
    · obtain ⟨f, hfS, hfA, hfB⟩ := hsub _ _ hμ
      subst hfB
      rw [← hfA] at hμ hlt
      refine ⟨f, mem_filter.2 ⟨hfS, hμ⟩, Or.inl ⟨hfA.symm, ?_⟩⟩
      rw [rankA_ends, hfA, rankA_ends] at hlt
      exact hlt
    · obtain ⟨f, hfS, hfA, hfB⟩ := hsub _ _ hμ
      subst hfA
      rw [← hfB] at hμ hlt
      refine ⟨f, mem_filter.2 ⟨hfS, hμ⟩, Or.inr ⟨hfB.symm, ?_⟩⟩
      rw [rankB_ends, hfB, rankB_ends] at hlt
      have := (φ f).isLt
      have := (φ x).isLt
      change (φ x : ℕ) < φ f
      omega

end Galvin
