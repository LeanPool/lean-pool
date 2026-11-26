/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.Bridge
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-! Padding and connectivity for the host-graph construction. -/

@[expose] public section

namespace GapExtremal

open Finset

/-- Split graphs: a clique and an independent set covering all vertices. -/
def IsSplit {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ K : Set V, (∀ x ∈ K, ∀ y ∈ K, x ≠ y → G.Adj x y) ∧ (∀ x ∉ K, ∀ y ∉ K, ¬ G.Adj x y)

theorem isSplit_hostGraph {V H : Type*}
    (N : H → Finset V) : IsSplit (hostGraph N) := by
  refine ⟨Set.range Sum.inl, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
    exact fun e => h (by rw [e])
  · rintro (x | h) hx (y | h') hy
    · exact absurd ⟨x, rfl⟩ hx
    · exact absurd ⟨x, rfl⟩ hx
    · exact absurd ⟨y, rfl⟩ hy
    · exact hostGraph_inr_inr N h h'

/-! ### Padding a host family -/

section Pad

variable {V : Type*} [Fintype V] [DecidableEq V] {H : Type*} [Fintype H] [DecidableEq H]

/-- Padded palettes: empty palettes become `{x₀}`, and `k` new hosts with palette `{x₀}`. -/
def padN (N : H → Finset V) (x0 : V) (k : ℕ) : H ⊕ Fin k → Finset V
  | .inl h => if N h = ∅ then {x0} else N h
  | .inr _ => {x0}

omit [DecidableEq H] [Fintype H] [Fintype V] in
theorem padN_nonempty (N : H → Finset V) (x0 : V) (k : ℕ) (h : H ⊕ Fin k) : (padN N x0 k
  h).Nonempty := by
  rcases h with h | i
  · simp only [padN]
    split_ifs with h0
    · exact Finset.singleton_nonempty _
    · exact Finset.nonempty_iff_ne_empty.mpr h0
  · exact Finset.singleton_nonempty _

omit [DecidableEq H] [Fintype H] [Fintype V] in
theorem HostHyp.pad {B : SimpleGraph V} {N : H → Finset V} {φ : V → V → H}
    (hH : HostHyp B N φ) (x0 : V) (k : ℕ) :
    HostHyp B (padN N x0 k) (fun x y => Sum.inl (φ x y)) where
  indep := by
    rintro (h | i) x hx y hy hxy
    · simp only [padN] at hx hy
      split_ifs at hx hy with h0
      · rw [Finset.mem_singleton] at hx hy
        subst hx; subst hy
        exact B.loopless.irrefl _ hxy
      · exact hH.indep h x hx y hy hxy
    · simp only [padN, Finset.mem_singleton] at hx hy
      subst hx; subst hy
      exact B.loopless.irrefl _ hxy
  cover := by
    intro x y hne hadj
    obtain ⟨hx, hy⟩ := hH.cover x y hne hadj
    have h0 : N (φ x y) ≠ ∅ := Finset.ne_empty_of_mem hx
    simp only [padN, ite_eq_right h0]
    exact ⟨hx, hy⟩
  symm := fun x y => by rw [hH.symm x y]
  inj := fun x y y' h1 h2 h3 h4 h => hH.inj x y y' h1 h2 h3 h4 (Sum.inl_injective h)

omit [DecidableEq H] [DecidableEq V] in
theorem card_pad (k : ℕ) :
    Fintype.card (V ⊕ (H ⊕ Fin k)) = Fintype.card (V ⊕ H) + k := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  ring

omit [DecidableEq V] [Fintype V] in
/-- A host graph with a nonempty core and nonempty palettes is connected. -/
theorem connected_hostGraph {H' : Type*} (N : H' → Finset V) (x0 : V)
    (hN : ∀ h, (N h).Nonempty) :
    (hostGraph N).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  have hcore : ∀ y : V, (hostGraph N).Reachable (.inl x0) (.inl y) := fun y => by
    by_cases hy : x0 = y
    · rw [hy]
    · exact SimpleGraph.Adj.reachable ((hostGraph_inl_inl N _ _).mpr hy)
  refine ⟨.inl x0, ?_⟩
  rintro (y | h)
  · exact hcore y
  · obtain ⟨y, hy⟩ := hN h
    exact (hcore y).trans (SimpleGraph.Adj.reachable ((hostGraph_inl_inr N _ _).mpr hy))

end Pad

end GapExtremal
