/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Tutte
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Tauto
public import LeanPool.ClassicalMatchingFactors.Factors.Nec
public import LeanPool.ClassicalMatchingFactors.Factors.Count

/-!

Imported from [jtraverso/tutte-f-factor](https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactor.lean), registered as PALOMAR-2026-10-18-000005. The original proof is retained; module paths and imports are adapted for this collection.

# Tutte's f-factor theorem

Let `G` be a finite simple graph and `f : V → ℕ`. An *f-factor* of `G` is a spanning subgraph
`H ≤ G` with `deg_H v = f v` for every vertex `v`.

For disjoint vertex sets `S` and `T`, let `q(S, T)` (`FFactor.oddCount`) be the number of connected
components `C` of `G − (S ∪ T)` such that `∑_{v ∈ C} f v + e(C, T)` is odd, where `e(C, T)` is the
number of edges between `C` and `T`.

* `FFactor.tutte_f_factor`: **Tutte (1952, 1954).** `G` has an f-factor if and only if, for all
  disjoint `S, T`,
  `q(S, T) ≤ ∑_{v ∈ S} f v − ∑_{v ∈ T} f v + ∑_{v ∈ T} deg_{G − S} v`,
  where `deg_{G − S} v` is the number of neighbours of `v` outside `S`.
-/

@[expose] public section

open Finset SimpleGraph

namespace FFactor

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tutte's f-factor theorem.** A finite simple graph `G` has a spanning subgraph `H` with
`deg_H v = f v` for every vertex `v` if and only if, for all disjoint vertex sets `S` and `T`,
`q(S, T) ≤ ∑_{v ∈ S} f v − ∑_{v ∈ T} f v + ∑_{v ∈ T} deg_{G − S} v`. -/
theorem tutte_f_factor (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℕ) :
    (∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj, H ≤ G ∧ ∀ v, H.degree v = f v) ↔
      ∀ S T : Finset V, Disjoint S T →
        (oddCount G f S T : ℤ) ≤ ∑ v ∈ S, (f v : ℤ) - ∑ v ∈ T, (f v : ℤ) +
          ∑ v ∈ T, (#{u ∈ G.neighborFinset v | u ∉ S} : ℤ) := by
  have hD : ∀ (H : SimpleGraph V) [DecidableRel H.Adj] v, H.degree v =
      @Finset.card V (@Finset.filter V (fun u => H.Adj v u)
        (fun _ => Classical.propDecidable _) univ) := by
    intro H _ v
    rw [← card_neighborFinset_eq_degree]
    congr 1
    ext u
    simp
  constructor
  · rintro ⟨H, _, hHG, hdeg⟩ S T hST
    have := oddCnt_le_of_factor G H hHG f (fun v => (hD H v).symm.trans (hdeg v)) S T hST
    convert this using 4 with v
    congr 1
    ext u
    simp
  · intro h
    obtain ⟨H, hHG, hdeg⟩ := exists_factor_of_condition G f (fun S T hST => by
      have := h S T hST
      convert this using 4 with v
      congr 1
      ext u
      simp)
    classical
    exact ⟨H, inferInstance, hHG, fun v => (hD H v).trans (hdeg v)⟩

end FFactor
