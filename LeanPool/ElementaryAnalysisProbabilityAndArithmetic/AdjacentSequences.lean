/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Adjacent sequences

Two adjacent sequences (one monotone, one antitone, with difference tending to zero) converge to
the same limit, in a conditionally complete linearly ordered commutative group with the order
topology, for sequences indexed by a nonempty directed preorder. The multiplicative statements
are stated with quotients `v / u` tending to one, and their additive versions with `v - u`
tending to zero.

## Main statements

* `Monotone.le_of_antitone_of_tendsto_sub`: the monotone sequence lies below the antitone one.
* `Monotone.exists_tendsto_of_antitone_of_tendsto_sub`: both sequences converge to the same
  limit.
-/

public section

open Filter Set Topology

variable {ι H : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  [ConditionallyCompleteLinearOrder H] [CommGroup H] [IsOrderedMonoid H] [TopologicalSpace H]
  [OrderTopology H] {u v : ι → H}

/-- If `u` is monotone, `v` is antitone and `v / u` tends to one, then `u ≤ v`. -/
@[to_additive /-- If `u` is monotone, `v` is antitone and `v - u` tends to zero, then
`u ≤ v`. -/]
theorem Monotone.le_of_antitone_of_tendsto_div (hu : Monotone u) (hv : Antitone v)
    (h : Tendsto (v / u) atTop (𝓝 1)) (i : ι) : u i ≤ v i := by
  rw [← one_le_div']
  exact _root_.le_of_tendsto h <| eventually_atTop.2 ⟨i, fun j hj ↦ div_le_div'' (hv hj) (hu hj)⟩

/-- **Adjacent sequences**: if `u` is monotone, `v` is antitone and `v / u` tends to one, then
`u` and `v` converge to the same limit. -/
@[to_additive /-- **Adjacent sequences**: if `u` is monotone, `v` is antitone and `v - u` tends
to zero, then `u` and `v` converge to the same limit. -/]
theorem Monotone.exists_tendsto_of_antitone_of_tendsto_div (hu : Monotone u) (hv : Antitone v)
    (h : Tendsto (v / u) atTop (𝓝 1)) :
    ∃ l, Tendsto u atTop (𝓝 l) ∧ Tendsto v atTop (𝓝 l) := by
  have hle := hu.le_of_antitone_of_tendsto_div hv h
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hbdd : BddAbove (range u) := by
    refine ⟨v i₀, forall_mem_range.2 fun i ↦ ?_⟩
    obtain ⟨j, hij, hi₀j⟩ := exists_ge_ge i i₀
    exact (hu hij).trans ((hle j).trans (hv hi₀j))
  have hu' := tendsto_atTop_ciSup hu hbdd
  exact ⟨_, hu', by simpa using h.mul hu'⟩
