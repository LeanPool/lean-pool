/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3DiscChainChord
import LeanPool.GraphMinor.GM06.Section2Count
import LeanPool.GraphMinor.GM11.Regions

/-!
# The VI chain condition from a proper-normal-chord bound

In the one-disc case of XII (3.2), pages 247--248, a VI chain
between distinct boundary points supplies a proper normal chord.
Its drawing vertex count is at most the chain length. A bound on
the division count by every such chord therefore gives nonnegative
chain redundancy. When both endpoints agree, the division count is
zero or one. In the latter case the boundary endpoint itself must
be a vertex term of the chain, so its length is at least one.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM06 GM11

private theorem chainLength_pos_of_vertex_endpoint
    {S : Type*} [TopologicalSpace S] {G : Drawing S} {x y : S}
    {A : List (ChainTerm S)} (hA : IsXYChain G x y A) (hxV : x ∈ G.V) :
    0 < chainLength A := by
  have hhead := hA.head_matches
  have hmem : Sum.inl x ∈ A := by
    rcases he : A.head hA.ne_nil with v | r
    · rw [he] at hhead
      change v = x at hhead
      have h := List.head_mem hA.ne_nil
      rw [he, hhead] at h
      exact h
    · rw [he] at hhead
      have hr : r ∈ G.R := by
        have hvalid := hA.valid (A.head hA.ne_nil) (List.head_mem hA.ne_nil)
        rwa [he] at hvalid
      exact False.elim (region_subset hr hhead (G.V_subset_U hxV))
  have hfiltered : Sum.inl x ∈ A.filter (fun t => decide t.IsVertex) := by
    exact List.mem_filter.mpr ⟨hmem, by rfl⟩
  apply List.length_pos_of_ne_nil
  intro he
  rw [he] at hfiltered
  exact List.not_mem_nil hfiltered

/-- The chain-redundancy step of the VI (3.6) application in XII
(3.2), pages 247--248. Every required chord bound is used on the
proper normal chord extracted from the given chain. -/
theorem chainRedundancy_nonneg_of_normal_chord_bound
    {S : Type*} [TopologicalSpace S] {G : Drawing S} {Δ : Set (Set S)}
    (hDisc : IsClosedDiscSpace S) (hProper : G.IsProper)
    (hΔ : IsDivision Δ) (hUnion : divisionUnion Δ = G.V ∩ bd S)
    (hchord : ∀ (x y : S), x ∈ bd S → y ∈ bd S → x ≠ y →
      ∀ L : Set S, IsLineWithEnds L x y → G.IsNormal L → L ∩ bd S = {x, y} →
        divisionCount (bd S) Δ x y ≤ (G.V ∩ L).ncard)
    {x y : S} {A : List (ChainTerm S)} (hxB : x ∈ bd S) (hyB : y ∈ bd S)
    (hA : IsXYChain G x y A) : 0 ≤ chainRedundancy G Δ x y A := by
  have hbound : divisionCount (bd S) Δ x y ≤ chainLength A := by
    by_cases hxy : x = y
    · subst y
      by_cases hxΔ : x ∈ divisionUnion Δ
      · rw [divisionCount_self_eq_one_of_mem hΔ hxΔ]
        exact chainLength_pos_of_vertex_endpoint hA ((hUnion ▸ hxΔ).1)
      · rw [divisionCount_self_eq_zero_of_not_mem hxΔ]
        exact Nat.zero_le _
    · obtain ⟨L, hL, hn, hcap, hlen⟩ :=
        exists_normal_chord_of_disc_chain hDisc hProper hA hxy hxB hyB
      exact (hchord x y hxB hyB hxy L hL hn hcap).trans hlen
  unfold chainRedundancy
  exact sub_nonneg.mpr (by exact_mod_cast hbound)

end GraphMinor.GM12
