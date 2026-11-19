/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import LeanPool.HubbardMoments.Combinatorics.Subsets
public import LeanPool.HubbardMoments.Torus
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The second-moment theorem: counting the hops

Let `G` be a finite simple graph with `N` vertices and `|E|` edges, and place `n`
particles on distinct vertices: a configuration is an `n`-subset `S` of the vertices.
A *hop* out of `S` is a directed edge `(i, j)` of `G` with `i ∈ S` and `j ∉ S`: one
particle moves to an empty neighbouring site. Write `M(S)` for the number of hops.

In the paper, the diagonal element of `H∞²` at a configuration with occupied set `S`
is `λ² M(S)`, so the second moment `μ₂` is `λ²` times the average of `M` over the
configurations. This file proves the average.

## Main results

* `sum_card_hops_mul`, the exact count, valid for every `n` and every graph:
  `(∑_S M(S)) · N(N - 1) = 2|E| · n(N - n) · C(N, n)`.
* `average_card_hops`: for `n ≤ N` and `N ≥ 2`, the average of `M` over the
  `C(N, n)` configurations is `2|E| · n(N - n) / (N(N - 1))`.
* `average_card_hops_regular`: on a `z`-regular graph the average is
  `n z (N - n) / (N - 1)`.
* `average_card_hops_torus`: on the `L × L` torus with `L ≥ 3`, it is
  `4n(L² - n)/(L² - 1)`. For example it is `64/5 = 12.8` for `L = 4, n = 4`, and `14`
  for `L = 5, n = 4`, the values `μ₂(U → ∞)` printed by the sparse-trace code at
  `λ = 1`.

The key fact (`card_occupied_empty`) is that a fixed ordered pair of distinct sites
`(i, j)` is a hop for exactly `C(N - 2, n - 1)` of the `n`-subsets, whether or not
`i` and `j` are neighbours.

## Not covered

* The operator identity `(H∞²)_{SS} = λ² M(S)` and the reduction from the spinful
  basis to `n`-subsets. This file proves the counting statement that the paper's
  theorem reduces to, not the statement about `H∞`.
-/

@[expose] public section

namespace HubbardMoments

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- There are `2|E|` directed edges. -/
theorem card_arcs : (arcs G).card = 2 * G.edgeFinset.card := by
  rw [← G.sum_degrees_eq_twice_card_edges, arcs, ← univ_product_univ, card_filter,
    sum_product]
  refine sum_congr rfl fun v _ => ?_
  rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter, card_filter]

/-- A fixed ordered pair of distinct vertices `(i, j)` has `i` occupied and `j` empty in
exactly `C(N - 2, n - 1)` of the `n`-subsets. -/
theorem card_occupied_empty {i j : V} (hij : i ≠ j) (n : ℕ) (hn : 1 ≤ n) :
    ((powersetCard n univ).filter (fun S => i ∈ S ∧ j ∉ S)).card =
      (Fintype.card V - 2).choose (n - 1) := by
  have h := card_trace_eq ({i, j} : Finset V) {i} (by simp) n (by simpa using hn)
  rw [card_pair_eq_two_iff.mpr hij, card_singleton] at h
  rw [← h]
  congr 1
  refine filter_congr fun S _ => ?_
  constructor
  · rintro ⟨hi, hj⟩
    ext a
    simp only [mem_inter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, ha⟩
      · rfl
      · exact absurd ha hj
    · rintro rfl
      exact ⟨Or.inl rfl, hi⟩
  · intro h
    have hi : i ∈ ({i, j} : Finset V) ∩ S := by
      rw [h]
      exact mem_singleton_self i
    have hj : j ∉ ({i, j} : Finset V) ∩ S := by
      rw [h, mem_singleton]
      exact hij.symm
    exact ⟨(mem_inter.mp hi).2, fun hjS => hj (mem_inter.mpr ⟨by simp, hjS⟩)⟩

/-- Summed over all `n`-subsets (`n ≥ 1`), the number of hops is the number of directed
edges times `C(N - 2, n - 1)`. -/
theorem sum_card_hops (n : ℕ) (hn : 1 ≤ n) :
    ∑ S ∈ powersetCard n (univ : Finset V), (hops G S).card =
      (arcs G).card * (Fintype.card V - 2).choose (n - 1) := by
  calc ∑ S ∈ powersetCard n (univ : Finset V), (hops G S).card
      = ∑ S ∈ powersetCard n (univ : Finset V),
          ∑ p ∈ arcs G, if p.1 ∈ S ∧ p.2 ∉ S then 1 else 0 := by
        simp only [hops, card_filter]
    _ = ∑ p ∈ arcs G, ∑ S ∈ powersetCard n (univ : Finset V),
          if p.1 ∈ S ∧ p.2 ∉ S then 1 else 0 := sum_comm
    _ = ∑ p ∈ arcs G,
          ((powersetCard n (univ : Finset V)).filter (fun S => p.1 ∈ S ∧ p.2 ∉ S)).card := by
        simp only [card_filter]
    _ = ∑ _p ∈ arcs G, (Fintype.card V - 2).choose (n - 1) := by
        refine sum_congr rfl fun p hp => ?_
        have hadj : G.Adj p.1 p.2 := (mem_filter.mp hp).2
        exact card_occupied_empty hadj.ne n hn
    _ = (arcs G).card * (Fintype.card V - 2).choose (n - 1) := by
        rw [sum_const, smul_eq_mul]

/-- The binomial identity `C(N - 2, n - 1) · N(N - 1) = n(N - n) · C(N, n)` for
`n ≥ 1`, which turns the count above into an average. -/
theorem choose_sub_two_mul (N n : ℕ) (hn : 1 ≤ n) :
    (N - 2).choose (n - 1) * (N * (N - 1)) = n * (N - n) * N.choose n := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  rcases Nat.lt_or_ge N 2 with hN | hN
  · interval_cases N
    · simp
    · cases r <;> simp
  · obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
    have h1 : (m + 1) * m.choose r = (m + 1).choose (r + 1) * (r + 1) :=
      Nat.add_one_mul_choose_eq m r
    have h2 : (m + 1).choose (r + 1) * (m + 2) = (m + 2).choose (r + 1) * (m + 2 - (r + 1)) :=
      Nat.choose_mul_succ_eq (m + 1) (r + 1)
    rw [show m + 2 - 2 = m by omega, show r + 1 - 1 = r by omega,
      show m + 2 - 1 = m + 1 by omega]
    calc m.choose r * ((m + 2) * (m + 1))
        = (m + 1) * m.choose r * (m + 2) := by ring
      _ = (m + 1).choose (r + 1) * (r + 1) * (m + 2) := by rw [h1]
      _ = (r + 1) * ((m + 1).choose (r + 1) * (m + 2)) := by ring
      _ = (r + 1) * ((m + 2).choose (r + 1) * (m + 2 - (r + 1))) := by rw [h2]
      _ = (r + 1) * (m + 2 - (r + 1)) * (m + 2).choose (r + 1) := by ring

/-- **The exact hop count.** For every `n` and every finite simple graph,
`(∑_S M(S)) · N(N - 1) = (number of directed edges) · n(N - n) · C(N, n)`. -/
theorem sum_card_hops_mul (n : ℕ) :
    (∑ S ∈ powersetCard n (univ : Finset V), (hops G S).card) *
        (Fintype.card V * (Fintype.card V - 1)) =
      (arcs G).card * (n * (Fintype.card V - n)) * (Fintype.card V).choose n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hops]
  · rw [sum_card_hops G n hn, mul_assoc, choose_sub_two_mul _ _ hn]
    ring

/-- **The average hop count.** For `n ≤ N` and `N ≥ 2`, the average of `M` over the
`C(N, n)` configurations is `2|E| · n(N - n) / (N(N - 1))`. -/
theorem average_card_hops (n : ℕ) (hn : n ≤ Fintype.card V) (hN : 2 ≤ Fintype.card V) :
    ((∑ S ∈ powersetCard n (univ : Finset V), (hops G S).card : ℕ) : ℚ) /
        (Fintype.card V).choose n =
      2 * G.edgeFinset.card * n * (Fintype.card V - n) /
        (Fintype.card V * (Fintype.card V - 1)) := by
  have hN' : (2 : ℚ) ≤ Fintype.card V := by exact_mod_cast hN
  have hC : ((Fintype.card V).choose n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hn).ne'
  have hD : (Fintype.card V : ℚ) * (Fintype.card V - 1) ≠ 0 := by
    apply mul_ne_zero <;> apply ne_of_gt <;> linarith
  rw [div_eq_div_iff hC hD]
  have h := congrArg (Nat.cast : ℕ → ℚ) (sum_card_hops_mul G n)
  rw [card_arcs] at h
  push_cast [Nat.cast_sub hn, Nat.cast_sub (by omega : 1 ≤ Fintype.card V)] at h ⊢
  linear_combination h

/-- On a `z`-regular graph the average hop count is `n z (N - n)/(N - 1)`. -/
theorem average_card_hops_regular {z : ℕ} (hz : G.IsRegularOfDegree z) (n : ℕ)
    (hn : n ≤ Fintype.card V) (hN : 2 ≤ Fintype.card V) :
    ((∑ S ∈ powersetCard n (univ : Finset V), (hops G S).card : ℕ) : ℚ) /
        (Fintype.card V).choose n =
      n * z * (Fintype.card V - n) / (Fintype.card V - 1) := by
  rw [average_card_hops G n hn hN]
  have hE : 2 * G.edgeFinset.card = Fintype.card V * z := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    simp [hz.degree_eq]
  have hE' : (2 * G.edgeFinset.card : ℚ) = Fintype.card V * z := by exact_mod_cast hE
  have hN' : (2 : ℚ) ≤ Fintype.card V := by exact_mod_cast hN
  have hN0 : (Fintype.card V : ℚ) ≠ 0 := by apply ne_of_gt; linarith
  have hN1 : (Fintype.card V : ℚ) - 1 ≠ 0 := by apply ne_of_gt; linarith
  rw [hE']
  field_simp

/-- On the `L × L` torus (`L ≥ 3`, `N = L²`, `z = 4`) the average hop count of `n`
particles is `4n(L² - n)/(L² - 1)`. -/
theorem average_card_hops_torus (L : ℕ) (hL : 3 ≤ L) (n : ℕ) (hn : n ≤ L * L) :
    ((∑ S ∈ powersetCard n (univ : Finset (Fin L × Fin L)), (hops (torus L) S).card : ℕ) : ℚ) /
        (L * L).choose n =
      4 * n * (L * L - n) / (L * L - 1) := by
  have hcard : Fintype.card (Fin L × Fin L) = L * L := by simp
  -- `convert` identifies the two finiteness instances for the neighbour sets of the
  -- torus (box-product and generic); they are equal because `Fintype` is a subsingleton.
  have h := average_card_hops_regular (torus L) (by convert torus_isRegularOfDegree L hL) n
    (by rw [hcard]; exact hn) (by rw [hcard]; nlinarith)
  rw [hcard] at h
  push_cast at h ⊢
  rw [h]
  ring

/-- `L = 4`, `n = 4`: the average hop count is `64/5 = 12.8`. -/
theorem average_card_hops_torus_L4_n4 :
    ((∑ S ∈ powersetCard 4 (univ : Finset (Fin 4 × Fin 4)), (hops (torus 4) S).card : ℕ) : ℚ) /
        (4 * 4).choose 4 = 64 / 5 := by
  rw [average_card_hops_torus 4 (by norm_num) 4 (by norm_num)]
  norm_num

/-- `L = 5`, `n = 4`: the average hop count is `14`. -/
theorem average_card_hops_torus_L5_n4 :
    ((∑ S ∈ powersetCard 4 (univ : Finset (Fin 5 × Fin 5)), (hops (torus 5) S).card : ℕ) : ℚ) /
        (5 * 5).choose 4 = 14 := by
  rw [average_card_hops_torus 5 (by norm_num) 4 (by norm_num)]
  norm_num

end HubbardMoments
