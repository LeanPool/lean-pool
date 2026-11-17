/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
import LeanPool.GraphExtremal.Extremal.WeightShifting
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The Motzkin–Straus theorem

For a finite graph `G` with clique number `ω`, the maximum of the quadratic form
`p ⬝ᵥ G.adjMatrix ℝ *ᵥ p = ∑_{x ~ y} p x * p y` (a sum over ordered adjacent pairs) over the
standard simplex is `1 - 1 / ω`. It is attained by the uniform weighting of a maximum clique.
This gives a proof of Turán's theorem, and its weighted form drives many extremal arguments.

## Main statements

* `SimpleGraph.dotProduct_adjMatrix_mulVec_le`: if `G` has no `(r + 1)`-clique, then
  `p ⬝ᵥ G.adjMatrix ℝ *ᵥ p ≤ (1 - 1 / r) * (∑ i, p i) ^ 2` for all `p ≥ 0`.
* `SimpleGraph.dotProduct_adjMatrix_mulVec_cliqueWeight`: equality for the uniform weighting of an
  `r`-clique.
* `SimpleGraph.isGreatest_dotProduct_adjMatrix_mulVec`: the maximum over the standard simplex is
  `1 - 1 / G.cliqueNum`.
* `SimpleGraph.card_edgeFinset_le_of_cliqueFree`: Turán's theorem, from the uniform weighting: a
  graph on `n` vertices with no `(r + 1)`-clique has at most `(1 - 1 / r) * n ^ 2 / 2` edges.
  `SimpleGraph.four_mul_card_edgeFinset_le_of_cliqueFree_three` is Mantel's theorem.

## Implementation notes

The quadratic form is affine along every direction `Pi.single u 1 - Pi.single v 1` with `u ≠ v`
non-adjacent, so `SimpleGraph.exists_isClique_support_le_of_affine` reduces the bound to weightings
supported on a clique, where it is the Cauchy–Schwarz inequality.

## References

* [T. S. Motzkin, E. G. Straus,
  *Maxima for graphs and a new proof of a theorem of Turán*][MotzkinStraus1965]
* [P. Turán, *Eine Extremalaufgabe aus der Graphentheorie*][Turan1941]
* [W. Mantel, *Vraagstuk XXVIII*][Mantel1907]
-/

@[expose] public section

open Finset Matrix

namespace SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The adjacency quadratic form is the sum of `p x * p y` over ordered adjacent pairs. -/
theorem dotProduct_adjMatrix_mulVec (p : V → ℝ) :
    p ⬝ᵥ G.adjMatrix ℝ *ᵥ p = ∑ x, ∑ y, if G.Adj x y then p x * p y else 0 := by
  simp only [dotProduct, mulVec, adjMatrix_apply, mul_sum]
  refine sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ ?_
  split_ifs <;> ring

/-- The adjacency quadratic form is symmetric as a bilinear form. -/
private theorem dotProduct_adjMatrix_mulVec_comm (x y : V → ℝ) :
    x ⬝ᵥ G.adjMatrix ℝ *ᵥ y = y ⬝ᵥ G.adjMatrix ℝ *ᵥ x := by
  rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, transpose_adjMatrix]

/-- Along a direction `Pi.single u 1 - Pi.single v 1` with `u, v` non-adjacent, the adjacency
quadratic form is affine. -/
theorem dotProduct_adjMatrix_mulVec_add_smul [DecidableEq V] {u v : V} (hnadj : ¬ G.Adj u v)
    (p : V → ℝ) (t : ℝ) :
    (p + t • (Pi.single u 1 - Pi.single v 1)) ⬝ᵥ
        G.adjMatrix ℝ *ᵥ (p + t • (Pi.single u 1 - Pi.single v 1)) =
      p ⬝ᵥ G.adjMatrix ℝ *ᵥ p +
        2 * ((Pi.single u 1 - Pi.single v 1) ⬝ᵥ G.adjMatrix ℝ *ᵥ p) * t := by
  set d : V → ℝ := Pi.single u 1 - Pi.single v 1
  have hdd : d ⬝ᵥ G.adjMatrix ℝ *ᵥ d = 0 := by
    have hvu : ¬ G.Adj v u := fun h ↦ hnadj h.symm
    simp [d, mulVec_sub, sub_dotProduct, dotProduct_sub, adjMatrix_apply, hnadj, hvu]
  rw [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, dotProduct_add, smul_dotProduct,
    smul_dotProduct, dotProduct_smul, dotProduct_smul, hdd, dotProduct_adjMatrix_mulVec_comm G p d]
  simp only [smul_eq_mul]
  ring

/-- On a weighting supported on a clique, the adjacency quadratic form is
`(∑ i, q i) ^ 2 - ∑ i, q i ^ 2`. -/
theorem dotProduct_adjMatrix_mulVec_of_isClique {q : V → ℝ}
    (hq : G.IsClique (Function.support q)) :
    q ⬝ᵥ G.adjMatrix ℝ *ᵥ q = (∑ i, q i) ^ 2 - ∑ i, q i ^ 2 := by
  classical
  have hpair : ∀ x y, (if G.Adj x y then q x * q y else 0) =
      q x * q y - if x = y then q x * q y else 0 := by
    intro x y
    by_cases hxy : x = y
    · subst hxy; simp
    · by_cases h0 : q x * q y = 0
      · simp [h0]
      · have hadj : G.Adj x y := hq (left_ne_zero_of_mul h0) (right_ne_zero_of_mul h0) hxy
        simp [hadj, hxy]
  rw [dotProduct_adjMatrix_mulVec]
  simp only [hpair, sum_sub_distrib, sum_ite_eq, mem_univ, ↓reduceIte, ← mul_sum, ← sum_mul, sq]

omit [DecidableRel G.Adj] in
/-- The support of a weighting supported on a clique has at most `r` elements when `G` has no
`(r + 1)`-clique. -/
private theorem card_support_le {r : ℕ} (hG : G.CliqueFree (r + 1)) {q : V → ℝ}
    (hq : G.IsClique (Function.support q)) : #{i | q i ≠ 0} ≤ r := by
  by_contra! h
  obtain ⟨t, hts, htc⟩ := exists_subset_card_eq (show r + 1 ≤ #{i | q i ≠ 0} by omega)
  refine hG t ⟨hq.subset fun x hx ↦ ?_, htc⟩
  simpa using (mem_filter.1 (hts hx)).2

/-- **Motzkin–Straus**, upper bound. If `G` has no `(r + 1)`-clique, then
`p ⬝ᵥ G.adjMatrix ℝ *ᵥ p ≤ (1 - 1 / r) * (∑ i, p i) ^ 2` for every nonnegative weighting `p`. -/
theorem dotProduct_adjMatrix_mulVec_le {r : ℕ} (hG : G.CliqueFree (r + 1)) {p : V → ℝ}
    (hp : 0 ≤ p) : p ⬝ᵥ G.adjMatrix ℝ *ᵥ p ≤ (1 - 1 / r) * (∑ i, p i) ^ 2 := by
  classical
  obtain ⟨q, -, hsum, -, hcl, hpq⟩ := exists_isClique_support_le_of_affine
    (f := fun p ↦ p ⬝ᵥ G.adjMatrix ℝ *ᵥ p)
    (fun _ _ _ hnadj p ↦ ⟨_, dotProduct_adjMatrix_mulVec_add_smul G hnadj p⟩) hp
  refine hpq.trans ?_
  rw [dotProduct_adjMatrix_mulVec_of_isClique G hcl, ← hsum]
  -- Cauchy–Schwarz on the support, which has at most `r` elements
  have hcs : (∑ i, q i) ^ 2 ≤ r * ∑ i, q i ^ 2 := by
    rw [← sum_filter_ne_zero, ← sum_filter_of_ne (s := univ) (f := fun i ↦ q i ^ 2)
      (p := fun i ↦ q i ≠ 0) fun i _ h ↦ by simpa using h]
    exact sq_sum_le_card_mul_sum_sq.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast card_support_le G hG hcl) (sum_nonneg fun i _ ↦ sq_nonneg _))
  have : (∑ i, q i) ^ 2 / r ≤ ∑ i, q i ^ 2 :=
    div_le_of_le_mul₀ r.cast_nonneg (sum_nonneg fun i _ ↦ sq_nonneg _) (by linarith)
  linarith [show (1 - 1 / (r : ℝ)) * (∑ i, q i) ^ 2 = (∑ i, q i) ^ 2 - (∑ i, q i) ^ 2 / r by ring]

/-- The uniform weighting `1 / r` on a finite set `s`, and `0` elsewhere. -/
noncomputable def uniformWeight [DecidableEq V] (s : Finset V) (r : ℕ) : V → ℝ :=
  fun i ↦ if i ∈ s then 1 / r else 0

/-- **Motzkin–Straus**, equality case. The uniform weighting of an `r`-clique, `r ≥ 1`, is a
probability vector and gives the value `1 - 1 / r`. -/
theorem dotProduct_adjMatrix_mulVec_cliqueWeight [DecidableEq V] {r : ℕ} (hr : r ≠ 0)
    {s : Finset V}
    (hs : G.IsNClique r s) :
    0 ≤ uniformWeight s r ∧ ∑ i, uniformWeight s r i = 1 ∧
      uniformWeight s r ⬝ᵥ G.adjMatrix ℝ *ᵥ uniformWeight s r = 1 - 1 / r := by
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
  have hsum : ∑ i, uniformWeight s r i = 1 := by
    simp only [uniformWeight, sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul, hs.card_eq]
    field_simp
  have hsupp : Function.support (uniformWeight s r) = s := by
    ext i; simp [uniformWeight, hr']
  refine ⟨fun i ↦ ?_, hsum, ?_⟩
  · unfold uniformWeight; split_ifs <;> positivity
  · rw [dotProduct_adjMatrix_mulVec_of_isClique G (hsupp ▸ hs.isClique), hsum]
    have : ∑ i, uniformWeight s r i ^ 2 = 1 / r := by
      simp only [uniformWeight, ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul, hs.card_eq]
      field_simp
    rw [this]; ring

/-- **The Motzkin–Straus theorem.** For a nonempty finite graph, the maximum of the adjacency
quadratic form over the standard simplex `{p | 0 ≤ p ∧ ∑ i, p i = 1}` is `1 - 1 / G.cliqueNum`. -/
theorem isGreatest_dotProduct_adjMatrix_mulVec [Nonempty V] :
    IsGreatest ((fun p ↦ p ⬝ᵥ G.adjMatrix ℝ *ᵥ p) '' {p | 0 ≤ p ∧ ∑ i, p i = 1})
      (1 - 1 / G.cliqueNum) := by
  classical
  have hfree : G.CliqueFree (G.cliqueNum + 1) := fun t ht ↦ by
    have := IsClique.card_le_cliqueNum (G := G) (t := t) (tc := ht.isClique)
    rw [ht.card_eq] at this
    omega
  have hω : G.cliqueNum ≠ 0 := fun h0 ↦
    not_isEmpty_of_nonempty V (cliqueFree_one.1 (h0 ▸ hfree))
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  obtain ⟨hnonneg, hone, heq⟩ := dotProduct_adjMatrix_mulVec_cliqueWeight G hω hs
  refine ⟨⟨_, ⟨hnonneg, hone⟩, heq⟩, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  simpa [hp.2] using G.dotProduct_adjMatrix_mulVec_le hfree hp.1

/-! ### Turán's theorem -/

/-- The adjacency quadratic form of the all-ones weighting counts every edge twice. -/
theorem one_dotProduct_adjMatrix_mulVec_one :
    (1 : V → ℝ) ⬝ᵥ G.adjMatrix ℝ *ᵥ 1 = 2 * #G.edgeFinset := by
  classical
  rw [dotProduct_adjMatrix_mulVec]
  simp only [Pi.one_apply, mul_one, sum_boole, ← neighborFinset_eq_filter,
    card_neighborFinset_eq_degree]
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

/-- **Turán's theorem**, deduced from Motzkin–Straus: a graph on `n` vertices with no
`(r + 1)`-clique has at most `(1 - 1 / r) * n ^ 2 / 2` edges. Mathlib's
`SimpleGraph.CliqueFree.card_edgeFinset_le` is the exact bound, by the Turán number. -/
theorem card_edgeFinset_le_of_cliqueFree {r : ℕ} (hG : G.CliqueFree (r + 1)) :
    (#G.edgeFinset : ℝ) ≤ (1 - 1 / r) * Fintype.card V ^ 2 / 2 := by
  have h := G.dotProduct_adjMatrix_mulVec_le hG (p := 1) zero_le_one
  rw [one_dotProduct_adjMatrix_mulVec_one] at h
  simp only [Pi.one_apply, sum_const, card_univ, nsmul_eq_mul, mul_one] at h
  linarith

/-- **Mantel's theorem**: a triangle-free graph on `n` vertices has at most `n ^ 2 / 4` edges. -/
theorem four_mul_card_edgeFinset_le_of_cliqueFree_three (hG : G.CliqueFree 3) :
    4 * #G.edgeFinset ≤ Fintype.card V ^ 2 := by
  have h := G.card_edgeFinset_le_of_cliqueFree (r := 2) hG
  have h' : (4 * #G.edgeFinset : ℝ) ≤ Fintype.card V ^ 2 := by norm_num at h; linarith
  exact_mod_cast h'

end SimpleGraph
