/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Basic.Real.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Shifting weight along non-edges

Let `f` be a function of vertex weights `p : V → ℝ` that is convex along every line
`t ↦ p + t • (Pi.single u 1 - Pi.single v 1)` with `u ≠ v` non-adjacent. Moving all the weight of
`v` onto `u`, or all the weight of `u` onto `v`, does not decrease `f` for one of the two choices.
Repeating this, every nonnegative weighting can be replaced by one supported on a clique, with the
same total weight, a smaller support and a value of `f` at least as large.

This is the weight-shifting argument of Motzkin and Straus. Both of its classical applications
need only functions that are affine along these lines: the quadratic form of the adjacency matrix
(the Motzkin–Straus theorem, `SimpleGraph.dotProduct_adjMatrix_mulVec_le`) and the weighted
clique count (Zykov's bound, `SimpleGraph.cliqueWeight_le`).

## Main statements

* `SimpleGraph.exists_isClique_support_le`: the shifting lemma for convex `f`.
* `SimpleGraph.exists_isClique_support_le_of_affine`: the same for `f` affine along each line.

## References

* [T. S. Motzkin, E. G. Straus,
  *Maxima for graphs and a new proof of a theorem of Turán*][MotzkinStraus1965]
-/

@[expose] public section

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Moving the weight `p v` from `v` to `u` keeps the weights nonnegative and the total weight
fixed, and shrinks the support. -/
private theorem shift_spec {p : V → ℝ} (hp : 0 ≤ p) {u v : V} (huv : u ≠ v) (hu : p u ≠ 0)
    (hv : p v ≠ 0) :
    0 ≤ p + p v • (Pi.single u 1 - Pi.single v 1 : V → ℝ) ∧
      ∑ i, (p + p v • (Pi.single u 1 - Pi.single v 1 : V → ℝ)) i = ∑ i, p i ∧
      Function.support (p + p v • (Pi.single u 1 - Pi.single v 1 : V → ℝ)) ⊆ Function.support p ∧
      #{i | (p + p v • (Pi.single u 1 - Pi.single v 1 : V → ℝ)) i ≠ 0} < #{i | p i ≠ 0} := by
  have hval : ∀ i, (p + p v • (Pi.single u 1 - Pi.single v 1 : V → ℝ)) i =
      if i = u then p u + p v else if i = v then 0 else p i := fun i ↦ by
    rcases eq_or_ne i u with rfl | hiu
    · simp [huv]
    rcases eq_or_ne i v with rfl | hiv <;> simp [*]
  have hsub : ∀ i, (p + p v • (Pi.single u 1 - Pi.single v 1 : V → ℝ)) i ≠ 0 → p i ≠ 0 :=
    fun i hi ↦ by
      rw [hval] at hi
      split_ifs at hi with h1 h2
      exacts [h1 ▸ hu, absurd rfl hi, hi]
  refine ⟨fun i ↦ ?_, by simp [sum_add_distrib, ← mul_sum, sum_sub_distrib], fun i ↦ hsub i,
    card_lt_card ⟨fun i hi ↦ by simpa using hsub i (by simpa using hi), fun h ↦ ?_⟩⟩
  · rw [hval]
    split_ifs
    exacts [add_nonneg (hp u) (hp v), le_rfl, hp i]
  · have := h (mem_filter.2 ⟨mem_univ v, hv⟩)
    simp [hval, huv.symm] at this

/-- **Weight shifting.** If `f` is convex along every line `t ↦ p + t • (Pi.single u 1 -
Pi.single v 1)` with `u ≠ v` non-adjacent, then every nonnegative weighting `p` is dominated by a
nonnegative weighting `q` with the same total weight, supported on a clique inside the support of
`p`. -/
theorem exists_isClique_support_le {f : (V → ℝ) → ℝ}
    (hf : ∀ ⦃u v : V⦄, u ≠ v → ¬ G.Adj u v → ∀ p : V → ℝ,
      ConvexOn ℝ Set.univ fun t : ℝ ↦ f (p + t • (Pi.single u 1 - Pi.single v 1)))
    {p : V → ℝ} (hp : 0 ≤ p) :
    ∃ q : V → ℝ, 0 ≤ q ∧ ∑ i, q i = ∑ i, p i ∧ Function.support q ⊆ Function.support p ∧
      G.IsClique (Function.support q) ∧ f p ≤ f q := by
  induction hn : #{i | p i ≠ 0} using Nat.strong_induction_on generalizing p with
  | _ n ih =>
  by_cases hcl : G.IsClique (Function.support p)
  · exact ⟨p, hp, rfl, subset_rfl, hcl, le_rfl⟩
  obtain ⟨u, hu, v, hv, huv, hnadj⟩ :
      ∃ u ∈ Function.support p, ∃ v ∈ Function.support p, u ≠ v ∧ ¬ G.Adj u v := by
    by_contra! H
    exact hcl fun a ha b hb hab ↦ H a ha b hb hab
  rw [Function.mem_support] at hu hv
  have hpu : 0 < p u := (hp u).lt_of_ne' hu
  have hpv : 0 < p v := (hp v).lt_of_ne' hv
  -- `t = 0` lies between the two endpoints `t = -p u` and `t = p v`
  have hmax := (hf huv hnadj p).le_on_segment (Set.mem_univ (-p u)) (Set.mem_univ (p v))
    (show (0 : ℝ) ∈ segment ℝ (-p u) (p v) by
      rw [segment_eq_Icc (by linarith)]; constructor <;> linarith)
  simp only [zero_smul, add_zero] at hmax
  -- the endpoint `t = -p u` moves the weight of `u` onto `v`
  have hswap : p + (-p u) • (Pi.single u 1 - Pi.single v 1 : V → ℝ) =
      p + p u • (Pi.single v 1 - Pi.single u 1 : V → ℝ) := by
    ext i; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  rw [hswap] at hmax
  have descend : ∀ q : V → ℝ, 0 ≤ q → ∑ i, q i = ∑ i, p i →
      Function.support q ⊆ Function.support p →
      #{i | q i ≠ 0} < n → f p ≤ f q →
      ∃ q : V → ℝ, 0 ≤ q ∧ ∑ i, q i = ∑ i, p i ∧ Function.support q ⊆ Function.support p ∧
        G.IsClique (Function.support q) ∧ f p ≤ f q := by
    intro q hq hsum hsupp hcard hfq
    obtain ⟨r, hr, hrsum, hrsupp, hrcl, hfr⟩ := ih _ hcard hq rfl
    exact ⟨r, hr, hrsum.trans hsum, hrsupp.trans hsupp, hrcl, hfq.trans hfr⟩
  rcases le_max_iff.1 hmax with h | h
  · obtain ⟨hq, hsum, hsupp, hcard⟩ := shift_spec hp huv.symm hv hu
    exact descend _ hq hsum hsupp (hn ▸ hcard) h
  · obtain ⟨hq, hsum, hsupp, hcard⟩ := shift_spec hp huv hu hv
    exact descend _ hq hsum hsupp (hn ▸ hcard) h

/-- **Weight shifting, affine form.** If `f` is affine along every line `t ↦ p + t • (Pi.single u 1
- Pi.single v 1)` with `u ≠ v` non-adjacent, then every nonnegative weighting `p` is dominated by a
nonnegative weighting `q` with the same total weight, supported on a clique inside the support of
`p`. -/
theorem exists_isClique_support_le_of_affine {f : (V → ℝ) → ℝ}
    (hf : ∀ ⦃u v : V⦄, u ≠ v → ¬ G.Adj u v → ∀ p : V → ℝ, ∃ c : ℝ, ∀ t : ℝ,
      f (p + t • (Pi.single u 1 - Pi.single v 1)) = f p + c * t)
    {p : V → ℝ} (hp : 0 ≤ p) :
    ∃ q : V → ℝ, 0 ≤ q ∧ ∑ i, q i = ∑ i, p i ∧ Function.support q ⊆ Function.support p ∧
      G.IsClique (Function.support q) ∧ f p ≤ f q := by
  refine exists_isClique_support_le (fun u v huv hnadj p ↦ ?_) hp
  obtain ⟨c, hc⟩ := hf huv hnadj p
  have : (fun t : ℝ ↦ f (p + t • (Pi.single u 1 - Pi.single v 1))) =
      fun t ↦ f p + (LinearMap.mulLeft ℝ c) t := funext fun t ↦ by simp [hc]
  rw [this]
  exact (convexOn_const _ convex_univ).add ((LinearMap.mulLeft ℝ c).convexOn convex_univ)

end SimpleGraph
