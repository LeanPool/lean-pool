/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.Average.Iterate

/-!
# The influences of a function with rows of bounded cost

Let `f` have a row of cost at most `K` at every point and `V = Var f > 0`. Let
`L = L(f) = ∑_k L_k(f)` be the sum of the mean absolute increments (it is positive, by the bound
for the mean absolute increments) and `R = {j : 5 L · Inf_j f < 2 V · L_j f}` (the coordinates
whose influence is small compared with the mean absolute increment). Then
`∑_{j ∈ R} Inf_j f ≤ (2/5) V`, so the average `g` of `f` over the coordinates of `R`
(`Average.exists_avg_set`) has `Var g ≥ (3/5) V`. The bound for the mean absolute increments,
applied to `g`, gives `j` with `Var(g)^3 ≤ 36 K^4 L_j(g)²` and `L_j(g) > 0`; so `j ∉ R`, and
`2 V L_j(g) ≤ 2 V L_j(f) ≤ 5 L · Inf_j f`. Together (Theorem 8.3 of the paper):

`3 V^5 ≤ 3125 L(f)² K^4 (Inf_j f)²`
(`influence_of_meanIncrement : MeanIncrementBound → InfluenceBound`),

that is, `Inf_j f ≥ (√15 / 125) · V^{5/2} / (L(f) K²)`.

Further statements of this file:

* `Average.sum_meanAbsIncr_pos` — `L(f) > 0` (and `L(f) ≤ K` is
  `Level.sum_meanAbsIncr_le_cost`);
* `Average.influence_of_incr` — if `∑_j |f(u) - f(u^j)| ≤ G` at every point `u`, then
  `L(f) ≤ G` and `3 V^5 ≤ 3125 G² K^4 (Inf_j f)²`;
* `Average.influence_cost` — in particular, since `L(f) ≤ K`: `3 V^5 ≤ 3125 K^6 (Inf_j f)²`;
* `Average.exists_inflR_ge_sqrt` — the bound for the influences with the power `5/2` written as
  `V² · √V`: `√15 V^{5/2} ≤ 125 L(f) K² Inf_j f` (the two forms are equivalent:
  `Average.pow_le_iff_sqrt_mul_le`).
-/

@[expose] public section

namespace AaronsonAmbainis

open Finset

namespace Average

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The bound for the mean absolute increments, with the positivity of the increment that it
gives. -/
lemma exists_meanAbsIncr_pos (hMI : MeanIncrementBound) (g : Cube ι → ℝ) (b : Cube ι → ι → ℝ)
    {K : ℝ} (hb0 : ∀ x i, 0 ≤ b x i) (hbK : ∀ x, ∑ i, b x i ≤ K)
    (hbrow : ∀ x y, |g x - g y| ≤ ∑ i ∈ diffSet x y, b x i) (hg : 0 < variance g) :
    ∃ j, 0 < meanAbsIncr g j ∧ variance g ^ 3 ≤ 36 * K ^ 4 * meanAbsIncr g j ^ 2 := by
  obtain ⟨j, hj⟩ := hMI ι g K b hb0 hbK hbrow hg
  refine ⟨j, ?_, hj⟩
  by_contra h
  have h0 : meanAbsIncr g j = 0 := le_antisymm (not_lt.mp h) (Level.meanAbsIncr_nonneg g j)
  have h3 : 0 < variance g ^ 3 := pow_pos hg 3
  have e : 36 * K ^ 4 * (0 : ℝ) ^ 2 = 0 := by ring
  rw [h0, e] at hj
  linarith

/-- The sum `L(f)` of the mean absolute increments of a function with rows of cost at most `K`
and positive variance is positive. -/
lemma sum_meanAbsIncr_pos (hMI : MeanIncrementBound) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    {K : ℝ} (ha : ∀ x i, 0 ≤ a x i) (hsum : ∀ x, ∑ i, a x i ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i) (hvar : 0 < variance f) :
    0 < ∑ k, meanAbsIncr f k := by
  obtain ⟨j0, hj0, -⟩ := exists_meanAbsIncr_pos hMI f a ha hsum hrow hvar
  exact lt_of_lt_of_le hj0 (Finset.single_le_sum (f := meanAbsIncr f)
    (fun k _ => Level.meanAbsIncr_nonneg f k) (Finset.mem_univ j0))

end Average

/-- The bound for the influences (Theorem 8.3 of the paper) from the bound for the mean absolute
increments (Theorem 7.10): if `f` has a row of cost at most `K` at every point and `Var f > 0`,
then some coordinate `j` has `3 Var(f)^5 ≤ 3125 L(f)² K^4 (Inf_j f)²`, where
`L(f) = ∑_k L_k(f)`. -/
theorem influence_of_meanIncrement : MeanIncrementBound → InfluenceBound := by
  intro hMI ι _ _ f K a ha hsum hrow hvar
  classical
  -- the sum `L` of the mean absolute increments is positive
  have hLpos : 0 < ∑ k, meanAbsIncr f k :=
    Average.sum_meanAbsIncr_pos hMI f a ha hsum hrow hvar
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = variance f := ⟨_, rfl⟩
  obtain ⟨L, hLf⟩ : ∃ L : ℝ, L = ∑ k, meanAbsIncr f k := ⟨_, rfl⟩
  rw [← hV] at hvar
  rw [← hLf] at hLpos
  rw [← hV, ← hLf]
  -- the average over the coordinates of small influence
  obtain ⟨g, b, hb0, hbK, hbrow, hvarg, -, hL1, hzero⟩ := Average.exists_avg_set f a ha hsum hrow
    (univ.filter (fun j => 5 * L * inflR f j < 2 * V * meanAbsIncr f j))
  rw [← hV] at hvarg
  have h5 : 5 * L * ∑ j ∈ univ.filter (fun j => 5 * L * inflR f j < 2 * V * meanAbsIncr f j),
      inflR f j ≤ 2 * V * L := by
    rw [Finset.mul_sum]
    calc ∑ j ∈ univ.filter (fun j => 5 * L * inflR f j < 2 * V * meanAbsIncr f j),
          5 * L * inflR f j
        ≤ ∑ j ∈ univ.filter (fun j => 5 * L * inflR f j < 2 * V * meanAbsIncr f j),
          2 * V * meanAbsIncr f j :=
          Finset.sum_le_sum (fun j hj => (Finset.mem_filter.mp hj).2.le)
      _ ≤ ∑ j, 2 * V * meanAbsIncr f j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun j _ _ => mul_nonneg (mul_nonneg (by norm_num) hvar.le)
              (Level.meanAbsIncr_nonneg f j))
      _ = 2 * V * L := by rw [← Finset.mul_sum, hLf]
  have hsumR : 5 * ∑ j ∈ univ.filter
      (fun j => 5 * L * inflR f j < 2 * V * meanAbsIncr f j), inflR f j ≤ 2 * V := by
    have h6 : L * (5 * ∑ j ∈ univ.filter
        (fun j => 5 * L * inflR f j < 2 * V * meanAbsIncr f j), inflR f j)
        ≤ L * (2 * V) := by linarith
    exact le_of_mul_le_mul_left h6 hLpos
  have hVg : 3 / 5 * V ≤ variance g := by linarith
  -- the bound for the mean absolute increments of the average
  obtain ⟨j, hgj, hj⟩ :=
    Average.exists_meanAbsIncr_pos hMI g b hb0 hbK hbrow (by linarith : 0 < variance g)
  refine ⟨j, ?_⟩
  have hjR : j ∉ univ.filter (fun j => 5 * L * inflR f j < 2 * V * meanAbsIncr f j) := by
    intro h
    rw [hzero j h] at hgj
    exact lt_irrefl 0 hgj
  have h4 : 2 * V * meanAbsIncr f j ≤ 5 * L * inflR f j := by
    by_contra h
    exact hjR (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_le.mp h⟩)
  have h2V : (0 : ℝ) ≤ 2 * V := by linarith
  have h7 : 2 * V * meanAbsIncr g j ≤ 5 * L * inflR f j :=
    le_trans (mul_le_mul_of_nonneg_left (hL1 j) h2V) h4
  have h8 : (2 * V * meanAbsIncr g j) ^ 2 ≤ (5 * L * inflR f j) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg h2V hgj.le) h7 2
  have h9 : (3 / 5 * V) ^ 3 ≤ 36 * K ^ 4 * meanAbsIncr g j ^ 2 :=
    le_trans (pow_le_pow_left₀ (by linarith) hVg 3) hj
  have hK4 : (0 : ℝ) ≤ 36 * K ^ 4 := by positivity
  calc 3 * V ^ 5 = 125 / 36 * ((3 / 5 * V) ^ 3 * (2 * V) ^ 2) := by ring
    _ ≤ 125 / 36 * (36 * K ^ 4 * meanAbsIncr g j ^ 2 * (2 * V) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h9 (sq_nonneg _)) (by norm_num)
    _ = 125 / 36 * (36 * K ^ 4 * (2 * V * meanAbsIncr g j) ^ 2) := by ring
    _ ≤ 125 / 36 * (36 * K ^ 4 * (5 * L * inflR f j) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h8 hK4) (by norm_num)
    _ = 3125 * L ^ 2 * K ^ 4 * inflR f j ^ 2 := by ring

namespace Average

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The bound for the influences with a bound `G` for the sums of the increments at the points:
`3 Var(f)^5 ≤ 3125 G² K^4 (Inf_j f)²`. -/
theorem influence_of_incr (hI : InfluenceBound) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ) {K G : ℝ}
    (ha : ∀ x i, 0 ≤ a x i) (hsum : ∀ x, ∑ i, a x i ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i)
    (hG : ∀ u, ∑ j, |f u - f (flipSet u {j})| ≤ G) (hvar : 0 < variance f) :
    ∃ j, 3 * variance f ^ 5 ≤ 3125 * G ^ 2 * K ^ 4 * inflR f j ^ 2 := by
  obtain ⟨j, hj⟩ := hI ι f K a ha hsum hrow hvar
  refine ⟨j, le_trans hj ?_⟩
  have hL0 : 0 ≤ ∑ k, meanAbsIncr f k :=
    Finset.sum_nonneg fun k _ => Level.meanAbsIncr_nonneg f k
  have hL2 : (∑ k, meanAbsIncr f k) ^ 2 ≤ G ^ 2 :=
    pow_le_pow_left₀ hL0 (Level.sum_meanAbsIncr_le f hG) 2
  have hX : 0 ≤ K ^ 4 * inflR f j ^ 2 := by positivity
  have h := mul_le_mul_of_nonneg_right hL2 hX
  linarith

/-- The bound for the influences in terms of the cost alone: if `f` has a row of cost at most
`K` at every point and `Var f > 0`, then some coordinate `j` has
`3 Var(f)^5 ≤ 3125 K^6 (Inf_j f)²`. -/
theorem influence_cost (hI : InfluenceBound) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ) {K : ℝ}
    (ha : ∀ x i, 0 ≤ a x i) (hsum : ∀ x, ∑ i, a x i ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i) (hvar : 0 < variance f) :
    ∃ j, 3 * variance f ^ 5 ≤ 3125 * K ^ 6 * inflR f j ^ 2 := by
  obtain ⟨j, hj⟩ := influence_of_incr hI f a ha hsum hrow
    (Level.sum_abs_incr_le_of_rows hsum hrow) hvar
  refine ⟨j, le_trans hj (le_of_eq ?_)⟩
  ring

/-- For `V, L, I ≥ 0`: `3 V^5 ≤ 3125 L² K^4 I²` if and only if `√15 V^{5/2} ≤ 125 L K² I`, where
`V^{5/2}` is written `V² · √V`. -/
theorem pow_le_iff_sqrt_mul_le {V L K I : ℝ} (hV : 0 ≤ V) (hL : 0 ≤ L) (hI : 0 ≤ I) :
    3 * V ^ 5 ≤ 3125 * L ^ 2 * K ^ 4 * I ^ 2
      ↔ Real.sqrt 15 * (V ^ 2 * Real.sqrt V) ≤ 125 * L * K ^ 2 * I := by
  have ha : 0 ≤ Real.sqrt 15 * (V ^ 2 * Real.sqrt V) := by positivity
  have hb : 0 ≤ 125 * L * K ^ 2 * I :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) (sq_nonneg K)) hI
  have e1 : (Real.sqrt 15 * (V ^ 2 * Real.sqrt V)) ^ 2 = 15 * V ^ 5 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15), Real.sq_sqrt hV]
    ring
  have e2 : (125 * L * K ^ 2 * I) ^ 2 = 5 * (3125 * L ^ 2 * K ^ 4 * I ^ 2) := by ring
  constructor
  · intro h
    apply le_of_pow_le_pow_left₀ two_ne_zero hb
    rw [e1, e2]
    linarith
  · intro h
    have h2 := pow_le_pow_left₀ ha h 2
    rw [e1, e2] at h2
    linarith

/-- The bound for the influences with the power `5/2` written as `Var² · √Var`: some coordinate
`j` has `√15 Var(f)^{5/2} ≤ 125 L(f) K² Inf_j(f)`, that is,
`Inf_j(f) ≥ (√15 / 125) Var(f)^{5/2} / (L(f) K²)`, where `L(f) = ∑_k L_k(f)`. -/
theorem exists_inflR_ge_sqrt (hI : InfluenceBound) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    {K : ℝ} (ha : ∀ x i, 0 ≤ a x i) (hsum : ∀ x, ∑ i, a x i ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i) (hvar : 0 < variance f) :
    ∃ j, Real.sqrt 15 * (variance f ^ 2 * Real.sqrt (variance f))
      ≤ 125 * (∑ k, meanAbsIncr f k) * K ^ 2 * inflR f j := by
  obtain ⟨j, hj⟩ := hI ι f K a ha hsum hrow hvar
  exact ⟨j, (pow_le_iff_sqrt_mul_le hvar.le
    (Finset.sum_nonneg fun k _ => Level.meanAbsIncr_nonneg f k) (Level.inflR_nonneg f j)).mp hj⟩

end Average

end AaronsonAmbainis
