/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.DiscreteLayerCake
public import LeanPool.DistinctDistances.ThinAnnulus
public import LeanPool.DistinctDistances.PalettePairCounting
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The centroid defect identity and its Riemann bounds

Formalizes the identity (AB0) of Lemma AB in
`docs/results/explicit-constant-gain-2-89-2026-10-20.md` (§2) and the two Riemann bounds
that give the case rows CASElo and CASEhi of §3, step 4 of that file (the families `CASElo`
and `CASEhi` of `scripts/verify_constant_gain_1_40.py`, built from `int_rhoX`).

Let `c` be the centroid of the configuration, `ρ² = distanceAnnulusRadiusSq p`, `D` the number
of ordered distance values and `Q = 3D - n + 1`. Write `d_r(i)` for the number of points at
distance `r` from `p i`, `R(t)` for the number of palette values `r` with `r² ≤ t`, and
`P(t) = Σ_j (N_j(t) - 1)`, where `N_j(t)` counts the points within squared distance `t` of
`p j` (the centre included). All thresholds are squared. The normalized quantities of the
source are `yMean = n⁻¹ Σ_i (|p_i - c|²/ρ² - σ²)`, `ω = 1 - σ²`, `𝔮 = Q/n` and
`𝒳(g) = 3ℛ(g) - 𝒜(g) = (3nR(g²ρ²) - P(g²ρ²))/n²`.

* The identity (`mul_sum_centroid_sq_eq`, no degree cap):
  `n Σ_i |p_i - c|² = (n² - 4nQ) ρ² + Σ_i Σ_r (3 - d_r(i)) (4ρ² - r²)`.
  This is (AB0) times `n²ρ²`: by the layer-cake formula
  `2 n² ∫₀² g 𝒳(g) dg = Σ_i Σ_r (3 - d_r(i)) (4 - r²/ρ²)`.
  The normalized count form (`mul_sum_centroid_sq_div_sub_eq`) is (AB0) times `n²`.
* The upper Riemann bound (`mul_sum_centroid_sq_div_sub_le_upper_sum`): for squared grid
  values `0 ≤ τ 0 ≤ τ 1 ≤ … ≤ τ k` with `τ k ≥ 4`, under the degree cap three,
  `n Σ_i |p_i - c|²/ρ² - n²σ² ≤ n²(1 - σ²) - 4nQ
    + Σ_{i<k} (τ (i+1) - τ i) (3nR(τ (i+1) ρ²) - P(τ (i+1) ρ²)) + τ 0 (3nR(τ 0 ρ²) - P(τ 0 ρ²))`.
  This is `yMean ≤ ω - 4𝔮 + 2 Up` times `n²`.
* The lower Riemann bound (`lower_sum_le_mul_sum_centroid_sq_div_sub`): for
  `0 ≤ τ 0 ≤ … ≤ τ k ≤ 4`, under the degree cap three,
  `n²(1 - σ²) - 4nQ + Σ_{i<k} (τ (i+1) - τ i) (3nR(τ i ρ²) - P(τ i ρ²))
    ≤ n Σ_i |p_i - c|²/ρ² - n²σ²`.
  This is `ω - 4𝔮 + 2 Lo ≤ yMean` times `n²`.

The proofs follow `Esgk/SecondMomentLowerSum.lean`: `3nR(t) - P(t)` is the sum of the
deficits `3 - d_r(j)` over the points `j` and the palette values `r` with `r² ≤ t`, each
deficit is nonnegative under the degree cap, and each palette value `r` (with `r² ≤ 4ρ²`)
contributes `4ρ² - r²` up to the telescoping error of the grid.
-/

@[expose] public section

namespace Esgk

open scoped BigOperators

variable {n : ℕ}

/-! ### Telescoping -/

/-- Upper telescoping: for `y` nondecreasing on `0, …, k` with `y 0 ≥ 0` and `x ≥ 0`, the
value `y 0` when `x ≤ y 0`, plus the increments `y (i+1) - y i` over the indices `i < k` with
`x ≤ y (i+1)`, sum to at least `max 0 (y k - x)`. -/
private lemma max_le_ite_add_sum_ite_increment {k : ℕ} (y : ℕ → ℝ) (hy0 : 0 ≤ y 0)
    (hy : ∀ i < k, y i ≤ y (i + 1)) {x : ℝ} (hx : 0 ≤ x) :
    max 0 (y k - x) ≤
      (if x ≤ y 0 then y 0 else 0) +
        ∑ i ∈ Finset.range k, (if x ≤ y (i + 1) then y (i + 1) - y i else 0) := by
  induction k with
  | zero =>
    rw [Finset.sum_range_zero, add_zero]
    by_cases h : x ≤ y 0
    · rw [ite_eq_left h]
      exact max_le hy0 (by linarith)
    · rw [ite_eq_right h]
      exact max_le le_rfl (by linarith [not_le.mp h])
  | succ k ih =>
    have ih' := ih (fun i hi ↦ hy i (by omega))
    have hk := hy k (by omega)
    rw [Finset.sum_range_succ, ← add_assoc]
    by_cases h : x ≤ y (k + 1)
    · rw [ite_eq_left h]
      exact max_le (by linarith [le_max_left 0 (y k - x)])
        (by linarith [le_max_right 0 (y k - x)])
    · rw [ite_eq_right h, add_zero]
      exact max_le ((le_max_left 0 (y k - x)).trans ih')
        (by linarith [le_max_left 0 (y k - x), not_le.mp h])

/-- The lower Riemann weights of one squared value `x ≤ 4c`: the scaled increments over the
thresholds `τ i * c ≥ x` sum to at most `4c - x`, when `τ k ≤ 4` and `c ≥ 0`. -/
private lemma mul_sum_lower_indicator_le {k : ℕ} (τ : ℕ → ℝ)
    (hτ : ∀ i < k, τ i ≤ τ (i + 1)) (hτk : τ k ≤ 4) {c x : ℝ} (hc : 0 ≤ c)
    (hx : x ≤ 4 * c) :
    c * ∑ i ∈ Finset.range k, (τ (i + 1) - τ i) * (if x ≤ τ i * c then 1 else 0) ≤
      4 * c - x := by
  have h := sum_ite_increment_le_max (fun i ↦ τ i * c)
    (fun i hi ↦ mul_le_mul_of_nonneg_right (hτ i hi) hc) x
  have hkc : τ k * c ≤ 4 * c := mul_le_mul_of_nonneg_right hτk hc
  have hmax : max 0 (τ k * c - x) ≤ 4 * c - x := max_le (by linarith) (by linarith)
  calc c * ∑ i ∈ Finset.range k, (τ (i + 1) - τ i) * (if x ≤ τ i * c then 1 else 0)
      = ∑ i ∈ Finset.range k, (if x ≤ τ i * c then τ (i + 1) * c - τ i * c else 0) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by split_ifs <;> ring
    _ ≤ 4 * c - x := h.trans hmax

/-- The upper Riemann weights of one squared value `x ≥ 0`: the scaled increments over the
thresholds `τ (i+1) * c ≥ x`, plus `τ 0 * c` when `τ 0 * c ≥ x`, sum to at least `4c - x`,
when `τ 0 ≥ 0`, `τ k ≥ 4` and `c ≥ 0`. -/
private lemma four_mul_sub_le_mul_upper_indicator {k : ℕ} (τ : ℕ → ℝ) (hτ0 : 0 ≤ τ 0)
    (hτ : ∀ i < k, τ i ≤ τ (i + 1)) (hτk : 4 ≤ τ k) {c x : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) :
    4 * c - x ≤
      c * (∑ i ∈ Finset.range k, (τ (i + 1) - τ i) * (if x ≤ τ (i + 1) * c then 1 else 0) +
        τ 0 * (if x ≤ τ 0 * c then 1 else 0)) := by
  have h := max_le_ite_add_sum_ite_increment (fun i ↦ τ i * c) (mul_nonneg hτ0 hc)
    (fun i hi ↦ mul_le_mul_of_nonneg_right (hτ i hi) hc) hx
  have hkc : 4 * c ≤ τ k * c := mul_le_mul_of_nonneg_right hτk hc
  have h1 : ∑ i ∈ Finset.range k,
        (if x ≤ τ (i + 1) * c then τ (i + 1) * c - τ i * c else 0) =
      ∑ i ∈ Finset.range k, c * ((τ (i + 1) - τ i) * (if x ≤ τ (i + 1) * c then 1 else 0)) :=
    Finset.sum_congr rfl fun i _ ↦ by split_ifs <;> ring
  have h2 : (if x ≤ τ 0 * c then τ 0 * c else 0) =
      c * (τ 0 * (if x ≤ τ 0 * c then 1 else 0)) := by
    split_ifs <;> ring
  calc 4 * c - x ≤ max 0 (τ k * c - x) := by linarith [le_max_right 0 (τ k * c - x)]
    _ ≤ (if x ≤ τ 0 * c then τ 0 * c else 0) +
        ∑ i ∈ Finset.range k,
          (if x ≤ τ (i + 1) * c then τ (i + 1) * c - τ i * c else 0) := h
    _ = _ := by
        rw [h1, h2, mul_add, Finset.mul_sum]
        ring

/-! ### The deficit form of `3nR - P` -/

/-- For a squared threshold `t ≥ 0`, `3n R(t) - P(t)` is the sum over the points `j` and the
palette values `r` with `r² ≤ t` of the deficit `3 - d_r(j)`. -/
private lemma three_mul_palette_sub_closedBall_eq_sum_deficit (p : Config n) {t : ℝ}
    (ht : 0 ≤ t) :
    3 * (n : ℝ) * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t)).card : ℝ) -
        ∑ j, ((((Finset.univ : Finset (Fin n)).filter
          (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) - 1) =
      ∑ j, ∑ r ∈ OrderedDistanceValues p,
        (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) *
          (if r ^ 2 ≤ t then 1 else 0) := by
  have hj (j : Fin n) :
      ∑ r ∈ OrderedDistanceValues p,
          (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) *
            (if r ^ 2 ≤ t then 1 else 0) =
        3 * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t)).card : ℝ) -
          ((((Finset.univ : Finset (Fin n)).filter
            (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) - 1) := by
    have h1 : ∑ r ∈ OrderedDistanceValues p,
          (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) *
            (if r ^ 2 ≤ t then 1 else 0) =
        ∑ r ∈ (OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t),
          (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) := by
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun r _ ↦ by split_ifs <;> ring
    rw [h1, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      closedBall_sq_card_eq_closePairRow_card_add_one p ht j, closePairRow_card_eq_sum]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun j _ ↦ hj j]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-- A weighted sum of the counts `3nR(t i) - P(t i)` over `i < k`, for thresholds `t i ≥ 0`,
regrouped over the points `j` and the palette values `r`: each deficit `3 - d_r(j)` is
weighted by the sum of the weights `w i` of the thresholds `t i ≥ r²`. -/
private lemma sum_weight_mul_palette_sub_closedBall_eq (p : Config n) {k : ℕ} (w t : ℕ → ℝ)
    (ht : ∀ i ∈ Finset.range k, 0 ≤ t i) :
    ∑ i ∈ Finset.range k, w i *
        (3 * (n : ℝ) * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t i)).card : ℝ) -
          ∑ j, ((((Finset.univ : Finset (Fin n)).filter
            (fun q ↦ dist (p j) (p q) ^ 2 ≤ t i)).card : ℝ) - 1)) =
      ∑ j, ∑ r ∈ OrderedDistanceValues p,
        (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) *
          ∑ i ∈ Finset.range k, w i * (if r ^ 2 ≤ t i then 1 else 0) := by
  have h1 : ∀ i ∈ Finset.range k, w i *
        (3 * (n : ℝ) * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t i)).card : ℝ) -
          ∑ j, ((((Finset.univ : Finset (Fin n)).filter
            (fun q ↦ dist (p j) (p q) ^ 2 ≤ t i)).card : ℝ) - 1)) =
      ∑ j, ∑ r ∈ OrderedDistanceValues p,
        w i * ((3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) *
          (if r ^ 2 ≤ t i then 1 else 0)) := by
    intro i hi
    rw [three_mul_palette_sub_closedBall_eq_sum_deficit p (ht i hi), Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl h1]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun j _ ↦ ?_)
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun r _ ↦ ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-! ### The identity (AB0) -/

/-- The centroid defect identity, (AB0) of Lemma AB in
`docs/results/explicit-constant-gain-2-89-2026-10-20.md` times `n²ρ²`. With
`ρ² = distanceAnnulusRadiusSq p`, `c` the centroid and `Q = 3D - n + 1`,
`n Σ_i |p_i - c|² = (n² - 4nQ) ρ² + Σ_i Σ_r (3 - d_r(i)) (4ρ² - r²)`,
where `r` runs over the ordered distance values and `d_r(i)` counts the points at distance
`r` from `p i`. The last sum is `2n²ρ² ∫₀² g 𝒳(g) dg`. No degree cap is needed. -/
theorem mul_sum_centroid_sq_eq {p : Config n} (hn : 0 < n) {ρ : ℝ}
    (hρsq : ρ ^ 2 = distanceAnnulusRadiusSq p) :
    (n : ℝ) * ∑ i, dist (p i) (configCentroid p) ^ 2 =
      ((n : ℝ) ^ 2 - 4 * (n : ℝ) * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1)) * ρ ^ 2 +
        ∑ i, ∑ r ∈ OrderedDistanceValues p,
          (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) * (4 * ρ ^ 2 - r ^ 2) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hrad : (n : ℝ) * ρ ^ 2 =
      3 * (∑ r ∈ OrderedDistanceValues p, r ^ 2) - centroidSquaredMass p := by
    rw [hρsq, distanceAnnulusRadiusSq]
    field_simp
  have hrow (i : Fin n) :
      ∑ r ∈ OrderedDistanceValues p,
          (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) * (4 * ρ ^ 2 - r ^ 2) =
        4 * ρ ^ 2 * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) - (n : ℝ) * ρ ^ 2 +
          (n : ℝ) * dist (p i) (configCentroid p) ^ 2 := by
    have hsplit : ∑ r ∈ OrderedDistanceValues p,
          (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) * (4 * ρ ^ 2 - r ^ 2) =
        (∑ r ∈ OrderedDistanceValues p,
            (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ))) * (4 * ρ ^ 2) -
          ∑ r ∈ OrderedDistanceValues p,
            (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) * r ^ 2 := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun r _ ↦ by ring
    rw [hsplit, sum_distanceDegreeDeficit p hn i, sum_weighted_distanceDegreeDeficit,
      sum_sqDistance_eq_centroid p hn i]
    linear_combination hrad
  rw [Finset.sum_congr rfl fun i _ ↦ hrow i, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  ring

/-- The centroid defect identity (AB0) of Lemma AB in
`docs/results/explicit-constant-gain-2-89-2026-10-20.md` in count form, times `n²`. With
`ρ > 0`, `ρ² = distanceAnnulusRadiusSq p`, `c` the centroid, `Q = 3D - n + 1` and any real `σ`,
`n Σ_i |p_i - c|²/ρ² - n²σ² = n²(1 - σ²) - 4nQ + Σ_i Σ_r (3 - d_r(i)) (4 - r²/ρ²)`.
Normalized: `yMean = ω - 4𝔮 + 2∫₀² g 𝒳(g) dg` with `ω = 1 - σ²` and `𝔮 = Q/n`. -/
theorem mul_sum_centroid_sq_div_sub_eq {p : Config n} (hn : 0 < n) {ρ : ℝ} (hρ : 0 < ρ)
    (hρsq : ρ ^ 2 = distanceAnnulusRadiusSq p) (σ : ℝ) :
    (n : ℝ) * (∑ i, dist (p i) (configCentroid p) ^ 2 / ρ ^ 2) - (n : ℝ) ^ 2 * σ ^ 2 =
      (n : ℝ) ^ 2 * (1 - σ ^ 2) -
          4 * (n : ℝ) * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) +
        ∑ i, ∑ r ∈ OrderedDistanceValues p,
          (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) * (4 - r ^ 2 / ρ ^ 2) := by
  have hρ2 : ρ ^ 2 ≠ 0 := by positivity
  have hid := mul_sum_centroid_sq_eq hn hρsq
  have hdiv : ∑ i, ∑ r ∈ OrderedDistanceValues p,
        (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) * (4 - r ^ 2 / ρ ^ 2) =
      (∑ i, ∑ r ∈ OrderedDistanceValues p,
        (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) * (4 * ρ ^ 2 - r ^ 2)) /
          ρ ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    field_simp
  rw [hdiv, ← Finset.sum_div, ← mul_div_assoc, hid]
  field_simp
  ring

/-! ### The Riemann bounds -/

/-- The upper Riemann bound of the centroid defect identity: the row CASElo of
`docs/results/explicit-constant-gain-2-89-2026-10-20.md` (§3, step 4) before the case
hypothesis `Y_lo ≤ yMean`, in count form times `n²`. Under the degree cap three, with `ρ > 0`,
`ρ² = distanceAnnulusRadiusSq p`, `c` the centroid, any real `σ`, and squared grid values
`0 ≤ τ 0 ≤ τ 1 ≤ … ≤ τ k` with `τ k ≥ 4`,
`n Σ_i |p_i - c|²/ρ² - n²σ² ≤ n²(1 - σ²) - 4nQ
  + Σ_{i<k} (τ (i+1) - τ i) (3nR(τ (i+1) ρ²) - P(τ (i+1) ρ²)) + τ 0 (3nR(τ 0 ρ²) - P(τ 0 ρ²))`,
where `R(t)` counts the palette values `r` with `r² ≤ t`, `P(t) = Σ_j (N_j(t) - 1)` and
`Q = 3D - n + 1`. Normalized: `yMean ≤ ω - 4𝔮 + 2 Up`, with
`Up = Σ_cells ((b² - a²)/2) 𝒳(b) + (g₀²/2) 𝒳(g₀)` and `τ i = g_i²`. -/
theorem mul_sum_centroid_sq_div_sub_le_upper_sum {p : Config n} (hn : 0 < n)
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) {ρ : ℝ} (hρ : 0 < ρ)
    (hρsq : ρ ^ 2 = distanceAnnulusRadiusSq p) (σ : ℝ) {k : ℕ} (τ : ℕ → ℝ) (hτ0 : 0 ≤ τ 0)
    (hτ : ∀ i < k, τ i ≤ τ (i + 1)) (hτk : 4 ≤ τ k) :
    (n : ℝ) * (∑ i, dist (p i) (configCentroid p) ^ 2 / ρ ^ 2) - (n : ℝ) ^ 2 * σ ^ 2 ≤
      (n : ℝ) ^ 2 * (1 - σ ^ 2) -
          4 * (n : ℝ) * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) +
        ∑ i ∈ Finset.range k, (τ (i + 1) - τ i) *
          (3 * (n : ℝ) *
              (((OrderedDistanceValues p).filter
                (fun r ↦ r ^ 2 ≤ τ (i + 1) * ρ ^ 2)).card : ℝ) -
            ∑ j, ((((Finset.univ : Finset (Fin n)).filter
              (fun q ↦ dist (p j) (p q) ^ 2 ≤ τ (i + 1) * ρ ^ 2)).card : ℝ) - 1)) +
        τ 0 * (3 * (n : ℝ) *
            (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ τ 0 * ρ ^ 2)).card : ℝ) -
          ∑ j, ((((Finset.univ : Finset (Fin n)).filter
            (fun q ↦ dist (p j) (p q) ^ 2 ≤ τ 0 * ρ ^ 2)).card : ℝ) - 1)) := by
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hτnn : ∀ i ≤ k, 0 ≤ τ i := by
    intro i hi
    induction i with
    | zero => exact hτ0
    | succ i ih => exact (ih (by omega)).trans (hτ i (by omega))
  have hsum := sum_weight_mul_palette_sub_closedBall_eq p (k := k) (fun i ↦ τ (i + 1) - τ i)
    (fun i ↦ τ (i + 1) * ρ ^ 2)
    (fun i hi ↦ mul_nonneg (hτnn (i + 1) (Finset.mem_range.mp hi)) hρ2.le)
  have h0 := three_mul_palette_sub_closedBall_eq_sum_deficit p (mul_nonneg hτ0 hρ2.le)
  have hid := mul_sum_centroid_sq_eq hn hρsq
  have hA : ∑ j, ∑ r ∈ OrderedDistanceValues p,
        (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) * (4 * ρ ^ 2 - r ^ 2) ≤
      ρ ^ 2 * (∑ j, ∑ r ∈ OrderedDistanceValues p,
          (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) *
            ∑ i ∈ Finset.range k,
              (τ (i + 1) - τ i) * (if r ^ 2 ≤ τ (i + 1) * ρ ^ 2 then 1 else 0) +
        τ 0 * ∑ j, ∑ r ∈ OrderedDistanceValues p,
          (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) *
            (if r ^ 2 ≤ τ 0 * ρ ^ 2 then 1 else 0)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ ↦ ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ ↦ ?_
    have hc : ((DistanceOutNeighborsAtValue p j r).card : ℝ) ≤ 3 := by
      exact_mod_cast hcap j r
    have hb := four_mul_sub_le_mul_upper_indicator τ hτ0 hτ hτk hρ2.le (sq_nonneg r)
    calc (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) * (4 * ρ ^ 2 - r ^ 2)
        ≤ (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) *
            (ρ ^ 2 * (∑ i ∈ Finset.range k,
              (τ (i + 1) - τ i) * (if r ^ 2 ≤ τ (i + 1) * ρ ^ 2 then 1 else 0) +
              τ 0 * (if r ^ 2 ≤ τ 0 * ρ ^ 2 then 1 else 0))) :=
          mul_le_mul_of_nonneg_left hb (by linarith)
      _ = _ := by ring
  rw [hsum, h0, ← Finset.sum_div, ← mul_div_assoc]
  have hkey : (n : ℝ) * (∑ i, dist (p i) (configCentroid p) ^ 2) / ρ ^ 2 ≤
      (n : ℝ) ^ 2 - 4 * (n : ℝ) * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) +
        (∑ j, ∑ r ∈ OrderedDistanceValues p,
          (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) *
            ∑ i ∈ Finset.range k,
              (τ (i + 1) - τ i) * (if r ^ 2 ≤ τ (i + 1) * ρ ^ 2 then 1 else 0) +
        τ 0 * ∑ j, ∑ r ∈ OrderedDistanceValues p,
          (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) *
            (if r ^ 2 ≤ τ 0 * ρ ^ 2 then 1 else 0)) := by
    rw [div_le_iff₀ hρ2]
    linarith
  linarith

/-- The lower Riemann bound of the centroid defect identity: the row CASEhi of
`docs/results/explicit-constant-gain-2-89-2026-10-20.md` (§3, step 4) before the case
hypothesis `yMean ≤ Y_hi`, in count form times `n²`. Under the degree cap three, with `ρ > 0`,
`ρ² = distanceAnnulusRadiusSq p`, `c` the centroid, any real `σ`, and squared grid values
`0 ≤ τ 0 ≤ τ 1 ≤ … ≤ τ k ≤ 4`,
`n²(1 - σ²) - 4nQ + Σ_{i<k} (τ (i+1) - τ i) (3nR(τ i ρ²) - P(τ i ρ²))
  ≤ n Σ_i |p_i - c|²/ρ² - n²σ²`,
where `R(t)` counts the palette values `r` with `r² ≤ t`, `P(t) = Σ_j (N_j(t) - 1)` and
`Q = 3D - n + 1`. Normalized: `ω - 4𝔮 + 2 Lo ≤ yMean`, with `Lo = Σ_cells ((b² - a²)/2) 𝒳(a)`
and `τ i = g_i²`. -/
theorem lower_sum_le_mul_sum_centroid_sq_div_sub {p : Config n} (hn : 0 < n)
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) {ρ : ℝ} (hρ : 0 < ρ)
    (hρsq : ρ ^ 2 = distanceAnnulusRadiusSq p) (σ : ℝ) {k : ℕ} (τ : ℕ → ℝ) (hτ0 : 0 ≤ τ 0)
    (hτ : ∀ i < k, τ i ≤ τ (i + 1)) (hτk : τ k ≤ 4) :
    (n : ℝ) ^ 2 * (1 - σ ^ 2) -
          4 * (n : ℝ) * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) +
        ∑ i ∈ Finset.range k, (τ (i + 1) - τ i) *
          (3 * (n : ℝ) *
              (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ τ i * ρ ^ 2)).card : ℝ) -
            ∑ j, ((((Finset.univ : Finset (Fin n)).filter
              (fun q ↦ dist (p j) (p q) ^ 2 ≤ τ i * ρ ^ 2)).card : ℝ) - 1)) ≤
      (n : ℝ) * (∑ i, dist (p i) (configCentroid p) ^ 2 / ρ ^ 2) - (n : ℝ) ^ 2 * σ ^ 2 := by
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hτnn : ∀ i ≤ k, 0 ≤ τ i := by
    intro i hi
    induction i with
    | zero => exact hτ0
    | succ i ih => exact (ih (by omega)).trans (hτ i (by omega))
  have hpal : ∀ r ∈ OrderedDistanceValues p, r ^ 2 ≤ 4 * ρ ^ 2 := fun r hr ↦ by
    rw [hρsq]
    exact palette_sq_le_four_mul_distanceAnnulusRadiusSq hn hcap hr
  have hsum := sum_weight_mul_palette_sub_closedBall_eq p (k := k) (fun i ↦ τ (i + 1) - τ i)
    (fun i ↦ τ i * ρ ^ 2)
    (fun i hi ↦ mul_nonneg (hτnn i (Finset.mem_range.mp hi).le) hρ2.le)
  have hid := mul_sum_centroid_sq_eq hn hρsq
  have hA : ρ ^ 2 * ∑ j, ∑ r ∈ OrderedDistanceValues p,
          (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) *
            ∑ i ∈ Finset.range k,
              (τ (i + 1) - τ i) * (if r ^ 2 ≤ τ i * ρ ^ 2 then 1 else 0) ≤
      ∑ j, ∑ r ∈ OrderedDistanceValues p,
        (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) * (4 * ρ ^ 2 - r ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun r hr ↦ ?_
    have hc : ((DistanceOutNeighborsAtValue p j r).card : ℝ) ≤ 3 := by
      exact_mod_cast hcap j r
    have hb := mul_sum_lower_indicator_le τ hτ hτk hρ2.le (hpal r hr)
    calc ρ ^ 2 * ((3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) *
            ∑ i ∈ Finset.range k,
              (τ (i + 1) - τ i) * (if r ^ 2 ≤ τ i * ρ ^ 2 then 1 else 0))
        = (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) *
            (ρ ^ 2 * ∑ i ∈ Finset.range k,
              (τ (i + 1) - τ i) * (if r ^ 2 ≤ τ i * ρ ^ 2 then 1 else 0)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (by linarith)
  rw [hsum, ← Finset.sum_div, ← mul_div_assoc]
  have hkey : (n : ℝ) ^ 2 - 4 * (n : ℝ) * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) +
        ∑ j, ∑ r ∈ OrderedDistanceValues p,
          (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) *
            ∑ i ∈ Finset.range k,
              (τ (i + 1) - τ i) * (if r ^ 2 ≤ τ i * ρ ^ 2 then 1 else 0) ≤
      (n : ℝ) * (∑ i, dist (p i) (configCentroid p) ^ 2) / ρ ^ 2 := by
    rw [le_div_iff₀ hρ2]
    linarith
  linarith

end Esgk
