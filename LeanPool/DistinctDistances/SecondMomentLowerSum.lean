/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.ThinAnnulus
public import LeanPool.DistinctDistances.PalettePairCounting
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The second-moment identity and its lower Riemann sum

Formalizes Lemma M of `docs/results/explicit-constant-gain-5-239-2026-10-20.md` (§2), with
the exact identities (N1)–(N3) of §1, in the count form used by row 6 of Theorem C60 in
`docs/results/short-chain-constant-gain-1-60-2026-10-21.md` (§3).

Let `ρ² = distanceAnnulusRadiusSq p`, so `nρ² = 3 Σ_r r² - S` with `S` the centroid squared
mass (N1). Write `D` for the number of ordered distance values, `Q = 3D - n + 1`, `d_r(i)` for
the number of points at distance `r` from `p i`, `R(t)` for the number of palette values `r`
with `r² ≤ t`, and `P(t) = Σ_j (N_j(t) - 1)`, where `N_j(t)` counts the points within squared
distance `t` of `p j` (the centre included). All thresholds are squared.

* The identity (`sum_four_sub_sq_add_two_weighted_deficit_eq`):
  `Σ_{i,j} (4ρ² - |p_i p_j|²) + 2 Σ_i Σ_r (3 - d_r(i)) (4ρ² - r²) = (2n² + 8nQ) ρ²`.
  It needs no degree cap.
* The lower Riemann sum (`second_moment_lower_sum_le`): for `0 ≤ τ 0 ≤ τ 1 ≤ … ≤ τ k ≤ 4`
  and the degree cap three,
  `Σ_{i<k} (τ (i+1) - τ i) (6n R(τ i ρ²) - P(τ i ρ²)) ≤ 2n² + 8nQ - 4n`.
  This is `2n²` times the normalized row `Σ (𝒜 + 2𝒳) Δτ / 2 ≤ 1 + 4𝔮 - 2ε`.
* The seven-cell instance with top threshold `4` (`second_moment_lower_sum_le_seven`).

The proof of the lower sum splits `6nR(t) - P(t)` into the off-diagonal close pairs plus twice
the palette deficits below `t`. Each off-diagonal pair and each palette value contributes at
most `4ρ² - d²` by telescoping, since all squared distances are at most `4ρ²` (N3). The
diagonal is handled exactly: it contributes nothing to `P` and the term `-4n` comes from the
diagonal of the identity. The ball count `discrete_layer_cake_le` counts the centre point,
which would lose the term `-4n`; it is not used here.
-/

@[expose] public section

namespace Esgk

open scoped BigOperators

variable {n : ℕ}

/-! ### Telescoping -/

/-- Telescoping: for `τ` nondecreasing on `0, …, k`, the increments `τ (i+1) - τ i` over the
indices `i < k` with `x ≤ τ i` sum to at most `max 0 (τ k - x)`. This is a copy of the private
`sum_ite_increment_le_max` of `Esgk/CentroidFunctionalBounds.lean`. -/
private lemma sum_ite_increment_le_max_of_monotone {k : ℕ} (τ : ℕ → ℝ)
    (hτ : ∀ i < k, τ i ≤ τ (i + 1)) (x : ℝ) :
    ∑ i ∈ Finset.range k, (if x ≤ τ i then τ (i + 1) - τ i else 0) ≤ max 0 (τ k - x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have ih' := ih (fun i hi ↦ hτ i (by omega))
    have hk := hτ k (by omega)
    split_ifs with hx
    · rw [max_eq_right (by linarith)] at ih'
      linarith [le_max_right 0 (τ (k + 1) - x)]
    · rw [max_eq_left (by linarith)] at ih'
      linarith [le_max_left 0 (τ (k + 1) - x)]

/-- The scaled increments over the thresholds `τ i * c ≥ x` sum to at most `4c - x`, when
`τ k ≤ 4`, `c ≥ 0` and `x ≤ 4c`. -/
private lemma sum_increment_mul_indicator_le {k : ℕ} (τ : ℕ → ℝ)
    (hτ : ∀ i < k, τ i ≤ τ (i + 1)) (hτk : τ k ≤ 4) {c x : ℝ} (hc : 0 ≤ c)
    (hx : x ≤ 4 * c) :
    ∑ i ∈ Finset.range k, (τ (i + 1) - τ i) * c * (if x ≤ τ i * c then 1 else 0) ≤
      4 * c - x := by
  have h := sum_ite_increment_le_max_of_monotone (fun i ↦ τ i * c)
    (fun i hi ↦ mul_le_mul_of_nonneg_right (hτ i hi) hc) x
  have hkc : τ k * c ≤ 4 * c := mul_le_mul_of_nonneg_right hτk hc
  have hmax : max 0 (τ k * c - x) ≤ 4 * c - x := max_le (by linarith) (by linarith)
  calc ∑ i ∈ Finset.range k, (τ (i + 1) - τ i) * c * (if x ≤ τ i * c then 1 else 0)
      = ∑ i ∈ Finset.range k, (if x ≤ τ i * c then τ (i + 1) * c - τ i * c else 0) :=
        Finset.sum_congr rfl fun i _ ↦ by split_ifs <;> ring
    _ ≤ 4 * c - x := h.trans hmax

/-! ### The second-moment identity -/

/-- The second-moment identity (Lemma M, count form). With `ρ² = distanceAnnulusRadiusSq p`
and `Q = 3D - n + 1`,
`Σ_{i,j} (4ρ² - |p_i p_j|²) + 2 Σ_i Σ_r (3 - d_r(i)) (4ρ² - r²) = (2n² + 8nQ) ρ²`,
where `r` runs over the ordered distance values and `d_r(i)` counts the points at distance
`r` from `p i`. No degree cap is needed. -/
theorem sum_four_sub_sq_add_two_weighted_deficit_eq {p : Config n} (hn : 0 < n) {ρ : ℝ}
    (hρsq : ρ ^ 2 = distanceAnnulusRadiusSq p) :
    ∑ i, ∑ j, (4 * ρ ^ 2 - dist (p i) (p j) ^ 2) +
        2 * ∑ i, ∑ r ∈ OrderedDistanceValues p,
          (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) * (4 * ρ ^ 2 - r ^ 2) =
      (2 * (n : ℝ) ^ 2 + 8 * (n : ℝ) * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1)) *
        ρ ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hrad : (n : ℝ) * ρ ^ 2 =
      3 * (∑ r ∈ OrderedDistanceValues p, r ^ 2) - centroidSquaredMass p := by
    rw [hρsq, distanceAnnulusRadiusSq]
    field_simp
  have hrow (i : Fin n) :
      ∑ j, (4 * ρ ^ 2 - dist (p i) (p j) ^ 2) +
          2 * ∑ r ∈ OrderedDistanceValues p,
            (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) * (4 * ρ ^ 2 - r ^ 2) =
        4 * (n : ℝ) * ρ ^ 2 + 8 * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) * ρ ^ 2 -
          6 * (∑ r ∈ OrderedDistanceValues p, r ^ 2) +
          ((n : ℝ) * dist (p i) (configCentroid p) ^ 2 + centroidSquaredMass p) := by
    have hsplit : ∑ r ∈ OrderedDistanceValues p,
          (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) * (4 * ρ ^ 2 - r ^ 2) =
        (∑ r ∈ OrderedDistanceValues p,
            (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ))) * (4 * ρ ^ 2) -
          ∑ r ∈ OrderedDistanceValues p,
            (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) * r ^ 2 := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun r _ ↦ by ring
    rw [hsplit, sum_distanceDegreeDeficit p hn i, sum_weighted_distanceDegreeDeficit,
      Finset.sum_sub_distrib, sum_sqDistance_eq_centroid p hn i]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_congr rfl fun i _ ↦ hrow i]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [← Finset.mul_sum]
  have hS : ∑ i, dist (p i) (configCentroid p) ^ 2 = centroidSquaredMass p := rfl
  rw [hS]
  linear_combination 2 * (n : ℝ) * hrad

/-! ### The lower Riemann sum -/

/-- For a squared threshold `t ≥ 0`, `6n R(t) - P(t)` is the sum over the apexes `j` of the
off-diagonal close pairs at `j` plus twice the palette deficits at `j` below `t`. -/
private lemma six_mul_palette_sub_closedBall_eq_sum_apex (p : Config n) {t : ℝ}
    (ht : 0 ≤ t) :
    6 * (n : ℝ) * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t)).card : ℝ) -
        ∑ j, ((((Finset.univ : Finset (Fin n)).filter
          (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) - 1) =
      ∑ j, (∑ q, (if j ≠ q ∧ dist (p j) (p q) ^ 2 ≤ t then (1 : ℝ) else 0) +
        2 * ∑ r ∈ OrderedDistanceValues p,
          (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) *
            (if r ^ 2 ≤ t then 1 else 0)) := by
  have hball (j : Fin n) : ((((Finset.univ : Finset (Fin n)).filter
      (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) - 1) = ((ClosePairRow p j t).card : ℝ) := by
    rw [closedBall_sq_card_eq_closePairRow_card_add_one p ht j, Nat.cast_add, Nat.cast_one]
    ring
  have hcpr (j : Fin n) : ((ClosePairRow p j t).card : ℝ) =
      ∑ q, (if j ≠ q ∧ dist (p j) (p q) ^ 2 ≤ t then (1 : ℝ) else 0) := by
    rw [ClosePairRow, Finset.natCast_card_filter]
  have hdef (j : Fin n) :
      ∑ r ∈ OrderedDistanceValues p,
          (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) * (if r ^ 2 ≤ t then 1 else 0) =
        3 * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t)).card : ℝ) -
          ((ClosePairRow p j t).card : ℝ) := by
    have h1 : ∑ r ∈ OrderedDistanceValues p,
          (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) * (if r ^ 2 ≤ t then 1 else 0) =
        ∑ r ∈ (OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t),
          (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) := by
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun r _ ↦ by split_ifs <;> ring
    rw [h1, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, closePairRow_card_eq_sum,
      Nat.cast_sum]
    ring
  calc 6 * (n : ℝ) * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t)).card : ℝ) -
        ∑ j, ((((Finset.univ : Finset (Fin n)).filter
          (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) - 1)
      = 6 * (n : ℝ) * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t)).card : ℝ) -
          ∑ j, ((ClosePairRow p j t).card : ℝ) := by
        rw [Finset.sum_congr rfl fun j _ ↦ hball j]
    _ = ∑ j, (((ClosePairRow p j t).card : ℝ) +
          2 * (3 * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t)).card : ℝ) -
            ((ClosePairRow p j t).card : ℝ))) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ = _ := Finset.sum_congr rfl fun j _ ↦ by rw [hdef j, hcpr j]

/-- The lower Riemann sum of the second-moment identity (Lemma M, count form, off-diagonal).
Under the degree cap three, with `ρ > 0`, `ρ² = distanceAnnulusRadiusSq p`, and squared grid
values `0 ≤ τ 0 ≤ τ 1 ≤ … ≤ τ k ≤ 4`,
`Σ_{i<k} (τ (i+1) - τ i) (6n R(τ i ρ²) - P(τ i ρ²)) ≤ 2n² + 8nQ - 4n`,
where `R(t)` counts the palette values `r` with `r² ≤ t`, `P(t) = Σ_j (N_j(t) - 1)` counts the
ordered pairs of distinct indices within squared distance `t`, and `Q = 3D - n + 1`. -/
theorem second_moment_lower_sum_le {p : Config n} (hn : 0 < n)
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) {ρ : ℝ} (hρ : 0 < ρ)
    (hρsq : ρ ^ 2 = distanceAnnulusRadiusSq p) {k : ℕ} (τ : ℕ → ℝ) (hτ0 : 0 ≤ τ 0)
    (hτ : ∀ i < k, τ i ≤ τ (i + 1)) (hτk : τ k ≤ 4) :
    ∑ i ∈ Finset.range k, (τ (i + 1) - τ i) *
        (6 * (n : ℝ) *
            (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ τ i * ρ ^ 2)).card : ℝ) -
          ∑ j, ((((Finset.univ : Finset (Fin n)).filter
            (fun q ↦ dist (p j) (p q) ^ 2 ≤ τ i * ρ ^ 2)).card : ℝ) - 1)) ≤
      2 * (n : ℝ) ^ 2 + 8 * (n : ℝ) * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) -
        4 * (n : ℝ) := by
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hτnn : ∀ i ≤ k, 0 ≤ τ i := by
    intro i hi
    induction i with
    | zero => exact hτ0
    | succ i ih => exact (ih (by omega)).trans (hτ i (by omega))
  have hpal : ∀ r ∈ OrderedDistanceValues p, r ^ 2 ≤ 4 * ρ ^ 2 := fun r hr ↦ by
    rw [hρsq]
    exact palette_sq_le_four_mul_distanceAnnulusRadiusSq hn hcap hr
  have hpair : ∀ j q : Fin n, j ≠ q → dist (p j) (p q) ^ 2 ≤ 4 * ρ ^ 2 := fun j q hjq ↦
    hpal _ (Finset.mem_image.mpr ⟨(j, q), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hjq⟩, rfl⟩)
  -- The bound at one apex `j`.
  have hapex (j : Fin n) :
      ∑ l ∈ Finset.range k, (τ (l + 1) - τ l) * ρ ^ 2 *
          (∑ q, (if j ≠ q ∧ dist (p j) (p q) ^ 2 ≤ τ l * ρ ^ 2 then (1 : ℝ) else 0) +
            2 * ∑ r ∈ OrderedDistanceValues p,
              (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) *
                (if r ^ 2 ≤ τ l * ρ ^ 2 then 1 else 0)) ≤
        ∑ q, (4 * ρ ^ 2 - dist (p j) (p q) ^ 2) - 4 * ρ ^ 2 +
          2 * ∑ r ∈ OrderedDistanceValues p,
            (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) * (4 * ρ ^ 2 - r ^ 2) := by
    have e1 : ∑ l ∈ Finset.range k, (τ (l + 1) - τ l) * ρ ^ 2 *
          ∑ q, (if j ≠ q ∧ dist (p j) (p q) ^ 2 ≤ τ l * ρ ^ 2 then (1 : ℝ) else 0) =
        ∑ q, ∑ l ∈ Finset.range k, (τ (l + 1) - τ l) * ρ ^ 2 *
          (if j ≠ q ∧ dist (p j) (p q) ^ 2 ≤ τ l * ρ ^ 2 then (1 : ℝ) else 0) := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    have e2 : ∑ l ∈ Finset.range k, (τ (l + 1) - τ l) * ρ ^ 2 *
          (2 * ∑ r ∈ OrderedDistanceValues p,
            (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) *
              (if r ^ 2 ≤ τ l * ρ ^ 2 then 1 else 0)) =
        2 * ∑ r ∈ OrderedDistanceValues p,
          (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) *
            ∑ l ∈ Finset.range k, (τ (l + 1) - τ l) * ρ ^ 2 *
              (if r ^ 2 ≤ τ l * ρ ^ 2 then 1 else 0) := by
      simp_rw [Finset.mul_sum]
      refine Finset.sum_comm.trans
        (Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_)
      ring
    have hq (q : Fin n) : ∑ l ∈ Finset.range k, (τ (l + 1) - τ l) * ρ ^ 2 *
          (if j ≠ q ∧ dist (p j) (p q) ^ 2 ≤ τ l * ρ ^ 2 then (1 : ℝ) else 0) ≤
        (4 * ρ ^ 2 - dist (p j) (p q) ^ 2) - (if j = q then 4 * ρ ^ 2 else 0) := by
      by_cases hjq : j = q
      · subst hjq
        simp
      · have hfun : ∀ l, (if j ≠ q ∧ dist (p j) (p q) ^ 2 ≤ τ l * ρ ^ 2 then (1 : ℝ) else 0) =
            (if dist (p j) (p q) ^ 2 ≤ τ l * ρ ^ 2 then (1 : ℝ) else 0) := fun l ↦ by
          by_cases h : dist (p j) (p q) ^ 2 ≤ τ l * ρ ^ 2 <;> simp [h, hjq]
        simp only [hfun]
        rw [ite_eq_right hjq, sub_zero]
        exact sum_increment_mul_indicator_le τ hτ hτk hρ2.le (hpair j q hjq)
    have hr (r : ℝ) (hr : r ∈ OrderedDistanceValues p) :
        (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) *
            ∑ l ∈ Finset.range k, (τ (l + 1) - τ l) * ρ ^ 2 *
              (if r ^ 2 ≤ τ l * ρ ^ 2 then 1 else 0) ≤
          (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) * (4 * ρ ^ 2 - r ^ 2) := by
      have hc : ((DistanceOutNeighborsAtValue p j r).card : ℝ) ≤ 3 := by
        exact_mod_cast hcap j r
      exact mul_le_mul_of_nonneg_left
        (sum_increment_mul_indicator_le τ hτ hτk hρ2.le (hpal r hr)) (by linarith)
    rw [Finset.sum_congr rfl fun l _ ↦ mul_add _ _ _, Finset.sum_add_distrib, e1, e2]
    calc ∑ q, ∑ l ∈ Finset.range k, (τ (l + 1) - τ l) * ρ ^ 2 *
            (if j ≠ q ∧ dist (p j) (p q) ^ 2 ≤ τ l * ρ ^ 2 then (1 : ℝ) else 0) +
          2 * ∑ r ∈ OrderedDistanceValues p,
            (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) *
              ∑ l ∈ Finset.range k, (τ (l + 1) - τ l) * ρ ^ 2 *
                (if r ^ 2 ≤ τ l * ρ ^ 2 then 1 else 0)
        ≤ ∑ q, ((4 * ρ ^ 2 - dist (p j) (p q) ^ 2) - (if j = q then 4 * ρ ^ 2 else 0)) +
          2 * ∑ r ∈ OrderedDistanceValues p,
            (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) * (4 * ρ ^ 2 - r ^ 2) :=
          add_le_add (Finset.sum_le_sum fun q _ ↦ hq q)
            (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r hr' ↦ hr r hr') (by norm_num))
      _ = _ := by
          rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ j)]
  -- The sum over the cells, scaled by `ρ²`.
  have hkey : ∀ l ∈ Finset.range k,
      (τ (l + 1) - τ l) *
          (6 * (n : ℝ) *
              (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ τ l * ρ ^ 2)).card : ℝ) -
            ∑ j, ((((Finset.univ : Finset (Fin n)).filter
              (fun q ↦ dist (p j) (p q) ^ 2 ≤ τ l * ρ ^ 2)).card : ℝ) - 1)) * ρ ^ 2 =
        ∑ j, (τ (l + 1) - τ l) * ρ ^ 2 *
          (∑ q, (if j ≠ q ∧ dist (p j) (p q) ^ 2 ≤ τ l * ρ ^ 2 then (1 : ℝ) else 0) +
            2 * ∑ r ∈ OrderedDistanceValues p,
              (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) *
                (if r ^ 2 ≤ τ l * ρ ^ 2 then 1 else 0)) := by
    intro l hl
    have ht : 0 ≤ τ l * ρ ^ 2 :=
      mul_nonneg (hτnn l (Finset.mem_range.mp hl).le) hρ2.le
    rw [six_mul_palette_sub_closedBall_eq_sum_apex p ht, mul_right_comm, Finset.mul_sum]
  have hid := sum_four_sub_sq_add_two_weighted_deficit_eq hn hρsq
  have hmain :
      (∑ i ∈ Finset.range k, (τ (i + 1) - τ i) *
        (6 * (n : ℝ) *
            (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ τ i * ρ ^ 2)).card : ℝ) -
          ∑ j, ((((Finset.univ : Finset (Fin n)).filter
            (fun q ↦ dist (p j) (p q) ^ 2 ≤ τ i * ρ ^ 2)).card : ℝ) - 1))) * ρ ^ 2 ≤
      (2 * (n : ℝ) ^ 2 + 8 * (n : ℝ) * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) -
        4 * (n : ℝ)) * ρ ^ 2 := by
    rw [Finset.sum_mul, Finset.sum_congr rfl hkey, Finset.sum_comm]
    calc ∑ j, ∑ l ∈ Finset.range k, (τ (l + 1) - τ l) * ρ ^ 2 *
            (∑ q, (if j ≠ q ∧ dist (p j) (p q) ^ 2 ≤ τ l * ρ ^ 2 then (1 : ℝ) else 0) +
              2 * ∑ r ∈ OrderedDistanceValues p,
                (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) *
                  (if r ^ 2 ≤ τ l * ρ ^ 2 then 1 else 0))
        ≤ ∑ j, (∑ q, (4 * ρ ^ 2 - dist (p j) (p q) ^ 2) - 4 * ρ ^ 2 +
            2 * ∑ r ∈ OrderedDistanceValues p,
              (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) * (4 * ρ ^ 2 - r ^ 2)) :=
          Finset.sum_le_sum fun j _ ↦ hapex j
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [← Finset.mul_sum]
          linear_combination hid
  exact le_of_mul_le_mul_right hmain hρ2

/-- The lower Riemann sum of the second-moment identity on seven cells with top threshold `4`
(row 6 of Theorem C60 in count form). Under the degree cap three, with `ρ > 0`,
`ρ² = distanceAnnulusRadiusSq p` and squared grid values `0 ≤ τ₁ ≤ … ≤ τ₇ ≤ 4`,
`Σ_{i=1}^{7} (τ_{i+1} - τ_i) (6n R(τ_i ρ²) - P(τ_i ρ²)) ≤ 2n² + 8nQ - 4n` with `τ₈ = 4`,
where `R(t)` counts the palette values `r` with `r² ≤ t`, `P(t) = Σ_j (N_j(t) - 1)` and
`Q = 3D - n + 1`. -/
theorem second_moment_lower_sum_le_seven {p : Config n} (hn : 0 < n)
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) {ρ : ℝ} (hρ : 0 < ρ)
    (hρsq : ρ ^ 2 = distanceAnnulusRadiusSq p) {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ τ₇ : ℝ}
    (h₀ : 0 ≤ τ₁) (h₁ : τ₁ ≤ τ₂) (h₂ : τ₂ ≤ τ₃) (h₃ : τ₃ ≤ τ₄) (h₄ : τ₄ ≤ τ₅)
    (h₅ : τ₅ ≤ τ₆) (h₆ : τ₆ ≤ τ₇) (h₇ : τ₇ ≤ 4) :
    (τ₂ - τ₁) *
          (6 * (n : ℝ) *
              (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ τ₁ * ρ ^ 2)).card : ℝ) -
            ∑ j, ((((Finset.univ : Finset (Fin n)).filter
              (fun q ↦ dist (p j) (p q) ^ 2 ≤ τ₁ * ρ ^ 2)).card : ℝ) - 1)) +
        (τ₃ - τ₂) *
          (6 * (n : ℝ) *
              (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ τ₂ * ρ ^ 2)).card : ℝ) -
            ∑ j, ((((Finset.univ : Finset (Fin n)).filter
              (fun q ↦ dist (p j) (p q) ^ 2 ≤ τ₂ * ρ ^ 2)).card : ℝ) - 1)) +
        (τ₄ - τ₃) *
          (6 * (n : ℝ) *
              (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ τ₃ * ρ ^ 2)).card : ℝ) -
            ∑ j, ((((Finset.univ : Finset (Fin n)).filter
              (fun q ↦ dist (p j) (p q) ^ 2 ≤ τ₃ * ρ ^ 2)).card : ℝ) - 1)) +
        (τ₅ - τ₄) *
          (6 * (n : ℝ) *
              (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ τ₄ * ρ ^ 2)).card : ℝ) -
            ∑ j, ((((Finset.univ : Finset (Fin n)).filter
              (fun q ↦ dist (p j) (p q) ^ 2 ≤ τ₄ * ρ ^ 2)).card : ℝ) - 1)) +
        (τ₆ - τ₅) *
          (6 * (n : ℝ) *
              (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ τ₅ * ρ ^ 2)).card : ℝ) -
            ∑ j, ((((Finset.univ : Finset (Fin n)).filter
              (fun q ↦ dist (p j) (p q) ^ 2 ≤ τ₅ * ρ ^ 2)).card : ℝ) - 1)) +
        (τ₇ - τ₆) *
          (6 * (n : ℝ) *
              (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ τ₆ * ρ ^ 2)).card : ℝ) -
            ∑ j, ((((Finset.univ : Finset (Fin n)).filter
              (fun q ↦ dist (p j) (p q) ^ 2 ≤ τ₆ * ρ ^ 2)).card : ℝ) - 1)) +
        (4 - τ₇) *
          (6 * (n : ℝ) *
              (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ τ₇ * ρ ^ 2)).card : ℝ) -
            ∑ j, ((((Finset.univ : Finset (Fin n)).filter
              (fun q ↦ dist (p j) (p q) ^ 2 ≤ τ₇ * ρ ^ 2)).card : ℝ) - 1)) ≤
      2 * (n : ℝ) ^ 2 + 8 * (n : ℝ) * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) -
        4 * (n : ℝ) := by
  have h := second_moment_lower_sum_le hn hcap hρ hρsq (k := 7)
    (fun i ↦ [τ₁, τ₂, τ₃, τ₄, τ₅, τ₆, τ₇, 4].getD i 0) (by simpa using h₀)
    (fun i hi ↦ by interval_cases i <;> simpa) (by simp)
  simpa [Finset.sum_range_succ] using h

end Esgk
