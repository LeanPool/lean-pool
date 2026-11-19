/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import LeanPool.HubbardMoments.TorusBandDefinition
public import LeanPool.HubbardMoments.FinitePopulation
public import LeanPool.HubbardMoments.ProjectedHopping
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The tight-binding band of the torus and the `U = 0` moments

The single-particle energies of the `L × L` torus are
`ε(q) = -2t (cos q₁ + cos q₂)`, `q = 2π (m₁, m₂)/L` (`HubbardMoments.torusBand`).

* `torusBand_sum`: `∑_q ε(q) = 0` for `L ≥ 2`;
* `torusBand_sum_sq`: `∑_q ε(q)² = 4t² L²` for `L ≥ 3`, i.e. `σ₁² = z t²` with `z = 4`;
* `sampleMoment_torusBand_two`: for `n` free fermions of one spin species,
  `μ₂ = t² · 4n(L² - n)/(L² - 1)` (§5.3);
* `sampleMoment_torusBand_eq_secondMoment`: this equals the `U = ∞` second moment of
  `HubbardMoments.second_moment_torus` for one spin species: the momentum-space count
  (sampling without replacement) and the real-space count (hops to empty neighbours) agree;
* `fpc_table`: the six exact values of the paper's finite-population table (`L = 4`,
  `k = 2, 3, 4`, `t = 1`).

## Not covered

That the many-body energies of free fermions of one species are sums of distinct
single-particle energies (Slater determinants), and that `torusBand` is the spectrum of the
hopping matrix of `torus L` (plane waves). Both are standard.
-/

@[expose] public section

namespace HubbardMoments

open Finset Real

/-- A cosine sum over a full period vanishes. -/
theorem sum_range_cos_mul_eq_zero {L : ℕ} {a : ℝ} (ha : sin (a / 2) ≠ 0)
    (hLa : sin (L * a / 2) = 0) : ∑ i ∈ range L, cos (a * i) = 0 := by
  have h := Real.sin_mul_sum_cos L a 0
  simp only [add_zero, hLa, zero_mul] at h
  exact (mul_eq_zero.1 h).resolve_left ha

/-- `∑_{m < L} cos(2πm/L) = 0` for `L ≥ 2`. -/
theorem sum_cos_two_pi {L : ℕ} (hL : 2 ≤ L) :
    ∑ m : Fin L, cos (2 * π * (m : ℕ) / L) = 0 := by
  have hL0 : (0 : ℝ) < L := by positivity
  have hL1 : (1 : ℝ) < L := by exact_mod_cast hL
  rw [Fin.sum_univ_eq_sum_range (fun i => cos (2 * π * i / L))]
  have h := sum_range_cos_mul_eq_zero (L := L) (a := 2 * π / L)
    (ne_of_gt (sin_pos_of_pos_of_lt_pi (by positivity) (by
      rw [show 2 * π / L / 2 = π / L by ring]
      exact div_lt_self pi_pos hL1)))
    (by rw [show (L : ℝ) * (2 * π / L) / 2 = π by field_simp, sin_pi])
  rw [← h]
  exact sum_congr rfl fun i _ => by congr 1; ring

/-- `∑_{m < L} cos²(2πm/L) = L/2` for `L ≥ 3`. -/
theorem sum_cos_sq_two_pi {L : ℕ} (hL : 3 ≤ L) :
    ∑ m : Fin L, cos (2 * π * (m : ℕ) / L) ^ 2 = L / 2 := by
  have hL0 : (0 : ℝ) < L := by positivity
  have hL2 : (2 : ℝ) < L := by exact_mod_cast hL
  simp only [cos_sq, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← sum_div]
  rw [Fin.sum_univ_eq_sum_range (fun i => cos (2 * (2 * π * i / L)))]
  have h := sum_range_cos_mul_eq_zero (L := L) (a := 4 * π / L)
    (ne_of_gt (sin_pos_of_pos_of_lt_pi (by positivity) (by
      rw [show 4 * π / L / 2 = π * (2 / L) by ring]
      exact mul_lt_of_lt_one_right pi_pos ((div_lt_one hL0).2 hL2))))
    (by rw [show (L : ℝ) * (4 * π / L) / 2 = (2 : ℕ) * π by field_simp; ring,
      sin_nat_mul_pi])
  rw [show ∑ i ∈ range L, cos (2 * (2 * π * i / L)) = ∑ i ∈ range L, cos (4 * π / L * i) from
    sum_congr rfl fun i _ => by congr 1; ring, h]
  ring

/-- **The band is centred:** `∑_q ε(q) = 0` for `L ≥ 2`. -/
theorem torusBand_sum {L : ℕ} (hL : 2 ≤ L) (t : ℝ) : ∑ q, torusBand L t q = 0 := by
  simp only [torusBand, Fintype.sum_prod_type, ← mul_sum, sum_add_distrib, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, sum_cos_two_pi hL, mul_zero, add_zero]

/-- **The band variance:** `∑_q ε(q)² = 4t² L²` for `L ≥ 3`, so `σ₁² = 4t² = z t²`. -/
theorem torusBand_sum_sq {L : ℕ} (hL : 3 ≤ L) (t : ℝ) :
    ∑ q, torusBand L t q ^ 2 = 4 * t ^ 2 * L ^ 2 := by
  have e : ∀ q : Fin L × Fin L, torusBand L t q ^ 2 =
      4 * t ^ 2 * cos (2 * π * (q.1 : ℕ) / L) ^ 2 + 4 * t ^ 2 * cos (2 * π * (q.2 : ℕ) / L) ^ 2 +
        8 * t ^ 2 * (cos (2 * π * (q.1 : ℕ) / L) * cos (2 * π * (q.2 : ℕ) / L)) :=
    fun q => by simp only [torusBand]; ring
  simp only [e, Fintype.sum_prod_type, sum_add_distrib, ← mul_sum, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, sum_cos_sq_two_pi hL, sum_cos_two_pi (by omega : 2 ≤ L),
    mul_zero, add_zero]
  ring

/-- **`μ₂` at `U = 0` for one spin species on the torus** (§5.3): `n` free fermions of one
species on the `L × L` torus (`L ≥ 3`) have `μ₂ = t² · 4n(L² - n)/(L² - 1)`. -/
theorem sampleMoment_torusBand_two {L : ℕ} (hL : 3 ≤ L) (t : ℝ) {n : ℕ} (hn : n ≤ L * L) :
    sampleMoment (torusBand L t) n 2 = t ^ 2 * 4 * n * (L * L - n) / (L * L - 1) := by
  have hcard : Fintype.card (Fin L × Fin L) = L * L := by simp
  rw [sampleMoment_two_fpc (torusBand_sum (by omega) t) (by rw [hcard]; exact hn)
    (by rw [hcard]; nlinarith), torusBand_sum_sq hL, hcard]
  have hL0 : (L : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

/-- **The `U = 0` and `U = ∞` second moments agree for one spin species.** For one species
there is no double occupancy, so the two limits describe the same particles; the
momentum-space count of `sampleMoment_torusBand_two` and the real-space count of
`second_moment_torus` give the same `μ₂`. -/
theorem sampleMoment_torusBand_eq_secondMoment {L : ℕ} (hL : 3 ≤ L) {t : ℝ}
    {H : Matrix (Config (Fin L × Fin L) Unit) (Config (Fin L × Fin L) Unit) ℂ}
    (hH : IsProjectedHopping (torus L) t H) {n : ℕ}
    (hB : (basis (Fin L × Fin L) (fun _ : Unit => n)).Nonempty) :
    (sampleMoment (torusBand L t) n 2 : ℂ) =
      secondMoment (basis (Fin L × Fin L) (fun _ : Unit => n)) H := by
  obtain ⟨c, hc⟩ := hB
  have hn : n ≤ L * L := by
    have hcard := card_occ hc
    simp only [univ_unique, sum_singleton] at hcard
    simpa [hcard, Fintype.card_prod] using card_le_univ (occ c)
  rw [second_moment_torus hL hH _ ⟨c, hc⟩, sampleMoment_torusBand_two hL t hn]
  simp only [Finset.univ_unique, sum_singleton]
  push_cast
  ring

/-! ### The paper's finite-population table (`L = 4`, `t = 1`) -/

/-- The four cosines of the `L = 4` momentum grid: `1, 0, -1, 0`. -/
theorem cos_two_pi_div_four (m : Fin 4) : cos (2 * π * (m : ℕ) / 4) = ![1, 0, -1, 0] m := by
  fin_cases m
  · simp
  · simp only [Fin.mk_one, Nat.cast_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [show 2 * π * 1 / 4 = π / 2 by ring, cos_pi_div_two]
  · simp only [Fin.reduceFinMk, Matrix.cons_val]
    rw [show 2 * π * ((2 : ℕ) : ℝ) / 4 = π by push_cast; ring, cos_pi]
  · simp only [Fin.reduceFinMk, Matrix.cons_val]
    rw [show 2 * π * ((3 : ℕ) : ℝ) / 4 = π / 2 + π by push_cast; ring, cos_add_pi,
      cos_pi_div_two, neg_zero]

/-- `P₄ = ∑_q ε(q)⁴ = 640` at `L = 4`, `t = 1`. -/
theorem torusBand_four_sum_pow_four : ∑ q, torusBand 4 1 q ^ 4 = 640 := by
  simp only [torusBand, Fintype.sum_prod_type, Fin.sum_univ_four, Nat.cast_ofNat,
    cos_two_pi_div_four]
  norm_num

/-- **The finite-population table** (`L = 4`, `t = 1`): `μ₂` and `μ₄` of `k = 2, 3, 4` free
fermions of one species are `112/15, 2176/15`; `52/5, 9976/35`; `64/5, 197632/455`. -/
theorem fpc_table :
    sampleMoment (torusBand 4 1) 2 2 = 112 / 15 ∧ sampleMoment (torusBand 4 1) 2 4 = 2176 / 15 ∧
    sampleMoment (torusBand 4 1) 3 2 = 52 / 5 ∧ sampleMoment (torusBand 4 1) 3 4 = 9976 / 35 ∧
    sampleMoment (torusBand 4 1) 4 2 = 64 / 5 ∧
      sampleMoment (torusBand 4 1) 4 4 = 197632 / 455 := by
  have hε := torusBand_sum (L := 4) (by norm_num) 1
  have hP₂ : ∑ q, torusBand 4 1 q ^ 2 = 64 := by rw [torusBand_sum_sq (by norm_num)]; norm_num
  have hcard : Fintype.card (Fin 4 × Fin 4) = 16 := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [sampleMoment_torusBand_two (by norm_num) 1 (by norm_num)]; norm_num)
    | (rw [sampleMoment_four hε (by rw [hcard]; norm_num), hP₂, torusBand_four_sum_pow_four,
        hcard]
       norm_num [inclusionProb, Nat.descFactorial])

end HubbardMoments
