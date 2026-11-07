/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.CentroidFunctionalBounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The averaged cap of the layer cake at a general cut

Formalizes Lemma K of `docs/results/explicit-constant-gain-5-239-2026-10-20.md` (§2), as used
by the row `K` of Theorem S4 in `docs/results/explicit-constant-gain-1-40-2026-10-21.md`.

The points lie in the annulus `σ²ρ² ≤ |p_i - c|² ≤ ρ²` about their centroid `c`, with `0 < σ`.
Write `P(t) = Σ_j (N_j(t) - 1)` for the number of ordered pairs at squared distance at most `t`,
where `N_j(t)` counts the points within squared distance `t` of `p j` (the centre included).

* The cap at one point (`sum_max_sub_sq_dist_le_two_mul`): with the unit-direction functional
  `F_z(q) = 1 + ⟪p_q - c, p_z - c⟫/(ρ‖p_z - c‖)`, which is nonnegative and sums to `n`,
  `Σ_q max(0, (2σ² + 2σ)ρ² - |p_z - p_q|²) ≤ 2σnρ²`. In the source this is
  `F_z(q) ≥ φ_σ(|p_z - p_q|/ρ) = (ρ_e² - |p_z - p_q|²/ρ²)/(2σ)` with `ρ_e² = 2σ² + 2σ`.
* The averaged cap (`sum_increment_mul_sum_closedBall_sq_card_sub_one_le_two_mul`): for squared
  grid values `τ 0 ≤ τ 1 ≤ … ≤ τ k ≤ 2σ² + 2σ`, the discrete layer cake
  (`discrete_layer_cake_le`) and the sum over the points give
  `Σ_{i<k} (τ (i+1) - τ i) P(τ i ρ²) ≤ 2σn²`. This is the S2 row
  `Σ_i 𝒜(g_i)(g_{i+1}² - g_i²) ≤ 2sBar` times `n²`; the self term `n Σ_i (τ (i+1) - τ i) ≥ 0` of
  `Σ_z N_z = P + n` is dropped.
-/

@[expose] public section

namespace Esgk

open scoped RealInnerProductSpace

variable {n : ℕ}

/-- Lemma K at one point: in the annulus `σ²ρ² ≤ dist · c² ≤ ρ²` about the centroid `c`, with
`0 < σ`, `Σ_q max(0, (2σ² + 2σ)ρ² - |p z - p q|²) ≤ 2σnρ²`. Pointwise,
`‖p z - c‖ · max(0, (2σ² + 2σ)ρ² - |p z - p q|²) ≤ 2σρ (ρ‖p z - c‖ + ⟪p q - c, p z - c⟫)`, and
the right side sums to `2σnρ²‖p z - c‖`. -/
private lemma sum_max_sub_sq_dist_le_two_mul {p : Config n} {c : Point} {ρ σ : ℝ}
    (hsum : ∑ i, (p i - c) = 0) (hρ : 0 < ρ) (hσ : 0 < σ)
    (hlo : ∀ i, σ ^ 2 * ρ ^ 2 ≤ dist (p i) c ^ 2)
    (hhi : ∀ i, dist (p i) c ^ 2 ≤ ρ ^ 2) (z : Fin n) :
    ∑ q, max 0 ((2 * σ ^ 2 + 2 * σ) * ρ ^ 2 - dist (p z) (p q) ^ 2) ≤
      2 * σ * n * ρ ^ 2 := by
  obtain ⟨hf0, hfsum⟩ := unit_direction_functional hsum hρ hhi z
  have hAd : ‖p z - c‖ = dist (p z) c := (dist_eq_norm _ _).symm
  set A := ‖p z - c‖ with hA
  have hσρ : σ * ρ ≤ A := by
    rw [hAd]; exact (abs_le_of_sq_le_sq' (by rw [mul_pow]; exact hlo z) dist_nonneg).2
  have hA0 : 0 < A := (mul_pos hσ hρ).trans_le hσρ
  have hσρ0 : 0 ≤ σ * ρ := (mul_pos hσ hρ).le
  have hpt : ∀ q, A * max 0 ((2 * σ ^ 2 + 2 * σ) * ρ ^ 2 - dist (p z) (p q) ^ 2) ≤
      2 * σ * ρ * (ρ * A + ⟪p q - c, p z - c⟫) := by
    intro q
    rcases le_total ((2 * σ ^ 2 + 2 * σ) * ρ ^ 2 - dist (p z) (p q) ^ 2) 0 with hneg | hpos
    · rw [max_eq_left hneg, mul_zero]
      exact mul_nonneg (by positivity) (hf0 q)
    · rw [max_eq_right hpos]
      have hin := two_mul_inner_sub_center (p q) (p z) c
      rw [← hAd, dist_comm (p q) (p z)] at hin
      have k1 : 0 ≤ σ * ρ * (A - σ * ρ) ^ 2 := mul_nonneg hσρ0 (sq_nonneg _)
      have k2 : 0 ≤ dist (p z) (p q) ^ 2 * (A - σ * ρ) :=
        mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hσρ)
      have k3 : σ * ρ * (σ ^ 2 * ρ ^ 2) ≤ σ * ρ * dist (p q) c ^ 2 :=
        mul_le_mul_of_nonneg_left (hlo q) hσρ0
      nlinarith
  have hs := Finset.sum_le_sum fun q (_ : q ∈ (Finset.univ : Finset (Fin n))) ↦ hpt q
  rw [← Finset.mul_sum, ← Finset.mul_sum, hfsum] at hs
  have hmain : A * ∑ q, max 0 ((2 * σ ^ 2 + 2 * σ) * ρ ^ 2 - dist (p z) (p q) ^ 2) ≤
      A * (2 * σ * n * ρ ^ 2) := by
    calc A * ∑ q, max 0 ((2 * σ ^ 2 + 2 * σ) * ρ ^ 2 - dist (p z) (p q) ^ 2)
        ≤ 2 * σ * ρ * (n * (ρ * A)) := hs
      _ = A * (2 * σ * n * ρ ^ 2) := by ring
  exact le_of_mul_le_mul_left hmain hA0

/-- Averaged layer-cake cap (Lemma K of the S2 file at a general cut; the S2 row
`Σ_i 𝒜(g_i)(g_{i+1}² - g_i²) ≤ 2sBar` times `n²`). Let the points lie in the annulus
`σ²ρ² ≤ |p_i - c|² ≤ ρ²` about their centroid `c`, with `0 < σ`. For squared grid values
`τ 0 ≤ τ 1 ≤ … ≤ τ k` with `τ k ≤ 2σ² + 2σ`,
`Σ_{i<k} (τ (i+1) - τ i) P(τ i ρ²) ≤ 2σn²`, where `P(t) = Σ_j (N_j(t) - 1)` counts the ordered
pairs at squared distance at most `t`. No sign condition on `τ 0` is needed. -/
theorem sum_increment_mul_sum_closedBall_sq_card_sub_one_le_two_mul {p : Config n}
    {c : Point} {ρ σ : ℝ}
    (hsum : ∑ i, (p i - c) = 0) (hρ : 0 < ρ) (hσ : 0 < σ)
    (hlo : ∀ i, σ ^ 2 * ρ ^ 2 ≤ dist (p i) c ^ 2)
    (hhi : ∀ i, dist (p i) c ^ 2 ≤ ρ ^ 2) {k : ℕ} (τ : ℕ → ℝ)
    (hτ : ∀ i < k, τ i ≤ τ (i + 1)) (hτk : τ k ≤ 2 * σ ^ 2 + 2 * σ) :
    ∑ i ∈ Finset.range k, (τ (i + 1) - τ i) * ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ τ i * ρ ^ 2)).card : ℝ) - 1) ≤
      2 * σ * (n : ℝ) ^ 2 := by
  classical
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hτk' := mul_le_mul_of_nonneg_right hτk hρ2.le
  -- the discrete layer cake at one point, capped by the unit-direction functional
  have hz : ∀ z : Fin n, ∑ i ∈ Finset.range k, ((((Finset.univ : Finset (Fin n)).filter
      (fun q ↦ dist (p z) (p q) ^ 2 ≤ τ i * ρ ^ 2)).card : ℝ) - 1) *
        (τ (i + 1) * ρ ^ 2 - τ i * ρ ^ 2) ≤ 2 * σ * n * ρ ^ 2 := by
    intro z
    have hcake : ∑ i ∈ Finset.range k, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p z) (p q) ^ 2 ≤ τ i * ρ ^ 2)).card : ℝ) - 1) *
          (τ (i + 1) * ρ ^ 2 - τ i * ρ ^ 2) ≤
        ∑ q, max 0 (τ k * ρ ^ 2 - dist (p z) (p q) ^ 2) :=
      discrete_layer_cake_le z (fun i ↦ τ i * ρ ^ 2)
        (fun i ↦ ((((Finset.univ : Finset (Fin n)).filter
          (fun q ↦ dist (p z) (p q) ^ 2 ≤ τ i * ρ ^ 2)).card : ℝ) - 1))
        (fun i hi ↦ mul_le_mul_of_nonneg_right (hτ i hi) hρ2.le)
        (fun i _ ↦ by linarith)
    have hcut : ∑ q, max 0 (τ k * ρ ^ 2 - dist (p z) (p q) ^ 2) ≤
        ∑ q, max 0 ((2 * σ ^ 2 + 2 * σ) * ρ ^ 2 - dist (p z) (p q) ^ 2) :=
      Finset.sum_le_sum fun q _ ↦ max_le_max le_rfl (by linarith)
    exact hcake.trans (hcut.trans (sum_max_sub_sq_dist_le_two_mul hsum hρ hσ hlo hhi z))
  -- sum over the points and exchange the order of summation
  have htot := Finset.sum_le_sum fun z (_ : z ∈ (Finset.univ : Finset (Fin n))) ↦ hz z
  rw [Finset.sum_comm] at htot
  have hfac : ∀ i ∈ Finset.range k, ∑ z, ((((Finset.univ : Finset (Fin n)).filter
      (fun q ↦ dist (p z) (p q) ^ 2 ≤ τ i * ρ ^ 2)).card : ℝ) - 1) *
        (τ (i + 1) * ρ ^ 2 - τ i * ρ ^ 2) =
      ρ ^ 2 * ((τ (i + 1) - τ i) * ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ τ i * ρ ^ 2)).card : ℝ) - 1)) := by
    intro i _
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ ↦ by ring
  rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at htot
  have hmain : ρ ^ 2 * ∑ i ∈ Finset.range k, (τ (i + 1) - τ i) *
      ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ τ i * ρ ^ 2)).card : ℝ) - 1) ≤
      ρ ^ 2 * (2 * σ * (n : ℝ) ^ 2) := by
    calc _ ≤ (n : ℝ) * (2 * σ * n * ρ ^ 2) := htot
      _ = ρ ^ 2 * (2 * σ * (n : ℝ) ^ 2) := by ring
  exact le_of_mul_le_mul_left hmain hρ2

end Esgk
