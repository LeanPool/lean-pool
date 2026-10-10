/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Arithmetic.Estimates
public import Mathlib.Tactic.Positivity

/-!
Constants and positive thresholds for the corrected analytic iteration. The iteration exponent
is 8 * n + 24. Explicit identities verify the exponent balance in the remainder recurrence.
-/

@[expose] public section
noncomputable section
namespace KamProject.Arnold1963

/-- The small-divisor exponent used for arithmetic resonance bounds. -/
def arithmeticExponent (n : ℕ) : ℕ := n + 1
/-- The dimension-dependent exponent in the homological equation estimates. -/
def homologicalExponent (n : ℕ) : ℕ := 2 * n + 1
/-- The exponent governing the nonlinear remainder bound of one KAM step. -/
def stepExponent (n : ℕ) : ℕ := 2 * n + 3
/-- The initial perturbation exponent chosen to sustain the full iteration. -/
def iterationExponent (n : ℕ) : ℕ := 8 * n + 24

/-- The exponential coefficient used in dimension-dependent KAM estimates. -/
def constantL0 (n : ℕ) : ℝ := ((n + 1 : ℝ) / Real.exp 1) ^ (n + 1)
/-- The dimension-dependent coefficient used to bound the homological solution. -/
def constantL5 (n : ℕ) : ℝ := 4 ^ n * constantL0 n
/-- The numerical coefficient entering the first smallness threshold. -/
def constantL2 (n : ℕ) : ℝ := 16 * n * constantL5 n
/-- The numerical coefficient entering the quadratic remainder estimate. -/
def constantL3 (n : ℕ) : ℝ := (1 / 2 : ℝ) * n ^ 2 * constantL5 n ^ 2
/-- The exponential tail coefficient entering the Fourier remainder estimate. -/
def constantL4 (n : ℕ) : ℝ := 2 * ((2 * n : ℝ) / Real.exp 1) ^ n

/-- The common smallness bound for the fundamental step's numerical estimates. -/
def threshold0 (n : ℕ) (Θ : ℝ) : ℝ :=
  min (1 / 12) (min (constantL2 n)⁻¹ (min ((constantL3 n)⁻¹ * Θ⁻¹) (constantL4 n)⁻¹))
/-- The fundamental smallness bound adjusted for frequency-chart derivative bounds. -/
def threshold1 (n : ℕ) (θ Θ : ℝ) : ℝ := min (threshold0 n (2 * Θ)) (θ / (2 * n))
/-- The smallness bound controlling strip widths and the requested measure tolerance. -/
def threshold2 (n : ℕ) (κ ρ : ℝ) : ℝ :=
  min (((10 : ℝ) ^ (4 * n))⁻¹ * ρ ^ (4 * n)) (min ((4 : ℝ) ^ (4 * n))⁻¹ κ)
/-- The smallness bound controlling frequency-domain losses and their measure budget. -/
def threshold3 (n : ℕ) (θ Θ κ D : ℝ) : ℝ :=
  min (Real.exp (2 * n) / (32 * n ^ 2 + 100 * n) ^ (2 * n))
    (min (1 / (6 + 14 * Θ)) (((4 : ℝ) ^ (n + 2))⁻¹ * κ * θ ^ n / (Θ ^ n * D * n)))
/-- The smallness bound balancing the measure tolerance with the lower derivative bound. -/
def threshold4 (κ θ : ℝ) : ℝ := κ / (2 + θ⁻¹)
/-- The common initial smallness bound combining all iteration constraints. -/
def threshold5 (n : ℕ) (θ Θ ρ κ D : ℝ) : ℝ :=
  min (threshold1 n (θ / 2) (2 * Θ))
    (min (threshold2 n κ ρ) (min (threshold3 n θ Θ κ D) (threshold4 κ θ)))

theorem constants_pos {n : ℕ} (hn : 0 < n) :
    0 < constantL0 n ∧ 0 < constantL5 n ∧ 0 < constantL2 n ∧
      0 < constantL3 n ∧ 0 < constantL4 n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  dsimp [constantL0, constantL5, constantL2, constantL3, constantL4]
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor <;> positivity

theorem threshold0_pos {n : ℕ} (hn : 0 < n) {Θ : ℝ} (hΘ : 0 < Θ) :
    0 < threshold0 n Θ := by
  obtain ⟨_, _, h2, h3, h4⟩ := constants_pos hn
  unfold threshold0
  positivity

theorem threshold1_pos {n : ℕ} (hn : 0 < n) {θ Θ : ℝ}
    (hθ : 0 < θ) (hΘ : 0 < Θ) : 0 < threshold1 n θ Θ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  exact lt_min (threshold0_pos hn (by positivity)) (by positivity)

theorem threshold0_bounds {n : ℕ} {Θ δ : ℝ} (h : δ < threshold0 n Θ) :
    δ < 1 / 12 ∧ δ < (constantL2 n)⁻¹ ∧
      δ < (constantL3 n)⁻¹ * Θ⁻¹ ∧ δ < (constantL4 n)⁻¹ := by
  simpa only [threshold0, lt_min_iff] using h

theorem threshold0_budget_conditions {n : ℕ} (hn : 0 < n) {Θ δ : ℝ}
    (hΘ : 0 < Θ) (hδ : δ < threshold0 n Θ) :
    δ < 1 / 12 ∧ δ * constantL2 n < 1 ∧
      δ * (constantL3 n * Θ) < 1 ∧ δ * constantL4 n < 1 := by
  obtain ⟨hsmall, h2, h3, h4⟩ := threshold0_bounds hδ
  obtain ⟨_, _, hL2, hL3, hL4⟩ := constants_pos hn
  refine ⟨hsmall, ?_, ?_, ?_⟩
  · exact (lt_div_iff₀ hL2).mp (by simpa only [one_div] using h2)
  · exact (lt_div_iff₀ (mul_pos hL3 hΘ)).mp (by
      simpa only [one_div, mul_inv] using h3)
  · exact (lt_div_iff₀ hL4).mp (by simpa only [one_div] using h4)

theorem threshold1_bounds {n : ℕ} {θ Θ δ : ℝ} (h : δ < threshold1 n θ Θ) :
    δ < threshold0 n (2 * Θ) ∧ δ < θ / (2 * n) := lt_min_iff.mp h

theorem threshold5_bounds {n : ℕ} {θ Θ ρ κ D δ : ℝ}
    (h : δ < threshold5 n θ Θ ρ κ D) :
    δ < threshold1 n (θ / 2) (2 * Θ) ∧ δ < threshold2 n κ ρ ∧
      δ < threshold3 n θ Θ κ D ∧ δ < threshold4 κ θ := by
  simpa only [threshold5, lt_min_iff] using h

theorem threshold2_pos (n : ℕ) {κ ρ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ) :
    0 < threshold2 n κ ρ := by
  unfold threshold2
  positivity

theorem threshold3_pos {n : ℕ} (hn : 0 < n) {θ Θ κ D : ℝ}
    (hθ : 0 < θ) (hΘ : 0 < Θ) (hκ : 0 < κ) (hD : 0 < D) :
    0 < threshold3 n θ Θ κ D := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold threshold3
  positivity

theorem threshold4_pos {κ θ : ℝ} (hκ : 0 < κ) (hθ : 0 < θ) :
    0 < threshold4 κ θ := by unfold threshold4; positivity

theorem threshold5_pos {n : ℕ} (hn : 0 < n) {θ Θ ρ κ D : ℝ}
    (hθ : 0 < θ) (hΘ : 0 < Θ) (hρ : 0 < ρ) (hκ : 0 < κ) (hD : 0 < D) :
    0 < threshold5 n θ Θ ρ κ D := by
  exact lt_min (threshold1_pos hn (by positivity) (by positivity))
    (lt_min (threshold2_pos n hκ hρ)
      (lt_min (threshold3_pos hn hθ hΘ hκ hD) (threshold4_pos hκ hθ)))

/-- The perturbation threshold obtained from the initial smallness bound and iteration exponent. -/
def initialPerturbationThreshold (n : ℕ) (θ Θ ρ κ D : ℝ) : ℝ :=
  (threshold5 n θ Θ ρ κ D / 2) ^ iterationExponent n

theorem initialPerturbationThreshold_pos {n : ℕ} (hn : 0 < n)
    {θ Θ ρ κ D : ℝ} (hθ : 0 < θ) (hΘ : 0 < Θ)
    (hρ : 0 < ρ) (hκ : 0 < κ) (hD : 0 < D) :
    0 < initialPerturbationThreshold n θ Θ ρ κ D := by
  have := threshold5_pos hn hθ hΘ hρ hκ hD
  unfold initialPerturbationThreshold
  positivity

theorem strengthened_budget_two_mul (M δ β : ℝ) (n : ℕ) :
    (1 / 4 : ℝ) * (2 * M) ^ 2 / (δ ^ (2 * stepExponent n) * β ^ 2) =
      M ^ 2 / (δ ^ (2 * stepExponent n) * β ^ 2) := by ring

theorem budget_exponent_identity (n : ℕ) :
    2 * iterationExponent n = 2 * stepExponent n + 6 + (12 * n + 36) := by
  unfold iterationExponent stepExponent
  omega

theorem budget_step_eq {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    (δ ^ iterationExponent n) ^ 2 / (δ ^ (2 * stepExponent n) * (δ ^ 3) ^ 2) =
      δ ^ (12 * n + 36) := by
  apply (div_eq_iff (by positivity : δ ^ (2 * stepExponent n) * (δ ^ 3) ^ 2 ≠ 0)).mpr
  simp only [← pow_mul, ← pow_add]
  congr 1
  unfold iterationExponent stepExponent
  omega

end KamProject.Arnold1963
