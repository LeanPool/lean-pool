/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Scalar algebra of the background multiplier

This module is the pure real-analysis core of the weighted test used in the
proof of `prop:background-resolvent`.  It has no repository dependencies.

The paper sets, in `eq:background-multiplier`,

`s_n(y) = Σ_m r_m ϑ(|y - p_m| / R_m)`,  `β_n = F(s_n)`,
`F(s) = (s - 1) / (1 + s)^2`,

and uses only four scalar facts about `F` on `[0, ∞)`:

* `|F| ≤ 1` and `√ε ‖∇β_n‖_∞ ≤ C √δ₊ d(K₀)` — `eq:background-multiplier-bounds`;
  the gradient half needs `F` to be Lipschitz, i.e. `F'` bounded;
* `|s F(s)| ≤ 1` — used for the local coefficient bound
  `eq:background-local-coefficients`;
* `F'(s) = (3 - s) / (1 + s)^3`, bounded on `[0, ∞)`, which is the chain rule
  input of `eq:background-multiplier-bounds` (the paper uses only that `F'` is bounded);
* the Young phase inequality `eq:background-phase-positive`,

  `β_n (Im ζ + τ (s_n - 1)) ≥ (τ/2) ((s_n - 1)/(s_n + 1))^2`
  `  - M^2 / (2 τ (1 + s_n)^2) ≥ (τ c_q^2 / 2) 1_{𝒞_n} - M^2 / (2 τ)`,

  together with the ratio gap `c_q = (q - 1)/(q + 1)` coming from `r_m ≥ q`
  for `m < n` and `r_m ≤ q⁻¹` for `m > n`.

Finally we record the explicit choice of `τ` in `eq:axial-separation-choice`:
`M^2/(2τ) ≤ g_*/4` and `τ c_q^2/2 ≥ C₀ + 1`.  The threshold is a
literal `max`, and `C₀`, `C₁`, `c_q` and `M` are all independent of `τ`, so the
order `τ` then `K₀` of `prop:background-resolvent` is non-circular.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

/-! ## The scalar profile `F` -/

/-- The scalar profile `F(s) = (s - 1)/(1 + s)^2` of the background multiplier
`β_n = F(s_n)`; see `eq:background-multiplier`. -/
def backgroundMultiplierF (s : ℝ) : ℝ := (s - 1) / (1 + s) ^ 2

/-- The derivative profile `F'(s) = (3 - s)/(1 + s)^3` appearing in the chain
rule of `eq:background-multiplier-bounds`. -/
def backgroundMultiplierDeriv (s : ℝ) : ℝ := (3 - s) / (1 + s) ^ 3

/-- Away from the pole `s = -1` the profile `F` is differentiable with
derivative `(3 - s)/(1 + s)^3`. -/
theorem hasDerivAt_backgroundMultiplierF {s : ℝ} (hs : 1 + s ≠ 0) :
    HasDerivAt backgroundMultiplierF (backgroundMultiplierDeriv s) s := by
  have hnum : HasDerivAt (fun y : ℝ => y - 1) 1 s := by
    simpa using (hasDerivAt_id s).sub_const 1
  have hden : HasDerivAt (fun y : ℝ => (1 + y) ^ 2)
      ((2 : ℝ) * (1 + s) ^ (2 - 1) * 1) s :=
    ((hasDerivAt_id s).const_add 1).pow 2
  have hne : ((1 : ℝ) + s) ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have h := hnum.div hden hne
  have hval : (1 * (1 + s) ^ 2 - (s - 1) * ((2 : ℝ) * (1 + s) ^ (2 - 1) * 1)) /
      ((1 + s) ^ 2) ^ 2 = backgroundMultiplierDeriv s := by
    rw [backgroundMultiplierDeriv]
    field_simp
    ring
  rw [hval] at h
  exact h

/-! ## The two uniform bounds of `eq:background-multiplier-bounds` -/

/-- `|F(s)| ≤ 1` for `s ≥ 0`.  This is the bound `|β_n| ≤ 1` of
`eq:background-multiplier-bounds`. -/
theorem abs_backgroundMultiplierF_le_one {s : ℝ} (hs : 0 ≤ s) :
    |backgroundMultiplierF s| ≤ 1 := by
  have h1 : (0 : ℝ) < 1 + s := by linarith
  have hpos : (0 : ℝ) < (1 + s) ^ 2 := by positivity
  rw [backgroundMultiplierF, abs_div, abs_of_pos hpos, div_le_one hpos]
  rcases le_or_gt 1 s with h | h
  · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ s - 1)]
    nlinarith
  · rw [abs_of_nonpos (by linarith : s - 1 ≤ 0)]
    nlinarith

/-- `|s F(s)| ≤ 1` for `s ≥ 0`.  This is the bound `|r F(r)| ≤ 1` used for the
local coefficients in `eq:background-local-coefficients`; it is what makes `C₀`
independent of `τ`. -/
theorem abs_mul_backgroundMultiplierF_le_one {s : ℝ} (hs : 0 ≤ s) :
    |s * backgroundMultiplierF s| ≤ 1 := by
  have h1 : (0 : ℝ) < 1 + s := by linarith
  have hpos : (0 : ℝ) < (1 + s) ^ 2 := by positivity
  have hrw : s * backgroundMultiplierF s = s * (s - 1) / (1 + s) ^ 2 := by
    rw [backgroundMultiplierF, mul_div_assoc']
  rw [hrw, abs_div, abs_of_pos hpos, div_le_one hpos]
  rcases le_or_gt 1 s with h | h
  · rw [abs_of_nonneg (by nlinarith : (0 : ℝ) ≤ s * (s - 1))]
    nlinarith
  · rw [abs_of_nonpos (by nlinarith : s * (s - 1) ≤ 0)]
    nlinarith

/-- `|F'(s)| ≤ 3` for `s ≥ 0`.  The bound is attained at `s = 0`, so it is
sharp.  This is the Lipschitz constant used in the chain rule bound
`√ε ‖∇β_n‖_∞ ≤ C √δ₊ d(K₀)` of `eq:background-multiplier-bounds`. -/
theorem abs_backgroundMultiplierDeriv_le_three {s : ℝ} (hs : 0 ≤ s) :
    |backgroundMultiplierDeriv s| ≤ 3 := by
  have h1 : (0 : ℝ) < 1 + s := by linarith
  have hpos : (0 : ℝ) < (1 + s) ^ 3 := by positivity
  have hcube : (1 : ℝ) + 3 * s ≤ (1 + s) ^ 3 := by nlinarith [sq_nonneg s]
  rw [backgroundMultiplierDeriv, abs_div, abs_of_pos hpos,
    div_le_iff₀ hpos]
  rcases le_or_gt s 3 with h | h
  · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 3 - s)]
    linarith
  · rw [abs_of_nonpos (by linarith : 3 - s ≤ 0)]
    linarith

/-! ## The Young phase inequality -/

/-- **Sharp Young phase inequality**, the first line of
`eq:background-phase-positive`:

`F(s) (t + τ (s - 1)) ≥ (τ/2) ((s-1)/(1+s))^2 - M^2 / (2 τ (1 + s)^2)`

for `s ≥ 0`, `τ > 0` and any `t` with `|t| ≤ M` (in the application
`t = Im ζ` and `M = max_{ζ ∈ 𝒢} |Im ζ|`). -/
theorem backgroundMultiplierF_phase_lower_bound_sharp
    {s t M τ : ℝ} (hs : 0 ≤ s) (hτ : 0 < τ) (ht : |t| ≤ M) :
    τ / 2 * ((s - 1) / (1 + s)) ^ 2 - M ^ 2 / (2 * τ * (1 + s) ^ 2) ≤
      backgroundMultiplierF s * (t + τ * (s - 1)) := by
  have h1 : (0 : ℝ) < 1 + s := by linarith
  have hne : (1 : ℝ) + s ≠ 0 := ne_of_gt h1
  have hτne : τ ≠ 0 := ne_of_gt hτ
  have hbounds := abs_le.mp ht
  have ht2 : t ^ 2 ≤ M ^ 2 := by nlinarith [hbounds.1, hbounds.2]
  have hden : (0 : ℝ) < 2 * τ * (1 + s) ^ 2 :=
    mul_pos (by linarith) (pow_pos h1 2)
  rw [← sub_nonneg]
  have hrw : backgroundMultiplierF s * (t + τ * (s - 1)) -
      (τ / 2 * ((s - 1) / (1 + s)) ^ 2 - M ^ 2 / (2 * τ * (1 + s) ^ 2)) =
      (2 * τ * (s - 1) * t + τ ^ 2 * (s - 1) ^ 2 + M ^ 2) /
        (2 * τ * (1 + s) ^ 2) := by
    rw [backgroundMultiplierF]
    field_simp
    ring
  rw [hrw]
  refine div_nonneg ?_ hden.le
  nlinarith [sq_nonneg (τ * (s - 1) + t), ht2]

/-- **Young phase inequality**, the form used in the coercivity estimate
`eq:background-coercivity`:

`F(s) (t + τ (s - 1)) ≥ (τ/2) ((s-1)/(1+s))^2 - M^2/(2 τ)`,

for `s ≥ 0`, `τ > 0`, `|t| ≤ M`.  It follows from the sharp form because
`(1 + s)^2 ≥ 1`. -/
theorem backgroundMultiplierF_phase_lower_bound
    {s t M τ : ℝ} (hs : 0 ≤ s) (hτ : 0 < τ) (ht : |t| ≤ M) :
    τ / 2 * ((s - 1) / (1 + s)) ^ 2 - M ^ 2 / (2 * τ) ≤
      backgroundMultiplierF s * (t + τ * (s - 1)) := by
  have h1 : (0 : ℝ) < 1 + s := by linarith
  have hM : 0 ≤ M := le_trans (abs_nonneg t) ht
  have hone : (1 : ℝ) ≤ (1 + s) ^ 2 := by nlinarith
  have hden : (0 : ℝ) < 2 * τ := by linarith
  have hstep : M ^ 2 / (2 * τ * (1 + s) ^ 2) ≤ M ^ 2 / (2 * τ) := by
    apply div_le_div_of_nonneg_left (by positivity) hden
    nlinarith
  have := backgroundMultiplierF_phase_lower_bound_sharp hs hτ ht
  linarith

/-! ## The ratio gap `c_q` -/

/-- The ratio gap `c_q = (q - 1)/(q + 1)` of the proof of
`prop:background-resolvent`. -/
def backgroundRatioGap (q : ℝ) : ℝ := (q - 1) / (1 + q)

/-- `c_q > 0` whenever `q > 1`, which is the standing hypothesis on the scale
ratio `q` of the generation gap. -/
theorem backgroundRatioGap_pos {q : ℝ} (hq : 1 < q) : 0 < backgroundRatioGap q :=
  div_pos (by linarith) (by linarith)

/-- **Core lower bound, coarse cells.**  For `r ≥ q > 1`,
`|(r - 1)/(r + 1)| ≥ c_q`.  In the application `r = r_m = ℓ_m/ℓ_n ≥ q` for
`m < n`. -/
theorem backgroundRatioGap_le_abs_of_le {q r : ℝ} (hq : 1 < q) (hr : q ≤ r) :
    backgroundRatioGap q ≤ |(r - 1) / (1 + r)| := by
  have hr1 : 1 < r := lt_of_lt_of_le hq hr
  have hpos : (0 : ℝ) < 1 + r := by linarith
  rw [abs_div, abs_of_pos hpos, abs_of_nonneg (by linarith : (0 : ℝ) ≤ r - 1),
    backgroundRatioGap, div_le_div_iff₀ (by linarith) hpos]
  nlinarith

/-- **Core lower bound, fine cells.**  For `0 ≤ r ≤ q⁻¹` with `q > 1`,
`|(r - 1)/(r + 1)| ≥ c_q`.  In the application `r = r_m = ℓ_m/ℓ_n ≤ q⁻¹` for
`m > n`. -/
theorem backgroundRatioGap_le_abs_of_le_inv {q r : ℝ} (hq : 1 < q)
    (hr0 : 0 ≤ r) (hr : r ≤ q⁻¹) : backgroundRatioGap q ≤ |(r - 1) / (1 + r)| := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hrq : r * q ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hr hq0.le
    rwa [inv_mul_cancel₀ (ne_of_gt hq0)] at this
  have hpos : (0 : ℝ) < 1 + r := by linarith
  have hr1 : r ≤ 1 := le_trans hr (by
    rw [inv_le_one_iff₀]
    right
    exact hq.le)
  rw [abs_div, abs_of_pos hpos, abs_of_nonpos (by linarith : r - 1 ≤ 0),
    backgroundRatioGap, div_le_div_iff₀ (by linarith) hpos]
  nlinarith

/-- **Core lower bound.**  If `r` is separated from `1` on either side by the
ratio gap — `r ≥ q` or `0 ≤ r ≤ q⁻¹` — then `|(r - 1)/(r + 1)| ≥ c_q`. -/
theorem backgroundRatioGap_le_abs {q r : ℝ} (hq : 1 < q) (hr0 : 0 ≤ r)
    (hsep : q ≤ r ∨ r ≤ q⁻¹) : backgroundRatioGap q ≤ |(r - 1) / (1 + r)| := by
  rcases hsep with h | h
  · exact backgroundRatioGap_le_abs_of_le hq h
  · exact backgroundRatioGap_le_abs_of_le_inv hq hr0 h

/-- **The phase bound on a separated cell core**, the second line of
`eq:background-phase-positive`.  On the core
of a nonselected cell `s_n = r_m` is separated from `1`, and therefore

`F(r) (t + τ (r - 1)) ≥ τ c_q^2 / 2 - M^2 / (2 τ)`

for every `t` with `|t| ≤ M`. -/
theorem backgroundMultiplierF_phase_lower_bound_ratioGap
    {q r t M τ : ℝ} (hq : 1 < q) (hr0 : 0 ≤ r) (hτ : 0 < τ) (ht : |t| ≤ M)
    (hsep : q ≤ r ∨ r ≤ q⁻¹) :
    τ * backgroundRatioGap q ^ 2 / 2 - M ^ 2 / (2 * τ) ≤
      backgroundMultiplierF r * (t + τ * (r - 1)) := by
  have hgap := backgroundRatioGap_le_abs hq hr0 hsep
  have hc := (backgroundRatioGap_pos hq).le
  have hsq : backgroundRatioGap q ^ 2 ≤ ((r - 1) / (1 + r)) ^ 2 := by
    have h := mul_self_le_mul_self hc hgap
    have habs : |(r - 1) / (1 + r)| * |(r - 1) / (1 + r)| =
        ((r - 1) / (1 + r)) ^ 2 := by
      rw [← abs_mul, abs_mul_self, sq]
    nlinarith [h, habs]
  have hmain := backgroundMultiplierF_phase_lower_bound hr0 hτ ht
  nlinarith [hmain, hsq, hτ]

/-! ## The choice of `τ` -/

/-- The explicit threshold of `eq:axial-separation-choice`:

`τ₀ = max (2 M^2 / g_*) (2 (C₀ + 1) / c_q^2)`.

Every `τ ≥ τ₀` satisfies `M^2/(2τ) ≤ g_*/4` and `τ c_q^2/2 ≥ C₀ + 1`.  All four
arguments are independent of `τ`, so this choice is non-circular. -/
def backgroundTauThreshold (gStar M C₀ cq : ℝ) : ℝ :=
  max (2 * M ^ 2 / gStar) (2 * (C₀ + 1) / cq ^ 2)

/-- The threshold is strictly positive, so any `τ ≥ τ₀` is admissible as a
positive axial shift. -/
theorem backgroundTauThreshold_pos {gStar M C₀ cq : ℝ} (hC : 0 ≤ C₀)
    (hcq : 0 < cq) : 0 < backgroundTauThreshold gStar M C₀ cq := by
  apply lt_of_lt_of_le _ (le_max_right _ _)
  positivity

/-- Every `τ` above the threshold is positive. -/
theorem backgroundTauThreshold_pos_of_le {gStar M C₀ cq τ : ℝ} (hC : 0 ≤ C₀)
    (hcq : 0 < cq) (hτ : backgroundTauThreshold gStar M C₀ cq ≤ τ) : 0 < τ :=
  lt_of_lt_of_le (backgroundTauThreshold_pos hC hcq) hτ

/-- **First half of `eq:axial-separation-choice`**: `M^2/(2τ) ≤ g_*/4`. -/
theorem backgroundTauThreshold_phase_error_le {gStar M C₀ cq τ : ℝ}
    (hg : 0 < gStar) (hC : 0 ≤ C₀) (hcq : 0 < cq)
    (hτ : backgroundTauThreshold gStar M C₀ cq ≤ τ) :
    M ^ 2 / (2 * τ) ≤ gStar / 4 := by
  have hτpos : 0 < τ := backgroundTauThreshold_pos_of_le hC hcq hτ
  have h1 : 2 * M ^ 2 / gStar ≤ τ := le_trans (le_max_left _ _) hτ
  have h2 : 2 * M ^ 2 ≤ τ * gStar := by
    rw [div_le_iff₀ hg] at h1
    linarith
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- **Second half of `eq:axial-separation-choice`**: `τ c_q^2/2 ≥ C₀ + 1`. -/
theorem backgroundTauThreshold_separation_ge {gStar M C₀ cq τ : ℝ}
    (hcq : 0 < cq)
    (hτ : backgroundTauThreshold gStar M C₀ cq ≤ τ) :
    C₀ + 1 ≤ τ * cq ^ 2 / 2 := by
  have h1 : 2 * (C₀ + 1) / cq ^ 2 ≤ τ := le_trans (le_max_right _ _) hτ
  have hsq : (0 : ℝ) < cq ^ 2 := by positivity
  rw [div_le_iff₀ hsq] at h1
  linarith

/-- **`eq:axial-separation-choice`** in one
statement: there is a positive `τ₀`, depending only on `g_*`, `M`, `C₀` and
`c_q`, such that every `τ ≥ τ₀` is positive and satisfies both
`M^2/(2τ) ≤ g_*/4` and `τ c_q^2/2 ≥ C₀ + 1`. -/
theorem exists_backgroundTau {gStar M C₀ cq : ℝ} (hg : 0 < gStar) (hC : 0 ≤ C₀)
    (hcq : 0 < cq) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℝ, τ₀ ≤ τ →
      0 < τ ∧ M ^ 2 / (2 * τ) ≤ gStar / 4 ∧ C₀ + 1 ≤ τ * cq ^ 2 / 2 := by
  refine ⟨backgroundTauThreshold gStar M C₀ cq,
    backgroundTauThreshold_pos hC hcq, fun τ hτ => ⟨?_, ?_, ?_⟩⟩
  · exact backgroundTauThreshold_pos_of_le hC hcq hτ
  · exact backgroundTauThreshold_phase_error_le hg hC hcq hτ
  · exact backgroundTauThreshold_separation_ge hcq hτ

end

end FastDynamo
