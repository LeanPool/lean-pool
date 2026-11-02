/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Nat.Choose.Cast

/-!
# Step3

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Step-3 arithmetic of the annular decomposition

Local helpers for ABK26, Section 4.1, proof of Proposition
`p.mathcalE.annular.decomp`, Step 3: the two arithmetic cores behind the
constants that convert the intermediate five-term estimate
`e.mathcalE.annular.decomp.pre.zero` into the final four-term display.

Everything here is a proved *conditional* helper over abstract reals.  The
caller-supplied inequalities (the three field-level order-of-summation
interchanges, the `sigma-bar` continuity sum, the `l^1`/`W^{2,infty}` sums) are
conditional A obligations, not source premises; no source node is claimed,
realized or closed by this module.

## Contents

* `poly2_geom_tail_le` -- the polynomial-times-geometric summation core
  `sum_i (i+1)^2 r^i <= 2 (1-r)^(-3)`, the origin of the `C s^(-3)` constants of
  the three Step-3 interchanges (`1 - 3^(-s/2)` is comparable to `s`).
* `sub_four_gamma_inv_cube_le` -- the `(s - 4 gamma)^(-3) <= 8 s^(-3)`
  absorption under the standing hypothesis `s >= 8 gamma`, which is what lets
  both `G_1^b` interchanges be quoted with the single constant `C s^(-3)`.
-/

namespace Algsuperdiff.Section4.Provider.Annular

noncomputable section

/-! ## The polynomial-times-geometric summation core -/

/-- **Polynomial-times-geometric tail (abstract reals).**  For `r` in `[0,1)`,
`sum_i (i+1)^2 r^i <= 2 (1-r)^(-3)`, via `sum_i C(i+2,2) r^i = (1-r)^(-3)` and
the termwise bound `(i+1)^2 <= 2 C(i+2,2)`.  With `1 - r` comparable to `s`
(base `r = 3^(-s/2)`) this is the origin of the `C s^(-3)` factors of Step 3. -/
theorem poly2_geom_tail_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' i : ℕ, ((i : ℝ) + 1) ^ 2 * r ^ i ≤ 2 / (1 - r) ^ 3 := by
  have hnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have hch : ∑' n : ℕ, ((n + 2).choose 2 : ℝ) * r ^ n = 1 / (1 - r) ^ (2 + 1) :=
    tsum_choose_mul_geometric_of_norm_lt_one 2 hnorm
  have hchSummable : Summable (fun n : ℕ => ((n + 2).choose 2 : ℝ) * r ^ n) :=
    summable_choose_mul_geometric_of_norm_lt_one 2 hnorm
  have hterm : ∀ i : ℕ, ((i : ℝ) + 1) ^ 2 * r ^ i
      ≤ 2 * (((i + 2).choose 2 : ℝ) * r ^ i) := by
    intro i
    have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have hle : ((i : ℝ) + 1) ^ 2 ≤ 2 * ((i + 2).choose 2 : ℝ) := by
      rw [Nat.cast_choose_two]
      push_cast
      linarith only [hi]
    have hrpow : 0 ≤ r ^ i := pow_nonneg hr0 i
    calc ((i : ℝ) + 1) ^ 2 * r ^ i ≤ 2 * ((i + 2).choose 2 : ℝ) * r ^ i :=
          mul_le_mul_of_nonneg_right hle hrpow
      _ = 2 * (((i + 2).choose 2 : ℝ) * r ^ i) := by ring
  have hgnn : ∀ i : ℕ, 0 ≤ ((i : ℝ) + 1) ^ 2 * r ^ i :=
    fun i => mul_nonneg (by positivity) (pow_nonneg hr0 i)
  have hgsum : Summable (fun i : ℕ => 2 * (((i + 2).choose 2 : ℝ) * r ^ i)) :=
    hchSummable.mul_left 2
  have hLsummable : Summable (fun i : ℕ => ((i : ℝ) + 1) ^ 2 * r ^ i) :=
    Summable.of_nonneg_of_le hgnn hterm hgsum
  calc ∑' i : ℕ, ((i : ℝ) + 1) ^ 2 * r ^ i
      ≤ ∑' i : ℕ, 2 * (((i + 2).choose 2 : ℝ) * r ^ i) :=
        Summable.tsum_le_tsum hterm hLsummable hgsum
    _ = 2 * ∑' i : ℕ, ((i + 2).choose 2 : ℝ) * r ^ i := tsum_mul_left
    _ = 2 / (1 - r) ^ 3 := by rw [hch]; ring

/-! ## The `(s - 4 gamma)^(-3)` absorption -/

/-- **The `(s - 4 gamma)^(-3) -> s^(-3)` absorption.**  The second Step-3
interchange produces the constant `C (s - 4 gamma)^(-3)`; under the standing
hypothesis `s >= 8 gamma` one has `s - 4 gamma >= s/2`, hence `(s - 4
gamma)^(-3) <= 8 s^(-3)`, so both interchanges may be quoted with the single
constant `C s^(-3)`. -/
theorem sub_four_gamma_inv_cube_le {s gamma : ℝ} (hs : 0 < s)
    (hsg : 8 * gamma ≤ s) : ((s - 4 * gamma) ^ 3)⁻¹ ≤ 8 * (s ^ 3)⁻¹ := by
  have hd : 0 < s - 4 * gamma := by linarith only [hs, hsg]
  have hcube : (s / 2) ^ 3 ≤ (s - 4 * gamma) ^ 3 :=
    pow_le_pow_left₀ (by linarith only [hs]) (by linarith only [hsg]) 3
  have key : s ^ 3 ≤ 8 * (s - 4 * gamma) ^ 3 := by linarith only [hcube]
  rw [← sub_nonneg]
  have hrw : 8 * (s ^ 3)⁻¹ - ((s - 4 * gamma) ^ 3)⁻¹
      = (8 * (s - 4 * gamma) ^ 3 - s ^ 3) / (s ^ 3 * (s - 4 * gamma) ^ 3) := by
    field_simp
  rw [hrw]
  exact div_nonneg (by linarith only [key]) (by positivity)

end

end Algsuperdiff.Section4.Provider.Annular
