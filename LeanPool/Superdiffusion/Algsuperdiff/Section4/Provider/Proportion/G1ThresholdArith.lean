/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.G1RatioTail

/-!
# G1ThresholdArith

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# An explicit majorant for the `𝒢₁` proportion threshold

The `𝒢₁` proportion tail is delivered at an existential, unexposed threshold
`T₀`, and only at the dependence range `r = 1`.  This module replaces that
existential by an **explicit closed form**, valid at every `r ≥ 1`:

* `g1ThresholdConst d r` — a positive constant depending only on `d` and `r`
  (through `Cstar`, `gammaMomentConst`, `atomG1bScale` and `log 3`);
* `g1Majorant d r s θ c₁ = √(g1ThresholdConst d r (1+c₁) / (s⁴ θ))`;
* `g1Majorant_le_shellThreshold` — the certificate that this majorant sits below
  the threshold at which the Section 4 support layer instantiates `𝒢₁`.

## The honest reading of the threshold condition

`g1Majorant_le_shellThreshold` certifies that this majorant sits below the
threshold `T = s ε √(c⋆) (√γ)⁻¹` at which the Section 4 support layer
instantiates `𝒢₁` inside `Support.goodEventBase`, under the explicit condition

```
K(d,r) (1 + c₁) γ ≤ θ c⋆ s⁶ ε²          (`hcond`)
```

which is exactly `T₀² ≤ (s ε)² c⋆ γ⁻¹` written out.  Measured against the
manuscript's printed side condition `e.theta.cond.two` (`T² ≥ C s^{-2}
max{s^{-1}, θ^{-1}}`), `hcond` is **one power of `s^{-2}` stronger**: the
printed condition would read `s⁴` where `hcond` needs `s⁶`.  Nothing in this
module consumes the printed condition, and no declaration here claims a source
node, or any fraction of one, closed.

## References

* ABK26, `l.ratio.of.good.scales.for.k`, Step 3.
* ABK26, `d.good.event.for.lambda`, (the `𝒢₁` threshold `s ε c⋆^{1/2}
  γ^{-1/2}`).
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability
open Algsuperdiff.Section4.Probability.ScalesConcentration
open Algsuperdiff.Section4.Probability.IndicatorDensity
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Abstract-real helpers

Every transcendental atom (`Real.exp`, `Real.log`, `Real.rpow`, `Real.sqrt`) is
confined to this section; the closed-form arithmetic below sees only opaque
reals. -/

/-- `a ≤ b` from `0 ≤ a`, `0 ≤ b` and `a² ≤ b²`. -/
private theorem le_of_sq_le_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ (2 : ℕ) ≤ b ^ (2 : ℕ)) : a ≤ b := by
  have h1 : Real.sqrt (a ^ (2 : ℕ)) ≤ Real.sqrt (b ^ (2 : ℕ)) := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq ha, Real.sqrt_sq hb] at h1

/-- `log(6r) + r ≥ 0` for every natural `r` (at `r = 0` both sides vanish). -/
private theorem logSixMul_nonneg (r : ℕ) : 0 ≤ Real.log (6 * (r : ℝ)) + (r : ℝ) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; norm_num
  · have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hlog := Real.log_nonneg (by linarith only [hrR] : (1 : ℝ) ≤ 6 * (r : ℝ))
    linarith only [hlog, hrR]

/-! ## 3. The explicit threshold constant and majorant -/

/-- The `d`- and `r`-only prefactor of the closed `𝒢₁` threshold.  The first
summand carries the large-waves lane (`54² · 66` times the squared Appendix-D
normaliser), the second the small-waves lane (`24 · 216 · 8 · 262` times the
`Γ₁` amplitude of the two-index array). -/
def g1ThresholdConst (d : ℕ) (r : ℕ) : ℝ :=
  (192456 * (1 + Cstar) ^ (2 : ℕ) * gammaMomentConst 2 ^ (2 : ℕ)
      + 10865664 * (1 + Cstar) * gammaMomentConst 1
          * (1 + 2 * (d : ℝ) * Real.log 3) * atomG1bScale ^ (2 : ℕ))
    * ((r : ℝ) * (Real.log (6 * (r : ℝ)) + (r : ℝ)))

/-- The explicit `𝒢₁` threshold majorant: `T₀ = √(K(d,r)(1+c₁)/(s⁴θ))`. -/
def g1Majorant (d : ℕ) (r : ℕ) (s theta c1 : ℝ) : ℝ :=
  Real.sqrt (g1ThresholdConst d r * (1 + c1) / (s ^ (4 : ℕ) * theta))

private theorem g1ThresholdFactor_pos (d : ℕ) :
    0 < 192456 * (1 + Cstar) ^ (2 : ℕ) * gammaMomentConst 2 ^ (2 : ℕ)
      + 10865664 * (1 + Cstar) * gammaMomentConst 1
          * (1 + 2 * (d : ℝ) * Real.log 3) * atomG1bScale ^ (2 : ℕ) := by
  have hC : (0 : ℝ) < 1 + Cstar := by linarith only [Cstar_pos]
  have hg2 : (0 : ℝ) < gammaMomentConst 2 := gammaMomentConst_pos (by norm_num)
  have hg1 : (0 : ℝ) < gammaMomentConst 1 := gammaMomentConst_pos (by norm_num)
  have hlog : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hdlog : (0 : ℝ) ≤ 2 * (d : ℝ) * Real.log 3 :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) hlog
  have hd : (0 : ℝ) < 1 + 2 * (d : ℝ) * Real.log 3 := by linarith only [hdlog]
  have hA : (0 : ℝ) < atomG1bScale ^ (2 : ℕ) := pow_pos atomG1bScale_pos 2
  have t1 : (0 : ℝ) < 192456 * (1 + Cstar) ^ (2 : ℕ) * gammaMomentConst 2 ^ (2 : ℕ) :=
    mul_pos (mul_pos (by norm_num) (pow_pos hC 2)) (pow_pos hg2 2)
  have t2 : (0 : ℝ) < 10865664 * (1 + Cstar) * gammaMomentConst 1
      * (1 + 2 * (d : ℝ) * Real.log 3) * atomG1bScale ^ (2 : ℕ) :=
    mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hC) hg1) hd) hA
  linarith only [t1, t2]

theorem g1ThresholdConst_nonneg (d r : ℕ) : 0 ≤ g1ThresholdConst d r :=
  mul_nonneg (g1ThresholdFactor_pos d).le
    (mul_nonneg (Nat.cast_nonneg r) (logSixMul_nonneg r))

theorem g1Majorant_nonneg (d r : ℕ) (s theta c1 : ℝ) :
    0 ≤ g1Majorant d r s theta c1 := Real.sqrt_nonneg _

/-! ## 5. The certificate against the Section 4 support threshold -/

/-- **The majorant sits below the frozen `𝒢₁` threshold.**

The right-hand side `s ε √(c⋆) (√γ)⁻¹` is exactly the threshold at which
`Support.goodEventBase` instantiates `𝒢₁`. -/
theorem g1Majorant_le_shellThreshold (M : ABKModel d) {s ep theta c1 : ℝ} {r : ℕ}
    (hs0 : 0 < s) (hep0 : 0 < ep) (htheta0 : 0 < theta) (hc1 : 0 ≤ c1)
    (hcond : g1ThresholdConst d r * (1 + c1) * M.gamma
        ≤ theta * Disorder.cstar M * s ^ (6 : ℕ) * ep ^ (2 : ℕ)) :
    g1Majorant d r s theta c1
      ≤ s * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹ := by
  have hgam0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hden : (0 : ℝ) < s ^ (4 : ℕ) * theta := mul_pos (pow_pos hs0 4) htheta0
  have hc1' : (0 : ℝ) ≤ 1 + c1 := by linarith only [hc1]
  have harg0 : (0 : ℝ) ≤ g1ThresholdConst d r * (1 + c1) / (s ^ (4 : ℕ) * theta) :=
    div_nonneg (mul_nonneg (g1ThresholdConst_nonneg d r) hc1') hden.le
  have hRHS0 : (0 : ℝ) ≤ s * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹ :=
    mul_nonneg (mul_nonneg (mul_nonneg hs0.le hep0.le) (Real.sqrt_nonneg _))
      (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hMajsq : g1Majorant d r s theta c1 ^ (2 : ℕ)
      = g1ThresholdConst d r * (1 + c1) / (s ^ (4 : ℕ) * theta) := Real.sq_sqrt harg0
  have hRsq : (s * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) ^ (2 : ℕ)
      = s ^ (2 : ℕ) * ep ^ (2 : ℕ) * Disorder.cstar M / M.gamma := by
    rw [mul_pow, mul_pow, mul_pow, inv_pow, Real.sq_sqrt hcs0.le, Real.sq_sqrt hgam0.le]
    ring
  refine le_of_sq_le_sq (g1Majorant_nonneg d r s theta c1) hRHS0 ?_
  rw [hMajsq, hRsq, div_le_iff₀ hden]
  have hrw : s ^ (2 : ℕ) * ep ^ (2 : ℕ) * Disorder.cstar M / M.gamma * (s ^ (4 : ℕ) * theta)
      = theta * Disorder.cstar M * s ^ (6 : ℕ) * ep ^ (2 : ℕ) / M.gamma := by
    field_simp
  rw [hrw, le_div_iff₀ hgam0]
  exact hcond

end

end Algsuperdiff.Section4.Provider.Proportion
