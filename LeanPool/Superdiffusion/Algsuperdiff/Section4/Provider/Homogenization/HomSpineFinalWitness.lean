/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepOneDisplay

/-!
# HomSpineFinalWitness

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5: two range transfers for the real defect witness

## What this module is

The frozen root asks for a **real-valued** `E_B: Ω → ℝ` with

```text
  0 ≤ E_B,   E_B measurable,
  ∫⁻ (ofReal E_B)^p ≤ ( C (√p + √|log γ|) √γ (log γ)² )^p
      for every p ∈ [1, C⁻¹ γ⁻¹ |log γ|⁻¹].
```

This repository's carrier `EthmB(m)` is `[0,∞]`-valued
(`HomStepEnvelope.ethmB`), so the real cut needs `EthmB < ∞` a.e., and the cut
is then made at

```text
  E_B(ω):= K · (EthmB(m)(ω)).toReal,
```

with `K` the Step-3/Step-4 absorption factor (the constant the manuscript
"absorbs into `EthmB(m)`"), carried as a parameter and paid for in the
constant `C`.

Two elementary transfers about the `p`-range are what that construction needs
from this file, and they are all it contains:

* `range_mono_of_le` — a `p`-range stated at the larger constant is contained
  in the `p`-range stated at the smaller one, so the root's own range
  `p ≤ C⁻¹γ⁻¹|log γ|⁻¹` implies every sub-range the chain reads;
* `gamma_mul_absLog_le` — `γ|log γ| ≤ 4√γ` on `0 < γ < 1`, the only place a
  logarithm meets a power of `γ` here.  It is spent exactly once, to put
  `p = 1` inside the range, which is where the a.e. finiteness of the `[0,∞]`
  carrier comes from.
-/

open Algsuperdiff.Section3
open MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. Two elementary transfers -/

/-- Shrinking a reciprocal range: a `p`-range stated at the larger constant is
contained in the `p`-range stated at the smaller one. -/
theorem range_mono_of_le {K C gam Lg p : ℝ} (hK : 0 < K) (hKC : K ≤ C)
    (hgam : 0 ≤ gam⁻¹) (hLg : 0 ≤ Lg⁻¹) (hp : p ≤ C⁻¹ * gam⁻¹ * Lg⁻¹) :
    p ≤ K⁻¹ * gam⁻¹ * Lg⁻¹ := by
  have hCpos : 0 < C := lt_of_lt_of_le hK hKC
  have hinv : C⁻¹ ≤ K⁻¹ := by
    rw [inv_le_inv₀ hCpos hK]
    exact hKC
  have hstep : C⁻¹ * gam⁻¹ * Lg⁻¹ ≤ K⁻¹ * gam⁻¹ * Lg⁻¹ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hinv hgam) hLg
  linarith only [hp, hstep]

/-- `γ|log γ| ≤ 4√γ` on `0 < γ < 1`: the `absLog_mul_sqrt_le` multiplied by
`√γ` and collapsed with `t³ ≤ t²` at `t = γ^{1/4} ≤ 1`.  This is the only place
a logarithm meets a power of `γ` in this module; it is spent exactly once, to
put `p = 1` inside the theorem's own range. -/
theorem gamma_mul_absLog_le {gamma : ℝ} (hg : 0 < gamma) (hg1 : gamma < 1) :
    gamma * |Real.log gamma| ≤ 4 * Real.sqrt gamma := by
  have htpos : 0 < Real.sqrt (Real.sqrt gamma) := quarticRoot_pos hg
  have htsq : Real.sqrt (Real.sqrt gamma) ^ (2 : ℕ) = Real.sqrt gamma :=
    quarticRoot_sq gamma
  have ht1 : Real.sqrt (Real.sqrt gamma) ≤ 1 :=
    sqrt_le_one_of_le_one (sqrt_le_one_of_le_one hg1.le)
  have hkey := absLog_mul_sqrt_le hg hg1
  have hsqnn : (0 : ℝ) ≤ Real.sqrt gamma := Real.sqrt_nonneg gamma
  have hgeq : gamma * |Real.log gamma| =
      Real.sqrt gamma * (|Real.log gamma| * Real.sqrt gamma) := by
    rw [mul_comm |Real.log gamma| (Real.sqrt gamma), ← mul_assoc,
      Real.mul_self_sqrt hg.le]
  have hcube : Real.sqrt (Real.sqrt gamma) ^ (2 : ℕ) * Real.sqrt (Real.sqrt gamma) ≤
      Real.sqrt (Real.sqrt gamma) ^ (2 : ℕ) * 1 :=
    mul_le_mul_of_nonneg_left ht1 (by positivity)
  calc gamma * |Real.log gamma|
      = Real.sqrt gamma * (|Real.log gamma| * Real.sqrt gamma) := hgeq
    _ ≤ Real.sqrt gamma * (4 * Real.sqrt (Real.sqrt gamma)) :=
        mul_le_mul_of_nonneg_left hkey hsqnn
    _ = 4 * (Real.sqrt (Real.sqrt gamma) ^ (2 : ℕ) * Real.sqrt (Real.sqrt gamma)) := by
        rw [htsq]; ring
    _ ≤ 4 * (Real.sqrt (Real.sqrt gamma) ^ (2 : ℕ) * 1) := by
        linarith only [hcube]
    _ = 4 * Real.sqrt gamma := by rw [htsq]; ring

end

end Algsuperdiff.Section4.Provider.Homogenization
