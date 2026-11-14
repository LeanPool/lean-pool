/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.G1ThresholdArith
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.LaneInterface

/-!
# LaneCertificates

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The frozen-anchor bridge arithmetic of the two lane couplings

ABK26, §4.1.  The `𝒢₀` and `𝒢₁` ratio-tail lanes are unconditional in
everything probabilistic; what each still needs is one explicit inequality
tying the model to the level `θ` and the rate `c₁`:

* `𝒢₀`: `C⁹γ² ≤ θ c⋆⁸` — the level-vs-regime coupling that replaces the proved
  `RatioTailClosed` packaging of `θ` *inside* the constant
  (`couplingG0_of_anchor`);
* `𝒢₁`: `K(d,r)(1+c₁)γ ≤ θ c⋆ s⁶ ε²` — the closed form of `T₀ ≤ s ε √c⋆
  γ^{-1/2}` at the substituted threshold of `e.lambda.good.events`
  (`couplingG1_of_anchor`).

Both are abstract-real implications recording what the frozen proportion
anchor's own parameter clauses give.  The anchor quantifies one constant `C_a`
before `(M, s, ε, θ)` and carries the regime `γ ≤ C_a^{-1}c⋆^{10}` together with
the level clause `C_a c⋆^{-2}s^{-4}ε^{-2}γ ≤ θ`; `regime_of_anchor` reads the
printed regime off that one.

## References

* ABK26, `p.independence.between.scales`; `l.good.scales.ratio.lambda`;
  `l.ratio.of.good.scales.for.k`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability
open Algsuperdiff.Section4.Probability.IndicatorDensity

noncomputable section

variable {d : ℕ}

/-- **The `𝒢₀` coupling from the anchor's own clauses.**  So one `C(d)` before
the parameters costs nothing on this lane. -/
theorem couplingG0_of_anchor {C Ca cs s ep theta gamma : ℝ}
    (hC : 6 ≤ C) (hcs0 : 0 < cs) (hcs32 : cs ≤ 3 / 2)
    (hs0 : 0 < s) (hs12 : s ≤ 1 / 2) (hep0 : 0 < ep) (hep12 : ep ≤ 1 / 2)
    (hg0 : 0 < gamma) (hCa : C ^ (5 : ℕ) ≤ Ca)
    (hreg : gamma ≤ Ca⁻¹ * cs ^ (10 : ℕ))
    (hthetacond : Ca * (cs⁻¹) ^ (2 : ℕ) * (s⁻¹) ^ (4 : ℕ) * (ep⁻¹) ^ (2 : ℕ) * gamma ≤ theta) :
    C ^ (10 : ℕ) * gamma ^ (2 : ℕ) ≤ theta * cs ^ (8 : ℕ) := by
  have hC0 : (0 : ℝ) < C := by linarith only [hC]
  have hCa0 : (0 : ℝ) < Ca := lt_of_lt_of_le (by positivity) hCa
  have hcs8 : (0 : ℝ) ≤ cs ^ (8 : ℕ) := by positivity
  have hA : (4 / 9 : ℝ) ≤ (cs⁻¹) ^ (2 : ℕ) := by
    have h : (2 / 3 : ℝ) ≤ cs⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hcs0]
      calc cs ≤ 3 / 2 := hcs32
        _ = ((2 : ℝ) / 3)⁻¹ := by norm_num
    calc (4 / 9 : ℝ) = (2 / 3 : ℝ) ^ (2 : ℕ) := by norm_num
      _ ≤ (cs⁻¹) ^ (2 : ℕ) := pow_le_pow_left₀ (by norm_num) h 2
  have hB : (16 : ℝ) ≤ (s⁻¹) ^ (4 : ℕ) := by
    have h : (2 : ℝ) ≤ s⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hs0]
      calc s ≤ 1 / 2 := hs12
        _ = (2 : ℝ)⁻¹ := by norm_num
    calc (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
      _ ≤ (s⁻¹) ^ (4 : ℕ) := pow_le_pow_left₀ (by norm_num) h 4
  have hE : (4 : ℝ) ≤ (ep⁻¹) ^ (2 : ℕ) := by
    have h : (2 : ℝ) ≤ ep⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hep0]
      calc ep ≤ 1 / 2 := hep12
        _ = (2 : ℝ)⁻¹ := by norm_num
    calc (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
      _ ≤ (ep⁻¹) ^ (2 : ℕ) := pow_le_pow_left₀ (by norm_num) h 2
  have hCg : (0 : ℝ) ≤ Ca * gamma := by positivity
  have hlow : 28 * Ca * gamma ≤ theta := by
    refine le_trans ?_ hthetacond
    calc 28 * Ca * gamma = 28 * (Ca * gamma) := by ring
      _ ≤ 256 / 9 * (Ca * gamma) := mul_le_mul_of_nonneg_right (by norm_num) hCg
      _ = Ca * (4 / 9) * 16 * 4 * gamma := by ring
      _ ≤ Ca * (cs⁻¹) ^ (2 : ℕ) * (s⁻¹) ^ (4 : ℕ) * (ep⁻¹) ^ (2 : ℕ) * gamma := by gcongr
  have hCasq : C ^ (10 : ℕ) ≤ Ca ^ (2 : ℕ) := by
    calc C ^ (10 : ℕ) = (C ^ (5 : ℕ)) ^ (2 : ℕ) := by ring
      _ ≤ Ca ^ (2 : ℕ) := pow_le_pow_left₀ (by positivity) hCa 2
  have hkey : Ca * gamma ≤ cs ^ (10 : ℕ) := by
    have h := mul_le_mul_of_nonneg_left hreg hCa0.le
    rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hCa0), one_mul] at h
  have hstep : Ca * (C ^ (10 : ℕ) * gamma ^ (2 : ℕ))
      ≤ Ca * (28 * Ca * gamma * cs ^ (8 : ℕ)) := by
    have h2 : C ^ (10 : ℕ) * gamma * (Ca * gamma) ≤ C ^ (10 : ℕ) * gamma * cs ^ (10 : ℕ) :=
      mul_le_mul_of_nonneg_left hkey (by positivity)
    have hcssq : cs ^ (10 : ℕ) ≤ 9 / 4 * cs ^ (8 : ℕ) := by
      have h : cs ^ (2 : ℕ) ≤ 9 / 4 := by
        calc cs ^ (2 : ℕ) ≤ (3 / 2 : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ hcs0.le hcs32 2
          _ = 9 / 4 := by norm_num
      calc cs ^ (10 : ℕ) = cs ^ (8 : ℕ) * cs ^ (2 : ℕ) := by ring
        _ ≤ cs ^ (8 : ℕ) * (9 / 4) := mul_le_mul_of_nonneg_left h hcs8
        _ = 9 / 4 * cs ^ (8 : ℕ) := by ring
    have h3 : C ^ (10 : ℕ) * gamma * cs ^ (10 : ℕ)
        ≤ C ^ (10 : ℕ) * gamma * (9 / 4 * cs ^ (8 : ℕ)) :=
      mul_le_mul_of_nonneg_left hcssq (by positivity)
    have h4 : 9 / 4 * (C ^ (10 : ℕ) * gamma * cs ^ (8 : ℕ))
        ≤ 28 * (Ca ^ (2 : ℕ) * gamma * cs ^ (8 : ℕ)) := by
      have hmono : C ^ (10 : ℕ) * gamma * cs ^ (8 : ℕ)
          ≤ Ca ^ (2 : ℕ) * gamma * cs ^ (8 : ℕ) := by gcongr
      linarith only [hmono,
        mul_nonneg (mul_nonneg (pow_nonneg hCa0.le 2) hg0.le) hcs8]
    calc Ca * (C ^ (10 : ℕ) * gamma ^ (2 : ℕ)) = C ^ (10 : ℕ) * gamma * (Ca * gamma) := by ring
      _ ≤ C ^ (10 : ℕ) * gamma * cs ^ (10 : ℕ) := h2
      _ ≤ C ^ (10 : ℕ) * gamma * (9 / 4 * cs ^ (8 : ℕ)) := h3
      _ = 9 / 4 * (C ^ (10 : ℕ) * gamma * cs ^ (8 : ℕ)) := by ring
      _ ≤ 28 * (Ca ^ (2 : ℕ) * gamma * cs ^ (8 : ℕ)) := h4
      _ = Ca * (28 * Ca * gamma * cs ^ (8 : ℕ)) := by ring
  calc C ^ (10 : ℕ) * gamma ^ (2 : ℕ) ≤ 28 * Ca * gamma * cs ^ (8 : ℕ) :=
        le_of_mul_le_mul_left hstep hCa0
    _ ≤ theta * cs ^ (8 : ℕ) := mul_le_mul_of_nonneg_right hlow hcs8

/-- The two hypotheses are **not** the printed ones: the manuscript's
`e.theta.cond.two` and the frozen theorem's clauses carry `s^{-4}` and `s⁵`.
Nothing downstream consumes the printed condition. -/
theorem couplingG1_of_anchor {K Ca cs s ep theta gamma c1 : ℝ}
    (hK0 : 0 < K) (hcs0 : 0 < cs) (hcs32 : cs ≤ 3 / 2)
    (hs0 : 0 < s) (hs12 : s ≤ 1 / 2) (hep0 : 0 < ep)
    (hg0 : 0 < gamma) (hCa : 3 * K ≤ Ca)
    (hthetacond : Ca * (cs⁻¹) ^ (2 : ℕ) * (s⁻¹) ^ (6 : ℕ) * (ep⁻¹) ^ (2 : ℕ) * gamma ≤ theta)
    (hrate : Ca * (c1 * gamma) ≤ cs ^ (2 : ℕ) * s ^ (7 : ℕ) * ep ^ (2 : ℕ) * theta) :
    K * (1 + c1) * gamma ≤ theta * cs * s ^ (6 : ℕ) * ep ^ (2 : ℕ) := by
  have hK : (0 : ℝ) < 3 * K := by linarith only [hK0]
  have hCa0 : (0 : ℝ) < Ca := lt_of_lt_of_le hK hCa
  have hQ0 : (0 : ℝ) < cs * s ^ (6 : ℕ) * ep ^ (2 : ℕ) := by positivity
  have h1 : Ca * gamma * cs⁻¹ ≤ theta * (cs * s ^ (6 : ℕ) * ep ^ (2 : ℕ)) := by
    have hmul := mul_le_mul_of_nonneg_right hthetacond hQ0.le
    calc Ca * gamma * cs⁻¹
        = Ca * (cs⁻¹) ^ (2 : ℕ) * (s⁻¹) ^ (6 : ℕ) * (ep⁻¹) ^ (2 : ℕ) * gamma *
            (cs * s ^ (6 : ℕ) * ep ^ (2 : ℕ)) := by
          field_simp
      _ ≤ theta * (cs * s ^ (6 : ℕ) * ep ^ (2 : ℕ)) := hmul
  have hcsinv : (2 : ℝ) / 3 ≤ cs⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hcs0]
    calc cs ≤ 3 / 2 := hcs32
      _ = ((2 : ℝ) / 3)⁻¹ := by norm_num
  have h2 : 2 * K * gamma ≤ Ca * gamma * cs⁻¹ := by
    have hstep : Ca * gamma * (2 / 3) ≤ Ca * gamma * cs⁻¹ :=
      mul_le_mul_of_nonneg_left hcsinv (by positivity)
    have hstep2 : 2 * K * gamma ≤ Ca * gamma * (2 / 3) := by
      have h : 3 * K * gamma ≤ Ca * gamma := mul_le_mul_of_nonneg_right hCa hg0.le
      linarith only [h]
    linarith only [hstep, hstep2]
  have h3 : 2 * (K * (c1 * gamma)) ≤ theta * (cs * s ^ (6 : ℕ) * ep ^ (2 : ℕ)) := by
    have hcss : 2 * K * (cs * s) ≤ Ca := by
      have hprod : cs * s ≤ 3 / 4 := by
        have h := mul_le_mul hcs32 hs12 hs0.le (by norm_num : (0 : ℝ) ≤ 3 / 2)
        calc cs * s ≤ 3 / 2 * (1 / 2) := h
          _ = 3 / 4 := by norm_num
      have hK2 : 2 * K * (cs * s) ≤ 2 * K * (3 / 4) :=
        mul_le_mul_of_nonneg_left hprod (by linarith only [hK0])
      linarith only [hK2, hCa, hK0]
    have hmul : 2 * K * (Ca * (c1 * gamma))
        ≤ 2 * K * (cs ^ (2 : ℕ) * s ^ (7 : ℕ) * ep ^ (2 : ℕ) * theta) :=
      mul_le_mul_of_nonneg_left hrate (by linarith only [hK0])
    have hcancel : Ca * (2 * (K * (c1 * gamma)))
        ≤ Ca * (theta * (cs * s ^ (6 : ℕ) * ep ^ (2 : ℕ))) := by
      calc Ca * (2 * (K * (c1 * gamma))) = 2 * K * (Ca * (c1 * gamma)) := by ring
        _ ≤ 2 * K * (cs ^ (2 : ℕ) * s ^ (7 : ℕ) * ep ^ (2 : ℕ) * theta) := hmul
        _ = (2 * K * (cs * s)) * (theta * (cs * s ^ (6 : ℕ) * ep ^ (2 : ℕ))) := by ring
        _ ≤ Ca * (theta * (cs * s ^ (6 : ℕ) * ep ^ (2 : ℕ))) := by
            refine mul_le_mul_of_nonneg_right hcss ?_
            exact le_trans (by positivity : (0 : ℝ) ≤ 2 * K * gamma) (le_trans h2 h1)
    exact le_of_mul_le_mul_left hcancel hCa0
  have hassoc : theta * cs * s ^ (6 : ℕ) * ep ^ (2 : ℕ)
      = theta * (cs * s ^ (6 : ℕ) * ep ^ (2 : ℕ)) := by ring
  have hsum : K * (1 + c1) * gamma = K * gamma + K * (c1 * gamma) := by ring
  rw [hsum, hassoc]
  linarith only [h1, h2, h3]

/-- **The printed regime is absorbable.**  The anchor's regime
`γ ≤ C_a^{-1}c⋆^{10}` at any `C_a ≥ C^{10}` gives the `𝒢₀` lane's printed regime
`γ ≤ (C^{-1})^{10}c⋆^{10}`. -/
theorem regime_of_anchor {C Ca cs gamma : ℝ} (hC0 : 0 < C)
    (hCa : C ^ (10 : ℕ) ≤ Ca) (hreg : gamma ≤ Ca⁻¹ * cs ^ (10 : ℕ)) :
    gamma ≤ (C⁻¹) ^ (10 : ℕ) * cs ^ (10 : ℕ) := by
  refine le_trans hreg (mul_le_mul_of_nonneg_right ?_ (by positivity))
  rw [inv_pow]
  exact inv_anti₀ (by positivity) hCa

end

end Algsuperdiff.Section4.Provider.Proportion
