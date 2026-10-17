/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.ShiftedG2Lane
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.G2SharpArith
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Disorder.CstarUpperBound

/-!
# G2ThresholdSharp

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `𝒢₂` proportion endpoint at the `θ`-free `ε`-threshold

`G2Threshold.ratioTail_eventG2_of_threshold_shift` restates the proved lane at
the named threshold `g2Threshold … = 36(1+C⋆)D/θ`.  This module restates it at
the *sharp* threshold `g2ThresholdSharp … = 108(1+C⋆)D`, which carries **no
divisor `θ`**: the quantile factor `θ^{-1/p}` is paid logarithmically
(`G2SharpArith.threshold_le_inv_sharp`) rather than by `θ^{-1/p} ≤ θ^{-1}`, and
the lane's own moment exponent already clears the requirement `θ⁻¹ ≤ p`
(`G2SharpArith.inv_theta_le_g2MomentExponent`).

Nothing else in the lane changes: the moment exponent, the normalizer, the
independence geometry, the per-cube display and the reduction are the proved
ones, character for character.

## Contents

* `ratioTail_eventG2_of_thresholdSharp_shift` — the explicit-threshold endpoint
  at `g2ThresholdSharp`, in the `LaneTailFrom` shape the proportion assembly
  consumes;
* `g2SharpAnchorConst`, `g2SharpAnchorConstTwo` — two `d`-only constants;
* `g2ThresholdSharp_le_of_anchor_rate` / `_solved` /
  `g2ThresholdSharp_le_of_anchor` — the threshold condition at the frozen
  proportion anchor's own parameter ranges, its regime clause and its `s⁻⁶`
  level clause, at the assembly rate `c₁ = 2A`.

## The headline

At the anchor's own clauses the sharp threshold condition reduces to the **two
parameter-free constant floors**

```
g2SharpAnchorConst d r C N ≤ C_a      and      g2SharpAnchorConstTwo d r C N ≤ C_a ,
```

both functions of `d` alone.  There is **no new anchor clause**: in particular
nothing of the shape `C_aθ ≥ κ(d)s` that the proved
`G2Threshold.g2Threshold_le_of_anchor` needed.  The anchor's own level clause
`C_a c⋆^{-2}s^{-6}ε^{-2}γ ≤ θ` does all the work, because the sharp threshold's
binding clause carries only **one** power of `θ` on its favourable side, and the
level clause supplies exactly one.

## Scope

Provider material: proved local helpers.  The `ε`-threshold condition of the
endpoint is a genuine hypothesis of the *lane*, not a source premise smuggled
into a frozen statement, and the two constant floors are explicit named
parameter conditions.

## References

* ABK26, `l.ratio.of.good.scales.for.mathcal.E`; `p.concentration.for.scales`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability
open Algsuperdiff.Section4.Probability.ScalesConcentration
open Algsuperdiff.Section4.Probability.IndicatorDensity

noncomputable section

variable {d : ℕ}

/-! ## 1. The endpoint at the `θ`-free threshold -/

/-- This is the shifted `𝒢₂` lane endpoint with its existential threshold
`∃ ε₀ > 0, ∀ ε ≥ ε₀` replaced by the named condition

```
0 < ε   and   g2ThresholdSharp d r C M s θ c₁ ≤ ε² ,
```

`g2ThresholdSharp … = 108(1+C⋆)·D` being a closed-form expression in the lane's parameters
with **no divisor `θ`** (contrast `g2Threshold … = 36(1+C⋆)D/θ`). Every other hypothesis
is that of the proved endpoint, unchanged: the honest range condition, the printed regime
`γ ≤ C^{−10}c⋆^{10}`, the standing window `s ∈ [8γ,1]`, the level condition `θ(r+1) < 1`
and `c₁ ≥ 0`.  The base `m₀` and the window `n` are quantified last, so the conclusion is
the `LaneTailFrom` shape the proportion assembly consumes. -/
theorem ratioTail_eventG2_of_thresholdSharp_shift (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ r : ℕ, 1 ≤ r →
        3 + 2 * (3 : ℝ) ^ (1 - (2 : ℤ)) * Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (r : ℕ) →
        ∀ M : ABKModel d, M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
          ∀ s : {s : ℝ // 0 < s}, (s : ℝ) ∈ Set.Icc (8 * M.gamma) 1 →
            ∀ theta : ℝ, 0 < theta → theta * ((r : ℝ) + 1) < 1 →
              ∀ c1 : ℝ, 0 ≤ c1 →
                ∀ ep : ℝ, 0 < ep →
                  g2ThresholdSharp d r C M (s : ℝ) theta c1 ≤ ep ^ (2 : ℕ) →
                    ∀ (m0 : ℤ) (n : ℕ),
                      (Cutoff.cutoffSampleLaw M).toMeasure
                          {omega | theta < scaleProp
                            (fun k => (Support.eventG2 M (m0 + k) s ep)ᶜ) n omega}
                        ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) := by
  classical
  obtain ⟨C, hC0, hbounds⟩ := exists_isTwoTermBigOWith_annularErrorObservable d
  refine ⟨C, hC0, ?_⟩
  intro r hr1 hrgap M hreg s hswin theta htheta0 hthetar c1 hc10 ep hep hthr m0 n
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hs0 : (0 : ℝ) < (s : ℝ) := s.2
  have hs1 : (s : ℝ) ≤ 1 := hswin.2
  have hs40 : (0 : ℝ) < (s : ℝ) / 4 := by linarith only [hs0]
  have hCs0 : (0 : ℝ) < Cstar := Cstar_pos
  have hgmc1 : (0 : ℝ) < gammaMomentConst 1 := gammaMomentConst_pos (by norm_num)
  have hgmc4 : (0 : ℝ) < gammaMomentConst (1 / 4) := gammaMomentConst_pos (by norm_num)
  -- the per-cube display, unconditional (the `hcube` slot)
  have hcube : ∀ k : ℤ,
      Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
        (gammaSigma 2) (gammaSigma (1 / 2)) (Support.annularErrorObservable M k s)
        (cubeAmpOne d C M (s : ℝ)) (cubeAmpTwo d C M) := by
    intro k
    exact hbounds M hreg (s : ℝ) hswin k
  -- the moment exponent `p` and the normalizer `D`, both named in closed form
  have hp1 : (1 : ℝ) ≤ g2MomentExponent r (s : ℝ) theta c1 :=
    one_le_g2MomentExponent r (s : ℝ) theta c1
  have hp0 : (0 : ℝ) < g2MomentExponent r (s : ℝ) theta c1 :=
    g2MomentExponent_pos r (s : ℝ) theta c1
  have hprpow : (0 : ℝ) < g2MomentExponent r (s : ℝ) theta c1 ^ (4 : ℝ) :=
    Real.rpow_pos_of_pos hp0 _
  have hD0 : 0 < g2Normalizer d r C M (s : ℝ) theta c1 :=
    g2Normalizer_pos hC0 M r hs0 theta c1
  have hsp : 1 ≤ (s : ℝ) / 4 * g2MomentExponent r (s : ℝ) theta c1 := by
    have hstep := mul_le_mul_of_nonneg_left
      (four_div_le_g2MomentExponent r (s : ℝ) theta c1) hs40.le
    have hone : (s : ℝ) / 4 * (4 / (s : ℝ)) = 1 := by field_simp
    rwa [hone] at hstep
  have hrate : Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)
      ≤ (s : ℝ) / 4 * g2MomentExponent r (s : ℝ) theta c1 * theta / (16 * (r : ℝ)) := by
    have hstep : 64 * (r : ℝ) * (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) / ((s : ℝ) * theta)
        * ((s : ℝ) * theta / 4)
        ≤ g2MomentExponent r (s : ℝ) theta c1 * ((s : ℝ) * theta / 4) :=
      mul_le_mul_of_nonneg_right (rate_le_g2MomentExponent r (s : ℝ) theta c1)
        (by positivity)
    have hval : 64 * (r : ℝ) * (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) / ((s : ℝ) * theta)
        * ((s : ℝ) * theta / 4)
        = 16 * (r : ℝ) * (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) := by
      have hsne : (s : ℝ) ≠ 0 := ne_of_gt hs0
      have htne : theta ≠ 0 := ne_of_gt htheta0
      field_simp
      ring
    rw [le_div_iff₀ (by linarith only [hrR] : (0 : ℝ) < 16 * (r : ℝ))]
    calc (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * (16 * (r : ℝ))
        = 16 * (r : ℝ) * (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) := by ring
      _ ≤ g2MomentExponent r (s : ℝ) theta c1 * ((s : ℝ) * theta / 4) := by
          rw [← hval]; exact hstep
      _ = (s : ℝ) / 4 * g2MomentExponent r (s : ℝ) theta c1 * theta := by ring
  have hnorm : gammaMomentConst 1 * g2MomentExponent r (s : ℝ) theta c1 *
        xcalScaleOne d (s : ℝ) (cubeAmpOne d C M (s : ℝ)) +
      gammaMomentConst (1 / 4) * g2MomentExponent r (s : ℝ) theta c1 ^ (4 : ℝ) *
        xcalScaleQuarter d (s : ℝ) (cubeAmpTwo d C M)
      ≤ g2Normalizer d r C M (s : ℝ) theta c1 := by
    rw [g2Normalizer]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (xcalScaleOne_le d hs0 hs1)
        (mul_nonneg hgmc1.le hp0.le))
      (mul_le_mul_of_nonneg_left (xcalScaleQuarter_le d hs0 hs1)
        (mul_nonneg hgmc4.le hprpow.le))
  -- the null set of the enlargement
  have hnull : (Cutoff.cutoffSampleLaw M).toMeasure (goodRowSetG2 M s)ᶜ = 0 :=
    measure_compl_goodRowSetG2 M s hs1 hcube
  -- the threshold identification, at the LOG-QUANTILE reading
  have hep2 : (0 : ℝ) < ep ^ (2 : ℕ) := pow_pos hep 2
  have hbase : 108 * (1 + Cstar) * g2Normalizer d r C M (s : ℝ) theta c1
      ≤ ep ^ (2 : ℕ) := by
    rw [g2ThresholdSharp] at hthr
    linarith only [hthr]
  have hDp0 : (0 : ℝ) < g2Normalizer d r C M (s : ℝ) theta c1 * (s : ℝ) / ep ^ (2 : ℕ) :=
    div_pos (mul_pos hD0 hs0) hep2
  have hkeythr : 27 * (g2Normalizer d r C M (s : ℝ) theta c1 * (s : ℝ) / ep ^ (2 : ℕ))
      * (1 + Cstar) ≤ (s : ℝ) / 4 := by
    have hrw : 27 * (g2Normalizer d r C M (s : ℝ) theta c1 * (s : ℝ) / ep ^ (2 : ℕ))
        * (1 + Cstar)
        = 27 * g2Normalizer d r C M (s : ℝ) theta c1 * (1 + Cstar) * (s : ℝ)
            / ep ^ (2 : ℕ) := by ring
    rw [hrw, div_le_iff₀ hep2]
    calc 27 * g2Normalizer d r C M (s : ℝ) theta c1 * (1 + Cstar) * (s : ℝ)
        = (s : ℝ) / 4 * (108 * (1 + Cstar) * g2Normalizer d r C M (s : ℝ) theta c1) := by
          ring
      _ ≤ (s : ℝ) / 4 * ep ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_left hbase (by linarith only [hs0])
  have hpth : theta⁻¹ ≤ g2MomentExponent r (s : ℝ) theta c1 :=
    inv_theta_le_g2MomentExponent hr1 hs0 hs1 htheta0 hc10
  have hthr0 := threshold_le_inv_sharp (sprime := (s : ℝ) / 4) (theta := theta)
    (p := g2MomentExponent r (s : ℝ) theta c1) hs40 htheta0 hp1 hpth hDp0 hkeythr
  have hinv : (g2Normalizer d r C M (s : ℝ) theta c1 * (s : ℝ) / ep ^ (2 : ℕ))⁻¹
      = (g2Normalizer d r C M (s : ℝ) theta c1)⁻¹ * (ep ^ (2 : ℕ) / (s : ℝ)) := by
    have hsne : (s : ℝ) ≠ 0 := ne_of_gt hs0
    have hDne : g2Normalizer d r C M (s : ℝ) theta c1 ≠ 0 := ne_of_gt hD0
    have hepne : ep ^ (2 : ℕ) ≠ 0 := ne_of_gt hep2
    field_simp
  rw [hinv] at hthr0
  -- the assembled tail for the enlarged family, at the base `m₀`
  have hmain := ratioTail_Xcal_shift M s (g2Normalizer d r C M (s : ℝ) theta c1)
    (fun k => Support.eventG2 M k s ep ∪ (goodRowSetG2 M s)ᶜ) m0
    (cubeAmpOne_pos_of hC0 M hs0) (cubeAmpTwo_pos_of C M) hD0 hp1 hs1 hsp hr1
    (by norm_num : (1 : ℝ) ≤ 3) htheta0 hthetar hc10
    hrate hcube hnorm hrgap (hreduce_eventG2_all M s hD0 hthr0)
  refine le_trans (measure_scaleProp_le_of_null_enlargement
    (Cutoff.cutoffSampleLaw M).toMeasure (fun k => Support.eventG2 M (m0 + k) s ep)
    ((goodRowSetG2 M s)ᶜ) hnull n) ?_
  exact hmain n

/-! ## 2. The sharp threshold at the frozen theorem's own parameters -/

private theorem div_le_div_right_of_le_sharp {a b c : ℝ} (hab : a ≤ b) (hc : 0 ≤ c) :
    a / c ≤ b / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hab (inv_nonneg.2 hc)

/-- Unlike its proved counterpart `G2Threshold.g2AnchorConst`, this constant is
asked to clear `C_a` **outright**: the anchor-side condition is
`g2SharpAnchorConst d r ≤ C_a`, with no `s` and no `θ` in it. -/
def g2SharpAnchorConst (d r : ℕ) (C N : ℝ) : ℝ :=
  6 * g2ThresholdConstOne d * (r : ℝ) ^ (2 : ℕ) * C ^ (2 : ℕ) * N

/-- **The constant-size floor the anchor's own constant must clear** so that the
exponentially small clause of the sharp threshold condition is free.  Like
`g2SharpAnchorConst` it constrains only `C_a` against `d`. -/
def g2SharpAnchorConstTwo (d r : ℕ) (C N : ℝ) : ℝ :=
  1 + 73710 * g2ThresholdConstTwo d * (r : ℝ) ^ (8 : ℕ) * C ^ (7 : ℕ) * N ^ (4 : ℕ)

/-- **The sharp threshold condition at the anchor's clauses, for an arbitrary
rate.**

The rate enters only through `hZ`, the requirement that `γ(1+c₁)` still obeys
the anchor's level clause up to a factor `2`.  Everything else is the anchor's
own data: its parameter ranges `s, ε, θ ∈ (0,½]`, its regime clause `γ ≤
C_a^{-1}c⋆^{10}`, its `s⁻⁶` level clause in solved form `hlev`, and the two
**parameter-free** constant floors `hkappa`, `hCaBig`.

This is the item-9 payoff: compare `G2Threshold.g2Threshold_le_of_anchor_rate`,
whose corresponding hypothesis is `g2AnchorConst d r · s ≤ C_a · θ` — a genuine
new clause coupling `θ` to `s`, which the verified consumer refutes.  Here
there is no such clause at all. -/
theorem g2ThresholdSharp_le_of_anchor_rate (M : ABKModel d)
    {C Ca N s ep theta c1 : ℝ} {r : ℕ}
    (hr1 : 1 ≤ r) (hC0 : 0 < C) (hN1 : 1 ≤ N) (hCa1 : 1 ≤ Ca)
    (hs0 : 0 < s) (hs12 : s ≤ 1 / 2) (hep0 : 0 < ep) (hep12 : ep ≤ 1 / 2)
    (hth0 : 0 < theta) (hth12 : theta ≤ 1 / 2) (hc10 : 0 ≤ c1)
    (hreg : M.gamma ≤ Ca⁻¹ * Disorder.cstar M ^ (10 : ℕ))
    (hlev : M.gamma
      ≤ theta * Disorder.cstar M ^ (2 : ℕ) * s ^ (6 : ℕ) * ep ^ (2 : ℕ) / Ca)
    (hZ : M.gamma * (1 + c1)
      ≤ 2 * (theta * Disorder.cstar M ^ (2 : ℕ) * s ^ (6 : ℕ) * ep ^ (2 : ℕ) / Ca))
    (hkappa : g2SharpAnchorConst d r C N ≤ Ca)
    (hCaBig : g2SharpAnchorConstTwo d r C N ≤ Ca) :
    g2ThresholdSharp d r C M s (theta / N) c1 ≤ ep ^ (2 : ℕ) := by
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcs32 : Disorder.cstar M ≤ 3 / 2 :=
    Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M
  have hG0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hCa0 : (0 : ℝ) < Ca := lt_of_lt_of_le zero_lt_one hCa1
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  have hs1 : s ≤ 1 := by linarith only [hs12]
  have hep1 : ep ≤ 1 := by linarith only [hep12]
  have hth1 : theta ≤ 1 := by linarith only [hth12]
  have hthN0 : (0 : ℝ) < theta / N := div_pos hth0 hN0
  have hthN1 : theta / N ≤ 1 := by
    rw [div_le_one hN0]
    linarith only [hth12, hN1]
  have hX0 : (0 : ℝ)
      ≤ theta * Disorder.cstar M ^ (2 : ℕ) * s ^ (6 : ℕ) * ep ^ (2 : ℕ) / Ca :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hth0.le (pow_nonneg hcs0.le 2))
      (pow_nonneg hs0.le 6)) (pow_nonneg hep0.le 2)) hCa0.le
  -- the binding clause
  have hcond1 : g2SharpConstOne d * (r : ℝ) ^ (2 : ℕ) * (1 + c1) * C ^ (2 : ℕ) * M.gamma
      ≤ theta / N * Disorder.cstar M ^ (2 : ℕ) * s ^ (5 : ℕ) * ep ^ (2 : ℕ) := by
    have hpre : (0 : ℝ) ≤ 3 * g2ThresholdConstOne d * (r : ℝ) ^ (2 : ℕ) * C ^ (2 : ℕ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (g2ThresholdConstOne_pos d).le)
        (pow_nonneg (Nat.cast_nonneg r) 2)) (pow_nonneg hC0.le 2)
    have hW0 : (0 : ℝ)
        ≤ theta * Disorder.cstar M ^ (2 : ℕ) * s ^ (5 : ℕ) * ep ^ (2 : ℕ) :=
      mul_nonneg (mul_nonneg (mul_nonneg hth0.le (pow_nonneg hcs0.le 2))
        (pow_nonneg hs0.le 5)) (pow_nonneg hep0.le 2)
    have hKnn : (0 : ℝ) ≤ g2SharpAnchorConst d r C N := by
      rw [g2SharpAnchorConst]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        (g2ThresholdConstOne_pos d).le) (pow_nonneg (Nat.cast_nonneg r) 2))
        (pow_nonneg hC0.le 2)) hN0.le
    have hks : g2SharpAnchorConst d r C N * s ≤ Ca := by
      have hstep := mul_le_mul_of_nonneg_left hs1 hKnn
      linarith only [hstep, hkappa]
    have hk := mul_le_mul_of_nonneg_right hks hW0
    rw [g2SharpAnchorConst] at hk
    calc g2SharpConstOne d * (r : ℝ) ^ (2 : ℕ) * (1 + c1) * C ^ (2 : ℕ) * M.gamma
        = 3 * g2ThresholdConstOne d * (r : ℝ) ^ (2 : ℕ) * C ^ (2 : ℕ)
            * (M.gamma * (1 + c1)) := by
          rw [g2SharpConstOne]; ring
      _ ≤ 3 * g2ThresholdConstOne d * (r : ℝ) ^ (2 : ℕ) * C ^ (2 : ℕ) *
            (2 * (theta * Disorder.cstar M ^ (2 : ℕ) * s ^ (6 : ℕ) * ep ^ (2 : ℕ) / Ca)) :=
          mul_le_mul_of_nonneg_left hZ hpre
      _ = 6 * g2ThresholdConstOne d * (r : ℝ) ^ (2 : ℕ) * C ^ (2 : ℕ) * theta
            * Disorder.cstar M ^ (2 : ℕ) * s ^ (6 : ℕ) * ep ^ (2 : ℕ) / Ca := by ring
      _ ≤ theta / N * Disorder.cstar M ^ (2 : ℕ) * s ^ (5 : ℕ) * ep ^ (2 : ℕ) := by
          rw [show theta / N * Disorder.cstar M ^ (2 : ℕ) * s ^ (5 : ℕ) * ep ^ (2 : ℕ)
              = theta * Disorder.cstar M ^ (2 : ℕ) * s ^ (5 : ℕ) * ep ^ (2 : ℕ)
                  / N from by ring]
          rw [div_le_div_iff₀ hCa0 hN0]
          linarith only [hk]
  -- the exponentially small clause
  have hY : M.gamma ≤ Disorder.cstar M ^ (10 : ℕ) / Ca := by
    rw [le_div_iff₀ hCa0]
    have h := mul_le_mul_of_nonneg_right hreg hCa0.le
    have hid : Ca⁻¹ * Disorder.cstar M ^ (10 : ℕ) * Ca = Disorder.cstar M ^ (10 : ℕ) := by
      have hCane : Ca ≠ 0 := ne_of_gt hCa0
      field_simp
    rwa [hid] at h
  have hG3 : M.gamma ^ (3 : ℕ)
      ≤ theta * Disorder.cstar M ^ (2 : ℕ) * s ^ (6 : ℕ) * ep ^ (2 : ℕ) / Ca
          * (Disorder.cstar M ^ (10 : ℕ) / Ca) ^ (2 : ℕ) := by
    have h2 : M.gamma ^ (2 : ℕ) ≤ (Disorder.cstar M ^ (10 : ℕ) / Ca) ^ (2 : ℕ) :=
      pow_le_pow_left₀ hG0.le hY 2
    calc M.gamma ^ (3 : ℕ) = M.gamma * M.gamma ^ (2 : ℕ) := by ring
      _ ≤ theta * Disorder.cstar M ^ (2 : ℕ) * s ^ (6 : ℕ) * ep ^ (2 : ℕ) / Ca
            * (Disorder.cstar M ^ (10 : ℕ) / Ca) ^ (2 : ℕ) :=
          mul_le_mul hlev h2 (pow_nonneg hG0.le 2) hX0
  have hZ4 : (M.gamma * (1 + c1)) ^ (4 : ℕ)
      ≤ (2 * (theta * Disorder.cstar M ^ (2 : ℕ) * s ^ (6 : ℕ) * ep ^ (2 : ℕ) / Ca))
          ^ (4 : ℕ) :=
    pow_le_pow_left₀ (mul_nonneg hG0.le (by linarith only [hc10])) hZ 4
  have hG7 : M.gamma ^ (7 : ℕ) * (1 + c1) ^ (4 : ℕ)
      ≤ 16 * (theta ^ (5 : ℕ) * Disorder.cstar M ^ (30 : ℕ) * s ^ (30 : ℕ) * ep ^ (10 : ℕ))
          / Ca ^ (7 : ℕ) := by
    calc M.gamma ^ (7 : ℕ) * (1 + c1) ^ (4 : ℕ)
        = M.gamma ^ (3 : ℕ) * (M.gamma * (1 + c1)) ^ (4 : ℕ) := by ring
      _ ≤ (theta * Disorder.cstar M ^ (2 : ℕ) * s ^ (6 : ℕ) * ep ^ (2 : ℕ) / Ca
            * (Disorder.cstar M ^ (10 : ℕ) / Ca) ^ (2 : ℕ))
            * (2 * (theta * Disorder.cstar M ^ (2 : ℕ) * s ^ (6 : ℕ) * ep ^ (2 : ℕ) / Ca))
                ^ (4 : ℕ) :=
          mul_le_mul hG3 hZ4 (pow_nonneg (mul_nonneg hG0.le (by linarith only [hc10])) 4)
            (mul_nonneg hX0 (pow_nonneg (div_nonneg (pow_nonneg hcs0.le 10) hCa0.le) 2))
      _ = 16 * (theta ^ (5 : ℕ) * Disorder.cstar M ^ (30 : ℕ) * s ^ (30 : ℕ)
            * ep ^ (10 : ℕ)) / Ca ^ (7 : ℕ) := by ring
  -- the sharp monotonicity step: one power of `θ` is now spent here, not in the threshold
  have hmono : theta ^ (5 : ℕ) * Disorder.cstar M ^ (30 : ℕ) * s ^ (30 : ℕ) * ep ^ (10 : ℕ)
      ≤ 39 * (theta ^ (4 : ℕ) * Disorder.cstar M ^ (21 : ℕ) * s ^ (9 : ℕ) * ep ^ (2 : ℕ)) := by
    have h1 : Disorder.cstar M ^ (30 : ℕ) ≤ 39 * Disorder.cstar M ^ (21 : ℕ) := by
      have h9 : Disorder.cstar M ^ (9 : ℕ) ≤ 39 :=
        le_trans (pow_le_pow_left₀ hcs0.le hcs32 9) (by norm_num)
      calc Disorder.cstar M ^ (30 : ℕ)
          = Disorder.cstar M ^ (21 : ℕ) * Disorder.cstar M ^ (9 : ℕ) := by ring
        _ ≤ Disorder.cstar M ^ (21 : ℕ) * 39 :=
            mul_le_mul_of_nonneg_left h9 (pow_nonneg hcs0.le 21)
        _ = 39 * Disorder.cstar M ^ (21 : ℕ) := by ring
    have h2 : s ^ (30 : ℕ) ≤ s ^ (9 : ℕ) := pow_le_pow_of_le_one hs0.le hs1 (by norm_num)
    have h3 : ep ^ (10 : ℕ) ≤ ep ^ (2 : ℕ) := pow_le_pow_of_le_one hep0.le hep1 (by norm_num)
    have h4 : theta ^ (5 : ℕ) ≤ theta ^ (4 : ℕ) :=
      pow_le_pow_of_le_one hth0.le hth1 (by norm_num)
    have hA : theta ^ (5 : ℕ) * Disorder.cstar M ^ (30 : ℕ)
        ≤ theta ^ (4 : ℕ) * (39 * Disorder.cstar M ^ (21 : ℕ)) :=
      mul_le_mul h4 h1 (pow_nonneg hcs0.le 30) (pow_nonneg hth0.le 4)
    have hAnn : (0 : ℝ) ≤ theta ^ (4 : ℕ) * (39 * Disorder.cstar M ^ (21 : ℕ)) :=
      mul_nonneg (pow_nonneg hth0.le 4)
        (by have h := pow_nonneg hcs0.le 21; linarith only [h])
    have hB : theta ^ (5 : ℕ) * Disorder.cstar M ^ (30 : ℕ) * s ^ (30 : ℕ)
        ≤ theta ^ (4 : ℕ) * (39 * Disorder.cstar M ^ (21 : ℕ)) * s ^ (9 : ℕ) :=
      mul_le_mul hA h2 (pow_nonneg hs0.le 30) hAnn
    have hBnn : (0 : ℝ) ≤ theta ^ (4 : ℕ) * (39 * Disorder.cstar M ^ (21 : ℕ)) * s ^ (9 : ℕ) :=
      mul_nonneg hAnn (pow_nonneg hs0.le 9)
    calc theta ^ (5 : ℕ) * Disorder.cstar M ^ (30 : ℕ) * s ^ (30 : ℕ) * ep ^ (10 : ℕ)
        ≤ theta ^ (4 : ℕ) * (39 * Disorder.cstar M ^ (21 : ℕ)) * s ^ (9 : ℕ) * ep ^ (2 : ℕ) :=
          mul_le_mul hB h3 (pow_nonneg hep0.le 10) hBnn
      _ = 39 * (theta ^ (4 : ℕ) * Disorder.cstar M ^ (21 : ℕ) * s ^ (9 : ℕ)
            * ep ^ (2 : ℕ)) := by ring
  have hCa7 : 73710 * g2ThresholdConstTwo d * (r : ℝ) ^ (8 : ℕ) * C ^ (7 : ℕ) * N ^ (4 : ℕ)
      ≤ Ca ^ (7 : ℕ) := by
    have h1 : Ca ≤ Ca ^ (7 : ℕ) := le_self_pow₀ hCa1 (by norm_num)
    rw [g2SharpAnchorConstTwo] at hCaBig
    linarith only [hCaBig, h1]
  have hcond2 : 945 / 8 * g2ThresholdConstTwo d * (r : ℝ) ^ (8 : ℕ) * (1 + c1) ^ (4 : ℕ)
        * C ^ (7 : ℕ) * M.gamma ^ (7 : ℕ)
      ≤ (theta / N) ^ (4 : ℕ) * Disorder.cstar M ^ (21 : ℕ) * s ^ (9 : ℕ) * ep ^ (2 : ℕ) := by
    have hpre : (0 : ℝ)
        ≤ 945 / 8 * g2ThresholdConstTwo d * (r : ℝ) ^ (8 : ℕ) * C ^ (7 : ℕ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (g2ThresholdConstTwo_pos d).le)
        (pow_nonneg (Nat.cast_nonneg r) 8)) (pow_nonneg hC0.le 7)
    have hW0 : (0 : ℝ)
        ≤ theta ^ (4 : ℕ) * Disorder.cstar M ^ (21 : ℕ) * s ^ (9 : ℕ) * ep ^ (2 : ℕ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hth0.le 4) (pow_nonneg hcs0.le 21))
        (pow_nonneg hs0.le 9)) (pow_nonneg hep0.le 2)
    have hstep2 : 1890 * g2ThresholdConstTwo d * (r : ℝ) ^ (8 : ℕ) * C ^ (7 : ℕ)
          * (theta ^ (5 : ℕ) * Disorder.cstar M ^ (30 : ℕ) * s ^ (30 : ℕ) * ep ^ (10 : ℕ))
          / Ca ^ (7 : ℕ)
        ≤ 1890 * g2ThresholdConstTwo d * (r : ℝ) ^ (8 : ℕ) * C ^ (7 : ℕ)
            * (39 * (theta ^ (4 : ℕ) * Disorder.cstar M ^ (21 : ℕ) * s ^ (9 : ℕ)
              * ep ^ (2 : ℕ))) / Ca ^ (7 : ℕ) := by
      refine div_le_div_right_of_le_sharp ?_ (pow_nonneg hCa0.le 7)
      refine mul_le_mul_of_nonneg_left hmono ?_
      have h := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1890)
        (g2ThresholdConstTwo_pos d).le) (pow_nonneg (Nat.cast_nonneg r) 8))
        (pow_nonneg hC0.le 7)
      linarith only [h]
    calc 945 / 8 * g2ThresholdConstTwo d * (r : ℝ) ^ (8 : ℕ) * (1 + c1) ^ (4 : ℕ)
          * C ^ (7 : ℕ) * M.gamma ^ (7 : ℕ)
        = 945 / 8 * g2ThresholdConstTwo d * (r : ℝ) ^ (8 : ℕ) * C ^ (7 : ℕ)
            * (M.gamma ^ (7 : ℕ) * (1 + c1) ^ (4 : ℕ)) := by ring
      _ ≤ 945 / 8 * g2ThresholdConstTwo d * (r : ℝ) ^ (8 : ℕ) * C ^ (7 : ℕ)
            * (16 * (theta ^ (5 : ℕ) * Disorder.cstar M ^ (30 : ℕ) * s ^ (30 : ℕ)
              * ep ^ (10 : ℕ)) / Ca ^ (7 : ℕ)) := mul_le_mul_of_nonneg_left hG7 hpre
      _ = 1890 * g2ThresholdConstTwo d * (r : ℝ) ^ (8 : ℕ) * C ^ (7 : ℕ)
            * (theta ^ (5 : ℕ) * Disorder.cstar M ^ (30 : ℕ) * s ^ (30 : ℕ) * ep ^ (10 : ℕ))
            / Ca ^ (7 : ℕ) := by ring
      _ ≤ 1890 * g2ThresholdConstTwo d * (r : ℝ) ^ (8 : ℕ) * C ^ (7 : ℕ)
            * (39 * (theta ^ (4 : ℕ) * Disorder.cstar M ^ (21 : ℕ) * s ^ (9 : ℕ)
              * ep ^ (2 : ℕ))) / Ca ^ (7 : ℕ) := hstep2
      _ = 73710 * g2ThresholdConstTwo d * (r : ℝ) ^ (8 : ℕ) * C ^ (7 : ℕ)
            * (theta ^ (4 : ℕ) * Disorder.cstar M ^ (21 : ℕ) * s ^ (9 : ℕ) * ep ^ (2 : ℕ))
            / Ca ^ (7 : ℕ) := by ring
      _ ≤ (theta / N) ^ (4 : ℕ) * Disorder.cstar M ^ (21 : ℕ) * s ^ (9 : ℕ)
            * ep ^ (2 : ℕ) := by
          rw [show (theta / N) ^ (4 : ℕ) * Disorder.cstar M ^ (21 : ℕ) * s ^ (9 : ℕ)
                * ep ^ (2 : ℕ)
              = theta ^ (4 : ℕ) * Disorder.cstar M ^ (21 : ℕ) * s ^ (9 : ℕ) * ep ^ (2 : ℕ)
                  / N ^ (4 : ℕ) from by ring]
          rw [div_le_div_iff₀ (pow_pos hCa0 7) (pow_pos hN0 4)]
          have h := mul_le_mul_of_nonneg_left hCa7 hW0
          linarith only [h]
  exact g2ThresholdSharp_le_of_gammaPow M hr1 hC0 hs0 hs1 hthN0 hthN1 hc10 hcond1 hcond2

/-- **The sharp threshold condition at the assembly rate `c₁ = 2A`, from the
level clause in solved form.**

`A = c⋆²s⁷ε²θ/(C_aγ)` is the rate the anchor clause carries.  The grouping
`γ(1+c₁) = γ + 2sX`, `X = θc⋆²s⁶ε²/C_a`, linearises the requirement at once: `γ
≤ X` and `2s ≤ 1` give `γ(1+c₁) ≤ 2X`. -/
theorem g2ThresholdSharp_le_of_anchor_solved (M : ABKModel d)
    {C Ca N s ep theta : ℝ} {r : ℕ}
    (hr1 : 1 ≤ r) (hC0 : 0 < C) (hN1 : 1 ≤ N) (hCa1 : 1 ≤ Ca)
    (hs0 : 0 < s) (hs12 : s ≤ 1 / 2) (hep0 : 0 < ep) (hep12 : ep ≤ 1 / 2)
    (hth0 : 0 < theta) (hth12 : theta ≤ 1 / 2)
    (hreg : M.gamma ≤ Ca⁻¹ * Disorder.cstar M ^ (10 : ℕ))
    (hlev : M.gamma
      ≤ theta * Disorder.cstar M ^ (2 : ℕ) * s ^ (6 : ℕ) * ep ^ (2 : ℕ) / Ca)
    (hkappa : g2SharpAnchorConst d r C N ≤ Ca)
    (hCaBig : g2SharpAnchorConstTwo d r C N ≤ Ca) :
    g2ThresholdSharp d r C M s (theta / N)
        (2 * (Disorder.cstar M ^ (2 : ℕ) * s ^ (7 : ℕ) * ep ^ (2 : ℕ) * theta
          / (Ca * M.gamma)))
      ≤ ep ^ (2 : ℕ) := by
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hG0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hCa0 : (0 : ℝ) < Ca := lt_of_lt_of_le zero_lt_one hCa1
  have hX0 : (0 : ℝ)
      ≤ theta * Disorder.cstar M ^ (2 : ℕ) * s ^ (6 : ℕ) * ep ^ (2 : ℕ) / Ca :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hth0.le (pow_nonneg hcs0.le 2))
      (pow_nonneg hs0.le 6)) (pow_nonneg hep0.le 2)) hCa0.le
  have hc10 : (0 : ℝ) ≤ 2 * (Disorder.cstar M ^ (2 : ℕ) * s ^ (7 : ℕ) * ep ^ (2 : ℕ) * theta
      / (Ca * M.gamma)) := by
    have h := div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hcs0.le 2)
      (pow_nonneg hs0.le 7)) (pow_nonneg hep0.le 2)) hth0.le) (mul_pos hCa0 hG0).le
    linarith only [h]
  have hZ : M.gamma * (1 + 2 * (Disorder.cstar M ^ (2 : ℕ) * s ^ (7 : ℕ) * ep ^ (2 : ℕ)
        * theta / (Ca * M.gamma)))
      ≤ 2 * (theta * Disorder.cstar M ^ (2 : ℕ) * s ^ (6 : ℕ) * ep ^ (2 : ℕ) / Ca) := by
    have hCane : Ca ≠ 0 := ne_of_gt hCa0
    have hGne : M.gamma ≠ 0 := ne_of_gt hG0
    have hZeq : M.gamma * (1 + 2 * (Disorder.cstar M ^ (2 : ℕ) * s ^ (7 : ℕ) * ep ^ (2 : ℕ)
          * theta / (Ca * M.gamma)))
        = M.gamma + 2 * s
            * (theta * Disorder.cstar M ^ (2 : ℕ) * s ^ (6 : ℕ) * ep ^ (2 : ℕ) / Ca) := by
      field_simp
    have h2sX : 2 * s * (theta * Disorder.cstar M ^ (2 : ℕ) * s ^ (6 : ℕ) * ep ^ (2 : ℕ) / Ca)
        ≤ theta * Disorder.cstar M ^ (2 : ℕ) * s ^ (6 : ℕ) * ep ^ (2 : ℕ) / Ca := by
      have h := mul_le_mul_of_nonneg_right (show 2 * s ≤ 1 by linarith only [hs12]) hX0
      linarith only [h]
    rw [hZeq]
    linarith only [hlev, h2sX]
  exact g2ThresholdSharp_le_of_anchor_rate M hr1 hC0 hN1 hCa1 hs0 hs12 hep0 hep12 hth0 hth12
    hc10 hreg hlev hZ hkappa hCaBig

/-- The lane is read at level `θ/N` and at the assembly rate `c₁ = 2A`, `A =
c⋆²s⁷ε²θ/(C_aγ)`.  Under the anchor's parameter ranges, its regime clause and
its `s⁻⁶` level clause, the whole `ε`-threshold condition reduces to the two
**parameter-free** constant floors

```
g2SharpAnchorConst d r C N ≤ C_a      and      g2SharpAnchorConstTwo d r C N ≤ C_a ,
```

both functions of `d` alone (once the lane's range `r(d)`, its constant `C(d)`
and the level divisor `N` are fixed).  There is **no residual clause in
`θ` or `s`**.

This resolves the `𝒢₂` side: the proved
`G2Threshold.g2Threshold_le_of_anchor` needed `g2AnchorConst d r · s ≤ C_aθ`,
which the verified consumer refutes as `θ → 0`; the log-quantile reading
removes it entirely. -/
theorem g2ThresholdSharp_le_of_anchor (M : ABKModel d) {C Ca N s ep theta : ℝ} {r : ℕ}
    (hr1 : 1 ≤ r) (hC0 : 0 < C) (hN1 : 1 ≤ N) (hCa1 : 1 ≤ Ca)
    (hs0 : 0 < s) (hs12 : s ≤ 1 / 2) (hep0 : 0 < ep) (hep12 : ep ≤ 1 / 2)
    (hth0 : 0 < theta) (hth12 : theta ≤ 1 / 2)
    (hreg : M.gamma ≤ Ca⁻¹ * Disorder.cstar M ^ (10 : ℕ))
    (hlevel : Ca * (Disorder.cstar M)⁻¹ ^ (2 : ℕ) * s⁻¹ ^ (6 : ℕ) * ep⁻¹ ^ (2 : ℕ) * M.gamma
      ≤ theta)
    (hkappa : g2SharpAnchorConst d r C N ≤ Ca)
    (hCaBig : g2SharpAnchorConstTwo d r C N ≤ Ca) :
    g2ThresholdSharp d r C M s (theta / N)
        (2 * (Disorder.cstar M ^ (2 : ℕ) * s ^ (7 : ℕ) * ep ^ (2 : ℕ) * theta
          / (Ca * M.gamma)))
      ≤ ep ^ (2 : ℕ) := by
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hCa0 : (0 : ℝ) < Ca := lt_of_lt_of_le zero_lt_one hCa1
  have hlev : M.gamma
      ≤ theta * Disorder.cstar M ^ (2 : ℕ) * s ^ (6 : ℕ) * ep ^ (2 : ℕ) / Ca := by
    have hcsne : Disorder.cstar M ≠ 0 := ne_of_gt hcs0
    have hsne : s ≠ 0 := ne_of_gt hs0
    have hepne : ep ≠ 0 := ne_of_gt hep0
    have hmulpos : (0 : ℝ) < Disorder.cstar M ^ (2 : ℕ) * s ^ (6 : ℕ) * ep ^ (2 : ℕ) :=
      mul_pos (mul_pos (pow_pos hcs0 2) (pow_pos hs0 6)) (pow_pos hep0 2)
    have h := mul_le_mul_of_nonneg_right hlevel hmulpos.le
    have hid : Ca * (Disorder.cstar M)⁻¹ ^ (2 : ℕ) * s⁻¹ ^ (6 : ℕ) * ep⁻¹ ^ (2 : ℕ) * M.gamma
        * (Disorder.cstar M ^ (2 : ℕ) * s ^ (6 : ℕ) * ep ^ (2 : ℕ)) = Ca * M.gamma := by
      field_simp
    rw [hid] at h
    rw [le_div_iff₀ hCa0]
    calc M.gamma * Ca = Ca * M.gamma := by ring
      _ ≤ theta * (Disorder.cstar M ^ (2 : ℕ) * s ^ (6 : ℕ) * ep ^ (2 : ℕ)) := h
      _ = theta * Disorder.cstar M ^ (2 : ℕ) * s ^ (6 : ℕ) * ep ^ (2 : ℕ) := by ring
  exact g2ThresholdSharp_le_of_anchor_solved M hr1 hC0 hN1 hCa1 hs0 hs12 hep0 hep12
    hth0 hth12 hreg hlev hkappa hCaBig

end

end Algsuperdiff.Section4.Provider.Proportion
