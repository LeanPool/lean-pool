/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepOneSeamAnchor
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepOneDisplay
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineTopScale
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamSpineBase

/-!
# HomSeamStepOneDisplay

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Step 1's display at the re-pinned base `s/8` and the ENLARGED `Y`

## What this file supplies

`HomSeamSpineBase.StepOneDisplayAt` at

```text
  sb = homSeamBase M hs = s/8,
  Y  = seamEnlargedY M m C_top Y₀
     = C_top · Y₀ · (1 + 𝓔sup_{1/8})(1 + 𝓔sup_{1/4}),
```

i.e. the sibling of Step 1's own display at the
re-pinned base AND at the enlarged `Y` slot
(`HomSpineTopScale.stepTwoEnlargedY` at the consumer pin `t = 1/4`).  Two
moves, one display.

## The bookkeeping

The anchor is consumed through the `exists_ethmB_seam_factor_moments` at the
boosted exponent

```text
  q = max( 8p, 64 d |log γ| ),
```

and the five slots land at `4p`, `4p`, `2p` (the three `EthmB` factors at the
re-pinned base) and `8p`, `8p` (the two enlarged-`Y` factors).  The Theorem-C
edge `Y₀` is used at `4p`, one Hölder step above the `2p` — this is the
`×16` on the printed `p`-range, and it is absorbed into the
produced constant, never into a hypothesis.

`t⁻¹ = 4` is kept displayed: at the consumer pin `t = 1/4`
it is the constant `4`, so the display stays at `|log γ|²`.

## The numeric collapse

`HomStepOneDisplay.display_collapse` is reused verbatim; the two seam moves
contribute exactly one bounded scalar factor

```text
  κ = 8 · C_top · (1 + 𝓔-budget)²  ≤  8 C_top (1 + 8 A D)²,
```

the `8` being the re-pinned base's own `(s/8)⁻¹ = 8|log γ|`.
`seam_display_collapse` is that observation and nothing more.
-/

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The enlarged `Y` slot -/

/-- **THE ENLARGED `Y` SLOT, as one function.**

`C_top · Y₀ · stepTwoEnlargedY`, with the enlargement at the consumer pin
`t = 1/4`: the deterministic Step-2 constant, the Theorem-C minimal-scale
factor, and the two honest error indices of the two-index Step-2 display. -/
def seamEnlargedY (M : ABKModel d) (m : ℤ) (Ctop : ℝ)
    (Y0 : Cutoff.CutoffSample d → ℝ≥0∞) : Cutoff.CutoffSample d → ℝ≥0∞ :=
  fun w =>
    ENNReal.ofReal Ctop *
      (Y0 w * stepTwoEnlargedY M m (show (0 : ℝ) < 1 / 4 by norm_num) w)

/-! ## 2. The Hölder budget of the enlargement -/

/-- **THE ENLARGED-`Y` HÖLDER BUDGET.**

The `2p`-moment of `C_top · (Y₀ · stepTwoEnlargedY)` from the Theorem-C edge at
`4p` and the two new `𝓔`-moments at `8p`.  This is the measured bookkeeping,
executed. -/
theorem seamEnlargedY_moment (M : ABKModel d) (m : ℤ) {t : ℝ} (ht : 0 < t)
    (Y0 : Cutoff.CutoffSample d → ℝ≥0∞)
    (hY0m : AEMeasurable Y0 (Cutoff.cutoffSampleLaw M).toMeasure)
    {Ctop : ℝ} (hCtop : 0 ≤ Ctop) {p R4 R5 : ℝ} (hp : 1 ≤ p)
    (hR4 : 0 ≤ R4) (hR5 : 0 ≤ R5)
    (hY0 : (∫⁻ w, Y0 w ^ (4 * p) ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal 2 ^ (4 * p))
    (h4 : (∫⁻ w,
        fluxCorrectedTwoScaleErrorObservableSup M m m ⟨t / 2, half_pos ht⟩ w ^ (8 * p)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal R4 ^ (8 * p))
    (h5 : (∫⁻ w, fluxCorrectedTwoScaleErrorObservableSup M m m ⟨t, ht⟩ w ^ (8 * p)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal R5 ^ (8 * p)) :
    (∫⁻ w, (ENNReal.ofReal Ctop * (Y0 w * stepTwoEnlargedY M m ht w)) ^ (2 * p)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (Ctop * (2 * ((1 + R4) * (1 + R5)))) ^ (2 * p) := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have h8p : (1 : ℝ) ≤ 8 * p := by linarith only [hp]
  have h4p0 : (0 : ℝ) < 4 * p := by linarith only [hp0]
  have h2p0 : (0 : ℝ) < 2 * p := by linarith only [hp0]
  have hm4 : AEMeasurable
      (fluxCorrectedTwoScaleErrorObservableSup M m m ⟨t / 2, half_pos ht⟩)
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    (measurable_fluxCorrectedTwoScaleErrorObservableSup M (le_refl m) _).aemeasurable
  have hm5 : AEMeasurable
      (fluxCorrectedTwoScaleErrorObservableSup M m m ⟨t, ht⟩)
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    (measurable_fluxCorrectedTwoScaleErrorObservableSup M (le_refl m) _).aemeasurable
  /- the two `(1 + 𝓔)` factors at `8p` -/
  have ha4 : (∫⁻ w, ((1 : ℝ≥0∞) +
      fluxCorrectedTwoScaleErrorObservableSup M m m ⟨t / 2, half_pos ht⟩ w) ^ (8 * p)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal (1 + R4) ^ (8 * p) :=
    lintegral_rpow_add_le_of_moments h8p aemeasurable_const hm4 zero_le_one hR4
      lintegral_rpow_one_le h4
  have ha5 : (∫⁻ w, ((1 : ℝ≥0∞) +
      fluxCorrectedTwoScaleErrorObservableSup M m m ⟨t, ht⟩ w) ^ (8 * p)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal (1 + R5) ^ (8 * p) :=
    lintegral_rpow_add_le_of_moments h8p aemeasurable_const hm5 zero_le_one hR5
      lintegral_rpow_one_le h5
  /- their product at `4p` -/
  have hprod : (∫⁻ w, (stepTwoEnlargedY M m ht w) ^ (4 * p)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal ((1 + R4) * (1 + R5)) ^ (4 * p) := by
    refine Algsuperdiff.Section4.Provider.BoundsEaL.lintegral_rpow_mul_le_of_moments
      h4p0 (aemeasurable_const.add hm4) (aemeasurable_const.add hm5)
      (by linarith only [hR4]) ?_ ?_
    · have he : (2 : ℝ) * (4 * p) = 8 * p := by ring
      rw [he]; exact ha4
    · have he : (2 : ℝ) * (4 * p) = 8 * p := by ring
      rw [he]; exact ha5
  /- `Y₀ · stepTwoEnlargedY` at `2p` -/
  have houter : (∫⁻ w, (Y0 w * stepTwoEnlargedY M m ht w) ^ (2 * p)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (2 * ((1 + R4) * (1 + R5))) ^ (2 * p) := by
    refine Algsuperdiff.Section4.Provider.BoundsEaL.lintegral_rpow_mul_le_of_moments
      h2p0 hY0m ((aemeasurable_const.add hm4).mul (aemeasurable_const.add hm5))
      (by norm_num) ?_ ?_
    · have he : (2 : ℝ) * (2 * p) = 4 * p := by ring
      rw [he]; exact hY0
    · have he : (2 : ℝ) * (2 * p) = 4 * p := by ring
      rw [he]; exact hprod
  exact lintegral_rpow_const_mul_le (by linarith only [hp0]) hCtop houter

/-! ## 3. The seam collapse constants -/

/-- The `√max` loss of the re-pinned boosted exponent `q = max(8p, 64 d |log γ|)`. -/
def homSeamSqrtLoss (d : ℕ) : ℝ := 3 + 8 * Real.sqrt (d : ℝ)

theorem homSeamSqrtLoss_nonneg (d : ℕ) : 0 ≤ homSeamSqrtLoss d := by
  have h : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  rw [homSeamSqrtLoss]; linarith only [h]

/-- The two `display_collapse` budgets, added. -/
def homSeamCollapseConst (A : ℝ) (d : ℕ) : ℝ :=
  2 * A * homSeamSqrtLoss d * (1 + 2 * A * homSeamSqrtLoss d) +
    (1 + 4 * A ^ (2 : ℕ) * homSeamSqrtLoss d ^ (2 : ℕ))

theorem homSeamCollapseConst_nonneg {A : ℝ} (hA : 0 ≤ A) (d : ℕ) :
    0 ≤ homSeamCollapseConst A d := by
  have hD : (0 : ℝ) ≤ homSeamSqrtLoss d := homSeamSqrtLoss_nonneg d
  rw [homSeamCollapseConst]
  have h1 : (0 : ℝ) ≤ 2 * A * homSeamSqrtLoss d * (1 + 2 * A * homSeamSqrtLoss d) := by
    positivity
  have h2 : (0 : ℝ) ≤ 4 * A ^ (2 : ℕ) * homSeamSqrtLoss d ^ (2 : ℕ) := by positivity
  linarith only [h1, h2]

/-- The seam enlargement's bounded scalar factor: the re-pinned base's own `8`,
the deterministic Step-2 constant, and the two `(1 + 𝓔)` budgets. -/
def homSeamKappa (A Ctop : ℝ) (d : ℕ) : ℝ :=
  8 * Ctop * (1 + 8 * A * homSeamSqrtLoss d) ^ (2 : ℕ) + 1

theorem one_le_homSeamKappa {A Ctop : ℝ} (hA : 0 ≤ A) (hCtop : 0 ≤ Ctop) (d : ℕ) :
    1 ≤ homSeamKappa A Ctop d := by
  have hD : (0 : ℝ) ≤ homSeamSqrtLoss d := homSeamSqrtLoss_nonneg d
  have h : (0 : ℝ) ≤ 8 * Ctop * (1 + 8 * A * homSeamSqrtLoss d) ^ (2 : ℕ) := by positivity
  rw [homSeamKappa]; linarith only [h]

/-- **The produced constant of the seam display.**  The `8A` summand is the
`q = 8p` boost of the `p`-range, the `2 C_gate` summand is the Theorem-C edge's
own `4p` reading, and the product is the collapse budget times the enlargement's
scalar. -/
def homSeamDisplayConst (A Ctop Cgate : ℝ) (d : ℕ) : ℝ :=
  8 * A + homSeamKappa A Ctop d * homSeamCollapseConst A d + 2 * Cgate + 1

theorem one_le_homSeamDisplayConst {A Ctop Cgate : ℝ} (hA : 0 ≤ A) (hCtop : 0 ≤ Ctop)
    (hCgate : 0 ≤ Cgate) (d : ℕ) : 1 ≤ homSeamDisplayConst A Ctop Cgate d := by
  have h1 : (0 : ℝ) ≤ 8 * A := by linarith only [hA]
  have h2 : (0 : ℝ) ≤ homSeamKappa A Ctop d * homSeamCollapseConst A d :=
    mul_nonneg (le_trans zero_le_one (one_le_homSeamKappa hA hCtop d))
      (homSeamCollapseConst_nonneg hA d)
  rw [homSeamDisplayConst]; linarith only [h1, h2, hCgate]

/-! ## 4. The seam collapse -/

/-- **THE SEAM COLLAPSE.**  `HomStepOneDisplay.display_collapse` with the two
seam moves — the base `s/8` (an `8`) and the enlarged `Y` (the factor
`C_top (1+R₄)(1+R₅)`) — carried as ONE bounded scalar. -/
private theorem seam_display_collapse {A D L S G W gam Cgap Ctop Cd C0 R4 R5 : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hL : 4 ≤ L) (hS : 3 ≤ S) (hG : 0 ≤ G) (hW : 0 ≤ W)
    (hgam0 : 0 ≤ gam) (hCgap : 0 ≤ Cgap) (hCtop : 0 ≤ Ctop)
    (_hR40 : 0 ≤ R4) (hR50 : 0 ≤ R5) (hR4 : R4 ≤ 8 * A * D) (hR5 : R5 ≤ 8 * A * D)
    (hWDS : W ≤ D * S) (hSG : S * G ≤ 2) (hgam5 : gam ^ (5 : ℕ) ≤ G)
    (h1 : 2 * A * D * (1 + 2 * A * D) ≤ Cd)
    (h2 : 1 + 4 * A ^ (2 : ℕ) * D ^ (2 : ℕ) ≤ Cd)
    (hC0 : (8 * Ctop * (1 + 8 * A * D) ^ (2 : ℕ) + 1) * Cd ≤ C0) :
    8 * L * (Ctop * (2 * ((1 + R4) * (1 + R5))) * (A * L * W * G * (1 + A * W * G))) +
        Cgap * gam ^ (5 : ℕ) * (1 + (A * L * W * G) ^ (2 : ℕ)) ≤
      C0 * (1 + Cgap) * S * G * L ^ (2 : ℕ) := by
  have hL0 : (0 : ℝ) ≤ L := by linarith only [hL]
  have hS0 : (0 : ℝ) ≤ S := by linarith only [hS]
  have hbase := display_collapse (A := A) (D := D) (L := L) (S := S) (G := G) (W := W)
    (gam := gam) (Cgap := Cgap) (C0 := Cd) hA hD hL hS hG hW hCgap hWDS hSG hgam5 h1 h2
  set T1 : ℝ := L * (2 * (A * L * W * G * (1 + A * W * G))) with hT1def
  set T2 : ℝ := Cgap * gam ^ (5 : ℕ) * (1 + (A * L * W * G) ^ (2 : ℕ)) with hT2def
  set kap : ℝ := 8 * Ctop * (1 + 8 * A * D) ^ (2 : ℕ) + 1 with hkapdef
  have hWG0 : (0 : ℝ) ≤ W * G := mul_nonneg hW hG
  have hWG2D : W * G ≤ 2 * D := by
    have hstep : W * G ≤ (D * S) * G := mul_le_mul_of_nonneg_right hWDS hG
    have hstep2 : D * (S * G) ≤ D * 2 := mul_le_mul_of_nonneg_left hSG hD
    calc W * G ≤ (D * S) * G := hstep
      _ = D * (S * G) := by ring
      _ ≤ D * 2 := hstep2
      _ = 2 * D := by ring
  /- the enlargement's factor is below `kap` -/
  have hfac : Ctop * (2 * ((1 + R4) * (1 + R5))) * 8 ≤ kap * 2 := by
    have hb4 : 1 + R4 ≤ 1 + 8 * A * D := by linarith only [hR4]
    have hb5 : 1 + R5 ≤ 1 + 8 * A * D := by linarith only [hR5]
    have hAD : (0 : ℝ) ≤ 8 * A * D := by positivity
    have hprod : (1 + R4) * (1 + R5) ≤ (1 + 8 * A * D) ^ (2 : ℕ) := by
      have := mul_le_mul hb4 hb5 (by linarith only [hR50]) (by linarith only [hAD])
      calc (1 + R4) * (1 + R5) ≤ (1 + 8 * A * D) * (1 + 8 * A * D) := this
        _ = (1 + 8 * A * D) ^ (2 : ℕ) := by ring
    have hC8 : (0 : ℝ) ≤ 8 * Ctop := by linarith only [hCtop]
    have hmul := mul_le_mul_of_nonneg_left hprod hC8
    have hnn : (0 : ℝ) ≤ 8 * Ctop * (1 + 8 * A * D) ^ (2 : ℕ) := by positivity
    rw [hkapdef]
    linarith only [hmul, hnn]
  /- `T1 ≥ 0`, `T2 ≥ 0` -/
  have hT10 : (0 : ℝ) ≤ T1 := by
    have hAWG : (0 : ℝ) ≤ A * W * G := by positivity
    rw [hT1def]
    have hin : (0 : ℝ) ≤ A * L * W * G * (1 + A * W * G) := by
      have h1' : (0 : ℝ) ≤ A * L * W * G := by positivity
      have h2' : (0 : ℝ) ≤ 1 + A * W * G := by linarith only [hAWG]
      exact mul_nonneg h1' h2'
    linarith only [hin, hL0, mul_nonneg hL0 hin]
  have hT20 : (0 : ℝ) ≤ T2 := by
    rw [hT2def]
    have hsq : (0 : ℝ) ≤ (A * L * W * G) ^ (2 : ℕ) := sq_nonneg _
    have hg5 : (0 : ℝ) ≤ gam ^ (5 : ℕ) := by positivity
    have hone : (0 : ℝ) ≤ 1 + (A * L * W * G) ^ (2 : ℕ) := by linarith only [hsq]
    have hmul := mul_nonneg (mul_nonneg hCgap hg5) hone
    linarith only [hmul]
  have hkap1 : (1 : ℝ) ≤ kap := by
    have h : (0 : ℝ) ≤ 8 * Ctop * (1 + 8 * A * D) ^ (2 : ℕ) := by positivity
    rw [hkapdef]; linarith only [h]
  /- the left-hand side is `≤ kap · (T1 + T2)` -/
  have hLHS : 8 * L * (Ctop * (2 * ((1 + R4) * (1 + R5))) *
      (A * L * W * G * (1 + A * W * G))) ≤ kap * T1 := by
    have hin0 : (0 : ℝ) ≤ L * (A * L * W * G * (1 + A * W * G)) := by
      have hAWG : (0 : ℝ) ≤ A * W * G := by positivity
      have h1' : (0 : ℝ) ≤ A * L * W * G := by positivity
      exact mul_nonneg hL0 (mul_nonneg h1' (by linarith only [hAWG]))
    have hmul := mul_le_mul_of_nonneg_right hfac hin0
    calc 8 * L * (Ctop * (2 * ((1 + R4) * (1 + R5))) *
          (A * L * W * G * (1 + A * W * G)))
        = (Ctop * (2 * ((1 + R4) * (1 + R5))) * 8) *
            (L * (A * L * W * G * (1 + A * W * G))) := by ring
      _ ≤ (kap * 2) * (L * (A * L * W * G * (1 + A * W * G))) := hmul
      _ = kap * T1 := by rw [hT1def]; ring
  have hT2kap : T2 ≤ kap * T2 := le_mul_of_one_le_left hT20 hkap1
  have hbase' : kap * (T1 + T2) ≤ kap * (Cd * (1 + Cgap) * S * G * L ^ (2 : ℕ)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith only [hkap1])
    exact hbase
  have hfinal : kap * (Cd * (1 + Cgap) * S * G * L ^ (2 : ℕ)) ≤
      C0 * (1 + Cgap) * S * G * L ^ (2 : ℕ) := by
    have hT : (0 : ℝ) ≤ (1 + Cgap) * S * G * L ^ (2 : ℕ) := by positivity
    have hstep : (kap * Cd) * ((1 + Cgap) * S * G * L ^ (2 : ℕ)) ≤
        C0 * ((1 + Cgap) * S * G * L ^ (2 : ℕ)) := by
      refine mul_le_mul_of_nonneg_right ?_ hT
      rw [hkapdef]; exact hC0
    calc kap * (Cd * (1 + Cgap) * S * G * L ^ (2 : ℕ))
        = (kap * Cd) * ((1 + Cgap) * S * G * L ^ (2 : ℕ)) := by ring
      _ ≤ C0 * ((1 + Cgap) * S * G * L ^ (2 : ℕ)) := hstep
      _ = C0 * (1 + Cgap) * S * G * L ^ (2 : ℕ) := by ring
  have hsum : kap * T1 + kap * T2 = kap * (T1 + T2) := by ring
  linarith only [hLHS, hT2kap, hbase', hfinal, hsum]

/-! ## 5. Two range transfers -/

/-- A `p`-range at a product constant transfers to the scaled exponent: this is
the only thing the two exponent boosts (`q = 8p` and the Theorem-C edge's `4p`)
cost. -/
private theorem range_scale {k K C gam Lg p : ℝ} (hk : 0 < k) (hK : 0 < K)
    (hkK : k * K ≤ C) (hgam : 0 ≤ gam⁻¹) (hLg : 0 ≤ Lg⁻¹)
    (hp : p ≤ C⁻¹ * gam⁻¹ * Lg⁻¹) : k * p ≤ K⁻¹ * gam⁻¹ * Lg⁻¹ := by
  have hCpos : 0 < C := lt_of_lt_of_le (mul_pos hk hK) hkK
  have hkey : k * C⁻¹ ≤ K⁻¹ := by
    refine le_of_mul_le_mul_right ?_ (mul_pos hCpos hK)
    have hl : (k * C⁻¹) * (C * K) = k * K * (C⁻¹ * C) := by ring
    have hr : K⁻¹ * (C * K) = C * (K⁻¹ * K) := by ring
    rw [hl, hr, inv_mul_cancel₀ (ne_of_gt hCpos), inv_mul_cancel₀ (ne_of_gt hK),
      mul_one, mul_one]
    exact hkK
  have hT : (0 : ℝ) ≤ gam⁻¹ * Lg⁻¹ := mul_nonneg hgam hLg
  have hstep : k * p ≤ k * (C⁻¹ * gam⁻¹ * Lg⁻¹) :=
    mul_le_mul_of_nonneg_left hp hk.le
  have hstep2 : (k * C⁻¹) * (gam⁻¹ * Lg⁻¹) ≤ K⁻¹ * (gam⁻¹ * Lg⁻¹) :=
    mul_le_mul_of_nonneg_right hkey hT
  calc k * p ≤ k * (C⁻¹ * gam⁻¹ * Lg⁻¹) := hstep
    _ = (k * C⁻¹) * (gam⁻¹ * Lg⁻¹) := by ring
    _ ≤ K⁻¹ * (gam⁻¹ * Lg⁻¹) := hstep2
    _ = K⁻¹ * gam⁻¹ * Lg⁻¹ := by ring

/-! ## 6. THE SEAM DISPLAY -/

private theorem homSeamStepOneDisplay_comparisonBounds1 :
    ∀ (d : ℕ) {Ctop Cgate : ℝ} (A : ℝ) (_ : (1 : ℝ) ≤ homSeamDisplayConst A Ctop Cgate d) (M :
      ABKModel d)
      (p : ℝ) (_ : (1 : ℝ) ≤ p) (_ : p ≤ (homSeamDisplayConst A Ctop Cgate d)⁻¹ * M.gamma⁻¹ *
        |Real.log M.gamma|⁻¹)
      (_ : (0 : ℝ) < M.gamma) (_ : (0 : ℝ) < √√M.gamma) (_ : √√M.gamma ^ (4 : ℕ) = M.gamma)
      (_ : √√M.gamma ≤ (1 / 16 : ℝ)) (_ : M.gamma < (1 : ℝ)) (_ : (4 : ℝ) ≤ |Real.log M.gamma|)
      (_ : |Real.log M.gamma| ≠ (0 : ℝ)) (_ : homS M ≤ (1 / 4 : ℝ))
      (_ : |Real.log M.gamma| ≤ (4 : ℝ) * (√√M.gamma)⁻¹) (_ : (0 : ℝ) ≤ |Real.log M.gamma|⁻¹)
      (_ : homS M = |Real.log M.gamma|⁻¹) (_ : (0 : ℝ) < p),
      let q : ℝ := max ((8 : ℝ) * p) ((64 : ℝ) * (↑d : ℝ) * |Real.log M.gamma|);
      ∀ (_ : (1 : ℝ) ≤ √p) (_ : (2 : ℝ) ≤ √|Real.log M.gamma|),
        (3 : ℝ) ≤ √p + √|Real.log M.gamma| ∧
          √q ≤ homSeamSqrtLoss d * (√p + √|Real.log M.gamma|) ∧
            (√p + √|Real.log M.gamma|) * √M.gamma ≤ (2 : ℝ) ∧ M.gamma ^ (5 : ℕ) ≤ √M.gamma := by
  intro d Ctop Cgate A hC0one M p _ hprange hgpos htpos ht4 ht16 hg1 _ _ hs4 hLu hLinv hSeq hp0 q
    hsqp hsqL
  have hS3 : (3 : ℝ) ≤ Real.sqrt p + Real.sqrt |Real.log M.gamma| := by
    linarith only [hsqp, hsqL]
  have hWDS : Real.sqrt q ≤ homSeamSqrtLoss d *
      (Real.sqrt p + Real.sqrt |Real.log M.gamma|) := by
    have hmax := sqrt_max_le (a := 8 * p) (b := 64 * (d : ℝ) * |Real.log M.gamma|)
      (by linarith only [hp0]) (by positivity)
    have he1 : Real.sqrt (8 * p) ≤ 3 * Real.sqrt p := by
      have h8 : Real.sqrt (8 * p) = Real.sqrt 8 * Real.sqrt p :=
        Real.sqrt_mul (by norm_num) p
      have h9 : Real.sqrt 8 ≤ 3 := by
        have h := Real.sqrt_le_sqrt (show (8 : ℝ) ≤ 9 by norm_num)
        have h3 : Real.sqrt 9 = 3 := by
          rw [show (9 : ℝ) = 3 ^ (2 : ℕ) from by norm_num,
            Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
        rwa [h3] at h
      rw [h8]
      exact mul_le_mul_of_nonneg_right h9 (Real.sqrt_nonneg _)
    have he2 : Real.sqrt (64 * (d : ℝ) * |Real.log M.gamma|) =
        8 * Real.sqrt (d : ℝ) * Real.sqrt |Real.log M.gamma| := by
      rw [Real.sqrt_mul (by positivity) _, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 64) _]
      have h64 : Real.sqrt 64 = 8 := by
        rw [show (64 : ℝ) = 8 ^ (2 : ℕ) from by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 8)]
      rw [h64]
    have hexp : homSeamSqrtLoss d * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) =
        3 * Real.sqrt p + 8 * Real.sqrt (d : ℝ) * Real.sqrt |Real.log M.gamma| +
          (3 * Real.sqrt |Real.log M.gamma| + 8 * Real.sqrt (d : ℝ) * Real.sqrt p) := by
      rw [homSeamSqrtLoss]; ring
    have hslack : (0 : ℝ) ≤ 3 * Real.sqrt |Real.log M.gamma| +
        8 * Real.sqrt (d : ℝ) * Real.sqrt p := by positivity
    rw [he2] at hmax
    rw [hexp]
    linarith only [hmax, he1, hslack]
  have hpg : p * M.gamma ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hprange hgpos.le
    have he : (homSeamDisplayConst A Ctop Cgate d)⁻¹ * M.gamma⁻¹ *
        |Real.log M.gamma|⁻¹ * M.gamma =
        (homSeamDisplayConst A Ctop Cgate d)⁻¹ * |Real.log M.gamma|⁻¹ := by
      field_simp
    rw [he] at h
    have hCinv : (homSeamDisplayConst A Ctop Cgate d)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ hC0one
    have hLq : |Real.log M.gamma|⁻¹ ≤ 1 / 4 := by
      rw [← hSeq]; exact hs4
    have hbd : (homSeamDisplayConst A Ctop Cgate d)⁻¹ * |Real.log M.gamma|⁻¹ ≤
        1 * (1 / 4) := mul_le_mul hCinv hLq hLinv zero_le_one
    linarith only [h, hbd]
  have hLg : |Real.log M.gamma| * M.gamma ≤ 1 := by
    have hstep : |Real.log M.gamma| * M.gamma ≤
        (4 * (Real.sqrt (Real.sqrt M.gamma))⁻¹) * M.gamma :=
      mul_le_mul_of_nonneg_right hLu hgpos.le
    have hne : Real.sqrt (Real.sqrt M.gamma) ≠ 0 := ne_of_gt htpos
    have he : (4 * (Real.sqrt (Real.sqrt M.gamma))⁻¹) * M.gamma =
        4 * Real.sqrt (Real.sqrt M.gamma) ^ (3 : ℕ) := by
      calc (4 * (Real.sqrt (Real.sqrt M.gamma))⁻¹) * M.gamma
          = (4 * (Real.sqrt (Real.sqrt M.gamma))⁻¹) *
              Real.sqrt (Real.sqrt M.gamma) ^ (4 : ℕ) := by rw [ht4]
        _ = 4 * ((Real.sqrt (Real.sqrt M.gamma))⁻¹ * Real.sqrt (Real.sqrt M.gamma)) *
              Real.sqrt (Real.sqrt M.gamma) ^ (3 : ℕ) := by ring
        _ = 4 * 1 * Real.sqrt (Real.sqrt M.gamma) ^ (3 : ℕ) := by
              rw [inv_mul_cancel₀ hne]
        _ = 4 * Real.sqrt (Real.sqrt M.gamma) ^ (3 : ℕ) := by ring
    have ht3 : Real.sqrt (Real.sqrt M.gamma) ^ (3 : ℕ) ≤ (1 / 16 : ℝ) ^ (3 : ℕ) :=
      pow_le_pow_left₀ htpos.le ht16 3
    have hnum : (1 / 16 : ℝ) ^ (3 : ℕ) = 1 / 4096 := by norm_num
    rw [hnum] at ht3
    rw [he] at hstep
    linarith only [hstep, ht3]
  have hSG : (Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma ≤ 2 := by
    have e1 : Real.sqrt p * Real.sqrt M.gamma = Real.sqrt (p * M.gamma) :=
      (Real.sqrt_mul hp0.le M.gamma).symm
    have e2 : Real.sqrt |Real.log M.gamma| * Real.sqrt M.gamma =
        Real.sqrt (|Real.log M.gamma| * M.gamma) :=
      (Real.sqrt_mul (abs_nonneg _) M.gamma).symm
    have b1 : Real.sqrt (p * M.gamma) ≤ 1 := sqrt_le_one_of_le_one hpg
    have b2 : Real.sqrt (|Real.log M.gamma| * M.gamma) ≤ 1 := sqrt_le_one_of_le_one hLg
    have he : (Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma =
        Real.sqrt p * Real.sqrt M.gamma +
          Real.sqrt |Real.log M.gamma| * Real.sqrt M.gamma := by ring
    rw [he, e1, e2]
    linarith only [b1, b2]
  have hgam5 : M.gamma ^ (5 : ℕ) ≤ Real.sqrt M.gamma := by
    have h5 : M.gamma ^ (5 : ℕ) ≤ M.gamma :=
      pow_le_of_le_one hgpos.le hg1.le (by norm_num)
    have hsq1 : Real.sqrt M.gamma ≤ 1 := sqrt_le_one_of_le_one hg1.le
    have hself : Real.sqrt M.gamma * Real.sqrt M.gamma = M.gamma :=
      Real.mul_self_sqrt hgpos.le
    have hle : M.gamma ≤ Real.sqrt M.gamma := by
      have hmul : Real.sqrt M.gamma * Real.sqrt M.gamma ≤ Real.sqrt M.gamma * 1 :=
        mul_le_mul_of_nonneg_left hsq1 (Real.sqrt_nonneg _)
      rw [hself] at hmul
      linarith only [hmul]
    linarith only [h5, hle]
  exact ⟨hS3, hWDS, hSG, hgam5⟩

private theorem homSeamStepOneDisplay_momentBounds1 :
    ∀ (d : ℕ) {Ctop Cgate : ℝ} (_ : (0 : ℝ) ≤ Ctop) (_ : (0 : ℝ) < Cgate) (A : ℝ) (_ : (1 : ℝ) ≤ A)
      (_ : (0 : ℝ) < A) (_ : (0 : ℝ) ≤ homSeamKappa A Ctop d * homSeamCollapseConst A d) (M :
        ABKModel d)
      (hs : (0 : ℝ) < homS M) (m : ℤ) (Y0 : Cutoff.CutoffSample d → ℝ≥0∞)
      (_ : AEMeasurable Y0 (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d)))
      (_ :
        ∀ (p : ℝ),
          (1 : ℝ) ≤ p →
            p ≤ Cgate⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
              ∫⁻ (w : Cutoff.CutoffSample d),
                  Y0 w ^ ((2 : ℝ) * p) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure
                    (Cutoff.CutoffSample d)) ≤
                ENNReal.ofReal (2 : ℝ) ^ ((2 : ℝ) * p))
      (Cgap : ℝ) (_ : (0 : ℝ) ≤ Cgap) (p : ℝ) (_ : (1 : ℝ) ≤ p)
      (_ : p ≤ (homSeamDisplayConst A Ctop Cgate d)⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹) (_ : (0
        : ℝ) < M.gamma)
      (_ : (4 : ℝ) ≤ |Real.log M.gamma|) (_ : (0 : ℝ) ≤ M.gamma⁻¹) (_ : (0 : ℝ) ≤ |Real.log
        M.gamma|⁻¹)
      (_ : (0 : ℝ) < p),
      let q : ℝ := max ((8 : ℝ) * p) ((64 : ℝ) * (↑d : ℝ) * |Real.log M.gamma|);
      ∀ (_ : (8 : ℝ) * p ≤ q) (ht40 : (0 : ℝ) < (1 / 4 : ℝ))
        (_ :
          ∫⁻ (omega : Cutoff.CutoffSample d),
              fluxCorrectedTwoScaleErrorObservableSup M m (homN M m) (homHalf (homSeamBase M hs))
                omega ^
                q ∂(↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d)) ≤
            ENNReal.ofReal (A * |Real.log M.gamma| * √q * √M.gamma) ^ q)
        (_ :
          ∫⁻ (omega : Cutoff.CutoffSample d),
              fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega ^
                q ∂(↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d)) ≤
            ENNReal.ofReal (A * √q * √M.gamma) ^ q)
        (_ :
          ∫⁻ (omega : Cutoff.CutoffSample d),
              fluxCorrectedTwoScaleErrorObservableSup M m (homN M m) (homQuarterOf (homSeamBase M
                hs)) omega ^
                q ∂(↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d)) ≤
            ENNReal.ofReal (A * |Real.log M.gamma| * √q * √M.gamma) ^ q)
        (_ :
          ∫⁻ (omega : Cutoff.CutoffSample d),
              fluxCorrectedTwoScaleErrorObservableSup M m m ⟨(1 / 4 : ℝ) / (2 : ℝ), half_pos ht40⟩
                omega ^
                q ∂(↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d)) ≤
            ENNReal.ofReal (A * (1 / 4 : ℝ)⁻¹ * √q * √M.gamma) ^ q)
        (_ :
          ∫⁻ (omega : Cutoff.CutoffSample d),
              fluxCorrectedTwoScaleErrorObservableSup M m m ⟨(1 / 4 : ℝ), ht40⟩ omega ^
                q ∂(↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d)) ≤
            ENNReal.ofReal (A * (1 / 4 : ℝ)⁻¹ * √q * √M.gamma) ^ q),
        (0 : ℝ) ≤ A * (1 / 4 : ℝ)⁻¹ * √q * √M.gamma ∧
          ∫⁻ (omega : Cutoff.CutoffSample d),
              ethmB M Cgap (seamEnlargedY M m Ctop Y0) m (homN M m) (homSeamBase M hs) omega ^
                p ∂(↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d)) ≤
            ENNReal.ofReal
                ((↑(homSeamBase M hs) : ℝ)⁻¹ *
                    (Ctop *
                        ((2 : ℝ) *
                          (((1 : ℝ) + A * (1 / 4 : ℝ)⁻¹ * √q * √M.gamma) * ((1 : ℝ) + A * (1 / 4 :
                            ℝ)⁻¹ * √q * √M.gamma))) *
                      (A * |Real.log M.gamma| * √q * √M.gamma * ((1 : ℝ) + A * √q * √M.gamma))) +
                  Cgap * M.gamma ^ (5 : ℕ) * ((1 : ℝ) + (A * |Real.log M.gamma| * √q * √M.gamma) ^
                    (2 : ℕ))) ^
              p := by
  intro _ Ctop Cgate hCtop hCgate A _ hApos hkap0 M hs m Y0 hY0m hY0 _ hCgap p hp hprange _ _
    hginv hLinv hp0 q hq8p ht40 hf1 hf2 hf3 hf4 hf5
  have hnm : homN M m ≤ m := homN_le M m
  have hm1 : AEMeasurable
      (fluxCorrectedTwoScaleErrorObservableSup M m (homN M m)
        (homHalf (homSeamBase M hs))) (Cutoff.cutoffSampleLaw M).toMeasure :=
    (measurable_fluxCorrectedTwoScaleErrorObservableSup M hnm _).aemeasurable
  have hm2 : AEMeasurable (fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter)
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    (measurable_fluxCorrectedTwoScaleErrorObservableSup M (le_refl m) _).aemeasurable
  have hm3 : AEMeasurable
      (fluxCorrectedTwoScaleErrorObservableSup M m (homN M m)
        (homQuarterOf (homSeamBase M hs))) (Cutoff.cutoffSampleLaw M).toMeasure :=
    (measurable_fluxCorrectedTwoScaleErrorObservableSup M hnm _).aemeasurable
  have hm4 : AEMeasurable
      (fluxCorrectedTwoScaleErrorObservableSup M m m ⟨1 / 4 / 2, half_pos ht40⟩)
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    (measurable_fluxCorrectedTwoScaleErrorObservableSup M (le_refl m) _).aemeasurable
  have hm5 : AEMeasurable
      (fluxCorrectedTwoScaleErrorObservableSup M m m ⟨1 / 4, ht40⟩)
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    (measurable_fluxCorrectedTwoScaleErrorObservableSup M (le_refl m) _).aemeasurable
  have h2p0 : (0 : ℝ) < 2 * p := by linarith only [hp0]
  have h4p0 : (0 : ℝ) < 4 * p := by linarith only [hp0]
  have h8p0 : (0 : ℝ) < 8 * p := by linarith only [hp0]
  have hq4p : 4 * p ≤ q := by linarith only [hq8p, hp0]
  have hq2p : 2 * p ≤ q := by linarith only [hq8p, hp0]
  have hd1 := lintegral_rpow_le_of_exponent_le hm1 h4p0 hq4p hf1
  have hd2 := lintegral_rpow_le_of_exponent_le hm2 h4p0 hq4p hf2
  have hd3 := lintegral_rpow_le_of_exponent_le hm3 h2p0 hq2p hf3
  have hd4 := lintegral_rpow_le_of_exponent_le hm4 h8p0 hq8p hf4
  have hd5 := lintegral_rpow_le_of_exponent_le hm5 h8p0 hq8p hf5
  /- ### the Theorem-C edge, read at `4p` -/
  have hY04p : (∫⁻ w, Y0 w ^ (4 * p) ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal 2 ^ (4 * p) := by
    have hrange2 : 2 * p ≤ Cgate⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ := by
      refine range_scale (by norm_num) hCgate ?_ hginv hLinv hprange
      rw [homSeamDisplayConst]
      have h8A : (0 : ℝ) ≤ 8 * A := by linarith only [hApos]
      linarith only [hkap0, h8A]
    have h := hY0 (2 * p) (by linarith only [hp]) hrange2
    rwa [show (2 : ℝ) * (2 * p) = 4 * p from by ring] at h
  /- ### the enlarged `Y` and its mome -/
  have hEm : AEMeasurable (stepTwoEnlargedY M m ht40)
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    (aemeasurable_const.add hm4).mul (aemeasurable_const.add hm5)
  have hYm : AEMeasurable (seamEnlargedY M m Ctop Y0)
      (Cutoff.cutoffSampleLaw M).toMeasure := (hY0m.mul hEm).const_mul _
  have hR40 : (0 : ℝ) ≤ A * (1 / 4 : ℝ)⁻¹ * Real.sqrt q * Real.sqrt M.gamma := by
    have hA0 : (0 : ℝ) ≤ A := hApos.le
    positivity
  have hYenl := seamEnlargedY_moment M m ht40 Y0 hY0m hCtop hp hR40 hR40 hY04p hd4 hd5
  /- ### the Hölder assembly at the re-pinned ba -/
  have hR1 : (0 : ℝ) ≤ A * |Real.log M.gamma| * Real.sqrt q * Real.sqrt M.gamma := by
    have hA0 : (0 : ℝ) ≤ A := hApos.le
    positivity
  have hR2 : (0 : ℝ) ≤ A * Real.sqrt q * Real.sqrt M.gamma := by
    have hA0 : (0 : ℝ) ≤ A := hApos.le
    positivity
  have hRY : (0 : ℝ) ≤ Ctop * (2 * ((1 + A * (1 / 4 : ℝ)⁻¹ * Real.sqrt q *
      Real.sqrt M.gamma) * (1 + A * (1 / 4 : ℝ)⁻¹ * Real.sqrt q * Real.sqrt M.gamma))) := by
    have h1 : (0 : ℝ) ≤ 1 + A * (1 / 4 : ℝ)⁻¹ * Real.sqrt q * Real.sqrt M.gamma := by
      linarith only [hR40]
    have := mul_nonneg h1 h1
    have h2 : (0 : ℝ) ≤ 2 * ((1 + A * (1 / 4 : ℝ)⁻¹ * Real.sqrt q * Real.sqrt M.gamma) *
        (1 + A * (1 / 4 : ℝ)⁻¹ * Real.sqrt q * Real.sqrt M.gamma)) := by
      linarith only [this]
    exact mul_nonneg hCtop h2
  have hassembly := ethmB_moment_of_factor_moments M hnm (homSeamBase M hs)
    (seamEnlargedY M m Ctop Y0) hYm hCgap hp hRY hR1 hR2 hR1 hYenl hd1 hd2 hd3
  exact ⟨hR40, hassembly⟩

/-- **STEP 1's DISPLAY AT THE RE-PINNED BASE AND THE ENLARGED `Y`.**

`HomSeamSpineBase.StepOneDisplayAt` at `sb = s/8` and `Y = seamEnlargedY M m
C_top Y₀`, from the five re-pinned factor moments, the Theorem-C edge `Y₀` read
at `4p`, and `display_collapse`.

Every hypothesis is either the anchor's own (inside
`exists_ethmB_seam_factor_moments`) or the Theorem-C edge `hY₀` at the gate
constant `C_gate`; nothing else is assumed. -/
theorem exists_ethmB_seam_moment_bound (d : ℕ) (cstar : ℝ) (hcstar : 0 < cstar)
    {Ctop Cgate : ℝ} (hCtop : 0 ≤ Ctop) (hCgate : 0 < Cgate) :
    ∃ gamma0 C0 : ℝ, 0 < gamma0 ∧ 1 ≤ C0 ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ (hs : 0 < homS M) (m : ℤ) (Y0 : Cutoff.CutoffSample d → ℝ≥0∞),
          AEMeasurable Y0 (Cutoff.cutoffSampleLaw M).toMeasure →
          (∀ p : ℝ, 1 ≤ p → p ≤ Cgate⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
            (∫⁻ w, Y0 w ^ (2 * p) ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
              ENNReal.ofReal 2 ^ (2 * p)) →
          ∀ Cgap : ℝ, 0 ≤ Cgap →
            StepOneDisplayAt M Cgap (seamEnlargedY M m Ctop Y0) m (homSeamBase M hs) C0 := by
  obtain ⟨g0, A, hg0, hA1, hanchor⟩ := exists_ethmB_seam_factor_moments d cstar hcstar
  have hApos : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA1
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hxpos : (0 : ℝ) < 1 + 1024 * (d : ℝ) * A := by positivity
  have hC0one : (1 : ℝ) ≤ homSeamDisplayConst A Ctop Cgate d :=
    one_le_homSeamDisplayConst hApos.le hCtop hCgate.le d
  have hC0pos : (0 : ℝ) < homSeamDisplayConst A Ctop Cgate d :=
    lt_of_lt_of_le zero_lt_one hC0one
  have hkap0 : (0 : ℝ) ≤ homSeamKappa A Ctop d * homSeamCollapseConst A d :=
    mul_nonneg (le_trans zero_le_one (one_le_homSeamKappa hApos.le hCtop d))
      (homSeamCollapseConst_nonneg hApos.le d)
  refine ⟨min g0 (min ((1 + 1024 * (d : ℝ) * A)⁻¹) (1 / 16) ^ (4 : ℕ)),
    homSeamDisplayConst A Ctop Cgate d, lt_min hg0 (by positivity), hC0one, ?_⟩
  intro M hcs hgamma hs m Y0 hY0m hY0 Cgap hCgap p hp hprange
  /- ### the two gate branch -/
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hg_g0 : M.gamma ≤ g0 := le_trans hgamma (min_le_left _ _)
  have hbmin : (0 : ℝ) < min ((1 + 1024 * (d : ℝ) * A)⁻¹) (1 / 16) :=
    lt_min (inv_pos.mpr hxpos) (by norm_num)
  have hg_b : M.gamma ≤ min ((1 + 1024 * (d : ℝ) * A)⁻¹) (1 / 16) ^ (4 : ℕ) :=
    le_trans hgamma (min_le_right _ _)
  have ht : Real.sqrt (Real.sqrt M.gamma) ≤
      min ((1 + 1024 * (d : ℝ) * A)⁻¹) (1 / 16) :=
    quarticRoot_le hgpos.le hbmin.le hg_b
  have htpos : 0 < Real.sqrt (Real.sqrt M.gamma) := quarticRoot_pos hgpos
  have ht4 : Real.sqrt (Real.sqrt M.gamma) ^ (4 : ℕ) = M.gamma :=
    quarticRoot_pow_four hgpos.le
  have ht16 : Real.sqrt (Real.sqrt M.gamma) ≤ 1 / 16 := le_trans ht (min_le_right _ _)
  have htA : Real.sqrt (Real.sqrt M.gamma) ≤ (1 + 1024 * (d : ℝ) * A)⁻¹ :=
    le_trans ht (min_le_left _ _)
  /- ### the elementary `γ`-consequenc -/
  have hgsmall : M.gamma ≤ 1 / 65536 := by
    rw [← ht4]
    calc Real.sqrt (Real.sqrt M.gamma) ^ (4 : ℕ) ≤ (1 / 16 : ℝ) ^ (4 : ℕ) :=
          pow_le_pow_left₀ htpos.le ht16 4
      _ = 1 / 65536 := by norm_num
  have hg1 : M.gamma < 1 := by linarith only [hgsmall]
  have hL4 : 4 ≤ |Real.log M.gamma| := four_le_absLog hgpos (by linarith only [hgsmall])
  have hLpos : (0 : ℝ) < |Real.log M.gamma| := by linarith only [hL4]
  have hLne : |Real.log M.gamma| ≠ 0 := ne_of_gt hLpos
  have hs4 : homS M ≤ 1 / 4 := homS_le_quarter hL4
  have hLu : |Real.log M.gamma| ≤ 4 * (Real.sqrt (Real.sqrt M.gamma))⁻¹ :=
    absLog_le_four_div_quarticRoot hgpos hg1
  have hginv : (0 : ℝ) ≤ M.gamma⁻¹ := (inv_pos.mpr hgpos).le
  have hLinv : (0 : ℝ) ≤ |Real.log M.gamma|⁻¹ := (inv_pos.mpr hLpos).le
  have hSeq : homS M = |Real.log M.gamma|⁻¹ := rfl
  /- ### the boosted anchor expone -/
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  set q : ℝ := max (8 * p) (64 * (d : ℝ) * |Real.log M.gamma|) with hqdef
  have hq8p : 8 * p ≤ q := le_max_left _ _
  have hqlo : 64 * (d : ℝ) * |Real.log M.gamma| ≤ q := le_max_right _ _
  /- ### the anchor's upper `q`-endpoi -/
  have hup1 : 8 * p ≤ A⁻¹ * M.gamma⁻¹ * homS M := by
    rw [hSeq]
    refine range_scale (by norm_num) hApos ?_ hginv hLinv hprange
    rw [homSeamDisplayConst]
    linarith only [hkap0, hCgate]
  have hAL : (0 : ℝ) < A * |Real.log M.gamma| := mul_pos hApos hLpos
  have heqdiv : A⁻¹ * M.gamma⁻¹ * homS M = M.gamma⁻¹ / (A * |Real.log M.gamma|) := by
    rw [homS]; field_simp
  have hup2 : 64 * (d : ℝ) * |Real.log M.gamma| ≤ A⁻¹ * M.gamma⁻¹ * homS M := by
    rw [heqdiv, le_div_iff₀ hAL]
    set u : ℝ := (Real.sqrt (Real.sqrt M.gamma))⁻¹ with hudef
    have hupos : (0 : ℝ) < u := inv_pos.mpr htpos
    have hu1 : 1 + 1024 * (d : ℝ) * A ≤ u := by
      have hmul : (1 + 1024 * (d : ℝ) * A) * Real.sqrt (Real.sqrt M.gamma) ≤ 1 := by
        have h := mul_le_mul_of_nonneg_left htA hxpos.le
        rwa [mul_inv_cancel₀ (ne_of_gt hxpos)] at h
      have hdiv : (1 + 1024 * (d : ℝ) * A) ≤ 1 / Real.sqrt (Real.sqrt M.gamma) :=
        (le_div_iff₀ htpos).mpr hmul
      rwa [one_div] at hdiv
    have hu4 : M.gamma⁻¹ = u ^ (4 : ℕ) := by rw [hudef, inv_pow, ht4]
    have hstep1 : 64 * (d : ℝ) * |Real.log M.gamma| * (A * |Real.log M.gamma|) ≤
        1024 * (d : ℝ) * A * (u * u) := by
      have hLL : |Real.log M.gamma| * |Real.log M.gamma| ≤ (4 * u) * (4 * u) :=
        mul_le_mul hLu hLu hLpos.le (by positivity)
      have hfacnn : (0 : ℝ) ≤ 64 * (d : ℝ) * A := by positivity
      have hmul := mul_le_mul_of_nonneg_left hLL hfacnn
      calc 64 * (d : ℝ) * |Real.log M.gamma| * (A * |Real.log M.gamma|)
          = 64 * (d : ℝ) * A * (|Real.log M.gamma| * |Real.log M.gamma|) := by ring
        _ ≤ 64 * (d : ℝ) * A * ((4 * u) * (4 * u)) := hmul
        _ = 1024 * (d : ℝ) * A * (u * u) := by ring
    have hu1' : (1 : ℝ) ≤ u := by
      have hnn : (0 : ℝ) ≤ 1024 * (d : ℝ) * A := by positivity
      linarith only [hu1, hnn]
    have hsq : 1024 * (d : ℝ) * A ≤ u * u := by
      have h1 : u ≤ u * u := le_mul_of_one_le_left hupos.le hu1'
      linarith only [hu1, h1]
    have hstep2 : 1024 * (d : ℝ) * A * (u * u) ≤ u ^ (4 : ℕ) := by
      have hnn : (0 : ℝ) ≤ u * u := by positivity
      have h := mul_le_mul_of_nonneg_right hsq hnn
      calc 1024 * (d : ℝ) * A * (u * u) ≤ (u * u) * (u * u) := h
        _ = u ^ (4 : ℕ) := by ring
    rw [hu4]
    linarith only [hstep1, hstep2]
  have hupq : q ≤ A⁻¹ * M.gamma⁻¹ * homS M := max_le hup1 hup2
  /- ### the five re-pinned factor momen -/
  have ht40 : (0 : ℝ) < 1 / 4 := by norm_num
  have htlo : homS M / 8 ≤ 1 / 4 := by linarith only [hs4, hs]
  obtain ⟨hf1, hf2, hf3, hf4, hf5⟩ :=
    hanchor M hcs hg_g0 hs m (1 / 4) ht40 htlo le_rfl q hqlo hupq
  obtain ⟨stage_hR40, stage_hassembly⟩ :=
    @homSeamStepOneDisplay_momentBounds1 (d) (Ctop) (Cgate) (hCtop) (hCgate) (A) (hA1) (hApos)
      (hkap0) (M) (hs) (m) (Y0) (hY0m) (hY0) (Cgap) (hCgap) (p) (hp) (hprange) (hgpos) (hL4)
        (hginv) (hLinv) (hp0) (hq8p) (ht40) (hf1) (hf2) (hf3) (hf4) (hf5)
  have hR40 : (0 : ℝ) ≤ A * (1 / 4 : ℝ)⁻¹ * Real.sqrt q * Real.sqrt M.gamma := stage_hR40
  have hassembly := stage_hassembly
  refine le_trans hassembly (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hp0.le)
  /- ### the numeric collap -/
  have hsinv : ((homSeamBase M hs : {s : ℝ // 0 < s}) : ℝ)⁻¹ =
      8 * |Real.log M.gamma| := by
    change (homS M / 8)⁻¹ = 8 * |Real.log M.gamma|
    rw [homS]
    field_simp
  rw [hsinv]
  have hsqp : (1 : ℝ) ≤ Real.sqrt p := by
    have h := Real.sqrt_le_sqrt hp
    rwa [Real.sqrt_one] at h
  have hsqL : (2 : ℝ) ≤ Real.sqrt |Real.log M.gamma| := by
    have h := Real.sqrt_le_sqrt hL4
    rwa [sqrt_four] at h
  obtain ⟨hS3, hWDS, hSG, hgam5⟩ :=
    @homSeamStepOneDisplay_comparisonBounds1 (d) (Ctop) (Cgate) (A) (hC0one) (M) (p) (hp)
      (hprange) (hgpos) (htpos) (ht4) (ht16) (hg1) (hL4) (hLne) (hs4) (hLu) (hLinv) (hSeq) (hp0)
        (hsqp) (hsqL)
  have hWG2D : Real.sqrt q * Real.sqrt M.gamma ≤ 2 * homSeamSqrtLoss d := by
    have hD : (0 : ℝ) ≤ homSeamSqrtLoss d := homSeamSqrtLoss_nonneg d
    have hstep : Real.sqrt q * Real.sqrt M.gamma ≤
        (homSeamSqrtLoss d * (Real.sqrt p + Real.sqrt |Real.log M.gamma|)) *
          Real.sqrt M.gamma := mul_le_mul_of_nonneg_right hWDS (Real.sqrt_nonneg _)
    have hstep2 : homSeamSqrtLoss d *
        ((Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma) ≤
        homSeamSqrtLoss d * 2 := mul_le_mul_of_nonneg_left hSG hD
    calc Real.sqrt q * Real.sqrt M.gamma
        ≤ (homSeamSqrtLoss d * (Real.sqrt p + Real.sqrt |Real.log M.gamma|)) *
            Real.sqrt M.gamma := hstep
      _ = homSeamSqrtLoss d *
            ((Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma) := by ring
      _ ≤ homSeamSqrtLoss d * 2 := hstep2
      _ = 2 * homSeamSqrtLoss d := by ring
  have hR4D : A * (1 / 4 : ℝ)⁻¹ * Real.sqrt q * Real.sqrt M.gamma ≤
      8 * A * homSeamSqrtLoss d := by
    have hinv : ((1 : ℝ) / 4)⁻¹ = 4 := by norm_num
    have hstep : 4 * A * (Real.sqrt q * Real.sqrt M.gamma) ≤
        4 * A * (2 * homSeamSqrtLoss d) := by
      refine mul_le_mul_of_nonneg_left hWG2D ?_
      linarith only [hApos]
    calc A * (1 / 4 : ℝ)⁻¹ * Real.sqrt q * Real.sqrt M.gamma
        = 4 * A * (Real.sqrt q * Real.sqrt M.gamma) := by rw [hinv]; ring
      _ ≤ 4 * A * (2 * homSeamSqrtLoss d) := hstep
      _ = 8 * A * homSeamSqrtLoss d := by ring
  have habs : |Real.log M.gamma| ^ (2 : ℕ) = Real.log M.gamma ^ (2 : ℕ) := sq_abs _
  rw [← habs]
  have hbudget1 : 2 * A * homSeamSqrtLoss d * (1 + 2 * A * homSeamSqrtLoss d) ≤
      homSeamCollapseConst A d := by
    have h : (0 : ℝ) ≤ 4 * A ^ (2 : ℕ) * homSeamSqrtLoss d ^ (2 : ℕ) := by
      have hD : (0 : ℝ) ≤ homSeamSqrtLoss d := homSeamSqrtLoss_nonneg d
      positivity
    rw [homSeamCollapseConst]; linarith only [h]
  have hbudget2 : 1 + 4 * A ^ (2 : ℕ) * homSeamSqrtLoss d ^ (2 : ℕ) ≤
      homSeamCollapseConst A d := by
    have hD : (0 : ℝ) ≤ homSeamSqrtLoss d := homSeamSqrtLoss_nonneg d
    have h : (0 : ℝ) ≤ 2 * A * homSeamSqrtLoss d * (1 + 2 * A * homSeamSqrtLoss d) := by
      positivity
    rw [homSeamCollapseConst]; linarith only [h]
  have hC0fin : (8 * Ctop * (1 + 8 * A * homSeamSqrtLoss d) ^ (2 : ℕ) + 1) *
      homSeamCollapseConst A d ≤ homSeamDisplayConst A Ctop Cgate d := by
    have h8A : (0 : ℝ) ≤ 8 * A := by linarith only [hApos]
    rw [homSeamDisplayConst, homSeamKappa]
    linarith only [h8A, hCgate]
  exact seam_display_collapse hApos.le (homSeamSqrtLoss_nonneg d) hL4 hS3
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hgpos.le hCgap hCtop hR40 hR40 hR4D hR4D
    hWDS hSG hgam5 hbudget1 hbudget2 hC0fin

end

end Algsuperdiff.Section4.Provider.Homogenization
