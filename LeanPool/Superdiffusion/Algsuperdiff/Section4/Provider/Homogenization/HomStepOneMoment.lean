/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepOneAnchor

/-!
# HomStepOneMoment

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5, Step 1: the Hölder assembly of the `EthmB(m)` moment

## The target

Step 1 ends with the sentence

> "Combining this estimate with the `bounds_mathcal_E_aL` lemma, using Hölder's
> inequality and `s = |log γ|⁻¹`, we obtain the moment bound announced in
> the `𝓔` estimate."

It is recorded that the Hölder bookkeeping is asserted, not displayed. This
module reconstructs it in full.  `EthmB(m)` is the sum of two products

```
T₁ = s⁻¹ · Y · ( 𝓔_{s₁} · (1 + 𝓔_{1/4}) ),     T₂ = C γ⁵ · ( 1 + 𝓔²_{s₁/2} ),
```

so the exponent boosts are `2` on the outer product, `4` on the inner one and
`2` on the square — NOT the uniform `3` a naive three-factor Hölder would ask
for.  The assembly is therefore:

| object | exponent at which it is consumed |
|---|---|
| `Y = 3^{(1-α)X_m(α)}` | `2p` |
| `𝓔_{s₁,∞,2}(□_m, n; ·)` | `4p` |
| `𝓔_{1/4,∞,2}(□_m; ·)` | `4p` |
| `𝓔_{s₁/2,∞,2}(□_m, n; ·)` | `2p` |

## The conditional edge (the ONE in this lane)

`Y` and its moment are the only inputs this module does not produce.  `Y` is
the minimal-scale factor `3^{(1-α) X_m(α)}` and its moment bound

```
𝔼[ (3^{(1-α)X_m(α)})^{2p} ] ≤ 2^{2p}
```

is the Markov/`Γ₁` step of Step 1, whose input is clause (a) of Theorem C
(`X_m(α) = 𝒪_{Γ₁}(C γ (1-α)^{-2})`).  Per the conditional-edge device it enters
here as a NAMED TRANSCRIBED HYPOTHESIS (`hY`), at the single exponent `2p` at
which it is consumed — never by importing Theorem C itself.  Theorem C is a
declared dependency of this step, so this is a node-internal edge, not a side
assumption.  NOTE for the consumer: the printed range of the Markov step is `p
≤ C⁻¹(1-α)γ⁻¹` with `1 - α = s/2`; the caller must respect it when discharging
`hY`.

## The output shape

The assembled majorant is left FACTORED,

```
s⁻¹ · ( R_Y · ( R₁ · (1 + R₂) ) )  +  C γ⁵ · ( 1 + R₃² ),
```

with `R_Y, R₁, R₂, R₃` the caller's own factor majorants (`R_Y = 2` at the
plain Theorem-C edge; the enlarged-`Y` re-pin passes the
`𝓔`-boosted majorant instead — the interface generalization).  This is the honest
output of Hölder: not one power of `γ`, of `s`, or of `|log γ|` has been moved
or absorbed ( forbids silent absorption of `s`-powers, since
`s = s(γ)` is not a constant).  The numeric collapse to the printed display
`C(√p + √|log γ|)√γ |log γ|²` is a separate, separately auditable step.
-/

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

/-! ## 1. Two generic `ℝ≥0∞` moment tools -/

section Tools

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- **Exponent monotonicity (Lyapunov) in the normal form.**

On a probability space the normal form at a LARGER exponent implies it at a
smaller one, with the SAME majorant.  This is what lets the Step-1 assembly
consume the anchor at the boosted exponent `q = max(4p, 2d s'⁻¹)` and still
read the result at `4p`:'s threshold `q ≥ 2 d s'⁻¹` is respected without
weakening the conclusion. -/
theorem lintegral_rpow_le_of_exponent_le [IsProbabilityMeasure mu] {F : Omega → ℝ≥0∞}
    {R a b : ℝ} (hFm : AEMeasurable F mu) (ha : 0 < a) (hab : a ≤ b)
    (h : (∫⁻ omega, F omega ^ b ∂mu) ≤ ENNReal.ofReal R ^ b) :
    (∫⁻ omega, F omega ^ a ∂mu) ≤ ENNReal.ofReal R ^ a := by
  rcases eq_or_lt_of_le hab with heq | hlt
  · rw [← heq] at h; exact h
  have hb : (0 : ℝ) < b := lt_trans ha hlt
  have hr0 : (0 : ℝ) < a / b := div_pos ha hb
  have hr1 : a / b ≤ 1 := (div_le_one hb).mpr hab
  have hba : b * (a / b) = a := by field_simp
  have hpt : ∀ omega : Omega, F omega ^ a =
      (F omega ^ b) ^ (a / b) * ((1 : ℝ≥0∞)) ^ (1 - a / b) := by
    intro omega
    rw [ENNReal.one_rpow, mul_one, ← ENNReal.rpow_mul, hba]
  have hone : (∫⁻ _omega : Omega, (1 : ℝ≥0∞) ∂mu) = 1 := by
    rw [lintegral_one, measure_univ]
  have hh := ENNReal.lintegral_mul_norm_pow_le (μ := mu)
    (f := fun omega => F omega ^ b) (g := fun _ => (1 : ℝ≥0∞))
    (hFm.pow_const b) aemeasurable_const (p := a / b) (q := 1 - a / b)
    hr0.le (by linarith only [hr1]) (by ring)
  have hstep : (∫⁻ omega, F omega ^ a ∂mu) ≤
      (∫⁻ omega, F omega ^ b ∂mu) ^ (a / b) * (1 : ℝ≥0∞) ^ (1 - a / b) := by
    calc (∫⁻ omega, F omega ^ a ∂mu)
        = ∫⁻ omega, (F omega ^ b) ^ (a / b) * ((1 : ℝ≥0∞)) ^ (1 - a / b) ∂mu :=
          lintegral_congr hpt
      _ ≤ (∫⁻ omega, F omega ^ b ∂mu) ^ (a / b) *
            (∫⁻ _omega : Omega, (1 : ℝ≥0∞) ∂mu) ^ (1 - a / b) := hh
      _ = (∫⁻ omega, F omega ^ b ∂mu) ^ (a / b) * (1 : ℝ≥0∞) ^ (1 - a / b) := by rw [hone]
  refine le_trans hstep ?_
  rw [ENNReal.one_rpow, mul_one]
  refine le_trans (ENNReal.rpow_le_rpow h hr0.le) (le_of_eq ?_)
  rw [← ENNReal.rpow_mul, hba]

/-- **The two-term Minkowski step**, in the normal form. -/
theorem lintegral_rpow_add_le_of_moments {F G : Omega → ℝ≥0∞} {RF RG q : ℝ}
    (hq : 1 ≤ q) (hF : AEMeasurable F mu) (hG : AEMeasurable G mu)
    (hRF : 0 ≤ RF) (hRG : 0 ≤ RG)
    (h1 : (∫⁻ omega, F omega ^ q ∂mu) ≤ ENNReal.ofReal RF ^ q)
    (h2 : (∫⁻ omega, G omega ^ q ∂mu) ≤ ENNReal.ofReal RG ^ q) :
    (∫⁻ omega, (F omega + G omega) ^ q ∂mu) ≤ ENNReal.ofReal (RF + RG) ^ q := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have hmink := ENNReal.lintegral_Lp_add_le (μ := mu) (f := F) (g := G) hF hG hq
  have hA : (∫⁻ omega, F omega ^ q ∂mu) ^ (1 / q) ≤ ENNReal.ofReal RF := by
    refine le_trans (ENNReal.rpow_le_rpow h1 (by positivity)) (le_of_eq ?_)
    rw [← ENNReal.rpow_mul, mul_one_div_cancel (ne_of_gt hq0), ENNReal.rpow_one]
  have hB : (∫⁻ omega, G omega ^ q ∂mu) ^ (1 / q) ≤ ENNReal.ofReal RG := by
    refine le_trans (ENNReal.rpow_le_rpow h2 (by positivity)) (le_of_eq ?_)
    rw [← ENNReal.rpow_mul, mul_one_div_cancel (ne_of_gt hq0), ENNReal.rpow_one]
  have hsum : (∫⁻ omega, (F omega + G omega) ^ q ∂mu) ^ (1 / q) ≤
      ENNReal.ofReal (RF + RG) := by
    refine le_trans hmink ?_
    rw [ENNReal.ofReal_add hRF hRG]
    exact add_le_add hA hB
  have hraise := ENNReal.rpow_le_rpow hsum hq0.le
  rwa [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (ne_of_gt hq0), ENNReal.rpow_one] at hraise

/-- The constant observable `1` sits in the normal form with majorant `1`. -/
theorem lintegral_rpow_one_le [IsProbabilityMeasure mu] {q : ℝ} :
    (∫⁻ _omega : Omega, (1 : ℝ≥0∞) ^ q ∂mu) ≤ ENNReal.ofReal 1 ^ q := by
  have h : (∫⁻ _omega : Omega, (1 : ℝ≥0∞) ^ q ∂mu) = 1 := by
    simp only [ENNReal.one_rpow]
    rw [lintegral_one, measure_univ]
  rw [h, ENNReal.ofReal_one, ENNReal.one_rpow]

end Tools

/-! ## 2. The assembly -/

variable {d : ℕ}

/-- **STEP 1's HÖLDER ASSEMBLY.**

Given the four factor moments — the minimal-scale factor `Y` at exponent
`2p` with majorant `R_Y` and the three `𝓔`-factors at `4p`, `4p`, `2p` — the
defect `EthmB(m)` obeys this development normal form at `p` with the factored
majorant

```
s⁻¹ · ( R_Y · ( R₁ · (1 + R₂) ) )  +  C γ⁵ · ( 1 + R₃² ).
```

Nothing is absorbed: this is the source's "using Hölder's inequality" written out. -/
theorem ethmB_moment_of_factor_moments (M : ABKModel d) {m n : ℤ} (hnm : n ≤ m)
    (s : {s : ℝ // 0 < s}) (Y : Cutoff.CutoffSample d → ℝ≥0∞)
    (hYm : AEMeasurable Y (Cutoff.cutoffSampleLaw M).toMeasure)
    {Cgap : ℝ} (hCgap : 0 ≤ Cgap) {p : ℝ} (hp : 1 ≤ p)
    {RY R1 R2 R3 : ℝ} (hRY : 0 ≤ RY) (hR1 : 0 ≤ R1) (hR2 : 0 ≤ R2) (hR3 : 0 ≤ R3)
    (hY : (∫⁻ omega, Y omega ^ (2 * p) ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal RY ^ (2 * p))
    (h1 : (∫⁻ omega,
        fluxCorrectedTwoScaleErrorObservableSup M m n (homHalf s) omega ^ (4 * p)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal R1 ^ (4 * p))
    (h2 : (∫⁻ omega,
        fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega ^ (4 * p)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal R2 ^ (4 * p))
    (h3 : (∫⁻ omega,
        fluxCorrectedTwoScaleErrorObservableSup M m n (homQuarterOf s) omega ^ (2 * p)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal R3 ^ (2 * p)) :
    (∫⁻ omega, ethmB M Cgap Y m n s omega ^ p
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal ((s : ℝ)⁻¹ * (RY * (R1 * (1 + R2))) +
        Cgap * M.gamma ^ (5 : ℕ) * (1 + R3 ^ (2 : ℕ))) ^ p := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have h2p : (1 : ℝ) ≤ 2 * p := by linarith only [hp]
  have h4p : (1 : ℝ) ≤ 4 * p := by linarith only [hp]
  have h2p0 : (0 : ℝ) < 2 * p := by linarith only [hp0]
  /- measurability of the three facto -/
  have hm1 : AEMeasurable
      (fluxCorrectedTwoScaleErrorObservableSup M m n (homHalf s))
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    (measurable_fluxCorrectedTwoScaleErrorObservableSup M hnm (homHalf s)).aemeasurable
  have hm2 : AEMeasurable
      (fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter)
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    (measurable_fluxCorrectedTwoScaleErrorObservableSup M (le_refl m) homQuarter).aemeasurable
  have hm3 : AEMeasurable
      (fluxCorrectedTwoScaleErrorObservableSup M m n (homQuarterOf s))
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    (measurable_fluxCorrectedTwoScaleErrorObservableSup M hnm (homQuarterOf s)).aemeasurable
  /- `(1 + 𝓔_{1/4})` at exponent `4p` -/
  have hmid : (∫⁻ omega,
      ((1 : ℝ≥0∞) + fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega) ^ (4 * p)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal (1 + R2) ^ (4 * p) :=
    lintegral_rpow_add_le_of_moments h4p aemeasurable_const hm2 zero_le_one hR2
      lintegral_rpow_one_le h2
  /- the inner product `𝓔_{s₁} · (1 + 𝓔_{1/4})` at exponent `2p` -/
  have hmidm : AEMeasurable
      (fun omega => (1 : ℝ≥0∞) +
        fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega)
      (Cutoff.cutoffSampleLaw M).toMeasure := aemeasurable_const.add hm2
  have hinner : (∫⁻ omega,
      (fluxCorrectedTwoScaleErrorObservableSup M m n (homHalf s) omega *
        ((1 : ℝ≥0∞) + fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega)) ^
          (2 * p) ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (R1 * (1 + R2)) ^ (2 * p) := by
    refine Algsuperdiff.Section4.Provider.BoundsEaL.lintegral_rpow_mul_le_of_moments
      h2p0 hm1 hmidm hR1 ?_ ?_
    · have he : (2 : ℝ) * (2 * p) = 4 * p := by ring
      rw [he]; exact h1
    · have he : (2 : ℝ) * (2 * p) = 4 * p := by ring
      rw [he]; exact hmid
  /- the outer product `Y · (𝓔_{s₁} · (1 + 𝓔_{1/4}))` at exponent `p` -/
  have hinnerm : AEMeasurable
      (fun omega => fluxCorrectedTwoScaleErrorObservableSup M m n (homHalf s) omega *
        ((1 : ℝ≥0∞) + fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega))
      (Cutoff.cutoffSampleLaw M).toMeasure := hm1.mul hmidm
  have houter : (∫⁻ omega,
      (Y omega *
        (fluxCorrectedTwoScaleErrorObservableSup M m n (homHalf s) omega *
          ((1 : ℝ≥0∞) +
            fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega))) ^ p
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (RY * (R1 * (1 + R2))) ^ p := by
    refine Algsuperdiff.Section4.Provider.BoundsEaL.lintegral_rpow_mul_le_of_moments
      hp0 hYm hinnerm hRY hY hinner
  /- the first summand `T₁` -/
  have hT1 : (∫⁻ omega,
      (ENNReal.ofReal ((s : ℝ)⁻¹) *
        (Y omega *
          (fluxCorrectedTwoScaleErrorObservableSup M m n (homHalf s) omega *
            ((1 : ℝ≥0∞) +
              fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega)))) ^ p
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal ((s : ℝ)⁻¹ * (RY * (R1 * (1 + R2)))) ^ p :=
    lintegral_rpow_const_mul_le hp0.le (le_of_lt (inv_pos.mpr s.2)) houter
  /- the square `𝓔²_{s₁/2}` at exponent `p` -/
  have hsq : (∫⁻ omega,
      (fluxCorrectedTwoScaleErrorObservableSup M m n (homQuarterOf s) omega ^ (2 : ℝ)) ^ p
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (R3 ^ (2 : ℕ)) ^ p := by
    have hpt : ∀ omega : Cutoff.CutoffSample d,
        (fluxCorrectedTwoScaleErrorObservableSup M m n (homQuarterOf s) omega ^ (2 : ℝ)) ^ p =
          fluxCorrectedTwoScaleErrorObservableSup M m n (homQuarterOf s) omega ^ (2 * p) := by
      intro omega
      rw [← ENNReal.rpow_mul]
    have hR : ENNReal.ofReal (R3 ^ (2 : ℕ)) ^ p = ENNReal.ofReal R3 ^ (2 * p) := by
      rw [ENNReal.ofReal_pow hR3, ← ENNReal.rpow_natCast (ENNReal.ofReal R3) 2,
        ← ENNReal.rpow_mul]
      norm_num
    rw [hR]
    calc (∫⁻ omega,
        (fluxCorrectedTwoScaleErrorObservableSup M m n (homQuarterOf s) omega ^ (2 : ℝ)) ^ p
          ∂(Cutoff.cutoffSampleLaw M).toMeasure)
        = ∫⁻ omega,
            fluxCorrectedTwoScaleErrorObservableSup M m n (homQuarterOf s) omega ^ (2 * p)
              ∂(Cutoff.cutoffSampleLaw M).toMeasure := lintegral_congr hpt
      _ ≤ ENNReal.ofReal R3 ^ (2 * p) := h3
  /- the second summand `T₂` -/
  have hsqm : AEMeasurable
      (fun omega =>
        fluxCorrectedTwoScaleErrorObservableSup M m n (homQuarterOf s) omega ^ (2 : ℝ))
      (Cutoff.cutoffSampleLaw M).toMeasure := hm3.pow_const _
  have hT2inner : (∫⁻ omega,
      ((1 : ℝ≥0∞) +
        fluxCorrectedTwoScaleErrorObservableSup M m n (homQuarterOf s) omega ^ (2 : ℝ)) ^ p
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (1 + R3 ^ (2 : ℕ)) ^ p :=
    lintegral_rpow_add_le_of_moments hp aemeasurable_const hsqm zero_le_one
      (by positivity) lintegral_rpow_one_le hsq
  have hT2 : (∫⁻ omega,
      (ENNReal.ofReal (Cgap * M.gamma ^ (5 : ℕ)) *
        ((1 : ℝ≥0∞) +
          fluxCorrectedTwoScaleErrorObservableSup M m n (homQuarterOf s) omega ^ (2 : ℝ))) ^ p
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (Cgap * M.gamma ^ (5 : ℕ) * (1 + R3 ^ (2 : ℕ))) ^ p := by
    refine lintegral_rpow_const_mul_le hp0.le ?_ hT2inner
    have hg : (0 : ℝ) ≤ M.gamma := M.shellPrefix.gamma_pos.le
    positivity
  /- the s -/
  have hT1m : AEMeasurable
      (fun omega => ENNReal.ofReal ((s : ℝ)⁻¹) *
        (Y omega *
          (fluxCorrectedTwoScaleErrorObservableSup M m n (homHalf s) omega *
            ((1 : ℝ≥0∞) +
              fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega))))
      (Cutoff.cutoffSampleLaw M).toMeasure := aemeasurable_const.mul (hYm.mul hinnerm)
  have hT2m : AEMeasurable
      (fun omega => ENNReal.ofReal (Cgap * M.gamma ^ (5 : ℕ)) *
        ((1 : ℝ≥0∞) +
          fluxCorrectedTwoScaleErrorObservableSup M m n (homQuarterOf s) omega ^ (2 : ℝ)))
      (Cutoff.cutoffSampleLaw M).toMeasure := aemeasurable_const.mul (aemeasurable_const.add hsqm)
  have hgnn : (0 : ℝ) ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hsnn : (0 : ℝ) ≤ (s : ℝ)⁻¹ := le_of_lt (inv_pos.mpr s.2)
  have hAnn : (0 : ℝ) ≤ (s : ℝ)⁻¹ * (RY * (R1 * (1 + R2))) :=
    mul_nonneg hsnn (by positivity)
  have hBnn : (0 : ℝ) ≤ Cgap * M.gamma ^ (5 : ℕ) * (1 + R3 ^ (2 : ℕ)) := by positivity
  exact lintegral_rpow_add_le_of_moments hp hT1m hT2m hAnn hBnn hT1 hT2

end

end Algsuperdiff.Section4.Provider.Homogenization
