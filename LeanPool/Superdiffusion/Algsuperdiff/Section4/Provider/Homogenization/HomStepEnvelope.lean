/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.FluxCorrectedTwoScale
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.MomentHolder

/-!
# HomStepEnvelope

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5: the defect random variable `EthmB(m)` and the
# parameter web of the §4.5 parameter choices

## The target

`t.homogenization`, the definition of `E_thmB`:

```
EthmB(m):= s^{-1} 3^{(1-α) X_m(α)}
              sup_{L ≥ m} 𝓔_{s₁,∞,2}(□_m, n; ã_{L,m}, σ_m)
              ( 1 + sup_{L ≥ m} 𝓔_{1/4,∞,2}(□_m; ã_{L,m}, σ_m) )
            + C γ⁵ ( 1 + sup_{L ≥ m} 𝓔²_{s₁/2,∞,2}(□_m, n; ã_{L,m}, σ_m) )
```

together with node the parameter selection:

```
s:= |log γ|⁻¹,  s₁:= s/2,  s₂:= 1/2,  α:= 1 - s/2,  k:= ⌈10|log γ|⌉,
n:= m - k.
```

## Carrier

The three `sup_{L ≥ m} 𝓔` factors are the OWN carrier: the two-argument
observable
`Algsuperdiff.Section4.Support.fluxCorrectedTwoScaleErrorObservableSup` of
`Support/FluxCorrectedTwoScale.lean`, which is the carrier of the anchor
`Algsuperdiff.Frozen.Section4.bounds_mathcal_E_aL`.  It already carries the
`L`-supremum and the flux correction `ã_{L,m} = a_L - (k_L - k_m)_{□_m}`, takes
values in `[0,∞]`, so that no convergence side condition enters the statement,
and reduces at a matched index pair `n = m` to the one-argument observable by
`rfl`.  The one-argument
`𝓔_{1/4,∞,2}(□_m; ·)` of the middle factor is therefore rendered as the
two-argument observable at `n = m`, exactly as the source's own convention
prescribes.

Consequently `ethmB` takes values in `ℝ≥0∞`.  The real-valued witness
`EB: Ω → ℝ` demanded by the frozen block of `generator_renormalization` is
obtained downstream, after the Step-1 moment bound has certified `ethmB < ∞`
a.e.; it is NOT formed here.

## Exponent binders

`ethmB` is parametrized by the base exponent `s: {s: ℝ // 0 < s}`; the
subordinate exponents `s₁ = s/2` and `s₁/2 = s/4` are formed inside the
definition from `s.2`, so no extra positivity binder is carried.  The §4.5
value `s = |log γ|⁻¹` is supplied by `homS` below and is NOT baked into the
definition: `homS M` is positive only under a `γ ≠ 1` gate, and the
convention is that gates live in theorems, not in definitions.
-/

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The exponent slots -/

/-- The fixed exponent `1/4` of the middle factor of `EthmB(m)`. -/
def homQuarter : {s : ℝ // 0 < s} := ⟨1 / 4, by norm_num⟩

@[simp] theorem homQuarter_val : (homQuarter : ℝ) = 1 / 4 := rfl

/-- `s₁:= s/2` (the §4.5 parameter choices). -/
def homHalf (s : {s : ℝ // 0 < s}) : {s : ℝ // 0 < s} := ⟨(s : ℝ) / 2, half_pos s.2⟩

@[simp] theorem homHalf_val (s : {s : ℝ // 0 < s}) : (homHalf s : ℝ) = (s : ℝ) / 2 := rfl

/-- `s₁/2 = s/4`, the exponent of the second summand of `EthmB(m)`. -/
def homQuarterOf (s : {s : ℝ // 0 < s}) : {s : ℝ // 0 < s} :=
  ⟨(s : ℝ) / 4, by have := s.2; linarith only [this]⟩

@[simp] theorem homQuarterOf_val (s : {s : ℝ // 0 < s}) :
    (homQuarterOf s : ℝ) = (s : ℝ) / 4 := rfl

/-! ## 2. The parameter web the §4.5 parameter choices + the mesoscale energy definition -/

/-- `s:= |log γ|⁻¹`. -/
def homS (M : ABKModel d) : ℝ := |Real.log M.gamma|⁻¹

/-- `α:= 1 - s/2`. -/
def homAlpha (M : ABKModel d) : ℝ := 1 - homS M / 2

/-- `k:= ⌈10 |log γ|⌉`. -/
def homK (M : ABKModel d) : ℕ := ⌈10 * |Real.log M.gamma|⌉₊

/-- `n:= m - k` (the mesoscale energy definition). -/
def homN (M : ABKModel d) (m : ℤ) : ℤ := m - (homK M : ℤ)

theorem homS_pos {M : ABKModel d} (hlog : 0 < |Real.log M.gamma|) : 0 < homS M :=
  inv_pos.mpr hlog

/-- The gate: `s ≤ 1/4` is exactly `|log γ| ≥ 4`. -/
theorem homS_le_quarter {M : ABKModel d} (hlog : 4 ≤ |Real.log M.gamma|) :
    homS M ≤ 1 / 4 := by
  have h0 : (0 : ℝ) < |Real.log M.gamma| := by linarith only [hlog]
  rw [homS, inv_le_comm₀ h0 (by norm_num)]
  linarith only [hlog]

/-- `1 - α = s/2`: the exponent that Step 1's Markov step consumes. -/
theorem one_sub_homAlpha (M : ABKModel d) : 1 - homAlpha M = homS M / 2 := by
  rw [homAlpha]; ring

theorem homAlpha_pos {M : ABKModel d} (hlog : 4 ≤ |Real.log M.gamma|) :
    0 < homAlpha M := by
  have h := homS_le_quarter (M := M) hlog
  rw [homAlpha]; linarith only [h]

/-- Ceiling honesty, lower half: `10|log γ| ≤ k`. -/
theorem homK_ge (M : ABKModel d) : 10 * |Real.log M.gamma| ≤ (homK M : ℝ) :=
  Nat.le_ceil _

/-- Ceiling honesty, upper half: `k ≤ 10|log γ| + 1` (:
the printed `3^{(1-α)(m-n)} ≤ 3^5` middle inequality is FALSE; the honest
envelope keeps the `+1` visible). -/
theorem homK_le (M : ABKModel d) : (homK M : ℝ) ≤ 10 * |Real.log M.gamma| + 1 := by
  have h : (0 : ℝ) ≤ 10 * |Real.log M.gamma| := by positivity
  exact le_of_lt (Nat.ceil_lt_add_one h)

theorem homN_le (M : ABKModel d) (m : ℤ) : homN M m ≤ m := by
  have : (0 : ℤ) ≤ (homK M : ℤ) := Int.natCast_nonneg _
  rw [homN]; omega

/-- The mesoscale gap in the real gauge the anchor's binders use. -/
theorem homN_gap (M : ABKModel d) (m : ℤ) :
    ((m : ℝ) - ((homN M m : ℤ) : ℝ)) = (homK M : ℝ) := by
  rw [homN]; push_cast; ring

/-! ## 3. The defect random variable `EthmB(m)` -/

/-- **`EthmB(m)`.**

The three `𝓔` factors are the anchor's own carrier; the middle one is the
one-argument functional, i.e. the two-argument observable at `n = m`. `Y` is
the minimal-scale factor `3^{(1-α) X_m(α)}` of Theorem C (an abstract
`[0,∞]`-valued observable here: its construction and its Step-1 exponential
moment are the business of the Step-1 module), and `Cgap` is the Step-3
gap-absorption constant `C = C(d, c⋆)` of the second summand. -/
def ethmB (M : ABKModel d) (Cgap : ℝ) (Y : Cutoff.CutoffSample d → ℝ≥0∞)
    (m n : ℤ) (s : {s : ℝ // 0 < s}) : Cutoff.CutoffSample d → ℝ≥0∞ :=
  fun omega =>
    ENNReal.ofReal ((s : ℝ)⁻¹) *
        (Y omega *
          (fluxCorrectedTwoScaleErrorObservableSup M m n (homHalf s) omega *
            (1 + fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega)))
      + ENNReal.ofReal (Cgap * M.gamma ^ (5 : ℕ)) *
          (1 +
            fluxCorrectedTwoScaleErrorObservableSup M m n (homQuarterOf s) omega ^ (2 : ℝ))

theorem measurable_ethmB (M : ABKModel d) (Cgap : ℝ) {Y : Cutoff.CutoffSample d → ℝ≥0∞}
    (hY : Measurable Y) {m n : ℤ} (hnm : n ≤ m) (s : {s : ℝ // 0 < s}) :
    Measurable (ethmB M Cgap Y m n s) := by
  have h1 := measurable_fluxCorrectedTwoScaleErrorObservableSup M hnm (homHalf s)
  have h2 := measurable_fluxCorrectedTwoScaleErrorObservableSup M (le_refl m) homQuarter
  have h3 := measurable_fluxCorrectedTwoScaleErrorObservableSup M hnm (homQuarterOf s)
  exact ((measurable_const.mul (hY.mul (h1.mul (measurable_const.add h2)))).add
    (measurable_const.mul (measurable_const.add (h3.pow_const _))))

/-! ## 4.: the moment bound must survive the Step-3 rescaling -/

/-- **The rescaling stability of the moment normal form.**

If `F` obeys `∫⁻ F^p ≤ (ofReal R)^p` and `lam ≥ 0`, then the rescaled
observable `ofReal lam * F` obeys the SAME normal form with the majorant
enlarged by exactly `lam`.  This is the honest disposition of: the source's
Step-3 sentence "absorbing the constant `C` into `EthmB(m)`" rescales a witness
whose moment bound was already proved, so the moment bound's constant must
absorb the same factor. -/
theorem lintegral_rpow_const_mul_le {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {F : Omega → ℝ≥0∞} {R lam p : ℝ} (hp : 0 ≤ p) (hlam : 0 ≤ lam)
    (h : (∫⁻ omega, F omega ^ p ∂mu) ≤ ENNReal.ofReal R ^ p) :
    (∫⁻ omega, (ENNReal.ofReal lam * F omega) ^ p ∂mu) ≤ ENNReal.ofReal (lam * R) ^ p := by
  have hpt : ∀ omega : Omega, (ENNReal.ofReal lam * F omega) ^ p =
      ENNReal.ofReal lam ^ p * F omega ^ p := fun omega =>
    ENNReal.mul_rpow_of_nonneg _ _ hp
  calc (∫⁻ omega, (ENNReal.ofReal lam * F omega) ^ p ∂mu)
      = ∫⁻ omega, ENNReal.ofReal lam ^ p * F omega ^ p ∂mu := lintegral_congr hpt
    _ = ENNReal.ofReal lam ^ p * ∫⁻ omega, F omega ^ p ∂mu :=
        lintegral_const_mul' _ _ (by
          exact ENNReal.rpow_ne_top_of_nonneg hp ENNReal.ofReal_ne_top)
    _ ≤ ENNReal.ofReal lam ^ p * ENNReal.ofReal R ^ p := mul_le_mul' (le_refl _) h
    _ = ENNReal.ofReal (lam * R) ^ p := by
        rw [ENNReal.ofReal_mul hlam, ENNReal.mul_rpow_of_nonneg _ _ hp]

/-- The `EthmB` instance of the previous lemma: the Step-1 moment bound of
`EthmB(m)` transports to the Step-3 rescaled witness `C · EthmB(m)` with the
moment constant multiplied by the same `C`. -/
theorem ethmB_const_smul_moment (M : ABKModel d) (Cgap : ℝ)
    {Y : Cutoff.CutoffSample d → ℝ≥0∞} {m n : ℤ} {s : {s : ℝ // 0 < s}} {R lam p : ℝ}
    (hp : 0 ≤ p) (hlam : 0 ≤ lam)
    (h : (∫⁻ omega, ethmB M Cgap Y m n s omega ^ p
            ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal R ^ p) :
    (∫⁻ omega, (ENNReal.ofReal lam * ethmB M Cgap Y m n s omega) ^ p
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal (lam * R) ^ p :=
  lintegral_rpow_const_mul_le hp hlam h

end

end Algsuperdiff.Section4.Provider.Homogenization
