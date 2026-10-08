/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryEstimates
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastLinearDecay

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastDelayExponentUniform

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The delay exponents, chosen before the law

the corresponding argument check.  The frozen `hcore` binder
(the cited theorem) reads

```
∃ cSc, 0 < cSc ∧ ∀ g ∈ Ico 0 1, ∃ alpha Cdelay, … ∀ cStar gBase Pbase Ebase Ψbase Kbase Sbase, …
```

so `Cdelay` — not only `alpha` — is chosen **before the law**.  The endpoint
takes `Cdelay := fusedDelay Centry Cpref A g` (the corresponding argument), and its two producers
are

```
entry_exponent_le_rpow : 3 ^ (2 * N₀) ≤ base ^ ((2 * N₀ : ℕ) : ℝ)     -- Centry := 2 N₀
exists_rpow_ge         : ∃ C, 0 ≤ C ∧ x ≤ base ^ C                    -- Cpref  := logb base x
```

**Neither is admissible at that quantifier order**, and this file says exactly
why and supplies the replacements:

* the real-power entry exponent returns `2 N₀`, and `N₀` is the burn-in
  — a law-dependent natural number.  The printed route is
  that `Π` rides in the *base* `2 + aspectRatio Ebase * Kbase` with a *law-free
  exponent*, i.e. one needs `3 ^ N₀ ≤ base ^ cburn` at a law-free `cburn`
  first; `entry_exponent_of_burnIn` then squares it.
* the base-dependent real-power bound returns `logb base x`, which **depends on
  the base**, hence
  on the law.  `exists_rpow_ge_uniform` gives one exponent good for *every*
  base `≥ 3` at once, by measuring the logarithm at the fixed base `3` and
  using `3 ≤ base` monotonically.

The capstone states the settlement in
the binder's own quantifier order: `∃ Centry Cpref, ∀ base, ∀ N₀, …`.  With it,
`Cdelay` is law-free as soon as `A` is — so the `Cdelay` side needs no carrier
wave, only the burn-in's own polynomial bound (the corresponding argument, and
`three_mul_max_one_le_rpow`
below is the step every such bound ends with).
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix

noncomputable section

/-! ## 1. The base-uniform exponent -/

/-- **One exponent for every base at once.**  The replacement for the
base-dependent bound, whose exponent `logb base x` depends on the base and so
may not be chosen before the law. -/
theorem exists_rpow_ge_uniform (x : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ base : ℝ, (3 : ℝ) ≤ base → x ≤ Real.rpow base C := by
  rcases le_or_gt x 1 with hle | hgt
  · refine ⟨0, le_rfl, fun base _ => ?_⟩
    change x ≤ base ^ (0 : ℝ)
    rw [Real.rpow_zero]
    exact hle
  · refine ⟨Real.logb 3 x, Real.logb_nonneg (by norm_num) hgt.le, fun base hbase => ?_⟩
    have hC0 : (0 : ℝ) ≤ Real.logb 3 x :=
      Real.logb_nonneg (by norm_num) hgt.le
    have hval : Real.rpow (3 : ℝ) (Real.logb 3 x) = x :=
      Real.rpow_logb (by norm_num) (by norm_num) (lt_trans one_pos hgt)
    have hmono : Real.rpow (3 : ℝ) (Real.logb 3 x) ≤ Real.rpow base (Real.logb 3 x) :=
      Real.rpow_le_rpow (by norm_num) hbase hC0
    rw [hval] at hmono
    exact hmono

/-! ## 2. The entry exponent from a law-free burn-in exponent -/

/-- **`hentry` at a law-free exponent.**  The real-power entry exponent returns
`2 * N₀`, which is law-dependent; once the burn-in itself is polynomial in the
base at a law-free exponent `cburn`, the entry clause holds at `2 * cburn`. -/
theorem entry_exponent_of_burnIn {base cburn : ℝ} {N₀ : ℕ}
    (hbase : (3 : ℝ) ≤ base)
    (hburn : (3 : ℝ) ^ N₀ ≤ Real.rpow base cburn) :
    (3 : ℝ) ^ (2 * N₀) ≤ Real.rpow base (2 * cburn) := by
  have hbase0 : (0 : ℝ) < base := by linarith only [hbase]
  have hsplit : (3 : ℝ) ^ (2 * N₀) = (3 : ℝ) ^ N₀ * (3 : ℝ) ^ N₀ := by
    rw [two_mul, pow_add]
  have hrsplit : Real.rpow base (2 * cburn) =
      Real.rpow base cburn * Real.rpow base cburn := by
    change base ^ (2 * cburn) = base ^ cburn * base ^ cburn
    rw [two_mul, Real.rpow_add hbase0]
  have h30 : (0 : ℝ) ≤ (3 : ℝ) ^ N₀ := by positivity
  rw [hsplit, hrsplit]
  exact mul_le_mul hburn hburn h30 (le_trans h30 hburn)

/-- An integer-index split cap supplies the cadence endpoint's natural,
squared entry cap after its coefficient is absorbed into the base. -/
theorem entry_exponent_of_integer_split_cap
    {base C cC c Centry : ℝ} {split : ℤ} {N₀ : ℕ}
    (hbase : (3 : ℝ) ≤ base)
    (hN₀ : (N₀ : ℤ) = split)
    (hsplit : (3 : ℝ) ^ split ≤ C * Real.rpow base c)
    (hC : C ≤ Real.rpow base cC)
    (hCentry : Centry = 2 * cC + 2 * c) :
    (3 : ℝ) ^ (2 * N₀) ≤ Real.rpow base Centry := by
  have hbase0 : (0 : ℝ) < base := by linarith only [hbase]
  have hpow0 : (0 : ℝ) ≤ Real.rpow base c :=
    Real.rpow_nonneg hbase0.le c
  have hNpow : (3 : ℝ) ^ N₀ = (3 : ℝ) ^ split := by
    rw [← hN₀, zpow_natCast]
  have hburn : (3 : ℝ) ^ N₀ ≤ Real.rpow base (cC + c) := by
    calc
      (3 : ℝ) ^ N₀ = (3 : ℝ) ^ split := hNpow
      _ ≤ C * Real.rpow base c := hsplit
      _ ≤ Real.rpow base cC * Real.rpow base c :=
        mul_le_mul_of_nonneg_right hC hpow0
      _ = Real.rpow base (cC + c) :=
        (Real.rpow_add hbase0 cC c).symm
  calc
    (3 : ℝ) ^ (2 * N₀) ≤ Real.rpow base (2 * (cC + c)) :=
      entry_exponent_of_burnIn hbase hburn
    _ = Real.rpow base (2 * cC + 2 * c) := by
      congr 1
      ring
    _ = Real.rpow base Centry := by rw [hCentry]

/-! ## 3. The step every polynomial burn-in bound ends with -/

/-- **`3 · max 1 x` stays polynomial.**  `three_pow_ceil_logb_le` bounds a
ceiling-of-logarithm delay by `3 * max 1 x`; if `x` is itself below a law-free
power of the base, the delay is below the next one. -/
theorem three_mul_max_one_le_rpow {base c x : ℝ}
    (hbase : (3 : ℝ) ≤ base) (hc : 0 ≤ c) (hx : x ≤ Real.rpow base c) :
    3 * max 1 x ≤ Real.rpow base (c + 1) := by
  have hbase0 : (0 : ℝ) < base := by linarith only [hbase]
  have hone : (1 : ℝ) ≤ Real.rpow base c := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith only [hbase] : (1 : ℝ) ≤ base) hc
    rwa [Real.one_rpow] at h
  have hmax : max 1 x ≤ Real.rpow base c := max_le hone hx
  have hstep : 3 * max 1 x ≤ base * Real.rpow base c := by
    have h1 : 3 * max 1 x ≤ 3 * Real.rpow base c := by linarith only [hmax]
    have h2 : 3 * Real.rpow base c ≤ base * Real.rpow base c :=
      mul_le_mul_of_nonneg_right hbase (by linarith only [hone])
    linarith only [h1, h2]
  have hadd : Real.rpow base (c + 1) = Real.rpow base c * base := by
    change base ^ (c + 1) = base ^ c * base
    rw [Real.rpow_add hbase0, Real.rpow_one]
  rw [hadd]
  linarith only [hstep]

/-! ## 4. The source gauge rides in the base -/

/-- **`growthBar` is below the telescope's own base.**  The source gauge needs
no separate polynomial bound: the base already contains it. -/
theorem growthBar_le_base {d : ℕ} {E : BlockMat d} {K : ℝ}
    (haspect : 1 ≤ aspectRatio E) (hK : 0 ≤ K) :
    growthBar K ≤ 2 + aspectRatio E * K := by
  have hKle : K ≤ aspectRatio E * K := by
    have := mul_le_mul_of_nonneg_right haspect hK
    linarith only [this]
  have h0 : (0 : ℝ) ≤ aspectRatio E * K := le_trans hK hKle
  rw [growthBar]
  exact max_le (by linarith only [h0]) (by linarith only [hKle])

/-! ## 5. The settlement, in the binder's quantifier order -/

/-! ## 6. The corrected-cadence prefactor interface -/

/-- A coefficient/base cap for the corrected cadence prefactor, with the
coefficient absorbed into the endpoint's base exponent.  The left side and
conclusion are the `hpref` input of `hcore_body_of_corrected_design`; the raw
cap remains with the threshold arithmetic that produces it. -/
theorem corrected_cadence_prefactor_of_uniform_cap
    {d : ℕ} {P : Measure (CoeffSpace d)} {lAl : ℤ} {E : BlockMat d}
    {N₀ ns cA : ℕ} {A alpha b0 bA b2 S0 S1 S2 d0 : ℝ}
    {base C cC c Cpref : ℝ}
    (hbase : (3 : ℝ) ≤ base)
    (hraw : 9 / 2 *
        ((1 + hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀ 0) *
          (3 : ℝ) ^ (linRate A alpha b0 bA b2 cA S0 *
            ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ))) *
        (Real.rpow (3 : ℝ) (linRate A alpha b0 bA b2 cA S0 / 2) + 1) ≤
      C * Real.rpow base c)
    (hC : C ≤ Real.rpow base cC)
    (hCpref : Cpref = cC + c) :
    9 / 2 *
        ((1 + hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀ 0) *
          (3 : ℝ) ^ (linRate A alpha b0 bA b2 cA S0 *
            ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ))) *
        (Real.rpow (3 : ℝ) (linRate A alpha b0 bA b2 cA S0 / 2) + 1) ≤
      Real.rpow base Cpref := by
  have hbase0 : (0 : ℝ) < base := by linarith only [hbase]
  have hpow0 : (0 : ℝ) ≤ Real.rpow base c :=
    Real.rpow_nonneg hbase0.le c
  calc
    9 / 2 *
          ((1 + hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀ 0) *
            (3 : ℝ) ^ (linRate A alpha b0 bA b2 cA S0 *
              ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ))) *
          (Real.rpow (3 : ℝ) (linRate A alpha b0 bA b2 cA S0 / 2) + 1) ≤
        C * Real.rpow base c := hraw
    _ ≤ Real.rpow base cC * Real.rpow base c :=
      mul_le_mul_of_nonneg_right hC hpow0
    _ = Real.rpow base (cC + c) := (Real.rpow_add hbase0 cC c).symm
    _ = Real.rpow base Cpref := by rw [hCpref]

end

end HCPolySupport.HighContrast.Quenched
