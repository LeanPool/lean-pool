/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepEnvelope

/-!
# HomMomentTail

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Theorem B, §4.5, Step 1: the missing glue `hY`

## The target

Step 1's display carries EXACTLY ONE conditional
edge, `hY`:

```
  ∫⁻ ω, Y ω ^ (2p) dμ ≤ (ENNReal.ofReal 2) ^ (2p),
      Y = 3^{(1-α) X_m(α)},
```

the exponential moment of the Theorem-C minimal-scale factor.  The missing glue
is exactly this: **tail ⟹ exponential moment for an `ℕ∞`-valued scale**, absent
repo-wide and in `CoarseGraining`.  This module supplies it.

## The carrier

`X_m(α)` is `ℕ∞`-valued (the `Provider.Regularity.minimalScaleX`), so
`3^{(1-α)X}` must be `ℝ≥0∞`-valued with the value `⊤` on `{X = ⊤}`.
`enatThreeRpow` is that function, defined by the `WithTop` recursor — NOT by a
truncation, a junk value, or a comparable surrogate: on `{X = k}` it is exactly
`3^{ck}` and on `{X = ⊤}` it is exactly `⊤`.

## The engine

`lintegral_homMinimalScaleFactor_rpow_le_two`.  Three elementary steps, no
layer-cake identity and no series inversion:

1. **The one-sided truncated layer bound**
   (`homMinimalScaleFactor_le_trunc_add_tsum`): for any cut `N₀`,
   ```
     3^{cX} ≤ 3^{cN₀} + Σ_{N ≥ N₀+1} 3^{cN} 1{X ≥ N},
   ```
   an inequality, valid pointwise including at `X = ⊤` (both sides `⊤`, because
   the tail series of terms `≥ 1` diverges).  This is where the naive layer-cake
   bound `E[b^X] ≤ Σ_N b^N P(X ≥ N)` — which overcounts by the cut length and
   is USELESS at `p = 1` — is avoided.
2. **Integration** (`lintegral_homMinimalScaleFactor_le`): `lintegral_tsum` plus
   `lintegral_indicator_const` turn the right-hand side into
   `3^{cN₀} + Σ_N 3^{cN} μ{X ≥ N}`.
3. **The geometric tail**: the tail `μ{X ≥ N} ≤ B e^{-θN}` makes the
   `N`-th term `B ρ^N` with `ρ = 3^c e^{-θ}`, and the three DISPLAYED gates
   * `hratio`: `ρ ≤ 1/2`   (the `p`-range: `2p(1-α)log 3 ≤ θ/2`),
   * `htrunc`: `3^{c·2p·N₀} ≤ 2^p`   (the `γ`-smallness `N₀ s log 3 ≤ log 2`),
   * `hsmall`: `2 B ρ^{N₀+1} ≤ 1`   (the cut is past the tail's turn-on),
   give `≤ 2^p + 1 ≤ 2^{2p}`.

The three gates are stated, not absorbed: they are exactly the `γ`-smallness
and `p`-range the §4.5 web must supply, and `homTailNormalForm` converts the
own tail (`step_two_minimalScaleX`'s fourth clause) into the `(B, θ)` shape
they speak about.

## Why `p = 1` is the binding case

At the bottom of the range the moment must be below `2^2 = 4` while the crude
layer-cake bound gives `≈ N₀`.  Step 1 above is exactly what avoids that: the
cut contributes `3^{cN₀} ≤ 2^p`, not `N₀`, and the tail contributes `≤ 1`.  -/

open Algsuperdiff.Section3
open MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-! ## 1. `3^{c n}` for an `ℕ∞`-valued scale -/

/-- `3^{c n}` for `n: ℕ∞`, with the value `⊤` at `n = ⊤`.  Faithful: no
truncation and no junk value. -/
def enatThreeRpow (c : ℝ) : ℕ∞ → ℝ≥0∞ :=
  WithTop.recTopCoe ⊤ fun k : ℕ => ENNReal.ofReal ((3 : ℝ) ^ (c * (k : ℝ)))

theorem enatThreeRpow_top (c : ℝ) : enatThreeRpow c ⊤ = ⊤ := rfl

theorem enatThreeRpow_coe (c : ℝ) (k : ℕ) :
    enatThreeRpow c ((k : ℕ) : ℕ∞) = ENNReal.ofReal ((3 : ℝ) ^ (c * (k : ℝ))) := rfl

/-- **The Theorem-C minimal-scale factor** `3^{(1-α) X_m(α)}` as an
`ℝ≥0∞`-valued observable — the `Y` slot of `EthmB(m)`. -/
def homMinimalScaleFactor (c : ℝ) (X : Omega → ℕ∞) : Omega → ℝ≥0∞ :=
  fun omega => enatThreeRpow c (X omega)

theorem measurable_homMinimalScaleFactor (c : ℝ) {X : Omega → ℕ∞} (hX : Measurable X) :
    Measurable (homMinimalScaleFactor c X) :=
  Measurable.of_discrete.comp hX

/-- Raising the factor to a positive power multiplies the exponent: this is what
turns `Y^{2p}` into the same object at `c ↦ 2pc`. -/
theorem enatThreeRpow_rpow {c r : ℝ} (hr : 0 < r) (n : ℕ∞) :
    enatThreeRpow c n ^ r = enatThreeRpow (c * r) n := by
  rcases eq_or_ne n ⊤ with htop | hfin
  · rw [htop, enatThreeRpow_top, enatThreeRpow_top, ENNReal.top_rpow_of_pos hr]
  · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfin
    rw [← hk]
    change ENNReal.ofReal ((3 : ℝ) ^ (c * (k : ℝ))) ^ r =
      ENNReal.ofReal ((3 : ℝ) ^ (c * r * (k : ℝ)))
    rw [ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos (by norm_num) _),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 2
    ring

omit [MeasurableSpace Omega] in
theorem homMinimalScaleFactor_rpow {c r : ℝ} (hr : 0 < r) (X : Omega → ℕ∞)
    (omega : Omega) :
    homMinimalScaleFactor c X omega ^ r = homMinimalScaleFactor (c * r) X omega :=
  enatThreeRpow_rpow hr (X omega)

/-! ## 2. The one-sided truncated layer bound -/

omit [MeasurableSpace Omega] in
/-- **The truncated layer bound**, pointwise and valid at `X = ⊤`:

```
  3^{cX} ≤ 3^{cN₀} + Σ_{N ≥ N₀+1} 3^{cN} 1{X ≥ N}.
```

Below the cut the first summand dominates; above it the matching term of the
series does.  Unlike the untruncated layer-cake bound this does not accumulate
`N₀` copies of `1`, which is what makes the `p = 1` endpoint reachable. -/
theorem homMinimalScaleFactor_le_trunc_add_tsum {c : ℝ} (hc : 0 ≤ c) (N0 : ℕ)
    (X : Omega → ℕ∞) (omega : Omega) :
    homMinimalScaleFactor c X omega ≤
      ENNReal.ofReal ((3 : ℝ) ^ (c * (N0 : ℝ))) +
        ∑' N : ℕ, Set.indicator {w : Omega | ((N0 + 1 + N : ℕ) : ℕ∞) ≤ X w}
          (fun _ => ENNReal.ofReal ((3 : ℝ) ^ (c * ((N0 + 1 + N : ℕ) : ℝ)))) omega := by
  rcases eq_or_ne (X omega) ⊤ with htop | hfin
  · have hterm : ∀ N : ℕ, (1 : ℝ≥0∞) ≤
        Set.indicator {w : Omega | ((N0 + 1 + N : ℕ) : ℕ∞) ≤ X w}
          (fun _ => ENNReal.ofReal ((3 : ℝ) ^ (c * ((N0 + 1 + N : ℕ) : ℝ)))) omega := by
      intro N
      have hmem : omega ∈ {w : Omega | ((N0 + 1 + N : ℕ) : ℕ∞) ≤ X w} := by
        rw [Set.mem_ofPred_eq, htop]
        exact le_top
      rw [Set.indicator_of_mem hmem, ← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      exact Real.one_le_rpow (by norm_num) (mul_nonneg hc (Nat.cast_nonneg _))
    have hdiv : (⊤ : ℝ≥0∞) ≤
        ∑' N : ℕ, Set.indicator {w : Omega | ((N0 + 1 + N : ℕ) : ℕ∞) ≤ X w}
          (fun _ => ENNReal.ofReal ((3 : ℝ) ^ (c * ((N0 + 1 + N : ℕ) : ℝ)))) omega := by
      calc (⊤ : ℝ≥0∞) = ∑' _N : ℕ, (1 : ℝ≥0∞) :=
            (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
        _ ≤ _ := ENNReal.tsum_le_tsum hterm
    have hLHS : homMinimalScaleFactor c X omega = ⊤ := by
      rw [homMinimalScaleFactor, htop, enatThreeRpow_top]
    rw [hLHS]
    exact le_trans hdiv le_add_self
  · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfin
    have hval : homMinimalScaleFactor c X omega =
        ENNReal.ofReal ((3 : ℝ) ^ (c * (k : ℝ))) := by
      rw [homMinimalScaleFactor, ← hk]
      rfl
    rw [hval]
    rcases le_or_gt k N0 with hkle | hkgt
    · refine le_trans ?_ le_self_add
      refine ENNReal.ofReal_le_ofReal ?_
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hknat : ((k : ℕ) : ℝ) ≤ ((N0 : ℕ) : ℝ) := Nat.cast_le.mpr hkle
      exact mul_le_mul_of_nonneg_left hknat hc
    · refine le_trans ?_ le_add_self
      have hkeq : (N0 + 1 + (k - (N0 + 1)) : ℕ) = k := by omega
      have hmem : omega ∈
          {w : Omega | ((N0 + 1 + (k - (N0 + 1)) : ℕ) : ℕ∞) ≤ X w} := by
        rw [Set.mem_ofPred_eq, ← hk, hkeq]
        exact le_rfl
      calc ENNReal.ofReal ((3 : ℝ) ^ (c * (k : ℝ)))
          = Set.indicator {w : Omega | ((N0 + 1 + (k - (N0 + 1)) : ℕ) : ℕ∞) ≤ X w}
              (fun _ => ENNReal.ofReal
                ((3 : ℝ) ^ (c * ((N0 + 1 + (k - (N0 + 1)) : ℕ) : ℝ)))) omega := by
            rw [Set.indicator_of_mem hmem, hkeq]
        _ ≤ _ := ENNReal.le_tsum (f := fun N : ℕ =>
            Set.indicator {w : Omega | ((N0 + 1 + N : ℕ) : ℕ∞) ≤ X w}
              (fun _ => ENNReal.ofReal ((3 : ℝ) ^ (c * ((N0 + 1 + N : ℕ) : ℝ)))) omega)
            (k - (N0 + 1))

/-! ## 3. Integration -/

/-- The truncated layer bound, integrated. -/
theorem lintegral_homMinimalScaleFactor_le {mu : Measure Omega} [IsProbabilityMeasure mu]
    {c : ℝ} (hc : 0 ≤ c) (N0 : ℕ) {X : Omega → ℕ∞} (hX : Measurable X) :
    (∫⁻ omega, homMinimalScaleFactor c X omega ∂mu) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (c * (N0 : ℝ))) +
        ∑' N : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (c * ((N0 + 1 + N : ℕ) : ℝ))) *
          mu {w : Omega | ((N0 + 1 + N : ℕ) : ℕ∞) ≤ X w} := by
  have hmeas : ∀ N : ℕ, MeasurableSet {w : Omega | ((N0 + 1 + N : ℕ) : ℕ∞) ≤ X w} := by
    intro N
    exact hX (MeasurableSet.of_discrete
      (s := {y : ℕ∞ | ((N0 + 1 + N : ℕ) : ℕ∞) ≤ y}))
  have hae : ∀ N : ℕ, AEMeasurable
      (Set.indicator {w : Omega | ((N0 + 1 + N : ℕ) : ℕ∞) ≤ X w}
        (fun _ => ENNReal.ofReal ((3 : ℝ) ^ (c * ((N0 + 1 + N : ℕ) : ℝ))))) mu :=
    fun N => (measurable_const.indicator (hmeas N)).aemeasurable
  calc (∫⁻ omega, homMinimalScaleFactor c X omega ∂mu)
      ≤ ∫⁻ omega, (ENNReal.ofReal ((3 : ℝ) ^ (c * (N0 : ℝ))) +
          ∑' N : ℕ, Set.indicator {w : Omega | ((N0 + 1 + N : ℕ) : ℕ∞) ≤ X w}
            (fun _ => ENNReal.ofReal ((3 : ℝ) ^ (c * ((N0 + 1 + N : ℕ) : ℝ))))
              omega) ∂mu :=
        lintegral_mono (homMinimalScaleFactor_le_trunc_add_tsum hc N0 X)
    _ = ENNReal.ofReal ((3 : ℝ) ^ (c * (N0 : ℝ))) +
          ∫⁻ omega, (∑' N : ℕ, Set.indicator {w : Omega | ((N0 + 1 + N : ℕ) : ℕ∞) ≤ X w}
            (fun _ => ENNReal.ofReal ((3 : ℝ) ^ (c * ((N0 + 1 + N : ℕ) : ℝ))))
              omega) ∂mu := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ = ENNReal.ofReal ((3 : ℝ) ^ (c * (N0 : ℝ))) +
          ∑' N : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (c * ((N0 + 1 + N : ℕ) : ℝ))) *
            mu {w : Omega | ((N0 + 1 + N : ℕ) : ℕ∞) ≤ X w} := by
        rw [lintegral_tsum hae]
        congr 1
        exact tsum_congr fun N => lintegral_indicator_const (hmeas N) _

/-! ## 4. The geometric tail -/

private theorem three_rpow_mul_exp_pow (c theta : ℝ) (M : ℕ) :
    (3 : ℝ) ^ (c * (M : ℝ)) * Real.exp (-(theta * (M : ℝ))) =
      ((3 : ℝ) ^ c * Real.exp (-theta)) ^ M := by
  have h1 : ((3 : ℝ) ^ c) ^ M = (3 : ℝ) ^ (c * (M : ℝ)) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ c) M, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have h2 : (Real.exp (-theta)) ^ M = Real.exp (-(theta * (M : ℝ))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [mul_pow, h1, h2]

/-- The extended-nonnegative geometric series is at most two for ratio at most one half. -/
theorem tsum_ofReal_pow_le_two {rho : ℝ} (h : rho ≤ 1 / 2) :
    ∑' _N : ℕ, ENNReal.ofReal rho ^ _N ≤ 2 := by
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
      ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  have hle : ENNReal.ofReal rho ≤ (2 : ℝ≥0∞)⁻¹ := by
    rw [← hhalf]
    exact ENNReal.ofReal_le_ofReal h
  have hgeom : ((1 : ℝ≥0∞) - (2 : ℝ≥0∞)⁻¹)⁻¹ = 2 := by
    have hsub : (1 : ℝ≥0∞) - (2 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ := by
      refine ENNReal.sub_eq_of_eq_add (by simp) ?_
      rw [ENNReal.inv_two_add_inv_two]
    rw [hsub, inv_inv]
  calc ∑' _N : ℕ, ENNReal.ofReal rho ^ _N ≤ ∑' _N : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ _N :=
        ENNReal.tsum_le_tsum fun N => pow_le_pow_left' hle N
    _ = ((1 : ℝ≥0∞) - (2 : ℝ≥0∞)⁻¹)⁻¹ := ENNReal.tsum_geometric _
    _ = 2 := hgeom

/-! ## 5. `hY`: the exponential moment -/

/-- **The `hY` discharge.**

For an `ℕ∞`-valued scale `X` with the geometric tail `μ{X ≥ N} ≤ B e^{-θN}`,
the Theorem-C factor `Y = 3^{cX}` obeys the moment normal form

```
  ∫⁻ Y^{2p} dμ ≤ (ENNReal.ofReal 2)^{2p}
```

under the three DISPLAYED gates `hratio`, `htrunc`, `hsmall`.  This is exactly
the shape of the conditional edge `hY`, so Step 1's display becomes
unconditional once the §4.5 web supplies the gates. -/
theorem lintegral_homMinimalScaleFactor_rpow_le_two {mu : Measure Omega}
    [IsProbabilityMeasure mu] {X : Omega → ℕ∞} (hX : Measurable X)
    {c B theta p : ℝ} {N0 : ℕ} (hc : 0 ≤ c) (hp : 1 ≤ p) (hB : 0 ≤ B)
    (htail : ∀ N : ℕ, mu {w : Omega | (N : ℕ∞) ≤ X w} ≤
      ENNReal.ofReal (B * Real.exp (-(theta * (N : ℝ)))))
    (hratio : (3 : ℝ) ^ (c * (2 * p)) * Real.exp (-theta) ≤ 1 / 2)
    (htrunc : (3 : ℝ) ^ (c * (2 * p) * (N0 : ℝ)) ≤ (2 : ℝ) ^ p)
    (hsmall : 2 * (B * ((3 : ℝ) ^ (c * (2 * p)) * Real.exp (-theta)) ^ (N0 + 1)) ≤ 1) :
    (∫⁻ omega, homMinimalScaleFactor c X omega ^ (2 * p) ∂mu) ≤
      ENNReal.ofReal 2 ^ (2 * p) := by
  have hppos : (0 : ℝ) < p := by linarith only [hp]
  have h2p : (0 : ℝ) < 2 * p := by linarith only [hppos]
  set c' : ℝ := c * (2 * p) with hc'
  have hc'nn : (0 : ℝ) ≤ c' := by
    rw [hc']; exact mul_nonneg hc h2p.le
  set rho : ℝ := (3 : ℝ) ^ c' * Real.exp (-theta) with hrho
  have hrho0 : (0 : ℝ) ≤ rho := by
    rw [hrho]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.exp_pos _).le
  /- Step 0: the power moves into the expone -/
  have hpow : (∫⁻ omega, homMinimalScaleFactor c X omega ^ (2 * p) ∂mu) =
      ∫⁻ omega, homMinimalScaleFactor c' X omega ∂mu := by
    refine lintegral_congr fun omega => ?_
    rw [homMinimalScaleFactor_rpow h2p X omega]
  /- Step 1--2: the truncated layer bound, integrat -/
  have hlayer := lintegral_homMinimalScaleFactor_le (mu := mu) hc'nn N0 hX
  /- Step 3: the geometric ta -/
  have hterm : ∀ N : ℕ,
      ENNReal.ofReal ((3 : ℝ) ^ (c' * ((N0 + 1 + N : ℕ) : ℝ))) *
          mu {w : Omega | ((N0 + 1 + N : ℕ) : ℕ∞) ≤ X w} ≤
        ENNReal.ofReal (B * rho ^ (N0 + 1)) * ENNReal.ofReal rho ^ N := by
    intro N
    have hbase : (0 : ℝ) ≤ (3 : ℝ) ^ (c' * ((N0 + 1 + N : ℕ) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hstep : ENNReal.ofReal ((3 : ℝ) ^ (c' * ((N0 + 1 + N : ℕ) : ℝ))) *
        mu {w : Omega | ((N0 + 1 + N : ℕ) : ℕ∞) ≤ X w} ≤
        ENNReal.ofReal ((3 : ℝ) ^ (c' * ((N0 + 1 + N : ℕ) : ℝ))) *
          ENNReal.ofReal (B * Real.exp (-(theta * ((N0 + 1 + N : ℕ) : ℝ)))) :=
      mul_le_mul' le_rfl (htail (N0 + 1 + N))
    refine hstep.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul hbase]
    have hid : (3 : ℝ) ^ (c' * ((N0 + 1 + N : ℕ) : ℝ)) *
        (B * Real.exp (-(theta * ((N0 + 1 + N : ℕ) : ℝ)))) =
        B * rho ^ (N0 + 1 + N) := by
      have h := three_rpow_mul_exp_pow c' theta (N0 + 1 + N)
      rw [← hrho] at h
      calc (3 : ℝ) ^ (c' * ((N0 + 1 + N : ℕ) : ℝ)) *
            (B * Real.exp (-(theta * ((N0 + 1 + N : ℕ) : ℝ))))
          = B * ((3 : ℝ) ^ (c' * ((N0 + 1 + N : ℕ) : ℝ)) *
              Real.exp (-(theta * ((N0 + 1 + N : ℕ) : ℝ)))) := by ring
        _ = B * rho ^ (N0 + 1 + N) := by rw [h]
    rw [hid, pow_add,
      show B * (rho ^ (N0 + 1) * rho ^ N) = B * rho ^ (N0 + 1) * rho ^ N by ring,
      ENNReal.ofReal_mul (mul_nonneg hB (pow_nonneg hrho0 _)),
      ENNReal.ofReal_pow hrho0]
  have hseries : (∑' N : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (c' * ((N0 + 1 + N : ℕ) : ℝ))) *
      mu {w : Omega | ((N0 + 1 + N : ℕ) : ℕ∞) ≤ X w}) ≤ 1 := by
    have hbound : (∑' N : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (c' * ((N0 + 1 + N : ℕ) : ℝ))) *
        mu {w : Omega | ((N0 + 1 + N : ℕ) : ℕ∞) ≤ X w}) ≤
        ENNReal.ofReal (B * rho ^ (N0 + 1)) * ∑' _N : ℕ, ENNReal.ofReal rho ^ _N := by
      rw [← ENNReal.tsum_mul_left]
      exact ENNReal.tsum_le_tsum hterm
    refine hbound.trans ?_
    have hgeom := tsum_ofReal_pow_le_two (rho := rho) hratio
    have hstep : ENNReal.ofReal (B * rho ^ (N0 + 1)) *
        ∑' _N : ℕ, ENNReal.ofReal rho ^ _N ≤
        ENNReal.ofReal (B * rho ^ (N0 + 1)) * 2 := mul_le_mul' le_rfl hgeom
    refine hstep.trans ?_
    have htwo : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by
      rw [ENNReal.ofReal_ofNat]
    rw [htwo, ← ENNReal.ofReal_mul (mul_nonneg hB (pow_nonneg hrho0 _)),
      ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have hcomm : B * rho ^ (N0 + 1) * 2 = 2 * (B * rho ^ (N0 + 1)) := by ring
    rw [hcomm, hrho]
    exact hsmall
  /- assemb -/
  have hcut : ENNReal.ofReal ((3 : ℝ) ^ (c' * (N0 : ℝ))) ≤ ENNReal.ofReal ((2 : ℝ) ^ p) :=
    ENNReal.ofReal_le_ofReal htrunc
  have hfinal : ENNReal.ofReal ((2 : ℝ) ^ p) + 1 ≤ ENNReal.ofReal 2 ^ (2 * p) := by
    have ht2 : (2 : ℝ) ≤ (2 : ℝ) ^ p := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp
      rwa [Real.rpow_one] at h
    have hsq : (2 : ℝ) ^ (2 * p) = ((2 : ℝ) ^ p) ^ (2 : ℕ) := by
      rw [show (2 : ℝ) * p = p * ((2 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    have hreal : (2 : ℝ) ^ p + 1 ≤ (2 : ℝ) ^ (2 * p) := by
      rw [hsq]
      have hexp : (((2 : ℝ) ^ p) ^ (2 : ℕ)) = ((2 : ℝ) ^ p) * ((2 : ℝ) ^ p) := by ring
      have hmul : (2 : ℝ) * ((2 : ℝ) ^ p) ≤ ((2 : ℝ) ^ p) * ((2 : ℝ) ^ p) :=
        mul_le_mul_of_nonneg_right ht2 (by linarith only [ht2])
      rw [hexp]
      linarith only [hmul, ht2]
    rw [ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2), ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add (Real.rpow_nonneg (by norm_num) _) zero_le_one]
    exact ENNReal.ofReal_le_ofReal hreal
  rw [hpow]
  refine hlayer.trans ?_
  exact le_trans (add_le_add hcut hseries) hfinal

/-! ## 6. The tail in the `(B, θ)` normal form -/

/-- **the Step-2 tail, rewritten.**  `step_two_minimalScaleX`'s fourth clause
gives `μ{X ≥ N} ≤ C exp(-((1-α)²(N - C))/(Cγ))`; that is the `(B, θ)` shape the
engine consumes, at

```
  B = C e^{(1-α)²/γ},      θ = (1-α)²/(Cγ).
```

An identity, not an estimate. -/
theorem homTailNormalForm {Cst gam alpha : ℝ} (hCst : Cst ≠ 0) (hgam : gam ≠ 0) (N : ℕ) :
    Cst * Real.exp (-((1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - Cst)) / (Cst * gam)) =
      (Cst * Real.exp ((1 - alpha) ^ (2 : ℕ) / gam)) *
        Real.exp (-(((1 - alpha) ^ (2 : ℕ) / (Cst * gam)) * (N : ℝ))) := by
  have hsplit : -((1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - Cst)) / (Cst * gam) =
      (1 - alpha) ^ (2 : ℕ) / gam +
        -(((1 - alpha) ^ (2 : ℕ) / (Cst * gam)) * (N : ℝ)) := by
    field_simp
    ring
  rw [hsplit, Real.exp_add]
  ring

/-! ## 7. `hY` at this development carrier -/

/-- **The `hY` discharge at the §4.5 carrier.**

The `step_two_minimalScaleX` supplies, for the own law, the tail

```
  P{ X_m(α) ≥ N } ≤ C exp( -((1-α)²(N - C)) / (Cγ) ),
```

and this theorem turns it into the conditional edge `hY` verbatim:

```
  ∫⁻ ω, (3^{(1-α)X_m(α)})^{2p} dP ≤ (ENNReal.ofReal 2)^{2p}.
```

The three gates are the `(B,θ)` instances of the engine's, at
`B = C e^{(1-α)²/γ}` and `θ = (1-α)²/(Cγ)`.  They are the §4.5 web's `γ`- and
`p`-side conditions, stated rather than absorbed. -/
theorem homY_moment_bound {d : ℕ} (M : ABKModel d) {X : Cutoff.CutoffSample d → ℕ∞}
    (hX : Measurable X) {Cst alpha p : ℝ} {N0 : ℕ} (hCst : 0 < Cst)
    (halpha : alpha ≤ 1) (hp : 1 ≤ p)
    (htail : ∀ N : ℕ, (Cutoff.cutoffSampleLaw M).toMeasure {omega | (N : ℕ∞) ≤ X omega} ≤
      ENNReal.ofReal (Cst *
        Real.exp (-((1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - Cst)) / (Cst * M.gamma))))
    (hratio : (3 : ℝ) ^ ((1 - alpha) * (2 * p)) *
        Real.exp (-((1 - alpha) ^ (2 : ℕ) / (Cst * M.gamma))) ≤ 1 / 2)
    (htrunc : (3 : ℝ) ^ ((1 - alpha) * (2 * p) * (N0 : ℝ)) ≤ (2 : ℝ) ^ p)
    (hsmall : 2 * ((Cst * Real.exp ((1 - alpha) ^ (2 : ℕ) / M.gamma)) *
        ((3 : ℝ) ^ ((1 - alpha) * (2 * p)) *
          Real.exp (-((1 - alpha) ^ (2 : ℕ) / (Cst * M.gamma)))) ^ (N0 + 1)) ≤ 1) :
    (∫⁻ omega, homMinimalScaleFactor (1 - alpha) X omega ^ (2 * p)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal 2 ^ (2 * p) := by
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hBnn : (0 : ℝ) ≤ Cst * Real.exp ((1 - alpha) ^ (2 : ℕ) / M.gamma) :=
    mul_nonneg hCst.le (Real.exp_pos _).le
  have hcnn : (0 : ℝ) ≤ 1 - alpha := by linarith only [halpha]
  have htail' : ∀ N : ℕ,
      (Cutoff.cutoffSampleLaw M).toMeasure {omega | (N : ℕ∞) ≤ X omega} ≤
        ENNReal.ofReal ((Cst * Real.exp ((1 - alpha) ^ (2 : ℕ) / M.gamma)) *
          Real.exp (-(((1 - alpha) ^ (2 : ℕ) / (Cst * M.gamma)) * (N : ℝ)))) := by
    intro N
    have hN := htail N
    rwa [homTailNormalForm (ne_of_gt hCst) (ne_of_gt hgpos) N] at hN
  exact lintegral_homMinimalScaleFactor_rpow_le_two hX hcnn hp hBnn htail' hratio htrunc
    hsmall

end

end Algsuperdiff.Section4.Provider.Homogenization
