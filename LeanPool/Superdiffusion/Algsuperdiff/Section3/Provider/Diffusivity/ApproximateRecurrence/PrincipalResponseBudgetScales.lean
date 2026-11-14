/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# PrincipalResponseBudgetScales

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
Binder descriptions below are an informal inventory only, NOT a source
certification; certification vocabulary is reserved for frozen source-facing
declarations.

# Provider: the two Orlicz scales of `e.new.induction.for.shom`

The induction hypothesis `d.mathcalS.def` of ABK26 controls
`mathcalE_{s,infinity,2}` by a sum of two one-sided weak-Orlicz terms, with
scales

```
  A_1(s) = E s^{-1} gamma^{1/2}          (class Gamma_2) ,
  A_2(s) = s^{-2} exp(-E^{-3} gamma^{-1})  (class Gamma_{1/2}) .
```

The budget `delta <=^2 |log gamma|^2 gamma` is the statement that the *first*
scale alone dictates the answer: `A_1(s)^2` is exactly `E^2 s^{-2} gamma`,
which at `s = |log gamma|^{-1}` is the printed `E^2 |log gamma|^2 gamma`.  This
module proves that in the parameter regime of the lemma the heavy scale is
dominated by the light one,

```
  A_2(s) <= A_1(s) ,
```

so that no separate constant survives from the `Gamma_{1/2}` leg.

## The regime, and where it comes from

`l.approximate.recurrence.formula` (label) assumes
`e.lower.bound.cgamma.cond.again.0`: `E >= C cstar^{-1}` and `gamma <= E^{-5}`,
with the constant `C = C(d)` still free at that point in the manuscript (it is
fixed inside the proof, at `e.cgamma.constraints`, label).  Two hypotheses are
used below:

* `hgamE : gamma <= (E^5)^{-1}` -- literally the second half of
  `e.lower.bound.cgamma.cond.again.0`;
* `h : 6 <= E` -- a numerical floor on the manuscript's own free constant.  It
  is what `E >= C cstar^{-1}` delivers once `cstar <= 1`; that last inequality
  is a separately tracked development gap and is **not** used here, the floor
  being taken as an explicit hypothesis instead.

The window hypothesis `8 gamma <= s` is the left endpoint of the induction
window `s in [8 gamma, 1]` of `e.new.induction.for.shom` itself.

## Why the window enters

At `s = 1` the inequality `A_2 <= A_1` would read
`exp(-E^{-3}gamma^{-1}) <= E gamma^{1/2}`, which the linear minorant of `exp`
already gives.  The honest amplitude of the heavy leg carries `s^{-2}`, so the
worst case of the window is `s = 8 gamma`, where the required inequality is
`exp(-u) <= 8 E gamma^{3/2}`.  The quintic minorant
`u^5 <= 3125 exp u` (`quintic_le_exp`, proved from `1 + x <= exp x` at `x = u/5`)
closes it with room to spare once `E >= 6`: the numerical content is
`9765625 <= 64 E^7`, and `64 * 6^7 = 17915904`.

## Scope

Everything here is elementary real analysis in three free reals `E`, `gamma`,
`s`.  Nothing refers to the model, the cube, the probe or the induction state,
and no source node is claimed.  Following the development convention, no
numeric tactic is applied to a term containing `Real.exp`, `Real.log` or
`Real.rpow`: the transcendental step is isolated in `quintic_le_exp`, and the
polynomial core in the private `window_leg_algebra`.

## Main results

* `quintic_le_exp`: `u^5 <= 3125 exp u` on `[0, infinity)`.
* `exp_leg_le_window_gaussian_leg`: **`A_2(s) <= A_1(s)`** on the induction
  window, in the regime `6 <= E`, `gamma <= E^{-5}`.

## References

* ABK26, `d.mathcalS.def`, `e.new.induction.for.shom`.
* ABK26, the labels `l.approximate.recurrence.formula`,
  `e.lower.bound.cgamma.cond.again.0`, `e.cgamma.constraints`, `d.mathcalS.def`,
  `e.new.induction.for.shom`.
* ABK26 (the budget).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

noncomputable section

/-! ## A quintic minorant of the exponential -/

/-- `u^5 <= 3125 exp u` for `u >= 0`, from `1 + x <= exp x` at `x = u/5`.  This
is the only transcendental input of the module. -/
theorem quintic_le_exp {u : ℝ} (hu : 0 ≤ u) : u ^ 5 ≤ 3125 * Real.exp u := by
  have h1 : u / 5 ≤ Real.exp (u / 5) := by
    have := Real.add_one_le_exp (u / 5)
    linarith
  have h2 : (u / 5) ^ 5 ≤ Real.exp (u / 5) ^ 5 :=
    pow_le_pow_left₀ (by positivity) h1 5
  have h3 : Real.exp (u / 5) ^ 5 = Real.exp u := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [h3] at h2
  nlinarith [h2]

/-! ## The polynomial core -/

/-- The polynomial core of `exp_leg_le_window_gaussian_leg`, over abstract reals
(`g` plays the role of `gamma^{1/2}`).  It is isolated so that no numeric tactic
ever meets `Real.exp` or `Real.sqrt`.

`E >= 6` and `E^5 g^2 <= 1` give `3125 g <= 8 E` by squaring, using
`64 E^7 >= 64 * 6^7 = 17915904 >= 9765625`; hence `3125 E^14 g^7 <= 8`, which is
the displayed bound after one factorization. -/
private theorem window_leg_algebra {E g : ℝ} (hE6 : 6 ≤ E) (hg : 0 < g)
    (hEg : E ^ 5 * g ^ 2 ≤ 1) :
    3125 * (E ^ 3 * g ^ 2) ^ 5 ≤ 8 * E * g ^ 2 * g := by
  have hE0 : (0 : ℝ) < E := by linarith
  have hE5 : (0 : ℝ) < E ^ 5 := by positivity
  have hE7 : (152588 : ℝ) ≤ E ^ 7 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 6) hE6 7
    norm_num at h
    linarith
  have hgsq2 : 9765625 * g ^ 2 ≤ 64 * E ^ 2 := by
    have hprod : (9765625 * g ^ 2) * E ^ 5 ≤ (64 * E ^ 2) * E ^ 5 := by
      calc (9765625 * g ^ 2) * E ^ 5 = 9765625 * (E ^ 5 * g ^ 2) := by ring
        _ ≤ 9765625 * 1 := by nlinarith
        _ ≤ 64 * E ^ 7 := by linarith
        _ = (64 * E ^ 2) * E ^ 5 := by ring
    exact le_of_mul_le_mul_right hprod hE5
  have hgE : 3125 * g ≤ 8 * E := by
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    calc (3125 * g) ^ 2 = 9765625 * g ^ 2 := by ring
      _ ≤ 64 * E ^ 2 := hgsq2
      _ = (8 * E) ^ 2 := by ring
  have hcube : (E ^ 5 * g ^ 2) ^ 3 ≤ 1 := by
    calc (E ^ 5 * g ^ 2) ^ 3 ≤ 1 ^ 3 := pow_le_pow_left₀ (by positivity) hEg 3
      _ = 1 := one_pow 3
  have hkey : 3125 * E ^ 14 * g ^ 7 ≤ 8 := by
    refine le_of_mul_le_mul_right ?_ hE0
    calc 3125 * E ^ 14 * g ^ 7 * E = 3125 * (E ^ 5 * g ^ 2) ^ 3 * g := by ring
      _ ≤ 3125 * 1 * g := by nlinarith
      _ = 3125 * g := by ring
      _ ≤ 8 * E := hgE
  calc 3125 * (E ^ 3 * g ^ 2) ^ 5
      = (3125 * E ^ 14 * g ^ 7) * (E * g ^ 3) := by ring
    _ ≤ 8 * (E * g ^ 3) := mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = 8 * E * g ^ 2 * g := by ring

/-! ## The heavy Orlicz leg is dominated by the light one -/

/-- **The heavy scale of `e.new.induction.for.shom` is below the light one, on
the induction window and in the regime of `l.approximate.recurrence.formula`.**

```
  s^{-2} exp(-E^{-3} gamma^{-1})  <=  E s^{-1} gamma^{1/2} .
```

The hypotheses are the manuscript's own `gamma <= E^{-5}` of
`e.lower.bound.cgamma.cond.again.0`, the left endpoint `8 gamma <= s` of the
induction window, and the numerical floor `6 <= E` on the free constant of that
same parameter condition. -/
theorem exp_leg_le_window_gaussian_leg {E gam s : ℝ} (hE6 : 6 ≤ E)
    (hgam : 0 < gam) (hgamE : gam ≤ (E ^ 5)⁻¹) (hs8 : 8 * gam ≤ s) :
    (s⁻¹) ^ 2 * Real.exp (-((E⁻¹) ^ 3 * gam⁻¹)) ≤ E * s⁻¹ * Real.sqrt gam := by
  have hE0 : (0 : ℝ) < E := by linarith
  have hs : 0 < s := by linarith
  have hg0 : 0 < Real.sqrt gam := Real.sqrt_pos.2 hgam
  have hgsq : Real.sqrt gam ^ 2 = gam := Real.sq_sqrt hgam.le
  have hE5 : (0 : ℝ) < E ^ 5 := by positivity
  have hinv3 : (E⁻¹ : ℝ) ^ 3 = (E ^ 3)⁻¹ := by rw [inv_pow]
  have hu : (0 : ℝ) < (E ^ 3)⁻¹ * gam⁻¹ := by positivity
  have hquint : Real.exp (-((E ^ 3)⁻¹ * gam⁻¹)) ≤ 3125 * (E ^ 3 * gam) ^ 5 := by
    have hq := quintic_le_exp hu.le
    have hepos : (0 : ℝ) < Real.exp ((E ^ 3)⁻¹ * gam⁻¹) := Real.exp_pos _
    have hone : ((E ^ 3)⁻¹ * gam⁻¹) ^ 5 * (E ^ 3 * gam) ^ 5 = 1 := by
      rw [← mul_pow]
      have hprod : ((E ^ 3)⁻¹ * gam⁻¹) * (E ^ 3 * gam) = 1 := by field_simp
      rw [hprod, one_pow]
    have hkey : 1 ≤ 3125 * (E ^ 3 * gam) ^ 5 * Real.exp ((E ^ 3)⁻¹ * gam⁻¹) := by
      calc (1 : ℝ) = ((E ^ 3)⁻¹ * gam⁻¹) ^ 5 * (E ^ 3 * gam) ^ 5 := hone.symm
        _ ≤ (3125 * Real.exp ((E ^ 3)⁻¹ * gam⁻¹)) * (E ^ 3 * gam) ^ 5 :=
            mul_le_mul_of_nonneg_right hq (by positivity)
        _ = 3125 * (E ^ 3 * gam) ^ 5 * Real.exp ((E ^ 3)⁻¹ * gam⁻¹) := by ring
    rw [Real.exp_neg]
    have h := (div_le_iff₀ hepos).mpr hkey
    rwa [one_div] at h
  have hEg : E ^ 5 * gam ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hgamE hE5.le
    rwa [mul_inv_cancel₀ hE5.ne'] at h
  have hEgsq : E ^ 5 * Real.sqrt gam ^ 2 ≤ 1 := by rw [hgsq]; exact hEg
  have hpoly : 3125 * (E ^ 3 * gam) ^ 5 ≤ 8 * E * gam * Real.sqrt gam := by
    have halg := window_leg_algebra hE6 hg0 hEgsq
    rwa [hgsq] at halg
  have hAB : Real.exp (-((E ^ 3)⁻¹ * gam⁻¹)) ≤ E * s * Real.sqrt gam := by
    refine hquint.trans (hpoly.trans ?_)
    calc 8 * E * gam * Real.sqrt gam = (E * Real.sqrt gam) * (8 * gam) := by ring
      _ ≤ (E * Real.sqrt gam) * s := mul_le_mul_of_nonneg_left hs8 (by positivity)
      _ = E * s * Real.sqrt gam := by ring
  have hss : s⁻¹ * s = 1 := inv_mul_cancel₀ (ne_of_gt hs)
  rw [hinv3]
  calc (s⁻¹) ^ 2 * Real.exp (-((E ^ 3)⁻¹ * gam⁻¹))
      ≤ (s⁻¹) ^ 2 * (E * s * Real.sqrt gam) :=
        mul_le_mul_of_nonneg_left hAB (by positivity)
    _ = (s⁻¹ * s) * (E * s⁻¹ * Real.sqrt gam) := by rw [sq]; ring
    _ = E * s⁻¹ * Real.sqrt gam := by rw [hss, one_mul]

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
