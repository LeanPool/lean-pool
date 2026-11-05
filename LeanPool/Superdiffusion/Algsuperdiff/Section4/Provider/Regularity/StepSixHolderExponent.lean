/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepOneParameters

/-!
# StepSixHolderExponent

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 6: verifying the Hölder exponent

## The target

The step converts the exponential prefactor of `e.oscillation.iteration.result`
into a Hölder rate:

```text
   choosing  C₁ ≥ 4 C (k+1) / log 3 ,
   exp( C₁⁻¹ C (1-α)(m-n) )  ≤  3^{(1/4)(1-α)(m-n)}
```



and then re-states `e.oscillation.iteration.result` as
`e.oscillation.Holder.bound`:

```text
   3^{-n'} ‖u - (u)_{U_{n'}}‖_{L²(U_{n'})}
     ≤ C 3^{(1/2)(1-α)(m-n)} · 3^{-m'} ‖u - (u)_{U_{m'}}‖_{L²(U_{m'})}
     + C 3^{(1/2)(1-α)(m-n)} · 3^{m/2} ( σ_m^{-1}[g]_{W^{1/2,∞}(□_m)}
                                        + ‖∇h‖_{W^{1/2,∞}(□_m)} 1_{z ∉ □_{m-1}} ) .
```

## What "composed into the shape" means, exactly

```text
  oscLo  := 3^{-n'} ‖u - (u)_{U_{n'}}‖_{L²(U_{n'})} ,
  oscHi  := 3^{-m'} ‖u - (u)_{U_{m'}}‖_{L²(U_{m'})} ,
  dataG  := 3^{m/2} σ_m^{-1} [g]_{W^{1/2,∞}(□_m)} ,
  dataH  := 3^{m/2} ‖∇h‖_{W^{1/2,∞}(□_m)} 1_{z ∉ □_{m-1}} ,
```

the inequality `oscLo ≤ C e^P (oscHi + C dataG) + C e^P dataH`, and
`e.oscillation.Holder.bound` is
`oscLo ≤ C' 3^{t/2} oscHi + C' 3^{t/2} (dataG + dataH)`.  The composition is
therefore the prefactor replacement together with the distribution of the inner
`C`; the produced constant is `C' = C + C²` (deviation D2 below), which
is the honest cost of the manuscript writing one letter `C` in both places.

## References

* ABK26, `t.regularity` Step 6, (`e.oscillation.Holder.bound`).
* ABK26, `e.oscillation.iteration.result`.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

noncomputable section

/-! ## 1. The abstract-real atoms near `exp` and `log` -/

/-- `exp a ≤ 3^t` as soon as `a ≤ t log 3`.  The only place `exp` and `rpow` meet
in this module; everything else is scalar arithmetic on `Real.log 3`, which is
kept opaque (only its positivity is used). -/
theorem exp_le_rpow_three_of_le_mul_log {a t : ℝ} (h : a ≤ t * Real.log 3) :
    Real.exp a ≤ Real.rpow (3 : ℝ) t := by
  rw [show Real.rpow (3 : ℝ) t = Real.exp (Real.log 3 * t) from
    Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3) t]
  exact Real.exp_le_exp.mpr (by linarith only [h])

/-- **The Step-6 floor, in ratio form.**  `C₁ ≥ 4 C_iter (k+1)/log 3` gives `C₁⁻¹
C_iter ≤ (log 3)/4`, which is the whole content of the step's displayed
computation.  The `(k+1)` factor is pure slack for THIS display (it is what
Step 5 needs when it absorbs `exp(C(k + |𝓑|))`); it is kept verbatim. -/
theorem stepSixRatio_le_of_floor {C1 Citer : ℝ} {k : ℕ} (hC1 : 0 < C1)
    (hCiter : 0 ≤ Citer)
    (hfloor : 4 * Citer * ((k : ℝ) + 1) / Real.log 3 ≤ C1) :
    C1⁻¹ * Citer ≤ Real.log 3 / 4 := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h1 : 4 * Citer * ((k : ℝ) + 1) ≤ C1 * Real.log 3 :=
    (div_le_iff₀ hlog).mp hfloor
  have h2 : 0 ≤ 4 * Citer * (k : ℝ) :=
    mul_nonneg (by linarith only [hCiter]) (Nat.cast_nonneg k)
  have h3 : 4 * Citer ≤ C1 * Real.log 3 := by linarith only [h1, h2]
  have h4 : C1⁻¹ * Citer ≤ C1⁻¹ * (C1 * Real.log 3 / 4) :=
    mul_le_mul_of_nonneg_left (by linarith only [h3]) (le_of_lt (inv_pos.mpr hC1))
  have h5 : C1⁻¹ * (C1 * Real.log 3 / 4) = Real.log 3 / 4 := by
    field_simp
  linarith only [h4, h5]

/-! ## 2. The step's own computation: the sharp `1/4` -/

/-- ```text
   exp( C₁⁻¹ C_iter t )  ≤  3^{(1/4) t}          for every  t ≥ 0 .
```

Here `t` is the source's `(1-α)(m-n)`; the statement is uniform in `t ≥ 0`.
This is the sharp form. -/
theorem exp_le_rpow_three_quarter_of_step6_floor {C1 Citer t : ℝ} {k : ℕ}
    (hC1 : 0 < C1) (hCiter : 0 ≤ Citer) (ht : 0 ≤ t)
    (hfloor : 4 * Citer * ((k : ℝ) + 1) / Real.log 3 ≤ C1) :
    Real.exp (C1⁻¹ * Citer * t) ≤ Real.rpow (3 : ℝ) (1 / 4 * t) := by
  refine exp_le_rpow_three_of_le_mul_log ?_
  have hr := stepSixRatio_le_of_floor hC1 hCiter hfloor
  have hmul := mul_le_mul_of_nonneg_right hr ht
  linarith only [hmul]

/-- `3^{(1/4)t} ≤ 3^{(1/2)t}` for `t ≥ 0` — the exact slack measures between Step
6's own computation and the exponent `e.oscillation.Holder.bound` is printed
at. -/
theorem rpow_three_quarter_le_rpow_three_half {t : ℝ} (ht : 0 ≤ t) :
    Real.rpow (3 : ℝ) (1 / 4 * t) ≤ Real.rpow (3 : ℝ) (1 / 2 * t) :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [ht])

/-- The Step-6 exponent argument `t := (1-α)(m-n)`. -/
def stepSixExponent (alpha : ℝ) (n m : ℤ) : ℝ := (1 - alpha) * ((m : ℝ) - (n : ℝ))

/-- `0 ≤ (1-α)(m-n)` in the Step-1/Step-3 regime (`α ≤ 1`, `n ≤ m`). -/
theorem stepSixExponent_nonneg {alpha : ℝ} {n m : ℤ} (halpha : alpha ≤ 1)
    (hnm : n ≤ m) : 0 ≤ stepSixExponent alpha n m := by
  have hn : ((n : ℝ)) ≤ ((m : ℝ)) := Int.cast_le.mpr hnm
  exact mul_nonneg (by linarith only [halpha]) (by linarith only [hn])

/-- **Step 6 at the Step-1 `C₁`, sharp**: the floor is discharged by
`step6_le_stepOneC1`, so no largeness hypothesis is carried. -/
theorem exp_stepOneC1_le_rpow_three_quarter (d : ℕ) {Cedos Cann Citer alpha : ℝ}
    {k : ℕ} {n m : ℤ} (hCiter : 0 ≤ Citer) (halpha : alpha ≤ 1) (hnm : n ≤ m) :
    Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer * stepSixExponent alpha n m) ≤
      Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) :=
  exp_le_rpow_three_quarter_of_step6_floor (stepOneC1_pos d Cedos Cann Citer k) hCiter
    (stepSixExponent_nonneg halpha hnm) (step6_le_stepOneC1 d Cedos Cann Citer k)

theorem exp_stepOneC1_le_rpow_three_half (d : ℕ) {Cedos Cann Citer alpha : ℝ}
    {k : ℕ} {n m : ℤ} (hCiter : 0 ≤ Citer) (halpha : alpha ≤ 1) (hnm : n ≤ m) :
    Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer * stepSixExponent alpha n m) ≤
      Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) :=
  le_trans (exp_stepOneC1_le_rpow_three_quarter d hCiter halpha hnm)
    (rpow_three_quarter_le_rpow_three_half (stepSixExponent_nonneg halpha hnm))

/-! ## 4. The composition into `e.oscillation.Holder.bound`'s shape -/

/-- The scalar core of the prefactor replacement, with NO transcendental atom in
sight: `E` is the exponential and `R` the power of `3`, both abstract reals. -/
private theorem holder_compose_aux {C E R oscLo oscHi dataG dataH : ℝ}
    (hC : 0 ≤ C) (hE : 0 ≤ E) (hER : E ≤ R) (hoscHi : 0 ≤ oscHi)
    (hdataG : 0 ≤ dataG) (hdataH : 0 ≤ dataH)
    (hiter : oscLo ≤ C * E * (oscHi + C * dataG) + C * E * dataH) :
    oscLo ≤ (C + C * C) * R * oscHi + (C + C * C) * R * (dataG + dataH) := by
  have hR : 0 ≤ R := le_trans hE hER
  have hCE : C * E ≤ C * R := mul_le_mul_of_nonneg_left hER hC
  have h2 : C * E * oscHi ≤ C * R * oscHi := mul_le_mul_of_nonneg_right hCE hoscHi
  have h3 : C * E * (C * dataG) ≤ C * R * (C * dataG) :=
    mul_le_mul_of_nonneg_right hCE (mul_nonneg hC hdataG)
  have h4 : C * E * dataH ≤ C * R * dataH := mul_le_mul_of_nonneg_right hCE hdataH
  have p1 : 0 ≤ C * C * R * oscHi :=
    mul_nonneg (mul_nonneg (mul_nonneg hC hC) hR) hoscHi
  have p2 : 0 ≤ C * R * dataG := mul_nonneg (mul_nonneg hC hR) hdataG
  have p3 : 0 ≤ C * C * R * dataH :=
    mul_nonneg (mul_nonneg (mul_nonneg hC hC) hR) hdataH
  linarith only [hiter, h2, h3, h4, p1, p2, p3]

/-- **`e.oscillation.Holder.bound` from `e.oscillation.iteration.result`**, as
printed: the exponential prefactor is replaced by `3^{(1/2)(1-α)(m-n)}` and the
inner constant is distributed.

`oscLo`, `oscHi`, `dataG`, `dataH` are the four real quantities named in the
module docstring.  The produced constant is `C + C²` (deviation D2). -/
theorem holderBound_of_iterationResult {C P t oscLo oscHi dataG dataH : ℝ}
    (hC : 0 ≤ C) (hoscHi : 0 ≤ oscHi) (hdataG : 0 ≤ dataG) (hdataH : 0 ≤ dataH)
    (hP : Real.exp P ≤ Real.rpow (3 : ℝ) t)
    (hiter : oscLo ≤ C * Real.exp P * (oscHi + C * dataG) + C * Real.exp P * dataH) :
    oscLo ≤ (C + C * C) * Real.rpow (3 : ℝ) t * oscHi +
      (C + C * C) * Real.rpow (3 : ℝ) t * (dataG + dataH) :=
  holder_compose_aux hC (Real.exp_pos P).le hP hoscHi hdataG hdataH hiter

/-- **`t.regularity` Step 6, assembled at the Step-1 `C₁` — the printed
exponent.**

From `e.oscillation.iteration.result` at the prefactor `C exp(C₁⁻¹ C_iter
(1-α)(m-n))`, Step 6 delivers `e.oscillation.Holder.bound` at
`3^{(1/2)(1-α)(m-n)}`.  The floor is discharged inside (`step6_le_stepOneC1`),
so the only hypotheses are the regime (`α ≤ 1`, `n ≤ m`), the constants' signs,
and the three nonnegativity facts of the transported quantities. -/
theorem oscillationHolderBound_of_iterationResult (d : ℕ)
    {Cedos Cann Citer C alpha : ℝ} {k : ℕ} {n m : ℤ}
    {oscLo oscHi dataG dataH : ℝ} (hC : 0 ≤ C) (hCiter : 0 ≤ Citer)
    (halpha : alpha ≤ 1) (hnm : n ≤ m) (hoscHi : 0 ≤ oscHi) (hdataG : 0 ≤ dataG)
    (hdataH : 0 ≤ dataH)
    (hiter : oscLo ≤
        C * Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer *
            stepSixExponent alpha n m) * (oscHi + C * dataG) +
          C * Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer *
            stepSixExponent alpha n m) * dataH) :
    oscLo ≤
      (C + C * C) * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * oscHi +
        (C + C * C) * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
          (dataG + dataH) :=
  holderBound_of_iterationResult hC hoscHi hdataG hdataH
    (exp_stepOneC1_le_rpow_three_half d hCiter halpha hnm) hiter

end

end Algsuperdiff.Section4.Provider.Regularity
