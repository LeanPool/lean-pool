/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Scales.RpowThreshold
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.InductionState
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Disorder.CstarUpperBound

/-!
# ShellNormalization

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
Binder descriptions below are an informal inventory only, NOT a source
certification; certification vocabulary is reserved for frozen source-facing
declarations.

# The deterministic normalization arithmetic of `e.nablaw.in.L.eight`

ABK26's display `e.nablaw.in.L.eight` is a three-line chain.  After the
Calderon-Zygmund step and the fresh-shell `L^8` estimate `e.km.kn.Lp`, the
manuscript's *last* inequality reads

```
  C shom_{m-h}^{-2} h 3^{2 gamma m}
    + O_{Gamma_1}( C shom_{m-h}^{-2} 3^{2 gamma m} h 3^{-(K-m) d / 8} )
  <=  C + O_{Gamma_1}( gamma^100 ) .
```

This module proves the two purely deterministic facts that this last line
consists of, in the exact shape in which the recurrence uses them.

* `inv_sigmaBarSq_mul_shellWidth_le` is the **deterministic head**: under the
  induction state `d.mathcalS.def` and the recurrence's own shell-width
  constraint `h <= 6 cstar gamma^{-1}`, the normalized quantity
  `shom_{m-h}^{-2} h 3^{2 gamma m}` is bounded by an **absolute** constant `24
  * 3^18`.  Only the lower half of `e.shom.h.bounds` and the absolute bound
  `cstar <= 3/2` are used.

* `rpow_gap_le_gammaPow_mul_spare` is the **fluctuation amplitude**: for `d >=
  2`, `gamma <= 1/4` and a scale gap `G >= 10^10 gamma^{-1}` (the manuscript's
  `e.recurrence.params`), the Calderon-Zygmund decay factor `3^{-(d/8) G}` is
  below `gamma^100` *with an exponentially large factor to spare*.  The spare
  factor is what absorbs the dimension-only constant, i.e. it is the
  quantitative content of "increasing `M` in `e.cgamma.constraints`, if
  necessary".

Putting the two together bounds the whole `O_{Gamma_1}` amplitude of the middle
line by `gamma^100`, with **no** smallness assumption on `gamma` beyond the
standing `gamma <= 1/4`: it is the case `C = 24 * 3^18` of
`const_mul_rpow_gap_le_gammaPow` below, whose smallness hypothesis holds there
because `24 * 3^18 <= 3^21` is already swallowed by the spare factor.  The
composition itself is the consumer's, and is not performed here.

* `const_mul_rpow_gap_le_gammaPow` carries an arbitrary nonnegative prefactor
  `C` (the dimension-only constant produced by Calderon-Zygmund and by
  `e.km.kn.Lp`) under the explicit smallness hypothesis
  `C <= 3^(10^9 / gamma)`, and `exists_gamma_threshold_for_gap_constant` shows
  that every `C` satisfies that hypothesis once `gamma` is small.  Together
  they are the machine-checked form of the manuscript's parenthetical
  "increasing `M` in `e.cgamma.constraints`, if necessary".

## Public binder audit

`M : ABKModel d` is standing data and `d` is implicit typing data.  `hS:
inductionState M m0 E` is the source induction hypothesis (`d.mathcalS.def`),
`hm : m - h <= m0` is its scale range, `hh` is the recurrence's own shell-width
constraint, and `hK` is `e.recurrence.params`.  No proof step is a binder: no
Calderon-Zygmund estimate, no corrector bound, and no oscillation estimate
appears as a hypothesis.

## References

* ABK26, `e.nablaw.in.L.eight`.
* ABK26, `d.mathcalS.def` / `e.shom.h.bounds`.
* ABK26, `l.approximate.recurrence.formula` (the constraints `h <= 6 cstar
  gamma^{-1}` and `K >= m + 10^10 gamma^{-1}`).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## An elementary logarithmic bound -/

/-- `1 <= log 3`. -/
private theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  have h : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
  linarith

/-! ## The deterministic head -/

/-- **The deterministic head of `e.nablaw.in.L.eight`.**

Under the induction state `d.mathcalS.def` and the recurrence's shell-width
constraint `h <= 6 cstar gamma^{-1}`, the normalization factor of the fresh
shell obeys

```
  shom_{m-h}^{-2} * h * 3^{2 gamma m}  <=  24 * 3^18 .
```

The constant is absolute: it depends on neither the dimension nor any model
parameter.  Only the lower branch of `e.shom.h.bounds` and the absolute bound
`cstar <= 3/2` enter. -/
theorem inv_sigmaBarSq_mul_shellWidth_le
    (M : ABKModel d) {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E)
    {m : ℤ} {h : ℕ} (hm : m - (h : ℤ) ≤ m0)
    (hh : (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹) :
    ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ) ^ 2)⁻¹ * (h : ℝ) *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) ≤ 24 * (3 : ℝ) ^ (18 : ℝ) := by
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hcstar : 0 < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcstar' : Disorder.cstar M ≤ 3 / 2 := Provider.Disorder.cstar_le_three_halves M
  have hsigma : 0 < (Annealed.sigmaBar M (m - (h : ℤ)) : ℝ) :=
    (Annealed.sigmaBar_characterization M (m - (h : ℤ))).1
  have hsigmaSq : 0 < (Annealed.sigmaBar M (m - (h : ℤ)) : ℝ) ^ 2 := by positivity
  set A : ℝ := (3 : ℝ) ^ (2 * M.gamma * ((m : ℝ) - (h : ℝ))) with hAdef
  have hApos : (0 : ℝ) < A := Real.rpow_pos_of_pos (by norm_num) _
  set T : ℝ := (3 : ℝ) ^ (2 * M.gamma * (h : ℝ)) with hTdef
  have hTpos : (0 : ℝ) < T := Real.rpow_pos_of_pos (by norm_num) _
  -- the lower branch of `e.shom.h.bounds`
  have hlow0 := (hS.1 (m - (h : ℤ)) hm).1
  have hlow : (1 / 4 : ℝ) * (Disorder.cstar M * M.gamma⁻¹ * A) ≤
      (Annealed.sigmaBar M (m - (h : ℤ)) : ℝ) ^ 2 := by
    refine le_trans ?_ hlow0
    have hcast : ((m - (h : ℤ) : ℤ) : ℝ) = (m : ℝ) - (h : ℝ) := by push_cast; ring
    rw [hcast]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
  -- the scale split `3^{2 gamma m} = A * T`
  have hsplit : (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) = A * T := by
    rw [hAdef, hTdef, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    ring_nf
  -- the shell-width constraint in multiplied form
  have hwidth : M.gamma * (h : ℝ) ≤ 6 * Disorder.cstar M := by
    have := mul_le_mul_of_nonneg_left hh hgamma.le
    calc M.gamma * (h : ℝ) ≤ M.gamma * (6 * Disorder.cstar M * M.gamma⁻¹) := this
      _ = 6 * Disorder.cstar M := by field_simp
  have hT : T ≤ (3 : ℝ) ^ (18 : ℝ) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    nlinarith [hwidth, hcstar']
  -- the core inequality after clearing `shom^2`
  have hcore : (h : ℝ) * ((3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ≤
      24 * (3 : ℝ) ^ (18 : ℝ) *
        ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ) ^ 2) := by
    have hconst : (0 : ℝ) < 24 * (3 : ℝ) ^ (18 : ℝ) := by
      have : (0 : ℝ) < (3 : ℝ) ^ (18 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
      linarith
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hlow hconst.le)
    rw [hsplit]
    have hstep : (h : ℝ) * T ≤ 6 * (3 : ℝ) ^ (18 : ℝ) * Disorder.cstar M * M.gamma⁻¹ := by
      have hhnn : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
      have h1 : (h : ℝ) * T ≤ (6 * Disorder.cstar M * M.gamma⁻¹) * ((3 : ℝ) ^ (18 : ℝ)) :=
        mul_le_mul hh hT hTpos.le
          (by positivity)
      calc (h : ℝ) * T ≤ (6 * Disorder.cstar M * M.gamma⁻¹) * ((3 : ℝ) ^ (18 : ℝ)) := h1
        _ = 6 * (3 : ℝ) ^ (18 : ℝ) * Disorder.cstar M * M.gamma⁻¹ := by ring
    have hA' : (0 : ℝ) ≤ A := hApos.le
    calc (h : ℝ) * (A * T) = ((h : ℝ) * T) * A := by ring
      _ ≤ (6 * (3 : ℝ) ^ (18 : ℝ) * Disorder.cstar M * M.gamma⁻¹) * A :=
          mul_le_mul_of_nonneg_right hstep hA'
      _ = 24 * (3 : ℝ) ^ (18 : ℝ) *
            ((1 / 4 : ℝ) * (Disorder.cstar M * M.gamma⁻¹ * A)) := by ring
  calc ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ) ^ 2)⁻¹ * (h : ℝ) *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))
      = ((h : ℝ) * ((3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))) /
          ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ) ^ 2) := by
        field_simp
    _ ≤ 24 * (3 : ℝ) ^ (18 : ℝ) := by
        rw [div_le_iff₀ hsigmaSq]
        exact hcore

/-! ## The fluctuation amplitude -/

/-- **The Calderon-Zygmund gap factor of `e.nablaw.in.L.eight`.**

For `d >= 2`, `0 < gamma <= 1/4` and a scale gap `G >= 10^10 gamma^{-1}` (the
manuscript's `e.recurrence.params`), the decay factor of the middle line of
`e.nablaw.in.L.eight` satisfies

```
  3^{-(d/8) G}  <=  gamma^100 * 3^{-10^9 / gamma} .
```

The trailing factor is the room left over for the dimension-only constants: it
is the quantitative form of the manuscript's "increasing `M` in
`e.cgamma.constraints`, if necessary". -/
theorem rpow_gap_le_gammaPow_mul_spare
    {gamma G : ℝ} (hgamma : 0 < gamma) (hquarter : gamma ≤ 1 / 4)
    (hd : 2 ≤ d) (hG : (10 : ℝ) ^ (10 : ℕ) * gamma⁻¹ ≤ G) :
    (3 : ℝ) ^ (-((d : ℝ) / 8) * G) ≤
      gamma ^ (100 : ℕ) * (3 : ℝ) ^ (-((10 : ℝ) ^ (9 : ℕ)) * gamma⁻¹) := by
  set t : ℝ := gamma⁻¹ with htdef
  have ht4 : (4 : ℝ) ≤ t := by
    rw [htdef]
    rw [le_inv_comm₀ (by norm_num) hgamma]
    linarith
  have htpos : (0 : ℝ) < t := by linarith
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hGpos : (0 : ℝ) < G := by
    have : (0 : ℝ) < (10 : ℝ) ^ (10 : ℕ) * t := by positivity
    linarith
  -- Step 1: the exponent comparison
  have hexp : -((d : ℝ) / 8) * G ≤ -((25 : ℝ) * 10 ^ (8 : ℕ)) * t := by
    have hkey : (25 : ℝ) * 10 ^ (8 : ℕ) * t ≤ (d : ℝ) / 8 * G := by
      have h1 : (1 / 4 : ℝ) * ((10 : ℝ) ^ (10 : ℕ) * t) ≤ (d : ℝ) / 8 * G := by
        have hmono : (1 / 4 : ℝ) ≤ (d : ℝ) / 8 := by linarith
        have := mul_le_mul hmono hG (by positivity) (by linarith)
        linarith [this]
      nlinarith [h1]
    linarith
  have hstep1 : (3 : ℝ) ^ (-((d : ℝ) / 8) * G) ≤
      (3 : ℝ) ^ (-((25 : ℝ) * 10 ^ (8 : ℕ)) * t) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  -- Step 2: split the spare factor off
  have hsplit : (3 : ℝ) ^ (-((25 : ℝ) * 10 ^ (8 : ℕ)) * t) =
      (3 : ℝ) ^ (-((15 : ℝ) * 10 ^ (8 : ℕ)) * t) *
        (3 : ℝ) ^ (-((10 : ℝ) ^ (9 : ℕ)) * t) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    ring_nf
  -- Step 3: the polynomial-beats-exponential estimate
  have hpoly : (3 : ℝ) ^ (-((15 : ℝ) * 10 ^ (8 : ℕ)) * t) ≤ gamma ^ (100 : ℕ) := by
    have hgpow : (0 : ℝ) < gamma ^ (100 : ℕ) := by positivity
    have hlhs : (0 : ℝ) < (3 : ℝ) ^ (-((15 : ℝ) * 10 ^ (8 : ℕ)) * t) :=
      Real.rpow_pos_of_pos (by norm_num) _
    rw [← Real.exp_log hlhs, ← Real.exp_log hgpow]
    refine Real.exp_le_exp.mpr ?_
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 3), Real.log_pow]
    have hloggamma : Real.log gamma = -Real.log t := by
      rw [htdef, Real.log_inv, neg_neg]
    rw [hloggamma]
    have hlogt : Real.log t ≤ t := by
      have := Real.log_le_sub_one_of_pos htpos
      linarith
    have hlogtnn : (0 : ℝ) ≤ Real.log t :=
      Real.log_nonneg (by linarith)
    have hmul : t * 1 ≤ t * Real.log 3 :=
      mul_le_mul_of_nonneg_left one_le_log_three htpos.le
    push_cast
    nlinarith [hlogt, hlogtnn, htpos, hmul]
  calc (3 : ℝ) ^ (-((d : ℝ) / 8) * G)
      ≤ (3 : ℝ) ^ (-((25 : ℝ) * 10 ^ (8 : ℕ)) * t) := hstep1
    _ = (3 : ℝ) ^ (-((15 : ℝ) * 10 ^ (8 : ℕ)) * t) *
          (3 : ℝ) ^ (-((10 : ℝ) ^ (9 : ℕ)) * t) := hsplit
    _ ≤ gamma ^ (100 : ℕ) * (3 : ℝ) ^ (-((10 : ℝ) ^ (9 : ℕ)) * t) :=
        mul_le_mul_of_nonneg_right hpoly (Real.rpow_pos_of_pos (by norm_num) _).le

/-- **The gap factor with a dimension-only prefactor.**

The form in which `e.nablaw.in.L.eight` actually needs the previous estimate:
once `gamma` is small enough that the dimension-only constant `C` produced by
Calderon-Zygmund and by `e.km.kn.Lp` is below the spare factor
`3^(10^9 / gamma)`, the whole prefactored decay term is below `gamma^100`. -/
theorem const_mul_rpow_gap_le_gammaPow
    {C gamma G : ℝ} (hCnonneg : 0 ≤ C) (hgamma : 0 < gamma)
    (hquarter : gamma ≤ 1 / 4) (hd : 2 ≤ d)
    (hG : (10 : ℝ) ^ (10 : ℕ) * gamma⁻¹ ≤ G)
    (hCsmall : C ≤ (3 : ℝ) ^ ((10 : ℝ) ^ (9 : ℕ) * gamma⁻¹)) :
    C * (3 : ℝ) ^ (-((d : ℝ) / 8) * G) ≤ gamma ^ (100 : ℕ) := by
  have hgap := rpow_gap_le_gammaPow_mul_spare (d := d) hgamma hquarter hd hG
  have hsparepos : (0 : ℝ) < (3 : ℝ) ^ ((10 : ℝ) ^ (9 : ℕ) * gamma⁻¹) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hinv : (3 : ℝ) ^ (-((10 : ℝ) ^ (9 : ℕ)) * gamma⁻¹) =
      ((3 : ℝ) ^ ((10 : ℝ) ^ (9 : ℕ) * gamma⁻¹))⁻¹ := by
    rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
    ring_nf
  have habsorb : C * (3 : ℝ) ^ (-((10 : ℝ) ^ (9 : ℕ)) * gamma⁻¹) ≤ 1 := by
    rw [hinv, mul_inv_le_iff₀ hsparepos, one_mul]
    exact hCsmall
  calc C * (3 : ℝ) ^ (-((d : ℝ) / 8) * G)
      ≤ C * (gamma ^ (100 : ℕ) *
          (3 : ℝ) ^ (-((10 : ℝ) ^ (9 : ℕ)) * gamma⁻¹)) :=
        mul_le_mul_of_nonneg_left hgap hCnonneg
    _ = (C * (3 : ℝ) ^ (-((10 : ℝ) ^ (9 : ℕ)) * gamma⁻¹)) * gamma ^ (100 : ℕ) := by
        ring
    _ ≤ 1 * gamma ^ (100 : ℕ) :=
        mul_le_mul_of_nonneg_right habsorb (by positivity)
    _ = gamma ^ (100 : ℕ) := one_mul _

/-- **"Increasing `M` in `e.cgamma.constraints`, if necessary".**

For every constant `C` there is a positive threshold below which the smallness
hypothesis of `const_mul_rpow_gap_le_gammaPow` holds.  Together with the
previous theorem this makes the manuscript's parenthetical quantitative: no
matter which dimension-only constant the Calderon-Zygmund step and
`e.km.kn.Lp` produce, the fluctuation amplitude of `e.nablaw.in.L.eight` is
below `gamma^100` once `gamma` is small. -/
theorem exists_gamma_threshold_for_gap_constant (C : ℝ) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
      ∀ gamma : ℝ, 0 < gamma → gamma ≤ gamma0 →
        C ≤ (3 : ℝ) ^ ((10 : ℝ) ^ (9 : ℕ) * gamma⁻¹) := by
  exact Algsuperdiff.exists_rpow_inverse_threshold (b := 3) (a := (10 : ℝ) ^ (9 : ℕ))
    (cap := 1 / 4) (C := C) (by norm_num) (by norm_num) (by norm_num)

end

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
