/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationGammaFold
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationNumericEllipticity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Disorder.CstarUpperBound

/-!
# LocalizationFluctuationSplitFoldArithmetic

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The regime arithmetic of the Step-2 annealed Hoelder fold

## The discrepancy this module settles
 ABK26 quotes the ellipticity moment of the annealed Hoelder fold as `C
 cgamma^{-1}`.
The proved producer

```
  LocalizationFluctuationNumericEllipticity.
    integral_gaugedEllipticitySum_pow_four_ancestorAtScale_le
```

delivers instead

```
  E[ (gauged ellipticity sum)^4 ]  <=  ( C * cstar^{-1} * cgamma^{-1} )^4 ,
```

Since `cstar` is a property of the model and not an absolute constant, the
extra factor cannot simply be folded into the `c1`, `c2` of
`LocalizationFluctuationGammaFold.exists_gamma_threshold_holder_fold`: those
must be **uniform in the model**, otherwise the produced `gamma`-threshold
would depend on `M` and the closure's `∀ M` quantifier would be violated.

## The resolution, and the exact cost

The manuscript's own standing regime supplies the two facts that absorb it.  At
one admissible pair `(n, n+h)` the closure reads

* `C * (cstar M)^{-1} <= E` --- the largeness gate, at a threshold `C` the
  *producer* names (`ClosureRegime`'s third clause), and
* `cgamma <= E^{-5}` --- the induction parameter's own smallness
  (`ClosureRegime`'s fourth clause), with `1 <= E`.

Together, `E <= cgamma^{-1/5} <= cgamma^{-1}`, hence

```
  C * cstar^{-1} * cgamma^{-1}  <=  E * cgamma^{-1}  <=  cgamma^{-2} .
```

So the ellipticity leg of the fold costs **`cgamma^{-2}`, not the printed
`cgamma^{-1}`**: exactly one extra power of `cgamma`.  The fold's printed margin
is three powers (`cgamma^{-1} * cgamma^{14} = cgamma^{13}` against the target
`cgamma^{10}`), so one extra power is affordable, and the numerical obligation
moves from `c1 cgamma^13 + c2 cgamma^27 <= cgamma^10` to

```
  c1 cgamma^12 + c2 cgamma^24 <= cgamma^10 ,
```

which `exists_gamma_threshold_regime_holder_fold` discharges for every pair of
nonnegative *absolute* constants once `cgamma` is small.  **The absorption does
not fail**; the only change is the pair of numerals, and both are still strictly
above `10`.

`gammaRegime_ellipticityLeg_pow_four_le` records the same statement at the
fourth power, which is the shape the `L^4` leg of
`LocalizationFluctuationGammaFold.integral_mul_mul_le_L4_L4_L2` consumes.

## The regime also supplies the ellipticity producer's own premises

`integral_gaugedEllipticitySum_pow_four_ancestorAtScale_le` asks for `max (exp
(2 C)) (cstar M)^{-1} <= E` and `E <= cgamma^{-1/5}`.  Both come from the same
two regime clauses once the producer's threshold is chosen large enough:
`gammaRegime_E_le_rpow_neg_fifth` is the second, and `gammaRegime_max_exp_le`
is the first, using the proved absolute cap
`Provider.Disorder.cstar_le_three_halves` to convert the *product* gate `C'
cstar^{-1} <= E` into the *plain* gate `exp (2 C) <= E`.  The threshold
`regimeEllipticityConst C` produced here is the value a consumer must pass as
the `Csplit` of the split input.

Nothing below is a source display: this module is arithmetic, and it is
deliberately separated from the fold assembly so that the numerals above can be
verified on their own.

## Binders

Every statement is real arithmetic under the regime's own clauses (`1 <= E`, `0
< cgamma`, the two gates) plus, where stated, the proved positivity and
absolute cap of `cstar`.  No smallness gate is assumed: the two
`gamma`-thresholds are **produced**.  Nothing about the corrector, the
coefficient field or the sample space occurs.

## Scope

There is no `sorry`, no `admit`, no custom axiom and no `set_option
maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2,
  `e.lower.bound.localization.terms`, `e.cg.ellip.upper`,
  `e.recurrence.params`, `e.cgamma.constraints`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3

noncomputable section

/-! ## The induction parameter under the regime's smallness clause -/

/-- on `1 <= E` and `0 < cgamma`; both are standing. -/
theorem gammaRegime_E_le_rpow_neg_fifth {E gamma : ℝ} (hE : 1 ≤ E) (hgamma : 0 < gamma)
    (hsmall : gamma ≤ E ^ (-5 : ℤ)) : E ≤ gamma ^ (-(1 / 5 : ℝ)) := by
  have hE0 : (0 : ℝ) < E := lt_of_lt_of_le zero_lt_one hE
  have hE5 : (0 : ℝ) < E ^ (5 : ℕ) := by positivity
  -- `gamma <= E^{-5}` is `E^5 <= gamma^{-1}`
  have hzpow : E ^ (-5 : ℤ) = (E ^ (5 : ℕ))⁻¹ := by
    rw [show (-5 : ℤ) = -((5 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
  rw [hzpow] at hsmall
  have hE5le : E ^ (5 : ℕ) ≤ gamma⁻¹ := (le_inv_comm₀ hE5 hgamma).mpr hsmall
  have hEeq : (E ^ (5 : ℕ)) ^ ((1 : ℝ) / 5) = E := by
    rw [← Real.rpow_natCast E 5, ← Real.rpow_mul hE0.le]
    norm_num
  have hinvrpow : (gamma⁻¹) ^ ((1 : ℝ) / 5) = gamma ^ (-(1 / 5 : ℝ)) := by
    rw [Real.inv_rpow hgamma.le, ← Real.rpow_neg hgamma.le]
  calc E = (E ^ (5 : ℕ)) ^ ((1 : ℝ) / 5) := hEeq.symm
    _ ≤ (gamma⁻¹) ^ ((1 : ℝ) / 5) :=
        Real.rpow_le_rpow (by positivity) hE5le (by norm_num)
    _ = gamma ^ (-(1 / 5 : ℝ)) := hinvrpow

/-- **`E <= cgamma^{-1}`.**  The crude form of the previous statement, which is
all the fold arithmetic needs.

Conditional on `1 <= E`, `0 < cgamma` and the regime's smallness clause. -/
theorem gammaRegime_E_le_inv {E gamma : ℝ} (hE : 1 ≤ E) (hgamma : 0 < gamma)
    (hsmall : gamma ≤ E ^ (-5 : ℤ)) : E ≤ gamma⁻¹ := by
  have hE5 : (0 : ℝ) < E ^ (5 : ℕ) := by positivity
  have hzpow : E ^ (-5 : ℤ) = (E ^ (5 : ℕ))⁻¹ := by
    rw [show (-5 : ℤ) = -((5 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
  rw [hzpow] at hsmall
  have hE5le : E ^ (5 : ℕ) ≤ gamma⁻¹ := (le_inv_comm₀ hE5 hgamma).mpr hsmall
  have hEle : E ≤ E ^ (5 : ℕ) := by
    calc E = E ^ (1 : ℕ) := (pow_one E).symm
      _ ≤ E ^ (5 : ℕ) := pow_le_pow_right₀ hE (by norm_num)
  linarith [hEle, hE5le]

/-! ## The `cstar^{-1}` absorption -/

/-- **The ellipticity leg of the fold costs `cgamma^{-2}`.**

This is the exact statement whose failure would break the fold; it does not
fail.

Conditional on `1 <= E`, `0 < cgamma` and the two regime gates. -/
theorem gammaRegime_ellipticityLeg_le {C cstarM E gamma : ℝ}
    (hE : 1 ≤ E) (hgamma : 0 < gamma)
    (hlarge : C * cstarM⁻¹ ≤ E) (hsmall : gamma ≤ E ^ (-5 : ℤ)) :
    C * cstarM⁻¹ * gamma⁻¹ ≤ (gamma ^ (2 : ℕ))⁻¹ := by
  have hEinv : E ≤ gamma⁻¹ := gammaRegime_E_le_inv hE hgamma hsmall
  have hginv0 : (0 : ℝ) < gamma⁻¹ := inv_pos.2 hgamma
  have hstep : C * cstarM⁻¹ * gamma⁻¹ ≤ E * gamma⁻¹ :=
    mul_le_mul_of_nonneg_right hlarge hginv0.le
  have hstep2 : E * gamma⁻¹ ≤ gamma⁻¹ * gamma⁻¹ :=
    mul_le_mul_of_nonneg_right hEinv hginv0.le
  have hsq : (gamma ^ (2 : ℕ))⁻¹ = gamma⁻¹ * gamma⁻¹ := by
    rw [pow_two, mul_inv]
  rw [hsq]
  linarith [hstep, hstep2]

/-- The fourth power of the previous statement, in the shape the `L^4` leg of
`LocalizationFluctuationGammaFold.integral_mul_mul_le_L4_L4_L2` consumes:

```
  E[ (gauged ellipticity sum)^4 ]  <=  ( C cstar^{-1} cgamma^{-1} )^4
                                   <=  ( cgamma^8 )^{-1} .
```

exactly as `gammaRegime_ellipticityLeg_le`, plus `0 <= C`. -/
theorem gammaRegime_ellipticityLeg_pow_four_le {C cstarM E gamma : ℝ} (hC : 0 ≤ C)
    (hcstar : 0 < cstarM) (hE : 1 ≤ E) (hgamma : 0 < gamma)
    (hlarge : C * cstarM⁻¹ ≤ E) (hsmall : gamma ≤ E ^ (-5 : ℤ)) :
    (C * cstarM⁻¹ * gamma⁻¹) ^ (4 : ℕ) ≤ (gamma ^ (8 : ℕ))⁻¹ := by
  have hbase := gammaRegime_ellipticityLeg_le hE hgamma hlarge hsmall
  have hcinv : (0 : ℝ) ≤ cstarM⁻¹ := (inv_pos.2 hcstar).le
  have hginv : (0 : ℝ) ≤ gamma⁻¹ := (inv_pos.2 hgamma).le
  have hnn : (0 : ℝ) ≤ C * cstarM⁻¹ * gamma⁻¹ := by positivity
  have hpow : (C * cstarM⁻¹ * gamma⁻¹) ^ (4 : ℕ) ≤ ((gamma ^ (2 : ℕ))⁻¹) ^ (4 : ℕ) :=
    pow_le_pow_left₀ hnn hbase 4
  have heq : ((gamma ^ (2 : ℕ))⁻¹) ^ (4 : ℕ) = (gamma ^ (8 : ℕ))⁻¹ := by
    rw [← inv_pow, ← pow_mul, inv_pow]
  rwa [heq] at hpow

/-! ## The numerical obligation -/

/-- **The annealed Hoelder fold at the regime exponents.**
 ABK26 combines the ellipticity moment, the load moment `C` and the oscillation
moment `C cgamma^{14}`.  With the ellipticity leg at `cgamma^{-2}`
(`gammaRegime_ellipticityLeg_le`) rather than the printed `cgamma^{-1}`, the
cross term is `c1 cgamma^{12}` and the quadratic term `c2 cgamma^{24}`; their
sum is below `cgamma^{10}` for every pair of nonnegative constants once
`cgamma` is small.

This is `LocalizationFluctuationGammaFold.exists_gamma_threshold_holder_fold`
with its numerals `(13, 27)` replaced by `(12, 24)`; both are still strictly
above `10`, which is the whole content.  The threshold is **produced**, not
assumed. -/
theorem exists_gamma_threshold_regime_holder_fold (c1 c2 : ℝ) (hc1 : 0 ≤ c1)
    (hc2 : 0 ≤ c2) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
      ∀ gamma : ℝ, 0 < gamma → gamma ≤ gamma0 →
        c1 * gamma ^ (12 : ℕ) + c2 * gamma ^ (24 : ℕ) ≤ gamma ^ (10 : ℕ) := by
  refine ⟨min (1 / 4) (1 / (c1 + c2 + 1)), ?_, min_le_left _ _, ?_⟩
  · have hpos : (0 : ℝ) < 1 / (c1 + c2 + 1) := by positivity
    exact lt_min (by norm_num) hpos
  · intro gamma hgamma hle
    have hq : gamma ≤ 1 / 4 := hle.trans (min_le_left _ _)
    have hsmall : gamma ≤ 1 / (c1 + c2 + 1) := hle.trans (min_le_right _ _)
    have hden : (0 : ℝ) < c1 + c2 + 1 := by linarith
    have hsq : gamma ^ (2 : ℕ) ≤ gamma := by nlinarith [hgamma, hq]
    have habs : (c1 + c2) * gamma ^ (2 : ℕ) ≤ 1 := by
      have h1 : (c1 + c2) * gamma ^ (2 : ℕ) ≤ (c1 + c2) * gamma :=
        mul_le_mul_of_nonneg_left hsq (by linarith)
      have h2 : (c1 + c2) * gamma ≤ (c1 + c2) * (1 / (c1 + c2 + 1)) :=
        mul_le_mul_of_nonneg_left hsmall (by linarith)
      have h3 : (c1 + c2) * (1 / (c1 + c2 + 1)) ≤ 1 := by
        rw [mul_one_div, div_le_one hden]
        linarith
      linarith
    have h24 : gamma ^ (24 : ℕ) ≤ gamma ^ (12 : ℕ) :=
      pow_le_pow_of_le_one hgamma.le (by linarith) (by norm_num)
    have hkey : c1 * gamma ^ (12 : ℕ) + c2 * gamma ^ (24 : ℕ) ≤
        (c1 + c2) * gamma ^ (12 : ℕ) := by
      have := mul_le_mul_of_nonneg_left h24 hc2
      linarith
    have hfinal : (c1 + c2) * gamma ^ (12 : ℕ) ≤ gamma ^ (10 : ℕ) := by
      have hsplit : gamma ^ (12 : ℕ) = gamma ^ (2 : ℕ) * gamma ^ (10 : ℕ) := by ring
      rw [hsplit, ← mul_assoc]
      have h10 : (0 : ℝ) ≤ gamma ^ (10 : ℕ) := by positivity
      calc (c1 + c2) * gamma ^ (2 : ℕ) * gamma ^ (10 : ℕ)
          ≤ 1 * gamma ^ (10 : ℕ) := mul_le_mul_of_nonneg_right habs h10
        _ = gamma ^ (10 : ℕ) := one_mul _
    linarith

/-! ## The producer threshold the split input must name -/

/-- The threshold a consumer passes as the split input's own `Csplit` in order that
the regime's largeness gate imply the proved ellipticity producer's plain gate
`exp (2 C) <= E`.  The factor `3/2` is the proved absolute cap
`Provider.Disorder.cstar_le_three_halves`. -/
def regimeEllipticityConst (C : ℝ) : ℝ := 3 / 2 * (Real.exp (2 * C) + 1)

theorem regimeEllipticityConst_pos (C : ℝ) : 0 < regimeEllipticityConst C := by
  have h : (0 : ℝ) < Real.exp (2 * C) := Real.exp_pos _
  unfold regimeEllipticityConst
  linarith

/-- **The regime's product gate implies the ellipticity producer's plain gate.**

`integral_gaugedEllipticitySum_pow_four_ancestorAtScale_le` asks for `max (exp
(2 C)) cstar^{-1} <= E`, while `ClosureRegime` supplies the product gate
`Csplit cstar^{-1} <= E`.  With `Csplit = regimeEllipticityConst C` and the
proved absolute cap `cstar <= 3/2` the two coincide: `cstar^{-1} >= 2/3`, so
the product gate already forces `E >= (2/3) * (3/2) (exp (2 C) + 1) > exp (2
C)`, and `cstar^{-1} <= E` follows because `regimeEllipticityConst C >= 1`.

Conditional on the proved positivity and cap of `cstar` and on the gate. -/
theorem gammaRegime_max_exp_le {C cstarM E : ℝ} (hcstar0 : 0 < cstarM)
    (hcstar : cstarM ≤ 3 / 2) (hgate : regimeEllipticityConst C * cstarM⁻¹ ≤ E) :
    max (Real.exp (2 * C)) cstarM⁻¹ ≤ E := by
  have hexp : (0 : ℝ) < Real.exp (2 * C) := Real.exp_pos _
  have hinv0 : (0 : ℝ) < cstarM⁻¹ := inv_pos.2 hcstar0
  have hinvlow : (2 : ℝ) / 3 ≤ cstarM⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hcstar0]
    linarith
  have hone : (1 : ℝ) ≤ regimeEllipticityConst C := by
    unfold regimeEllipticityConst
    linarith [hexp]
  refine max_le ?_ ?_
  · have hstep : regimeEllipticityConst C * (2 / 3 : ℝ) ≤ regimeEllipticityConst C * cstarM⁻¹ :=
      mul_le_mul_of_nonneg_left hinvlow (regimeEllipticityConst_pos C).le
    have hval : regimeEllipticityConst C * (2 / 3 : ℝ) = Real.exp (2 * C) + 1 := by
      unfold regimeEllipticityConst
      ring
    rw [hval] at hstep
    linarith [hstep, hgate]
  · have hstep : (1 : ℝ) * cstarM⁻¹ ≤ regimeEllipticityConst C * cstarM⁻¹ :=
      mul_le_mul_of_nonneg_right hone hinv0.le
    rw [one_mul] at hstep
    linarith [hstep, hgate]

/-! ## The ellipticity producer's exponential gate

The proved producer's fourth premise, `cgamma / 2 + exp (-(C^{-1} (E^{-1})^2
cgamma^{-1})) <= cgamma`, says that an exponentially small quantity sits below
`cgamma / 2`.  Under the regime's smallness clause the exponent is at least
`C^{-1} cgamma^{-1/2}` --- because `E^4 cgamma <= E^5 cgamma <= 1` forces
`E^{-2} >= sqrt cgamma` --- and `exp t >= t^3 / 27`, so the left-hand side is
`O(cgamma^{3/2})`.  The gate therefore holds once `cgamma` is small, and the
threshold is **produced**. -/

/-- `exp t >= t^3 / 27` for `t >= 0`: three applications of `x + 1 <= exp x`
through `exp t = (exp (t/3))^3`. -/
private theorem foldArith_pow_three_div_le_exp {t : ℝ} (ht : 0 ≤ t) :
    t ^ (3 : ℕ) / 27 ≤ Real.exp t := by
  have h1 : t / 3 ≤ Real.exp (t / 3) := by
    have hx := Real.add_one_le_exp (t / 3)
    linarith
  have h2 : (t / 3) ^ (3 : ℕ) ≤ (Real.exp (t / 3)) ^ (3 : ℕ) :=
    pow_le_pow_left₀ (by linarith) h1 3
  have h3 : Real.exp t = (Real.exp (t / 3)) ^ (3 : ℕ) := by
    rw [pow_succ, pow_succ, pow_one, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [h3]
  calc t ^ (3 : ℕ) / 27 = (t / 3) ^ (3 : ℕ) := by ring
    _ ≤ (Real.exp (t / 3)) ^ (3 : ℕ) := h2

/-- **The regime forces the ellipticity producer's exponential gate.**

For every `C > 0` there is a threshold below which, at every `E >= 1` obeying the
regime's smallness clause `cgamma <= E^{-5}`,

```
  cgamma / 2 + exp (-(C^{-1} (E^{-1})^2 cgamma^{-1}))  <=  cgamma .
```

This is verbatim the fourth premise of
`integral_gaugedEllipticitySum_pow_four_ancestorAtScale_le`.
The threshold is **produced**, not assumed. -/
theorem exists_gamma_threshold_ellipticityGate {C : ℝ} (hC : 0 < C) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
      ∀ E gamma : ℝ, 1 ≤ E → 0 < gamma → gamma ≤ gamma0 →
        gamma ≤ E ^ (-5 : ℤ) →
        gamma / 2 + Real.exp (-(C⁻¹ * (E⁻¹) ^ (2 : ℕ) * gamma⁻¹)) ≤ gamma := by
  have hden : (0 : ℝ) < 54 * C ^ (3 : ℕ) + 1 := by positivity
  refine ⟨min (1 / 4) (1 / (54 * C ^ (3 : ℕ) + 1) ^ (2 : ℕ)), ?_, min_le_left _ _, ?_⟩
  · have hpos : (0 : ℝ) < 1 / (54 * C ^ (3 : ℕ) + 1) ^ (2 : ℕ) := by positivity
    exact lt_min (by norm_num) hpos
  intro E gamma hE gpos hle hsmall
  have hCne : C ≠ 0 := ne_of_gt hC
  have hE0 : (0 : ℝ) < E := lt_of_lt_of_le zero_lt_one hE
  have hEne : E ≠ 0 := ne_of_gt hE0
  have hE2 : (0 : ℝ) < E ^ (2 : ℕ) := by positivity
  have hE5 : (0 : ℝ) < E ^ (5 : ℕ) := by positivity
  have hs0 : (0 : ℝ) < Real.sqrt gamma := Real.sqrt_pos.2 gpos
  have hsne : Real.sqrt gamma ≠ 0 := ne_of_gt hs0
  have hgne : gamma ≠ 0 := ne_of_gt gpos
  have hss : Real.sqrt gamma * Real.sqrt gamma = gamma := Real.mul_self_sqrt gpos.le
  -- the threshold, in the form `54 C^3 sqrt gamma <= 1`
  have hsqrtthr : Real.sqrt gamma ≤ 1 / (54 * C ^ (3 : ℕ) + 1) := by
    have hle2 : gamma ≤ (1 / (54 * C ^ (3 : ℕ) + 1)) ^ (2 : ℕ) := by
      have hstep := hle.trans (min_le_right _ _)
      rwa [show (1 : ℝ) / (54 * C ^ (3 : ℕ) + 1) ^ (2 : ℕ)
          = (1 / (54 * C ^ (3 : ℕ) + 1)) ^ (2 : ℕ) by rw [div_pow]; norm_num] at hstep
    calc Real.sqrt gamma ≤ Real.sqrt ((1 / (54 * C ^ (3 : ℕ) + 1)) ^ (2 : ℕ)) :=
          Real.sqrt_le_sqrt hle2
      _ = 1 / (54 * C ^ (3 : ℕ) + 1) := Real.sqrt_sq (by positivity)
  have hthr : 54 * (C ^ (3 : ℕ) * Real.sqrt gamma) ≤ 1 := by
    have hC3 : (0 : ℝ) ≤ 54 * C ^ (3 : ℕ) := by positivity
    have h1 := mul_le_mul_of_nonneg_left hsqrtthr hC3
    have h2 : 54 * C ^ (3 : ℕ) * (1 / (54 * C ^ (3 : ℕ) + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one hden]
      linarith
    linarith
  -- the regime's smallness clause forces `E^{-2} >= sqrt gamma`
  have hzpow : E ^ (-5 : ℤ) = (E ^ (5 : ℕ))⁻¹ := by
    rw [show (-5 : ℤ) = -((5 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
  rw [hzpow] at hsmall
  have hE5le : E ^ (5 : ℕ) ≤ gamma⁻¹ := (le_inv_comm₀ hE5 gpos).mpr hsmall
  have hE4le : E ^ (4 : ℕ) * gamma ≤ 1 := by
    have h45 : E ^ (4 : ℕ) ≤ E ^ (5 : ℕ) := pow_le_pow_right₀ hE (by norm_num)
    have hstep : E ^ (4 : ℕ) * gamma ≤ gamma⁻¹ * gamma :=
      mul_le_mul_of_nonneg_right (h45.trans hE5le) gpos.le
    rwa [inv_mul_cancel₀ hgne] at hstep
  have hprod : E ^ (2 : ℕ) * Real.sqrt gamma ≤ 1 := by
    have hnn : (0 : ℝ) ≤ E ^ (2 : ℕ) * Real.sqrt gamma := by positivity
    have hsqle : (E ^ (2 : ℕ) * Real.sqrt gamma) * (E ^ (2 : ℕ) * Real.sqrt gamma) ≤ 1 := by
      have hrw : (E ^ (2 : ℕ) * Real.sqrt gamma) * (E ^ (2 : ℕ) * Real.sqrt gamma) =
          E ^ (4 : ℕ) * (Real.sqrt gamma * Real.sqrt gamma) := by ring
      rw [hrw, hss]
      exact hE4le
    nlinarith [hnn, hsqle]
  have hEinvsq : Real.sqrt gamma ≤ (E⁻¹) ^ (2 : ℕ) := by
    rw [inv_pow]
    have hinvsq0 : (0 : ℝ) < (E ^ (2 : ℕ))⁻¹ := inv_pos.2 hE2
    have hid : (E ^ (2 : ℕ) * Real.sqrt gamma) * (E ^ (2 : ℕ))⁻¹ = Real.sqrt gamma := by
      field_simp
    have hstep := mul_le_mul_of_nonneg_right hprod hinvsq0.le
    rwa [hid, one_mul] at hstep
  -- the exponent is at least `t0 = C^{-1} (sqrt gamma)^{-1}`
  have hkey : Real.sqrt gamma * gamma⁻¹ = (Real.sqrt gamma)⁻¹ := by
    field_simp
    linarith [hss]
  have hCinv : (0 : ℝ) < C⁻¹ := inv_pos.2 hC
  set t0 : ℝ := C⁻¹ * (Real.sqrt gamma)⁻¹ with ht0def
  have ht0pos : (0 : ℝ) < t0 := by
    rw [ht0def]
    positivity
  have ht0le : t0 ≤ C⁻¹ * (E⁻¹) ^ (2 : ℕ) * gamma⁻¹ := by
    have h1 : Real.sqrt gamma * gamma⁻¹ ≤ (E⁻¹) ^ (2 : ℕ) * gamma⁻¹ :=
      mul_le_mul_of_nonneg_right hEinvsq (inv_nonneg.2 gpos.le)
    rw [hkey] at h1
    calc t0 = C⁻¹ * (Real.sqrt gamma)⁻¹ := ht0def
      _ ≤ C⁻¹ * ((E⁻¹) ^ (2 : ℕ) * gamma⁻¹) := mul_le_mul_of_nonneg_left h1 hCinv.le
      _ = C⁻¹ * (E⁻¹) ^ (2 : ℕ) * gamma⁻¹ := by ring
  -- `54 <= gamma * t0^3`
  have hCs : (0 : ℝ) < C ^ (3 : ℕ) * Real.sqrt gamma := by positivity
  have hCsne : C ^ (3 : ℕ) * Real.sqrt gamma ≠ 0 := ne_of_gt hCs
  have hinner : gamma * ((Real.sqrt gamma)⁻¹) ^ (3 : ℕ) = (Real.sqrt gamma)⁻¹ := by
    field_simp
    linarith [hss]
  have hgt0 : gamma * t0 ^ (3 : ℕ) = (C ^ (3 : ℕ) * Real.sqrt gamma)⁻¹ := by
    rw [ht0def, mul_pow]
    calc gamma * ((C⁻¹) ^ (3 : ℕ) * ((Real.sqrt gamma)⁻¹) ^ (3 : ℕ))
        = (C⁻¹) ^ (3 : ℕ) * (gamma * ((Real.sqrt gamma)⁻¹) ^ (3 : ℕ)) := by ring
      _ = (C⁻¹) ^ (3 : ℕ) * (Real.sqrt gamma)⁻¹ := by rw [hinner]
      _ = (C ^ (3 : ℕ) * Real.sqrt gamma)⁻¹ := by rw [mul_inv, inv_pow]
  have hcube54 : (54 : ℝ) ≤ gamma * t0 ^ (3 : ℕ) := by
    rw [hgt0]
    have hstep := mul_le_mul_of_nonneg_right hthr (inv_nonneg.2 hCs.le)
    rwa [mul_assoc, mul_inv_cancel₀ hCsne, mul_one, one_mul] at hstep
  -- `2 <= gamma * exp t0`
  have hprodexp : (2 : ℝ) ≤ gamma * Real.exp t0 := by
    have h1 : gamma * (t0 ^ (3 : ℕ) / 27) ≤ gamma * Real.exp t0 :=
      mul_le_mul_of_nonneg_left (foldArith_pow_three_div_le_exp ht0pos.le) gpos.le
    have h2 : (2 : ℝ) ≤ gamma * (t0 ^ (3 : ℕ) / 27) := by
      have hrw : gamma * (t0 ^ (3 : ℕ) / 27) = (gamma * t0 ^ (3 : ℕ)) / 27 := by ring
      rw [hrw, le_div_iff₀ (by norm_num : (0 : ℝ) < 27)]
      linarith [hcube54]
    linarith
  -- conclude
  have hexppos : (0 : ℝ) < Real.exp t0 := Real.exp_pos _
  have hexpne : Real.exp t0 ≠ 0 := ne_of_gt hexppos
  have h2 : Real.exp (-t0) ≤ gamma / 2 := by
    rw [Real.exp_neg]
    have hmul := mul_le_mul_of_nonneg_left hprodexp (inv_nonneg.2 hexppos.le)
    have hrw : (Real.exp t0)⁻¹ * (gamma * Real.exp t0) = gamma := by field_simp
    rw [hrw] at hmul
    linarith [hmul]
  have h1 : Real.exp (-(C⁻¹ * (E⁻¹) ^ (2 : ℕ) * gamma⁻¹)) ≤ Real.exp (-t0) :=
    Real.exp_le_exp.2 (by linarith [ht0le])
  linarith [h1, h2]

/-! ## The ellipticity leg of the fold, under the regime alone -/

/-- **The Step-2 ellipticity moment, with all four of the proved producer's
premises replaced by the regime's own two clauses.**

`integral_gaugedEllipticitySum_pow_four_ancestorAtScale_le`
carries four ad-hoc premises (the induction state, a `max` gate, an `rpow`
smallness bound and an exponential gate).  Under the two clauses
`Cell * cstar^{-1} <= E` and `cgamma <= E^{-5}` of the closure's own regime, at
the *produced* threshold `Cell` and below a *produced* `gamma0`, all four hold,
and the resulting bound is the **absolute** `(cgamma^8)^{-1}`:

```
  E[ (gauged ellipticity sum at the scale-m ancestor)^4 ]  <=  cgamma^{-8} .
```

Neither the producer's constant nor `cstar` survives.  This is the ellipticity
leg of the annealed Hoelder fold, discharged.

Proved from the frozen theorem `coarse_ellipticity_bounds`, through its
producer. -/
theorem exists_regime_gaugedEllipticitySum_pow_four_le (d : ℕ) :
    ∃ Cell gamma0 : ℝ, 0 < Cell ∧ 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
      ∀ (M : ABKModel d) (m : ℤ) (Ec : {E : ℝ // 1 ≤ E}),
        M.gamma ≤ gamma0 →
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) Ec →
        Cell * (Disorder.cstar M)⁻¹ ≤ (Ec : ℝ) →
        M.gamma ≤ (Ec : ℝ) ^ (-5 : ℤ) →
        ∀ R : TriadicCube d, R.scale ≤ m →
          ∫ omega : Cutoff.CutoffSample d,
              gaugedEllipticitySum (Annealed.sigmaBar M (m - 1) : ℝ)
                  (ancestorAtScale R m) M.gamma
                  (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega) ^ (4 : ℕ)
              ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤ (M.gamma ^ (8 : ℕ))⁻¹  := by
  obtain ⟨C, hC0, hmain⟩ := integral_gaugedEllipticitySum_pow_four_ancestorAtScale_le d
  obtain ⟨g0, hg00, hg0q, hgate⟩ := exists_gamma_threshold_ellipticityGate hC0
  refine ⟨regimeEllipticityConst C, g0, regimeEllipticityConst_pos C, hg00, hg0q, ?_⟩
  intro M m Ec hMgamma hstate hlarge hsmall R hm
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcstar0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcstar : Disorder.cstar M ≤ 3 / 2 := Provider.Disorder.cstar_le_three_halves M
  have hEone : (1 : ℝ) ≤ (Ec : ℝ) := Ec.property
  have hmax : max (Real.exp (2 * C)) (Disorder.cstar M)⁻¹ ≤ (Ec : ℝ) :=
    gammaRegime_max_exp_le hcstar0 hcstar hlarge
  have hrpow : (Ec : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) :=
    gammaRegime_E_le_rpow_neg_fifth hEone hgamma0 hsmall
  have hgateM : M.gamma / 2 +
      Real.exp (-(C⁻¹ * (((Ec : ℝ))⁻¹) ^ (2 : ℕ) * M.gamma⁻¹)) ≤ M.gamma :=
    hgate (Ec : ℝ) M.gamma hEone hgamma0 hMgamma hsmall
  have hbase := hmain M m Ec hstate hmax hrpow hgateM R hm
  refine hbase.trans ?_
  have hCle : C * (Disorder.cstar M)⁻¹ ≤ (Ec : ℝ) := by
    have hCsmall : C ≤ regimeEllipticityConst C := by
      have hexp : (0 : ℝ) < Real.exp (2 * C) := Real.exp_pos _
      have hCC : C ≤ Real.exp (2 * C) := by
        have := Real.add_one_le_exp (2 * C)
        linarith
      unfold regimeEllipticityConst
      linarith
    have hinv0 : (0 : ℝ) ≤ (Disorder.cstar M)⁻¹ := (inv_pos.2 hcstar0).le
    have := mul_le_mul_of_nonneg_right hCsmall hinv0
    linarith [this, hlarge]
  exact gammaRegime_ellipticityLeg_pow_four_le hC0.le hcstar0 hEone hgamma0 hCle hsmall

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
