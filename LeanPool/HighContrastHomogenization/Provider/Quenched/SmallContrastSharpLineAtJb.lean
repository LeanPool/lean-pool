/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastLineProducer

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSharpLineAtJb

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The recursion line stated at its own base index

The original sharp line takes `hjb : 3 * n / 4 ≤ jb` and uses antitonicity to
deduce `F jb ≤ F (3 * n / 4)`; its conclusion is then
stated at the weaker index `3 * n / 4` and `jb` disappears.  That is exactly
right when the iteration runs from the origin, and exactly wrong when it runs
from an offset: a proportional index measured from the origin lags out of the
shifted clock, and no offset makes the two compatible.

Here each declaration concludes at `F jb`, the recurrence's chosen base index,
and asks instead the one
fact the quadratic step really needs, `jb ≤ n`, which the one-step family
already supplies as the upper half of `t - Hw ≤ jb ≤ t`.

At `jb = 3 * n / 4`, these statements specialize to the three-quarter-index
forms because `3 * n / 4 ≤ n`.

The base index may then lag inside the shifted clock,

```
jb n  :=  n₀ + 3 * (n - n₀) / 4 ,
```

whose three admissibility facts are proved at the end of the file: it dominates
`3 * n / 4`, it is bounded by `n`, and after the shift it
is the free index `3 * j / 4`, which satisfies the iteration lemma's
`j ≤ 2 * l' j + 1` at every `j`.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The scalar step, at the base index -/

/-- `hrec_of_one_step_sharp_at_jb` with the quadratic slot left at `jb`. -/
theorem hrec_of_one_step_sharp_at_jb {F : ℕ → ℝ}
    (hFnn : ∀ j, 0 ≤ F j) (hFmono : ∀ p q : ℕ, p ≤ q → F q ≤ F p)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {n H jb : ℕ} (hH : H + 1 ≤ n) (hjbn : jb ≤ n)
    {a bq cw : ℝ} (ha : 0 ≤ a) (hbq0 : 0 ≤ bq) (hcw : 0 ≤ cw)
    {W u v w cdrop : ℝ} (hW0 : 0 ≤ W)
    (hstep : F n ≤ a * (F (n - H) - F n) + bq * F n ^ 2 + cw * W ^ 2)
    (hWsplit : W ≤ u + v * F jb + w)
    (hwsq : w ^ 2 ≤ cdrop * iterationDropSum r F n) :
    F n ≤
      (a * (r ^ H)⁻¹ + 3 * cw * cdrop) * iterationDropSum r F n +
        (bq + 3 * cw * v ^ 2) * F jb ^ 2 + 3 * cw * u ^ 2 := by
  classical
  have hdrop := single_drop_le_iteration_sharp hFmono hr0 hr1 hH
  have hdrop' : a * (F (n - H) - F n) ≤
      (a * (r ^ H)⁻¹) * iterationDropSum r F n := by
    have h := mul_le_mul_of_nonneg_left hdrop ha
    calc a * (F (n - H) - F n)
        ≤ a * ((r ^ H)⁻¹ * iterationDropSum r F n) := h
      _ = (a * (r ^ H)⁻¹) * iterationDropSum r F n := by ring
  have hWsq : W ^ 2 ≤ (u + v * F jb + w) ^ 2 := pow_le_pow_left₀ hW0 hWsplit 2
  have hsplit : (u + v * F jb + w) ^ 2 ≤
      3 * (u ^ 2 + (v * F jb) ^ 2 + w ^ 2) := sq_add_three_le u (v * F jb) w
  have hjbsq : (v * F jb) ^ 2 = v ^ 2 * F jb ^ 2 := by ring
  have hWchain : cw * W ^ 2 ≤
      3 * cw * cdrop * iterationDropSum r F n +
        3 * cw * v ^ 2 * F jb ^ 2 + 3 * cw * u ^ 2 := by
    have hbase : W ^ 2 ≤
        3 * u ^ 2 + 3 * (v ^ 2 * F jb ^ 2) +
          3 * (cdrop * iterationDropSum r F n) := by
      have h := le_trans hWsq hsplit
      linarith only [h, hjbsq.le, hjbsq.ge, hwsq]
    have h := mul_le_mul_of_nonneg_left hbase hcw
    linarith only [h]
  have hFn : F n ≤ F jb := hFmono _ _ hjbn
  have hFn0 : 0 ≤ F n := hFnn n
  have hFnsq : F n ^ 2 ≤ F jb ^ 2 := pow_le_pow_left₀ hFn0 hFn 2
  have hbq : bq * F n ^ 2 ≤ bq * F jb ^ 2 :=
    mul_le_mul_of_nonneg_left hFnsq hbq0
  linarith only [hstep, hdrop', hWchain, hbq]

/-! ## The isotropy line, at the base index -/

/-! ## The shifted base index, and its three admissibility facts -/

end

end HCPolySupport.HighContrast.Quenched
