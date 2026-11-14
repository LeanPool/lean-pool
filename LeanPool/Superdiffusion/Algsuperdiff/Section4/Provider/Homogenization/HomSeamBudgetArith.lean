/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineSupFormClause
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineCzGridDepthTest
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepEnvelope

/-!
# HomSeamBudgetArith

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The budget: the two `|log γ|` costs multiply to exactly ONE `|log γ|`

## What this file supplies

The corrected statement enlarges the moment display of
Theorem B from `|log γ|²` to `|log γ|³`.  It assigns the ONE
new log to the product of the two machine-pinned costs of realizing Step 3 at
the fixed exponent `p = 4d`:

```text
  D3   = coarseGrainingGeomFactor (4d) (s/4)          ≈ |log γ|^{1/(4d)}
  CA   = (1 + (s·p')⁻¹)^{1/p'}                        ≈ |log γ|^{1-1/(4d)}
```

This file proves, over abstract reals and with NO model in sight, that the
product is at most `2·|log γ|` on the printed gate `4 ≤ |log γ|` — i.e. that
the one extra log of the frozen display is enough, with a numeral to spare and
with NO dependence of the budget constant on `d`.

```text
  coarseGrainingGeomFactor_le_one_add_inv   -- D3 ≤ (1 + (w·p)⁻¹)^{1/p}
  geomFactor_mul_farBandFactor_le_two_mul   -- the product, at conjugate (p,q)
  recut_geomBudget_le                       -- the same at the §4.5 pin p = 4d
  recut_geomBudget_le_absLog                -- and at s = homS M, on the gate
```

The two `≈` above are necessity records — the `D3` lower bound and the
far-band lower bound; this file supplies the matching UPPER bounds, which is what
the budget slot consumes.
-/

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

/-! ## 1. `log 3 ≥ 1`, and the elementary convexity bound it feeds -/

/-- `e ≤ 3`, hence `1 ≤ log 3`. -/
theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  have hexp : Real.exp 1 ≤ 3 := by
    have h := Real.exp_one_lt_d9
    linarith only [h]
  exact (Real.le_log_iff_exp_le (by norm_num)).mpr hexp

/-- **`1 + x ≤ 3^x` for `x ≥ 0`.**  `exp` dominates its tangent at `0` and
`log 3 ≥ 1`. -/
theorem one_add_le_three_rpow {x : ℝ} (hx : 0 ≤ x) : 1 + x ≤ (3 : ℝ) ^ x := by
  have hbase := Real.add_one_le_exp (Real.log 3 * x)
  have hrw : (3 : ℝ) ^ x = Real.exp (Real.log 3 * x) :=
    Real.rpow_def_of_pos (by norm_num) x
  have hlog : x ≤ Real.log 3 * x := by
    have h := mul_le_mul_of_nonneg_right one_le_log_three hx
    linarith only [h]
  rw [hrw]
  linarith only [hbase, hlog]

/-! ## 2. The `D3` upper bound -/

/-- **THE `D3` FACTOR, FROM ABOVE.**

`coarseGrainingGeomFactor p w = (1-3^{-wp})^{-1/p} ≤ (1 + (w·p)⁻¹)^{1/p}`.

This is the exact companion of the `D3` necessity record: both sides behave
like `(wp)^{-1/p}`
as `w·p → 0`, so nothing is lost here.  No gate, no `γ`, no `d`. -/
theorem coarseGrainingGeomFactor_le_one_add_inv {p w : ℝ} (hp : 0 < p) (hw : 0 < w) :
    coarseGrainingGeomFactor p w ≤ (1 + (w * p)⁻¹) ^ (1 / p) := by
  have hx : (0 : ℝ) < w * p := mul_pos hw hp
  have hxle : 1 + w * p ≤ (3 : ℝ) ^ (w * p) := one_add_le_three_rpow hx.le
  have hxpos : (0 : ℝ) < 1 + w * p := by linarith only [hx]
  have hneg : (3 : ℝ) ^ (-(w * p)) = ((3 : ℝ) ^ (w * p))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  have hinvle : ((3 : ℝ) ^ (w * p))⁻¹ ≤ (1 + w * p)⁻¹ := inv_anti₀ hxpos hxle
  have hden : (1 + w * p)⁻¹ * (1 + w * p) = 1 := inv_mul_cancel₀ (ne_of_gt hxpos)
  have hlow : (w * p) / (1 + w * p) ≤ 1 - (3 : ℝ) ^ (-(w * p)) := by
    have hval : (1 : ℝ) - (1 + w * p)⁻¹ = (w * p) / (1 + w * p) := by
      field_simp
      ring
    rw [hneg, ← hval]
    linarith only [hinvle]
  have hlow0 : (0 : ℝ) < (w * p) / (1 + w * p) := div_pos hx hxpos
  have hstep : (1 - (3 : ℝ) ^ (-(w * p)))⁻¹ ≤ ((w * p) / (1 + w * p))⁻¹ :=
    inv_anti₀ hlow0 hlow
  have hval2 : ((w * p) / (1 + w * p))⁻¹ = 1 + (w * p)⁻¹ := by
    field_simp
    ring
  rw [hval2] at hstep
  have hden0 : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(w * p)) := by linarith only [hlow, hlow0]
  rw [coarseGrainingGeomFactor_def]
  exact Real.rpow_le_rpow (le_of_lt (inv_pos.mpr hden0)) hstep (by positivity)

/-! ## 3. THE BUDGET: the two costs multiply to one `L` -/

/-- **THE BUDGET INEQUALITY, over abstract reals.**

At a conjugate pair `(p, q)` (`1/p + 1/q = 1`) the product of

* the `ℓ^p` depth-aggregation energy factor `coarseGrainingGeomFactor p w`, and
* the dual-converse far-band factor `(1 + (L⁻¹·q)⁻¹)^{1/q}`

is at most `2·L`, provided only that `(w·p)⁻¹ ≤ L` and `1 ≤ L`.  The two
exponents `1/p` and `1/q` add to `1`: that is the whole content — one log, not
two, and the constant is the numeral `2`. -/
theorem geomFactor_mul_farBandFactor_le_two_mul {p q L w : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : 1 / p + 1 / q = 1) (hL : 1 ≤ L)
    (hw : 0 < w) (hwpL : (w * p)⁻¹ ≤ L) :
    coarseGrainingGeomFactor p w * (1 + (L⁻¹ * q)⁻¹) ^ (1 / q) ≤ 2 * L := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL
  have h2L : (0 : ℝ) < 2 * L := by linarith only [hL0]
  have hwp : (0 : ℝ) < w * p := mul_pos hw hp0
  /- the two bases, each below `2 * L` -/
  have hA : 1 + (w * p)⁻¹ ≤ 2 * L := by linarith only [hwpL, hL]
  have hBval : (L⁻¹ * q)⁻¹ = L * q⁻¹ := by
    rw [mul_inv, inv_inv]
  have hqinv : q⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq
  have hB : 1 + (L⁻¹ * q)⁻¹ ≤ 2 * L := by
    rw [hBval]
    have h := mul_le_mul_of_nonneg_left hqinv hL0.le
    rw [mul_one] at h
    linarith only [h, hL]
  /- the two factors, each below `(2L)` to its own reciprocal expone -/
  have hA0 : (0 : ℝ) ≤ 1 + (w * p)⁻¹ := by positivity
  have hB0 : (0 : ℝ) ≤ 1 + (L⁻¹ * q)⁻¹ := by
    rw [hBval]; positivity
  have hfac1 : coarseGrainingGeomFactor p w ≤ (2 * L) ^ (1 / p) :=
    le_trans (coarseGrainingGeomFactor_le_one_add_inv hp0 hw)
      (Real.rpow_le_rpow hA0 hA (by positivity))
  have hfac2 : (1 + (L⁻¹ * q)⁻¹) ^ (1 / q) ≤ (2 * L) ^ (1 / q) :=
    Real.rpow_le_rpow hB0 hB (by positivity)
  have hf20 : (0 : ℝ) ≤ (1 + (L⁻¹ * q)⁻¹) ^ (1 / q) := Real.rpow_nonneg hB0 _
  have hprod : coarseGrainingGeomFactor p w * (1 + (L⁻¹ * q)⁻¹) ^ (1 / q) ≤
      (2 * L) ^ (1 / p) * (2 * L) ^ (1 / q) :=
    mul_le_mul hfac1 hfac2 hf20 (Real.rpow_nonneg h2L.le _)
  have hsum : (2 * L) ^ (1 / p) * (2 * L) ^ (1 / q) = 2 * L := by
    rw [← Real.rpow_add h2L, hpq, Real.rpow_one]
  linarith only [hprod, hsum.le, hsum.ge]

/-! ## 4. THE BUDGET AT THE §4.5 PIN `p = 4d` -/

/-- **THE BUDGET AT THE PIN.**  `p = 4d`, `w = s/4` with `s = L⁻¹`, and `q` the
Hölder conjugate of `4d`: the product of the D3 energy factor and the
dual-converse far-band factor is at most `2·L`.

The pin's arithmetic is `w·p = (L⁻¹/4)·(4d) = d/L`, so `(w·p)⁻¹ = L/d ≤ L` as
soon as `1 ≤ d`.  The `d`-dependence of the two individual factors
(`L^{1/(4d)}` and `L^{1-1/(4d)}`) cancels EXACTLY: the budget constant is the
numeral `2`. -/
theorem recut_geomBudget_le (d : ℕ) (hd1 : 1 ≤ d) {L : ℝ} (hL : 1 ≤ L) :
    coarseGrainingGeomFactor ((recutExponent d hd1).exponent.toReal) (L⁻¹ / 4) *
        (1 + (L⁻¹ * (recutExponent d hd1).conjugate.exponent.toReal)⁻¹) ^
          (1 / (recutExponent d hd1).conjugate.exponent.toReal) ≤
      2 * L := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL
  have hconj := holderConjugate_toReal (recutExponent d hd1)
  have hp1 : (1 : ℝ) ≤ (recutExponent d hd1).exponent.toReal := by
    rw [recutExponent_toReal]; linarith only [hdR]
  have hq1 : (1 : ℝ) ≤ (recutExponent d hd1).conjugate.exponent.toReal :=
    le_of_lt (one_lt_finiteLpExponent_toReal (recutExponent d hd1).conjugate)
  have hpq : 1 / (recutExponent d hd1).exponent.toReal +
      1 / (recutExponent d hd1).conjugate.exponent.toReal = 1 := by
    have h := Real.HolderConjugate.inv_add_inv_eq_one hconj
    rw [one_div, one_div]
    exact h
  have hw : (0 : ℝ) < L⁻¹ / 4 := by positivity
  have hwp : L⁻¹ / 4 * (recutExponent d hd1).exponent.toReal = L⁻¹ * (d : ℝ) := by
    rw [recutExponent_toReal]; ring
  have hwpL : (L⁻¹ / 4 * (recutExponent d hd1).exponent.toReal)⁻¹ ≤ L := by
    rw [hwp, mul_inv, inv_inv]
    have hdinv : (d : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hdR
    have h := mul_le_mul_of_nonneg_left hdinv hL0.le
    rw [mul_one] at h
    exact h
  exact geomFactor_mul_farBandFactor_le_two_mul hp1 hq1 hpq hL hw hwpL

/-- **THE `D3` FACTOR ALONE IS INSIDE THE BUDGET.**

At the §4.5 pin the geometric factor of the `ℓ^p` energy slot is at most `2·L`
all by itself: it is `≍ L^{1/(4d)}`, and one whole log is more than enough.
This discharges the factor `D3` on its own, inside the frozen budget. -/
theorem recut_geomFactor_le_two_mul (d : ℕ) (hd1 : 1 ≤ d) {L : ℝ} (hL : 1 ≤ L) :
    coarseGrainingGeomFactor ((recutExponent d hd1).exponent.toReal) (L⁻¹ / 4) ≤ 2 * L := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL
  have h2L : (1 : ℝ) ≤ 2 * L := by linarith only [hL]
  have hp1 : (1 : ℝ) ≤ (recutExponent d hd1).exponent.toReal := by
    rw [recutExponent_toReal]; linarith only [hdR]
  have hp0 : (0 : ℝ) < (recutExponent d hd1).exponent.toReal := by linarith only [hp1]
  have hw : (0 : ℝ) < L⁻¹ / 4 := by positivity
  have hwp : L⁻¹ / 4 * (recutExponent d hd1).exponent.toReal = L⁻¹ * (d : ℝ) := by
    rw [recutExponent_toReal]; ring
  have hbase : 1 + (L⁻¹ / 4 * (recutExponent d hd1).exponent.toReal)⁻¹ ≤ 2 * L := by
    rw [hwp, mul_inv, inv_inv]
    have hdinv : (d : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hdR
    have h := mul_le_mul_of_nonneg_left hdinv hL0.le
    rw [mul_one] at h
    linarith only [h, hL]
  have hbase0 : (0 : ℝ) ≤ 1 + (L⁻¹ / 4 * (recutExponent d hd1).exponent.toReal)⁻¹ := by
    have hwp0 : (0 : ℝ) < L⁻¹ / 4 * (recutExponent d hd1).exponent.toReal := mul_pos hw hp0
    have := (inv_pos.mpr hwp0).le
    linarith only [this]
  have hexp : 1 / (recutExponent d hd1).exponent.toReal ≤ 1 := by
    rw [div_le_one hp0]; exact hp1
  calc coarseGrainingGeomFactor ((recutExponent d hd1).exponent.toReal) (L⁻¹ / 4)
      ≤ (1 + (L⁻¹ / 4 * (recutExponent d hd1).exponent.toReal)⁻¹) ^
          (1 / (recutExponent d hd1).exponent.toReal) :=
        coarseGrainingGeomFactor_le_one_add_inv hp0 hw
    _ ≤ (2 * L) ^ (1 / (recutExponent d hd1).exponent.toReal) :=
        Real.rpow_le_rpow hbase0 hbase (by positivity)
    _ ≤ (2 * L) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h2L hexp
    _ = 2 * L := Real.rpow_one _

/-- **D3, DISCHARGED ON THE PRINTED GATE.**  `GEOM ≤ 2·|log γ|`. -/
theorem recut_geomFactor_le_absLog {d : ℕ} (hd1 : 1 ≤ d) (M : ABKModel d)
    (hlog : 4 ≤ |Real.log M.gamma|) :
    coarseGrainingGeomFactor ((recutExponent d hd1).exponent.toReal) (homS M / 4) ≤
      2 * |Real.log M.gamma| := by
  have hs : homS M = |Real.log M.gamma|⁻¹ := rfl
  rw [hs]
  exact recut_geomFactor_le_two_mul d hd1 (by linarith only [hlog])

/-- **THE BUDGET ON THE PRINTED GATE**, at the own order
`s = homS M = |log γ|⁻¹`.  This is the inequality the frozen display's free
factor slot has to absorb, machine-checked: `D3 · CA ≤ 2·|log γ|`. -/
theorem recut_geomBudget_le_absLog {d : ℕ} (hd1 : 1 ≤ d) (M : ABKModel d)
    (hlog : 4 ≤ |Real.log M.gamma|) :
    coarseGrainingGeomFactor ((recutExponent d hd1).exponent.toReal) (homS M / 4) *
        (1 + (homS M * (recutExponent d hd1).conjugate.exponent.toReal)⁻¹) ^
          (1 / (recutExponent d hd1).conjugate.exponent.toReal) ≤
      2 * |Real.log M.gamma| := by
  have hs : homS M = |Real.log M.gamma|⁻¹ := rfl
  rw [hs]
  exact recut_geomBudget_le d hd1 (by linarith only [hlog])

end

end Algsuperdiff.Section4.Provider.Homogenization
