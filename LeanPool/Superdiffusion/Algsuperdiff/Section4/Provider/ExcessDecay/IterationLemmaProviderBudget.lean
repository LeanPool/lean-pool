/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.IterationLemmaProviderGeometry
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.IterationLemma
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.WeightedGoodRun

/-!
# IterationLemmaProviderBudget

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `C(d)` witness of the iteration anchor and its two prefactor budgets

The frozen iteration anchor is existential in `C`: `∃ C : ℝ, 0 < C ∧ …`.  This
module proves an explicit `C = iterConst d`, a closed-form function of `d`
alone, and proves the two budget inequalities the provider consumes:

* `iterBudgetOne` --- conclusion (i)'s prefactor
  `9 · Ci² · (goodConst · badConst)^{3|B|+3} ≤ exp(C (h+1)(|B|+1))`;
* `iterBudgetTwo` --- conclusion (ii)'s prefactor
  `(2 κ^{h+2})^{|B|+1} · (1 + (45/2) Ci) · (goodConst · badConst)^{3|B|+3}
     ≤ exp(C (h+1)(|B|+1))`.

Both reduce to **one** master product bound (`iterMaster`) at `|B| = 0`, because every
factor is `≥ 1` and the per-level factor is raised to the power `|B|+1` (`pow_succ_mul_le`).
The master is closed by a single logarithm computation whose only non-elementary input is

```
log (goodConst h κ Cstab) ≤ (h+1)(1 + log κ + log (5/2 + 35 Cstab/2 + 6 + 35 Cstab)) ,
```

i.e. `log_goodConst_le`: the good-run constant grows like `h κ^h`, so its
logarithm is `O(h log κ + log h)` and dividing by `h+1` leaves a `d`-only
bound.

## The witness versus the review's recorded floor (disclosed)

The freeze review recorded a *sufficient* floor for `C(d)`, built from the
**one-sided** slope constant `oneSidedSlopeConstTriadic d` and asking for
`2·goodRate`.  `iterConst d` below is **not** that expression: it is an
independently machine-verified witness built from the **two-sided** constant
`slopeStabilityConst d (1/9) κ`, which is the constant the proved engine's
`hstab` slot actually consumes (and which is `≤` the one-sided one, since the
latter is the former times `1 + κ`), and it asks for `goodRate` once, because
the route below pays the `∑ε` exponential exactly once.  Every other summand is
the same shape as the review's: `3(1 + log κ + log(a+b) + log badConst)` plus
explicit numeric slack.  The recorded floor is therefore not adopted verbatim;
what is proved is that *this* `C(d)` works, and `C` is existential in the
frozen statement.

## Tactic discipline

Every numeric closure here is an `exp`/`log` statement, so no numeric tactic is ever
applied to a transcendental atom: the polynomial content is isolated in the private
abstract-real lemma `budget_arith` (opaque variables only), the transcendental content is
`Real.log_le_iff_le_exp`, `Real.log_mul`, `Real.log_pow`, `Real.log_le_sub_one_of_pos` and
`Real.exp_nat_mul`, and no `nlinarith` occurs anywhere.

## References

* ABK26, `l.iteration.lemma` conclusions (i) and (ii).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section4.Support

noncomputable section

/-! ### The constants of the consumption class -/

/-- The quasi-monotonicity constant of the anchor's window family: `κ(d) = 3^{3+3d/2}`. -/
def iterKappa (d : ℕ) : ℝ := volumeRatioConstTriadic d

/-- The gradient-stability constant of the anchor's window family (the two-sided producer's
own constant, at the printed aspect ratio `1/9`). -/
def iterCstab (d : ℕ) : ℝ := slopeStabilityConst d (1 / 9 : ℝ) (volumeRatioConstTriadic d)

/-- The endpoint-comparison constant of the anchor's window family, at the printed aspect
ratio `1/9`. -/
def iterCi (d : ℕ) : ℝ := endpointConst d (1 / 9 : ℝ)

/-- The coefficient sum of the good-run constant: `goodConst h κ Cstab ≤ iterAB d · h κ^h`. -/
def iterAB (d : ℕ) : ℝ := 5 / 2 + 35 * iterCstab d / 2 + 6 + 35 * iterCstab d

/-- **The `C(d)` witness** of the frozen iteration anchor: an explicit function of `d`
alone.  Every summand is nonnegative, the leading `2` covers the `θ`-payback exponent
`(h+2)(|B|+1) ≤ C(h+1)(|B|+1)`, the `goodRate` summand covers the `∑ε` exponent, and the
remaining summands are the master budget's logarithmic pieces. -/
def iterConst (d : ℕ) : ℝ :=
  2 + goodRate (iterCstab d)
    + 3 * (1 + Real.log (iterKappa d) + Real.log (iterAB d))
    + 3 * Real.log (badConst (iterKappa d) (iterCstab d))
    + 2 * Real.log (iterKappa d)
    + 18 * iterCi d ^ 2 * (1 + 45 / 2 * iterCi d)

theorem one_le_iterKappa (d : ℕ) : (1 : ℝ) ≤ iterKappa d :=
  one_le_volumeRatioConstTriadic d

theorem iterCstab_nonneg (d : ℕ) : (0 : ℝ) ≤ iterCstab d :=
  slopeStabilityConst_nonneg (by norm_num)
    (le_trans zero_le_one (one_le_volumeRatioConstTriadic d))

theorem one_le_iterCi (d : ℕ) : (1 : ℝ) ≤ iterCi d :=
  one_le_endpointConst (by norm_num)

theorem eight_le_iterAB (d : ℕ) : (8 : ℝ) ≤ iterAB d := by
  have h := iterCstab_nonneg d
  rw [iterAB]
  linarith only [h]

theorem one_le_iterBadConst (d : ℕ) :
    (1 : ℝ) ≤ badConst (iterKappa d) (iterCstab d) :=
  one_le_badConst (one_le_iterKappa d) (iterCstab_nonneg d)

/-! ### The elementary properties of the witness -/

theorem iterConst_nonneg_parts (d : ℕ) :
    (0 : ℝ) ≤ 3 * (1 + Real.log (iterKappa d) + Real.log (iterAB d))
        + 3 * Real.log (badConst (iterKappa d) (iterCstab d))
        + 2 * Real.log (iterKappa d)
        + 18 * iterCi d ^ 2 * (1 + 45 / 2 * iterCi d) := by
  have h1 : 0 ≤ Real.log (iterKappa d) := Real.log_nonneg (one_le_iterKappa d)
  have h2 : 0 ≤ Real.log (iterAB d) :=
    Real.log_nonneg (by linarith only [eight_le_iterAB d])
  have h3 : 0 ≤ Real.log (badConst (iterKappa d) (iterCstab d)) :=
    Real.log_nonneg (one_le_iterBadConst d)
  have h4 : (1 : ℝ) ≤ iterCi d ^ 2 := one_le_pow₀ (one_le_iterCi d)
  have h5 : (1 : ℝ) ≤ 1 + 45 / 2 * iterCi d := by linarith only [one_le_iterCi d]
  have h6 : (0 : ℝ) ≤ 18 * iterCi d ^ 2 * (1 + 45 / 2 * iterCi d) := by
    have hm := mul_le_mul (by linarith only [h4] : (1 : ℝ) ≤ 18 * iterCi d ^ 2) h5
      (by norm_num) (by linarith only [h4])
    linarith only [hm]
  linarith only [h1, h2, h3, h6]

theorem two_le_iterConst (d : ℕ) : (2 : ℝ) ≤ iterConst d := by
  have h := iterConst_nonneg_parts d
  have hg : (0 : ℝ) ≤ goodRate (iterCstab d) := goodRate_nonneg (iterCstab_nonneg d)
  rw [iterConst]
  linarith only [h, hg]

theorem goodRate_le_iterConst (d : ℕ) : goodRate (iterCstab d) ≤ iterConst d := by
  have h := iterConst_nonneg_parts d
  rw [iterConst]
  linarith only [h]

theorem iterConst_pos (d : ℕ) : (0 : ℝ) < iterConst d := by
  have h := two_le_iterConst d
  linarith only [h]

/-! ### The logarithm of the good-run constant -/

/-- **The budget fact.**  `goodConst h κ Cstab` grows like `h κ^h`, so its logarithm is at
most `(h+1)` times a quantity depending on `κ` and `Cstab` only.  This is what makes a
`d`-only `C` possible in the frozen statement, and it is why the frozen exponent carries
the product `(h+1)(|B|+1)` rather than the printed sum. -/
theorem log_goodConst_le {κ Cstab : ℝ} (hκ : 1 ≤ κ) (hC : 0 ≤ Cstab) {h : ℕ}
    (hh : 1 ≤ h) :
    Real.log (goodConst h κ Cstab)
      ≤ ((h : ℝ) + 1) * (1 + Real.log κ
        + Real.log (5 / 2 + 35 * Cstab / 2 + 6 + 35 * Cstab)) := by
  have hS8 : (8 : ℝ) ≤ 5 / 2 + 35 * Cstab / 2 + 6 + 35 * Cstab := by linarith only [hC]
  have hSpos : (0 : ℝ) < 5 / 2 + 35 * Cstab / 2 + 6 + 35 * Cstab := by
    linarith only [hS8]
  have hκ0 : (0 : ℝ) < κ := by linarith only [hκ]
  have hhR : (0 : ℝ) < (h : ℝ) := by
    have h1 : 0 < h := lt_of_lt_of_le Nat.zero_lt_one hh
    exact_mod_cast h1
  have hhR1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hpow1 : (1 : ℝ) ≤ κ ^ h := one_le_pow₀ hκ
  have hM1 : (1 : ℝ) ≤ iterM h κ := by
    rw [iterM]
    have hm := mul_le_mul hhR1 hpow1 (by norm_num) (by linarith only [hhR1])
    linarith only [hm]
  have hMpos : (0 : ℝ) < iterM h κ := by linarith only [hM1]
  have hCM : 0 ≤ Cstab * iterM h κ - Cstab := by
    have h1 := mul_nonneg hC (by linarith only [hM1] : (0 : ℝ) ≤ iterM h κ - 1)
    have he : Cstab * (iterM h κ - 1) = Cstab * iterM h κ - Cstab := by ring
    linarith only [h1, he]
  have hgcle : goodConst h κ Cstab
      ≤ (5 / 2 + 35 * Cstab / 2 + 6 + 35 * Cstab) * iterM h κ := by
    rw [goodConst]
    have hexpand : 5 * Cstab * (7 / 2 * iterM h κ + 7)
        = 35 / 2 * (Cstab * iterM h κ) + 35 * Cstab := by ring
    have hrhs : (5 / 2 + 35 * Cstab / 2 + 6 + 35 * Cstab) * iterM h κ
        = 5 / 2 * iterM h κ + 35 / 2 * (Cstab * iterM h κ) + 6 * iterM h κ
          + 35 * (Cstab * iterM h κ) := by ring
    linarith only [hexpand, hrhs, hM1, hCM]
  have hgcpos : (0 : ℝ) < goodConst h κ Cstab :=
    lt_of_lt_of_le zero_lt_one (one_le_goodConst h hκ hC)
  have hlog1 : Real.log (goodConst h κ Cstab)
      ≤ Real.log ((5 / 2 + 35 * Cstab / 2 + 6 + 35 * Cstab) * iterM h κ) :=
    Real.log_le_log hgcpos hgcle
  have hlog2 : Real.log ((5 / 2 + 35 * Cstab / 2 + 6 + 35 * Cstab) * iterM h κ)
      = Real.log (5 / 2 + 35 * Cstab / 2 + 6 + 35 * Cstab) + Real.log (iterM h κ) :=
    Real.log_mul (ne_of_gt hSpos) (ne_of_gt hMpos)
  have hlog3 : Real.log (iterM h κ) = Real.log (h : ℝ) + (h : ℝ) * Real.log κ := by
    rw [iterM, Real.log_mul (ne_of_gt hhR) (ne_of_gt (pow_pos hκ0 h)), Real.log_pow]
  have hlogh : Real.log (h : ℝ) ≤ (h : ℝ) := by
    have h1 := Real.log_le_sub_one_of_pos hhR
    linarith only [h1]
  have hlogκ0 : 0 ≤ Real.log κ := Real.log_nonneg hκ
  have hlogS0 : 0 ≤ Real.log (5 / 2 + 35 * Cstab / 2 + 6 + 35 * Cstab) :=
    Real.log_nonneg (by linarith only [hS8])
  have hp1 : 0 ≤ (h : ℝ) * Real.log κ := mul_nonneg (le_of_lt hhR) hlogκ0
  have hp2 : 0 ≤ (h : ℝ) * Real.log (5 / 2 + 35 * Cstab / 2 + 6 + 35 * Cstab) :=
    mul_nonneg (le_of_lt hhR) hlogS0
  have hexpR : ((h : ℝ) + 1)
      * (1 + Real.log κ + Real.log (5 / 2 + 35 * Cstab / 2 + 6 + 35 * Cstab))
      = ((h : ℝ) + 1) + ((h : ℝ) * Real.log κ + Real.log κ)
        + ((h : ℝ) * Real.log (5 / 2 + 35 * Cstab / 2 + 6 + 35 * Cstab)
          + Real.log (5 / 2 + 35 * Cstab / 2 + 6 + 35 * Cstab)) := by ring
  linarith only [hlog1, hlog2, hlog3, hlogh, hlogκ0, hlogS0, hp1, hp2, hexpR]

/-! ### The master budget -/

/-- The polynomial core of the master budget, over opaque reals: no `log`, no `exp`. -/
private theorem budget_arith {hh Lk LS Lb A3 GR Lgc : ℝ} (hhh : 1 ≤ hh) (hLk : 0 ≤ Lk)
    (hLS : 0 ≤ LS) (hLb : 0 ≤ Lb) (hA3 : 0 ≤ A3) (hGR : 0 ≤ GR)
    (hLgc : Lgc ≤ (hh + 1) * (1 + Lk + LS)) :
    3 * (Lgc + Lb) + (hh + 2) * Lk + (A3 - 1)
      ≤ (2 + GR + 3 * (1 + Lk + LS) + 3 * Lb + 2 * Lk + A3) * (hh + 1) := by
  have p1 : 0 ≤ Lb * hh := mul_nonneg hLb (by linarith only [hhh])
  have p2 : 0 ≤ Lk * hh := mul_nonneg hLk (by linarith only [hhh])
  have p3 : 0 ≤ A3 * hh := mul_nonneg hA3 (by linarith only [hhh])
  have p4 : 0 ≤ LS * hh := mul_nonneg hLS (by linarith only [hhh])
  have p5 : 0 ≤ GR * hh := mul_nonneg hGR (by linarith only [hhh])
  have hexpR : (2 + GR + 3 * (1 + Lk + LS) + 3 * Lb + 2 * Lk + A3) * (hh + 1)
      = 2 * hh + 2 + GR * hh + GR + 3 * hh + 3 + 3 * (Lk * hh) + 3 * Lk
        + 3 * (LS * hh) + 3 * LS + 3 * (Lb * hh) + 3 * Lb + 2 * (Lk * hh) + 2 * Lk
        + A3 * hh + A3 := by ring
  have hexpL : (hh + 1) * (1 + Lk + LS)
      = hh + 1 + Lk * hh + Lk + LS * hh + LS := by ring
  have hexpM : (hh + 2) * Lk = Lk * hh + 2 * Lk := by ring
  have h3 : 3 * Lgc ≤ 3 * ((hh + 1) * (1 + Lk + LS)) := by linarith only [hLgc]
  linarith only [h3, hexpR, hexpL, hexpM, p1, p2, p3, p4, p5, hGR, hhh]

/-- **The master budget** (the `|B| = 0` level of both prefactors): the whole per-level
product of the two conclusions is below `exp(C(h+1))`. -/
theorem iterMaster (d : ℕ) {h : ℕ} (hh : 1 ≤ h) :
    (goodConst h (iterKappa d) (iterCstab d) * badConst (iterKappa d) (iterCstab d)) ^ 3
        * iterKappa d ^ (h + 2)
        * (18 * iterCi d ^ 2 * (1 + 45 / 2 * iterCi d))
      ≤ Real.exp (iterConst d * ((h : ℝ) + 1)) := by
  have hκ : (1 : ℝ) ≤ iterKappa d := one_le_iterKappa d
  have hCs : (0 : ℝ) ≤ iterCstab d := iterCstab_nonneg d
  have hCi : (1 : ℝ) ≤ iterCi d := one_le_iterCi d
  have hbc : (1 : ℝ) ≤ badConst (iterKappa d) (iterCstab d) := one_le_iterBadConst d
  have hgc : (1 : ℝ) ≤ goodConst h (iterKappa d) (iterCstab d) :=
    one_le_goodConst h hκ hCs
  have hgcbc : (1 : ℝ) ≤ goodConst h (iterKappa d) (iterCstab d)
      * badConst (iterKappa d) (iterCstab d) := by
    have hm := mul_le_mul_of_nonneg_left hbc (by linarith only [hgc] :
      (0 : ℝ) ≤ goodConst h (iterKappa d) (iterCstab d))
    linarith only [hm, hgc]
  have hA1pos : (0 : ℝ) < (goodConst h (iterKappa d) (iterCstab d)
      * badConst (iterKappa d) (iterCstab d)) ^ 3 :=
    pow_pos (by linarith only [hgcbc]) 3
  have hA2pos : (0 : ℝ) < iterKappa d ^ (h + 2) := pow_pos (by linarith only [hκ]) _
  have hA3pos : (0 : ℝ) < 18 * iterCi d ^ 2 * (1 + 45 / 2 * iterCi d) := by
    have h1 : (0 : ℝ) < iterCi d ^ 2 := pow_pos (by linarith only [hCi]) 2
    have h2 : (0 : ℝ) < 1 + 45 / 2 * iterCi d := by linarith only [hCi]
    have hm := mul_pos (by linarith only [h1] : (0 : ℝ) < 18 * iterCi d ^ 2) h2
    linarith only [hm]
  have hLHSpos : (0 : ℝ) < (goodConst h (iterKappa d) (iterCstab d)
        * badConst (iterKappa d) (iterCstab d)) ^ 3 * iterKappa d ^ (h + 2)
      * (18 * iterCi d ^ 2 * (1 + 45 / 2 * iterCi d)) :=
    mul_pos (mul_pos hA1pos hA2pos) hA3pos
  refine (Real.log_le_iff_le_exp hLHSpos).mp ?_
  have hsplit : Real.log ((goodConst h (iterKappa d) (iterCstab d)
        * badConst (iterKappa d) (iterCstab d)) ^ 3 * iterKappa d ^ (h + 2)
      * (18 * iterCi d ^ 2 * (1 + 45 / 2 * iterCi d)))
      = Real.log ((goodConst h (iterKappa d) (iterCstab d)
          * badConst (iterKappa d) (iterCstab d)) ^ 3)
        + Real.log (iterKappa d ^ (h + 2))
        + Real.log (18 * iterCi d ^ 2 * (1 + 45 / 2 * iterCi d)) := by
    rw [Real.log_mul (ne_of_gt (mul_pos hA1pos hA2pos)) (ne_of_gt hA3pos),
      Real.log_mul (ne_of_gt hA1pos) (ne_of_gt hA2pos)]
  have hlogA1 : Real.log ((goodConst h (iterKappa d) (iterCstab d)
        * badConst (iterKappa d) (iterCstab d)) ^ 3)
      = 3 * (Real.log (goodConst h (iterKappa d) (iterCstab d))
        + Real.log (badConst (iterKappa d) (iterCstab d))) := by
    rw [Real.log_pow, Real.log_mul (by linarith only [hgc] :
      goodConst h (iterKappa d) (iterCstab d) ≠ 0) (by linarith only [hbc] :
      badConst (iterKappa d) (iterCstab d) ≠ 0)]
    push_cast
    ring
  have hlogA2 : Real.log (iterKappa d ^ (h + 2))
      = ((h : ℝ) + 2) * Real.log (iterKappa d) := by
    rw [Real.log_pow]
    push_cast
    ring
  have hlogA3 : Real.log (18 * iterCi d ^ 2 * (1 + 45 / 2 * iterCi d))
      ≤ 18 * iterCi d ^ 2 * (1 + 45 / 2 * iterCi d) - 1 :=
    Real.log_le_sub_one_of_pos hA3pos
  have hloggc := log_goodConst_le hκ hCs hh
  have hbudget := budget_arith (hh := (h : ℝ))
    (Lk := Real.log (iterKappa d)) (LS := Real.log (iterAB d))
    (Lb := Real.log (badConst (iterKappa d) (iterCstab d)))
    (A3 := 18 * iterCi d ^ 2 * (1 + 45 / 2 * iterCi d))
    (GR := goodRate (iterCstab d))
    (Lgc := Real.log (goodConst h (iterKappa d) (iterCstab d)))
    (by exact_mod_cast hh) (Real.log_nonneg hκ)
    (Real.log_nonneg (by linarith only [eight_le_iterAB d]))
    (Real.log_nonneg hbc) (by linarith only [hA3pos]) (goodRate_nonneg hCs)
    (by rw [iterAB]; exact hloggc)
  rw [hsplit, hlogA1, hlogA2, iterConst]
  linarith only [hbudget, hlogA3]

/-! ### The two prefactor budgets -/

/-- Raising a per-level factor: if `X · Z ≤ Y` with `Z ≥ 1`, then `X^{p+1} · Z ≤ Y^{p+1}`. -/
private theorem pow_succ_mul_le {X Z Y : ℝ} (p : ℕ) (hX0 : 0 ≤ X) (hZ : 1 ≤ Z)
    (hXZ : X * Z ≤ Y) : X ^ (p + 1) * Z ≤ Y ^ (p + 1) := by
  have hZ0 : (0 : ℝ) ≤ Z := by linarith only [hZ]
  have h1 : Z ≤ Z ^ (p + 1) := le_self_pow₀ hZ (by omega)
  have h2 : X ^ (p + 1) * Z ≤ X ^ (p + 1) * Z ^ (p + 1) :=
    mul_le_mul_of_nonneg_left h1 (pow_nonneg hX0 _)
  have h3 : X ^ (p + 1) * Z ^ (p + 1) = (X * Z) ^ (p + 1) := (mul_pow X Z (p + 1)).symm
  have h4 : (X * Z) ^ (p + 1) ≤ Y ^ (p + 1) :=
    pow_le_pow_left₀ (mul_nonneg hX0 hZ0) hXZ (p + 1)
  linarith only [h2, h3, h4]

/-- `exp(x)^{c+1} = exp(x·(c+1))`, in the orientation the budgets need. -/
private theorem exp_pow_eq {x : ℝ} (c : ℕ) :
    Real.exp x ^ (c + 1) = Real.exp (x * ((c : ℝ) + 1)) := by
  rw [← Real.exp_nat_mul]
  push_cast
  rw [mul_comm]

/-- **Conclusion (i)'s prefactor budget.** -/
theorem iterBudgetOne (d : ℕ) {h : ℕ} (hh : 1 ≤ h) (c : ℕ) :
    9 * iterCi d ^ 2
        * (goodConst h (iterKappa d) (iterCstab d)
          * badConst (iterKappa d) (iterCstab d)) ^ (3 * c + 3)
      ≤ Real.exp (iterConst d * ((h : ℝ) + 1) * ((c : ℝ) + 1)) := by
  have hκ : (1 : ℝ) ≤ iterKappa d := one_le_iterKappa d
  have hCs : (0 : ℝ) ≤ iterCstab d := iterCstab_nonneg d
  have hCi : (1 : ℝ) ≤ iterCi d := one_le_iterCi d
  have hbc : (1 : ℝ) ≤ badConst (iterKappa d) (iterCstab d) := one_le_iterBadConst d
  have hgc : (1 : ℝ) ≤ goodConst h (iterKappa d) (iterCstab d) :=
    one_le_goodConst h hκ hCs
  have hgcbc : (1 : ℝ) ≤ goodConst h (iterKappa d) (iterCstab d)
      * badConst (iterKappa d) (iterCstab d) := by
    have hm := mul_le_mul_of_nonneg_left hbc (by linarith only [hgc] :
      (0 : ℝ) ≤ goodConst h (iterKappa d) (iterCstab d))
    linarith only [hm, hgc]
  have hZ : (1 : ℝ) ≤ 9 * iterCi d ^ 2 := by
    have h1 : (1 : ℝ) ≤ iterCi d ^ 2 := one_le_pow₀ hCi
    linarith only [h1]
  have hmaster := iterMaster d hh
  have hκpow : (1 : ℝ) ≤ iterKappa d ^ (h + 2) := one_le_pow₀ hκ
  have hA3 : (1 : ℝ) ≤ 18 * iterCi d ^ 2 * (1 + 45 / 2 * iterCi d) := by
    have h1 : (1 : ℝ) ≤ iterCi d ^ 2 := one_le_pow₀ hCi
    have h2 : (1 : ℝ) ≤ 1 + 45 / 2 * iterCi d := by linarith only [hCi]
    have hm := mul_le_mul (by linarith only [h1] : (1 : ℝ) ≤ 18 * iterCi d ^ 2) h2
      (by norm_num) (by linarith only [h1])
    linarith only [hm]
  have hXZ : (goodConst h (iterKappa d) (iterCstab d)
        * badConst (iterKappa d) (iterCstab d)) ^ 3 * (9 * iterCi d ^ 2)
      ≤ Real.exp (iterConst d * ((h : ℝ) + 1)) := by
    have hX0 : (0 : ℝ) ≤ (goodConst h (iterKappa d) (iterCstab d)
        * badConst (iterKappa d) (iterCstab d)) ^ 3 :=
      pow_nonneg (by linarith only [hgcbc]) 3
    have hstep : (goodConst h (iterKappa d) (iterCstab d)
          * badConst (iterKappa d) (iterCstab d)) ^ 3 * (9 * iterCi d ^ 2)
        ≤ (goodConst h (iterKappa d) (iterCstab d)
          * badConst (iterKappa d) (iterCstab d)) ^ 3 * iterKappa d ^ (h + 2)
          * (18 * iterCi d ^ 2 * (1 + 45 / 2 * iterCi d)) := by
      have h1 : (goodConst h (iterKappa d) (iterCstab d)
            * badConst (iterKappa d) (iterCstab d)) ^ 3 * (9 * iterCi d ^ 2)
          ≤ (goodConst h (iterKappa d) (iterCstab d)
            * badConst (iterKappa d) (iterCstab d)) ^ 3
            * (18 * iterCi d ^ 2 * (1 + 45 / 2 * iterCi d)) := by
        refine mul_le_mul_of_nonneg_left ?_ hX0
        have h2 : (1 : ℝ) ≤ 1 + 45 / 2 * iterCi d := by linarith only [hCi]
        have hsq : (1 : ℝ) ≤ iterCi d ^ 2 := one_le_pow₀ hCi
        have h3 : (0 : ℝ) ≤ 18 * iterCi d ^ 2 := by linarith only [hsq]
        have hm := mul_le_mul_of_nonneg_left h2 h3
        linarith only [hm, hsq]
      have h4 : (goodConst h (iterKappa d) (iterCstab d)
            * badConst (iterKappa d) (iterCstab d)) ^ 3
            * (18 * iterCi d ^ 2 * (1 + 45 / 2 * iterCi d))
          ≤ (goodConst h (iterKappa d) (iterCstab d)
            * badConst (iterKappa d) (iterCstab d)) ^ 3 * iterKappa d ^ (h + 2)
            * (18 * iterCi d ^ 2 * (1 + 45 / 2 * iterCi d)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by linarith only [hA3])
        have hm := mul_le_mul_of_nonneg_left hκpow hX0
        linarith only [hm]
      linarith only [h1, h4]
    linarith only [hstep, hmaster]
  have hpow := pow_succ_mul_le (X := (goodConst h (iterKappa d) (iterCstab d)
      * badConst (iterKappa d) (iterCstab d)) ^ 3) (Z := 9 * iterCi d ^ 2)
    (Y := Real.exp (iterConst d * ((h : ℝ) + 1))) c
    (pow_nonneg (by linarith only [hgcbc]) 3) hZ hXZ
  have hidx : (goodConst h (iterKappa d) (iterCstab d)
        * badConst (iterKappa d) (iterCstab d)) ^ (3 * c + 3)
      = ((goodConst h (iterKappa d) (iterCstab d)
        * badConst (iterKappa d) (iterCstab d)) ^ 3) ^ (c + 1) := by
    rw [← pow_mul, show 3 * (c + 1) = 3 * c + 3 from by ring]
  rw [hidx, ← exp_pow_eq c]
  calc 9 * iterCi d ^ 2
        * ((goodConst h (iterKappa d) (iterCstab d)
          * badConst (iterKappa d) (iterCstab d)) ^ 3) ^ (c + 1)
      = ((goodConst h (iterKappa d) (iterCstab d)
          * badConst (iterKappa d) (iterCstab d)) ^ 3) ^ (c + 1)
        * (9 * iterCi d ^ 2) := by ring
    _ ≤ Real.exp (iterConst d * ((h : ℝ) + 1)) ^ (c + 1) := hpow

/-- **Conclusion (ii)'s prefactor budget.** -/
theorem iterBudgetTwo (d : ℕ) {h : ℕ} (hh : 1 ≤ h) (c : ℕ) :
    (2 * iterKappa d ^ (h + 2)) ^ (c + 1)
        * ((1 + 45 / 2 * iterCi d)
          * (goodConst h (iterKappa d) (iterCstab d)
            * badConst (iterKappa d) (iterCstab d)) ^ (3 * c + 3))
      ≤ Real.exp (iterConst d * ((h : ℝ) + 1) * ((c : ℝ) + 1)) := by
  have hκ : (1 : ℝ) ≤ iterKappa d := one_le_iterKappa d
  have hCs : (0 : ℝ) ≤ iterCstab d := iterCstab_nonneg d
  have hCi : (1 : ℝ) ≤ iterCi d := one_le_iterCi d
  have hbc : (1 : ℝ) ≤ badConst (iterKappa d) (iterCstab d) := one_le_iterBadConst d
  have hgc : (1 : ℝ) ≤ goodConst h (iterKappa d) (iterCstab d) :=
    one_le_goodConst h hκ hCs
  have hgcbc : (1 : ℝ) ≤ goodConst h (iterKappa d) (iterCstab d)
      * badConst (iterKappa d) (iterCstab d) := by
    have hm := mul_le_mul_of_nonneg_left hbc (by linarith only [hgc] :
      (0 : ℝ) ≤ goodConst h (iterKappa d) (iterCstab d))
    linarith only [hm, hgc]
  have hgcbc3 : (1 : ℝ) ≤ (goodConst h (iterKappa d) (iterCstab d)
      * badConst (iterKappa d) (iterCstab d)) ^ 3 := one_le_pow₀ hgcbc
  have hκpow : (1 : ℝ) ≤ iterKappa d ^ (h + 2) := one_le_pow₀ hκ
  have hZ : (1 : ℝ) ≤ 1 + 45 / 2 * iterCi d := by linarith only [hCi]
  have hmaster := iterMaster d hh
  -- the per-level factor
  have hXZ : (2 * iterKappa d ^ (h + 2)
        * (goodConst h (iterKappa d) (iterCstab d)
          * badConst (iterKappa d) (iterCstab d)) ^ 3) * (1 + 45 / 2 * iterCi d)
      ≤ Real.exp (iterConst d * ((h : ℝ) + 1)) := by
    have hid : (2 * iterKappa d ^ (h + 2)
          * (goodConst h (iterKappa d) (iterCstab d)
            * badConst (iterKappa d) (iterCstab d)) ^ 3) * (1 + 45 / 2 * iterCi d)
        = (goodConst h (iterKappa d) (iterCstab d)
            * badConst (iterKappa d) (iterCstab d)) ^ 3 * iterKappa d ^ (h + 2)
          * (2 * (1 + 45 / 2 * iterCi d)) := by ring
    have hstep : (goodConst h (iterKappa d) (iterCstab d)
            * badConst (iterKappa d) (iterCstab d)) ^ 3 * iterKappa d ^ (h + 2)
          * (2 * (1 + 45 / 2 * iterCi d))
        ≤ (goodConst h (iterKappa d) (iterCstab d)
            * badConst (iterKappa d) (iterCstab d)) ^ 3 * iterKappa d ^ (h + 2)
          * (18 * iterCi d ^ 2 * (1 + 45 / 2 * iterCi d)) := by
      refine mul_le_mul_of_nonneg_left ?_ ?_
      · have h1 : (1 : ℝ) ≤ iterCi d ^ 2 := one_le_pow₀ hCi
        have hm := mul_le_mul_of_nonneg_right (by linarith only [h1] :
          (2 : ℝ) ≤ 18 * iterCi d ^ 2) (by linarith only [hZ] :
          (0 : ℝ) ≤ 1 + 45 / 2 * iterCi d)
        linarith only [hm]
      · have hm := mul_le_mul_of_nonneg_left hκpow (by linarith only [hgcbc3] :
          (0 : ℝ) ≤ (goodConst h (iterKappa d) (iterCstab d)
            * badConst (iterKappa d) (iterCstab d)) ^ 3)
        linarith only [hm, hgcbc3]
    rw [hid]
    linarith only [hstep, hmaster]
  have hX0 : (0 : ℝ) ≤ 2 * iterKappa d ^ (h + 2)
      * (goodConst h (iterKappa d) (iterCstab d)
        * badConst (iterKappa d) (iterCstab d)) ^ 3 := by
    have h1 : (0 : ℝ) ≤ 2 * iterKappa d ^ (h + 2) := by linarith only [hκpow]
    exact mul_nonneg h1 (by linarith only [hgcbc3])
  have hpow := pow_succ_mul_le (X := 2 * iterKappa d ^ (h + 2)
      * (goodConst h (iterKappa d) (iterCstab d)
        * badConst (iterKappa d) (iterCstab d)) ^ 3)
    (Z := 1 + 45 / 2 * iterCi d) (Y := Real.exp (iterConst d * ((h : ℝ) + 1))) c
    hX0 hZ hXZ
  have hidx : (goodConst h (iterKappa d) (iterCstab d)
        * badConst (iterKappa d) (iterCstab d)) ^ (3 * c + 3)
      = ((goodConst h (iterKappa d) (iterCstab d)
        * badConst (iterKappa d) (iterCstab d)) ^ 3) ^ (c + 1) := by
    rw [← pow_mul, show 3 * (c + 1) = 3 * c + 3 from by ring]
  rw [hidx, ← exp_pow_eq c]
  calc (2 * iterKappa d ^ (h + 2)) ^ (c + 1)
        * ((1 + 45 / 2 * iterCi d)
          * ((goodConst h (iterKappa d) (iterCstab d)
            * badConst (iterKappa d) (iterCstab d)) ^ 3) ^ (c + 1))
      = (2 * iterKappa d ^ (h + 2)
          * (goodConst h (iterKappa d) (iterCstab d)
            * badConst (iterKappa d) (iterCstab d)) ^ 3) ^ (c + 1)
        * (1 + 45 / 2 * iterCi d) := by
        rw [mul_pow]
        ring
    _ ≤ Real.exp (iterConst d * ((h : ℝ) + 1)) ^ (c + 1) := hpow

/-! ### The two prefactors in the exact shape the provider consumes -/

/-- **Conclusion (i)'s prefactor, with the `∑ε` exponential folded in.** -/
theorem iterPrefactorOne_le (d : ℕ) {h : ℕ} (hh : 1 ≤ h) (c : ℕ) {Se : ℝ}
    (hSe : 0 ≤ Se) :
    9 * iterCi d ^ 2
        * ((goodConst h (iterKappa d) (iterCstab d)
            * badConst (iterKappa d) (iterCstab d)) ^ (3 * c + 3)
          * Real.exp (goodRate (iterCstab d) * Se))
      ≤ Real.exp (iterConst d * ((h : ℝ) + 1) * ((c : ℝ) + 1) + iterConst d * Se) := by
  have hb := iterBudgetOne d hh c
  have hexp : Real.exp (goodRate (iterCstab d) * Se) ≤ Real.exp (iterConst d * Se) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (goodRate_le_iterConst d) hSe)
  have hid : 9 * iterCi d ^ 2
        * ((goodConst h (iterKappa d) (iterCstab d)
            * badConst (iterKappa d) (iterCstab d)) ^ (3 * c + 3)
          * Real.exp (goodRate (iterCstab d) * Se))
      = 9 * iterCi d ^ 2
          * (goodConst h (iterKappa d) (iterCstab d)
            * badConst (iterKappa d) (iterCstab d)) ^ (3 * c + 3)
        * Real.exp (goodRate (iterCstab d) * Se) := by ring
  rw [hid, Real.exp_add]
  exact mul_le_mul hb hexp (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))

/-- **Conclusion (ii)'s prefactor**, in the exact shape the weighted assembly produces:
the `θ`-payback `(κθ^{-1})^{h+2}` per level is split into the `κ`-part, absorbed by the
`exp` factor, and the `θ`-part, absorbed by the frozen statement's `θ^{-C(h+1)(|B|+1)}`
(legitimate because `C ≥ 2` and `(h+2)(c+1) ≤ 2(h+1)(c+1)`). -/
theorem iterPrefactorTwo_le (d : ℕ) {h : ℕ} (hh : 1 ≤ h) (c : ℕ) {θ Se : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hSe : 0 ≤ Se) :
    (2 * (iterKappa d * θ⁻¹) ^ (h + 2)) ^ (c + 1)
        * (1 + 45 / 2 * iterCi d
          * ((goodConst h (iterKappa d) (iterCstab d)
              * badConst (iterKappa d) (iterCstab d)) ^ (3 * c + 3)
            * Real.exp (goodRate (iterCstab d) * Se)))
      ≤ Real.rpow θ (-(iterConst d * ((h : ℝ) + 1) * ((c : ℝ) + 1)))
        * Real.exp (iterConst d * ((h : ℝ) + 1) * ((c : ℝ) + 1) + iterConst d * Se) := by
  have hκ : (1 : ℝ) ≤ iterKappa d := one_le_iterKappa d
  have hCs : (0 : ℝ) ≤ iterCstab d := iterCstab_nonneg d
  have hCi : (1 : ℝ) ≤ iterCi d := one_le_iterCi d
  have hbc : (1 : ℝ) ≤ badConst (iterKappa d) (iterCstab d) := one_le_iterBadConst d
  have hgc : (1 : ℝ) ≤ goodConst h (iterKappa d) (iterCstab d) :=
    one_le_goodConst h hκ hCs
  have hgcbc : (1 : ℝ) ≤ goodConst h (iterKappa d) (iterCstab d)
      * badConst (iterKappa d) (iterCstab d) := by
    have hm := mul_le_mul_of_nonneg_left hbc (by linarith only [hgc] :
      (0 : ℝ) ≤ goodConst h (iterKappa d) (iterCstab d))
    linarith only [hm, hgc]
  have hgcbcp : (1 : ℝ) ≤ (goodConst h (iterKappa d) (iterCstab d)
      * badConst (iterKappa d) (iterCstab d)) ^ (3 * c + 3) := one_le_pow₀ hgcbc
  have hexp1 : (1 : ℝ) ≤ Real.exp (goodRate (iterCstab d) * Se) := by
    rw [Real.one_le_exp_iff]
    exact mul_nonneg (goodRate_nonneg hCs) hSe
  have hκpow : (0 : ℝ) ≤ 2 * iterKappa d ^ (h + 2) := by
    have h1 : (1 : ℝ) ≤ iterKappa d ^ (h + 2) := one_le_pow₀ hκ
    linarith only [h1]
  -- split the level factor into its `κ`- and `θ`-parts
  have hsplit : (2 * (iterKappa d * θ⁻¹) ^ (h + 2)) ^ (c + 1)
      = (2 * iterKappa d ^ (h + 2)) ^ (c + 1) * (θ⁻¹) ^ ((h + 2) * (c + 1)) := by
    rw [mul_pow (iterKappa d) θ⁻¹ (h + 2),
      show 2 * (iterKappa d ^ (h + 2) * (θ⁻¹) ^ (h + 2))
        = 2 * iterKappa d ^ (h + 2) * (θ⁻¹) ^ (h + 2) from by ring,
      mul_pow, ← pow_mul]
  -- the `K`-factor
  have hKle : 1 + 45 / 2 * iterCi d
        * ((goodConst h (iterKappa d) (iterCstab d)
            * badConst (iterKappa d) (iterCstab d)) ^ (3 * c + 3)
          * Real.exp (goodRate (iterCstab d) * Se))
      ≤ (1 + 45 / 2 * iterCi d)
          * (goodConst h (iterKappa d) (iterCstab d)
            * badConst (iterKappa d) (iterCstab d)) ^ (3 * c + 3)
        * Real.exp (goodRate (iterCstab d) * Se) := by
    have hprod : (1 : ℝ) ≤ (goodConst h (iterKappa d) (iterCstab d)
          * badConst (iterKappa d) (iterCstab d)) ^ (3 * c + 3)
        * Real.exp (goodRate (iterCstab d) * Se) := by
      have hm := mul_le_mul hgcbcp hexp1 (by norm_num) (by linarith only [hgcbcp])
      linarith only [hm]
    have hid : (1 + 45 / 2 * iterCi d)
          * (goodConst h (iterKappa d) (iterCstab d)
            * badConst (iterKappa d) (iterCstab d)) ^ (3 * c + 3)
        * Real.exp (goodRate (iterCstab d) * Se)
        = (goodConst h (iterKappa d) (iterCstab d)
            * badConst (iterKappa d) (iterCstab d)) ^ (3 * c + 3)
            * Real.exp (goodRate (iterCstab d) * Se)
          + 45 / 2 * iterCi d
            * ((goodConst h (iterKappa d) (iterCstab d)
              * badConst (iterKappa d) (iterCstab d)) ^ (3 * c + 3)
              * Real.exp (goodRate (iterCstab d) * Se)) := by ring
    rw [hid]
    linarith only [hprod]
  -- the `κ`-part of the level factor against the master budget
  have hmain : (2 * iterKappa d ^ (h + 2)) ^ (c + 1)
        * ((1 + 45 / 2 * iterCi d)
            * (goodConst h (iterKappa d) (iterCstab d)
              * badConst (iterKappa d) (iterCstab d)) ^ (3 * c + 3)
          * Real.exp (goodRate (iterCstab d) * Se))
      ≤ Real.exp (iterConst d * ((h : ℝ) + 1) * ((c : ℝ) + 1) + iterConst d * Se) := by
    have hb := iterBudgetTwo d hh c
    have hexp : Real.exp (goodRate (iterCstab d) * Se) ≤ Real.exp (iterConst d * Se) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (goodRate_le_iterConst d) hSe)
    have hid : (2 * iterKappa d ^ (h + 2)) ^ (c + 1)
          * ((1 + 45 / 2 * iterCi d)
              * (goodConst h (iterKappa d) (iterCstab d)
                * badConst (iterKappa d) (iterCstab d)) ^ (3 * c + 3)
            * Real.exp (goodRate (iterCstab d) * Se))
        = (2 * iterKappa d ^ (h + 2)) ^ (c + 1)
            * ((1 + 45 / 2 * iterCi d)
              * (goodConst h (iterKappa d) (iterCstab d)
                * badConst (iterKappa d) (iterCstab d)) ^ (3 * c + 3))
          * Real.exp (goodRate (iterCstab d) * Se) := by ring
    rw [hid, Real.exp_add]
    exact mul_le_mul hb hexp (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))
  -- the `θ`-part against the frozen `θ`-power
  have hθpart : (θ⁻¹) ^ ((h + 2) * (c + 1))
      ≤ Real.rpow θ (-(iterConst d * ((h : ℝ) + 1) * ((c : ℝ) + 1))) := by
    have hid : (θ⁻¹) ^ ((h + 2) * (c + 1))
        = Real.rpow θ (-(((h + 2) * (c + 1) : ℕ) : ℝ)) := by
      change (θ⁻¹) ^ ((h + 2) * (c + 1)) = θ ^ (-(((h + 2) * (c + 1) : ℕ) : ℝ))
      rw [Real.rpow_neg (le_of_lt hθ0), Real.rpow_natCast, ← inv_pow]
    rw [hid]
    refine Real.rpow_le_rpow_of_exponent_ge hθ0 hθ1 ?_
    have hcast : (((h + 2) * (c + 1) : ℕ) : ℝ) = ((h : ℝ) + 2) * ((c : ℝ) + 1) := by
      push_cast
      ring
    rw [hcast]
    have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
    have hc0 : (0 : ℝ) ≤ (c : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) c
      linarith only [this]
    have h1 : ((h : ℝ) + 2) ≤ iterConst d * ((h : ℝ) + 1) := by
      have hm := mul_le_mul_of_nonneg_right (two_le_iterConst d)
        (by linarith only [hh0] : (0 : ℝ) ≤ (h : ℝ) + 1)
      linarith only [hm, hh0]
    have hm := mul_le_mul_of_nonneg_right h1 hc0
    linarith only [hm]
  -- assemble
  have hK0 : (0 : ℝ) ≤ 1 + 45 / 2 * iterCi d
      * ((goodConst h (iterKappa d) (iterCstab d)
          * badConst (iterKappa d) (iterCstab d)) ^ (3 * c + 3)
        * Real.exp (goodRate (iterCstab d) * Se)) := by
    have h1 : (0 : ℝ) ≤ 45 / 2 * iterCi d := by linarith only [hCi]
    have h2 : (0 : ℝ) ≤ (goodConst h (iterKappa d) (iterCstab d)
        * badConst (iterKappa d) (iterCstab d)) ^ (3 * c + 3)
      * Real.exp (goodRate (iterCstab d) * Se) := by
      have hm := mul_le_mul hgcbcp hexp1 (by norm_num) (by linarith only [hgcbcp])
      linarith only [hm]
    have hm := mul_nonneg h1 h2
    linarith only [hm]
  have hstep : (2 * iterKappa d ^ (h + 2)) ^ (c + 1)
        * (1 + 45 / 2 * iterCi d
          * ((goodConst h (iterKappa d) (iterCstab d)
              * badConst (iterKappa d) (iterCstab d)) ^ (3 * c + 3)
            * Real.exp (goodRate (iterCstab d) * Se)))
      ≤ Real.exp (iterConst d * ((h : ℝ) + 1) * ((c : ℝ) + 1) + iterConst d * Se) := by
    have hm := mul_le_mul_of_nonneg_left hKle (pow_nonneg hκpow (c + 1))
    exact le_trans hm hmain
  rw [hsplit]
  have hfin : (2 * iterKappa d ^ (h + 2)) ^ (c + 1) * (θ⁻¹) ^ ((h + 2) * (c + 1))
        * (1 + 45 / 2 * iterCi d
          * ((goodConst h (iterKappa d) (iterCstab d)
              * badConst (iterKappa d) (iterCstab d)) ^ (3 * c + 3)
            * Real.exp (goodRate (iterCstab d) * Se)))
      = ((2 * iterKappa d ^ (h + 2)) ^ (c + 1)
          * (1 + 45 / 2 * iterCi d
            * ((goodConst h (iterKappa d) (iterCstab d)
                * badConst (iterKappa d) (iterCstab d)) ^ (3 * c + 3)
              * Real.exp (goodRate (iterCstab d) * Se))))
        * (θ⁻¹) ^ ((h + 2) * (c + 1)) := by ring
  rw [hfin, mul_comm (Real.rpow θ (-(iterConst d * ((h : ℝ) + 1) * ((c : ℝ) + 1))))]
  exact mul_le_mul hstep hθpart (pow_nonneg (by
      have hi : 1 ≤ θ⁻¹ := one_le_inv_of_le_one hθ0 hθ1
      linarith only [hi]) _) (le_of_lt (Real.exp_pos _))

end

end Algsuperdiff.Section4.Provider.ExcessDecay
