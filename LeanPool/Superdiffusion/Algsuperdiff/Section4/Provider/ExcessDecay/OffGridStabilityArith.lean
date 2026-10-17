/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.MultiscaleEllipticity
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# OffGridStabilityArith

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The exponent and constant bookkeeping of the off-grid transport

The printed proof of `l.lambdas.stability` (ABK26) closes with a **double
geometric sum**: an inner sum over the depths of the greedy family,

```
∑_{n ≤ k} 3^{-2sn} · C 3^{n-k}  =  C 3^{-2sk} / (1 - 3^{-(1-2s)}) ,
```

and an outer sum over the scales of the target quantity, which together produce
the printed constant

```
C / (1 - 2s) · ( t / (t - s) )^{2/q} .
```

This module proves both sums and the constant, at `q = 2` and in the exact
`Homogenization.geometricWeight` normalization CoarseGraining's `𝓔_{·,∞,2}`
uses.  It is pure real analysis: no cube, no coefficient field, no error
functional appears.

## The two elementary inequalities that drive everything

For `y ∈ (0,1]`,

```
y / 2  ≤  1 - 3^{-y}  ≤  (3/2) y ,
```

the left from `e^z ≥ 1 + z` together with `1 ≤ log 3` (i.e. `e < 3`), the right
from `e^{-z} ≥ 1 - z` together with `log 3 ≤ 3/2` (i.e. `3 ≤ e^{3/2}`).  Both
sides are needed: the lower bound converts the two geometric denominators into
`2/(1-2u)` and `1/(t-u)`, and the upper bound converts the *numerator*
`c_{2t} = 1 - 3^{-2t}` into `3t`, which is what turns the naive `1/(t-u)` into
the printed `t/(t-u)`.

No `nlinarith` is used anywhere near an `rpow`/`exp` atom: every transcendental
step is isolated in a named `private` lemma and consumed through
`linarith only [...]`.

## The bookkeeping, end to end

With `k` the scale of the off-grid cube, `K` the scale of the enclosing grid
cube, `j = K - k`, `u` the index of the parent cap and `t` the index asked of
the off-grid cube (`0 < u < t ≤ 1/2`):

| step | input | output |
| --- | --- | --- |
| packing (geometry) | `∑_{depth δ} |Q|/|V| ≤ 2d·3^{1-δ}` | `C = 6d` |
| per-cube cap | `J(Q) ≤ 3^{2u(K - scale Q)}·𝓔_u²` | `3^{2uj}·3^{2u(l+δ)}·𝓔_u²` |
| inner sum | `tsum_depth_le` | `12d/(1-2u)` |
| outer sum | `tsum_geometricWeight_two_mul_le` | `3t/(t-u)` |
| product | `offGridStabilityConst` | `36dt/((t-u)(1-2u))` |

At the printed slot `(t,u) = (s/6, s/8)` of `e.mathcalE.stability.applied` this
is `36d·(s/6)/((s/24)(1 - s/4)) = 144 d/(1 - s/4) ≤ 192 d` for `s ≤ 1`: a pure
`C(d)`, with **no** `s`-power deviation from the printed constant.

## Main results

* `half_le_one_sub_rpow_three_neg`, `one_sub_rpow_three_neg_le` — the two-sided
  elementary bound.
* `tsum_depth_le` — the inner (greedy-family depth) sum.
* `tsum_geometricWeight_two_mul_le` — the outer (scale) sum.
* `offGridStabilityConst`, `offGridStabilityConst_slot_le` — the constant and
  its value at the printed slot.
* `offGridStabilityError_bound` — the shared nonnegative error-factor cap for any
  scale exponent at most one.

## References

* ABK26, `l.lambdas.stability`, (both geometric sums).
* ABK26, `e.mathcalE.stability.applied`, (the slot).
* CoarseGraining, `Homogenization/Book/Ch02/MultiscaleEllipticity.lean`
  (`geometricWeight`, `geometricDiscount`).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book

noncomputable section

/-! ## 0. Abstract-real helpers

Every step that would otherwise put a nonlinear tactic in sight of an `exp`,
`log` or `rpow` atom is isolated here as a statement about abstract reals. -/

private theorem aux_cube {E : ℝ} (hE : (3 / 2 : ℝ) ≤ E) : (3 : ℝ) ≤ E * E * E := by
  nlinarith only [hE]

private theorem aux_two_z_ge {y L : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) (hL : 1 ≤ L) :
    y * (1 + y * L) ≤ 2 * (y * L) := by
  have hLnn : (0 : ℝ) ≤ L := le_trans zero_le_one hL
  have hyLnn : (0 : ℝ) ≤ y * L := mul_nonneg hy0.le hLnn
  have h1 : y * (y * L) ≤ 1 * (y * L) := mul_le_mul_of_nonneg_right hy1 hyLnn
  have h2 : y * 1 ≤ y * L := mul_le_mul_of_nonneg_left hL hy0.le
  linarith only [h1, h2]

private theorem aux_inv_le {y z : ℝ} (hz : 0 < z) (h : y * (1 + z) ≤ 2 * z) :
    (1 + z)⁻¹ ≤ 1 - y / 2 := by
  have hpos : (0 : ℝ) < 1 + z := by linarith only [hz]
  rw [inv_eq_one_div, div_le_iff₀ hpos]
  nlinarith only [h]

private theorem aux_log_mul {y L : ℝ} (hy : 0 ≤ y) (hL : L ≤ (3 / 2 : ℝ)) :
    y * L ≤ (3 / 2 : ℝ) * y := by
  nlinarith only [hy, hL]

/-! ## 1. The two elementary bounds on `1 - 3^{-y}` -/

/-- `e < 3`, hence `1 ≤ log 3`. -/
theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  have hexp : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h := (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2 hexp
  exact h.le

/-- `3 ≤ e^{3/2}`, hence `log 3 ≤ 3/2`. -/
theorem log_three_le : Real.log 3 ≤ (3 / 2 : ℝ) := by
  have hhalf : (3 / 2 : ℝ) ≤ Real.exp (1 / 2 : ℝ) := by
    have := Real.add_one_le_exp (1 / 2 : ℝ)
    linarith only [this]
  have hcube : Real.exp (3 / 2 : ℝ) =
      Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) := by
    rw [← Real.exp_add, ← Real.exp_add]
    norm_num
  have h3 : (3 : ℝ) ≤ Real.exp (3 / 2 : ℝ) := by
    rw [hcube]
    exact aux_cube hhalf
  exact (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 3)).2 h3

private theorem rpow_three_neg_eq_exp (y : ℝ) :
    (3 : ℝ) ^ (-y) = Real.exp (-(y * Real.log 3)) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-- **The lower bound.**  For `y ∈ (0,1]`, `y/2 ≤ 1 - 3^{-y}`.

This is what converts the two geometric denominators of the printed proof into
`2/(1-2s)` and `1/(t-s)`. -/
theorem half_le_one_sub_rpow_three_neg {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    y / 2 ≤ 1 - (3 : ℝ) ^ (-y) := by
  have hL : (1 : ℝ) ≤ Real.log 3 := one_le_log_three
  have hLpos : (0 : ℝ) < Real.log 3 := by linarith only [hL]
  have hzpos : 0 < y * Real.log 3 := mul_pos hy0 hLpos
  have hexpz : 1 + y * Real.log 3 ≤ Real.exp (y * Real.log 3) := by
    have := Real.add_one_le_exp (y * Real.log 3)
    linarith only [this]
  have hinv : Real.exp (-(y * Real.log 3)) ≤ (1 + y * Real.log 3)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (by linarith only [hzpos]) hexpz
  have hkey : y * (1 + y * Real.log 3) ≤ 2 * (y * Real.log 3) := aux_two_z_ge hy0 hy1 hL
  have h2 : (1 + y * Real.log 3)⁻¹ ≤ 1 - y / 2 := aux_inv_le hzpos hkey
  rw [rpow_three_neg_eq_exp]
  linarith only [hinv, h2]

/-- **The upper bound.**  For `0 ≤ y`, `1 - 3^{-y} ≤ (3/2) y`.

This is what turns the numerator `c_{2t} = 1 - 3^{-2t}` into `3t`, hence the
naive `1/(t-s)` into the printed `t/(t-s)`. -/
theorem one_sub_rpow_three_neg_le {y : ℝ} (hy : 0 ≤ y) :
    1 - (3 : ℝ) ^ (-y) ≤ (3 / 2 : ℝ) * y := by
  have hexp : 1 + -(y * Real.log 3) ≤ Real.exp (-(y * Real.log 3)) := by
    have := Real.add_one_le_exp (-(y * Real.log 3))
    linarith only [this]
  have hzle : y * Real.log 3 ≤ (3 / 2 : ℝ) * y := aux_log_mul hy log_three_le
  rw [rpow_three_neg_eq_exp]
  linarith only [hexp, hzle]

/-! ## 2. The geometric engine -/

private theorem rpow_three_neg_pow (y : ℝ) (n : ℕ) :
    ((3 : ℝ) ^ (-y)) ^ n = (3 : ℝ) ^ (-(y * (n : ℝ))) := by
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (-y)) n, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

/-- **The geometric engine.**  A nonnegative sequence dominated by
`C · (3^{-y})^n` is summable with sum at most `2C/y`. -/
theorem summable_and_tsum_le_of_le_geometric {y C : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hC : 0 ≤ C) (f : ℕ → ℝ) (hf0 : ∀ n, 0 ≤ f n)
    (hf : ∀ n, f n ≤ C * ((3 : ℝ) ^ (-y)) ^ n) :
    Summable f ∧ ∑' n : ℕ, f n ≤ 2 * C / y := by
  set r : ℝ := (3 : ℝ) ^ (-y) with hr
  have hrpos : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hlow : y / 2 ≤ 1 - r := half_le_one_sub_rpow_three_neg hy0 hy1
  have hr1 : r < 1 := by linarith only [hlow, hy0]
  have hgeo : Summable fun n : ℕ => C * r ^ n :=
    (summable_geometric_of_lt_one hrpos.le hr1).mul_left C
  have hsum : Summable f := Summable.of_nonneg_of_le hf0 hf hgeo
  refine ⟨hsum, ?_⟩
  have hle : ∑' n : ℕ, f n ≤ ∑' n : ℕ, C * r ^ n :=
    Summable.tsum_le_tsum hf hsum hgeo
  have hgeoEq : ∑' n : ℕ, C * r ^ n = C * (1 - r)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hrpos.le hr1]
  have hinvle : (1 - r)⁻¹ ≤ 2 / y := by
    have h1 : (1 - r)⁻¹ ≤ (y / 2)⁻¹ := inv_anti₀ (by linarith only [hy0]) hlow
    have h2 : (y / 2 : ℝ)⁻¹ = 2 / y := by
      field_simp
    rwa [h2] at h1
  calc ∑' n : ℕ, f n ≤ C * (1 - r)⁻¹ := by rw [← hgeoEq]; exact hle
    _ ≤ C * (2 / y) := mul_le_mul_of_nonneg_left hinvle hC
    _ = 2 * C / y := by ring

/-! ## 3. The inner sum: the greedy-family depths -/

/-- **The inner sum of the printed proof.**

If the depth-`δ` weight of the greedy family is at most `C·3^{-δ}` — which is
the covering geometry's packing count with `C = 6d` — then, after the per-cube
cap has contributed its `3^{2uδ}`, the depth sum is at most `2C/(1-2u)`.

This is `∑_{n ≤ k} 3^{-2un}·C·3^{n-k} ≤ C·3^{-2uk}·2/(1-2u)` in the depth
variable `δ = k - n`. -/
theorem tsum_depth_le {u C : ℝ} (hu0 : 0 < u) (hu : u < 1 / 2) (hC : 0 ≤ C)
    (W : ℕ → ℝ) (hW0 : ∀ n : ℕ, 0 ≤ W n)
    (hW : ∀ n : ℕ, W n ≤ C * (3 : ℝ) ^ (-(n : ℝ))) :
    (Summable fun n : ℕ => W n * (3 : ℝ) ^ (2 * u * (n : ℝ))) ∧
      ∑' n : ℕ, W n * (3 : ℝ) ^ (2 * u * (n : ℝ)) ≤ 2 * C / (1 - 2 * u) := by
  have hy0 : (0 : ℝ) < 1 - 2 * u := by linarith only [hu]
  have hy1 : (1 : ℝ) - 2 * u ≤ 1 := by linarith only [hu0]
  refine summable_and_tsum_le_of_le_geometric hy0 hy1 hC _ ?_ ?_
  · intro n
    exact mul_nonneg (hW0 n) (Real.rpow_nonneg (by norm_num) _)
  · intro n
    have hpow : (0 : ℝ) < (3 : ℝ) ^ (2 * u * (n : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have hstep : W n * (3 : ℝ) ^ (2 * u * (n : ℝ)) ≤
        C * (3 : ℝ) ^ (-(n : ℝ)) * (3 : ℝ) ^ (2 * u * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right (hW n) hpow.le
    have hmerge : (3 : ℝ) ^ (-(n : ℝ)) * (3 : ℝ) ^ (2 * u * (n : ℝ)) =
        ((3 : ℝ) ^ (-(1 - 2 * u))) ^ n := by
      rw [rpow_three_neg_pow, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    calc W n * (3 : ℝ) ^ (2 * u * (n : ℝ))
        ≤ C * (3 : ℝ) ^ (-(n : ℝ)) * (3 : ℝ) ^ (2 * u * (n : ℝ)) := hstep
      _ = C * ((3 : ℝ) ^ (-(n : ℝ)) * (3 : ℝ) ^ (2 * u * (n : ℝ))) := by ring
      _ = C * ((3 : ℝ) ^ (-(1 - 2 * u))) ^ n := by rw [hmerge]

/-! ## 4. The outer sum: the scales of `𝓔_{·,∞,2}` -/

/-- **The outer sum of the printed proof, in CoarseGraining's own weight
normalization.**

If the shell maxima `M l` of the off-grid cube obey `M l ≤ A·3^{2ul}` — which is
what the inner sum delivers — then the `𝓔_{t,∞,2}`-weighted series is at most
`3t/(t-u)·A`.  The factor `t` in the numerator is the printed
`(t/(t-s))^{2/q}` at `q = 2`; it comes from `c_{2t} = 1 - 3^{-2t} ≤ 3t`. -/
theorem tsum_geometricWeight_two_mul_le {t u A : ℝ} (hu0 : 0 < u) (hut : u < t)
    (ht : t ≤ 1 / 2) (hA : 0 ≤ A) (M : ℕ → ℝ) (hM0 : ∀ l : ℕ, 0 ≤ M l)
    (hM : ∀ l : ℕ, M l ≤ A * (3 : ℝ) ^ (2 * u * (l : ℝ))) :
    (Summable fun l : ℕ => Ch02.geometricWeight t 2 l * M l) ∧
      ∑' l : ℕ, Ch02.geometricWeight t 2 l * M l ≤ 3 * t / (t - u) * A := by
  have ht0 : 0 < t := hu0.trans hut
  have hy0 : (0 : ℝ) < 2 * (t - u) := by linarith only [hut]
  have hy1 : 2 * (t - u) ≤ 1 := by linarith only [ht, hu0]
  set c : ℝ := 1 - (3 : ℝ) ^ (-(t * 2)) with hc
  have hcnn : 0 ≤ c := by
    have := half_le_one_sub_rpow_three_neg (y := t * 2) (by linarith only [ht0])
      (by linarith only [ht])
    rw [hc]
    linarith only [this, ht0]
  have hcle : c ≤ 3 * t := by
    have := one_sub_rpow_three_neg_le (y := t * 2) (by linarith only [ht0])
    rw [hc]
    linarith only [this]
  have hCnn : 0 ≤ c * A := mul_nonneg hcnn hA
  have hweight : ∀ l : ℕ, Ch02.geometricWeight t 2 l = c * (3 : ℝ) ^ (-(t * 2) * (l : ℝ)) := by
    intro l
    rw [Ch02.geometricWeight, Ch02.geometricDiscount, hc,
      show (-t * 2 : ℝ) = -(t * 2) from by ring]
    rfl
  have hterm : ∀ l : ℕ, Ch02.geometricWeight t 2 l * M l ≤
      c * A * ((3 : ℝ) ^ (-(2 * (t - u)))) ^ l := by
    intro l
    have hwpos : (0 : ℝ) ≤ (3 : ℝ) ^ (-(t * 2) * (l : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have hstep : Ch02.geometricWeight t 2 l * M l ≤
        c * (3 : ℝ) ^ (-(t * 2) * (l : ℝ)) * (A * (3 : ℝ) ^ (2 * u * (l : ℝ))) := by
      rw [hweight l]
      exact mul_le_mul_of_nonneg_left (hM l) (mul_nonneg hcnn hwpos)
    have hmerge : (3 : ℝ) ^ (-(t * 2) * (l : ℝ)) * (3 : ℝ) ^ (2 * u * (l : ℝ)) =
        ((3 : ℝ) ^ (-(2 * (t - u)))) ^ l := by
      rw [rpow_three_neg_pow, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    calc Ch02.geometricWeight t 2 l * M l
        ≤ c * (3 : ℝ) ^ (-(t * 2) * (l : ℝ)) * (A * (3 : ℝ) ^ (2 * u * (l : ℝ))) := hstep
      _ = c * A * ((3 : ℝ) ^ (-(t * 2) * (l : ℝ)) * (3 : ℝ) ^ (2 * u * (l : ℝ))) := by ring
      _ = c * A * ((3 : ℝ) ^ (-(2 * (t - u)))) ^ l := by rw [hmerge]
  have hnn : ∀ l : ℕ, 0 ≤ Ch02.geometricWeight t 2 l * M l := by
    intro l
    refine mul_nonneg ?_ (hM0 l)
    rw [hweight l]
    exact mul_nonneg hcnn (Real.rpow_nonneg (by norm_num) _)
  obtain ⟨hsum, hle⟩ :=
    summable_and_tsum_le_of_le_geometric hy0 hy1 hCnn _ hnn hterm
  refine ⟨hsum, le_trans hle ?_⟩
  have hApos : 0 ≤ A := hA
  have hden : (0 : ℝ) < t - u := by linarith only [hut]
  have hstep : 2 * (c * A) / (2 * (t - u)) = c * A / (t - u) := by
    field_simp
  rw [hstep]
  rw [div_le_iff₀ hden]
  have hmul : c * A ≤ 3 * t * A := mul_le_mul_of_nonneg_right hcle hApos
  have hrw : 3 * t / (t - u) * A * (t - u) = 3 * t * A := by
    field_simp
  rw [hrw]
  exact hmul

/-! ## 5. The composed constant -/

/-- The constant of the off-grid transport at `q = 2`:
`36 d t / ((t-u)(1-2u))`, the product of the inner sum's `12d/(1-2u)` and the
outer sum's `3t/(t-u)`.  Compare the printed `C(d)(1-2s)^{-1}(t/(t-s))^{2/q}`. -/
def offGridStabilityConst (d : ℕ) (t u : ℝ) : ℝ :=
  36 * (d : ℝ) * t / ((t - u) * (1 - 2 * u))

theorem offGridStabilityConst_nonneg {d : ℕ} {t u : ℝ} (hu0 : 0 < u) (hut : u < t)
    (ht : t ≤ 1 / 2) : 0 ≤ offGridStabilityConst d t u := by
  have hden : (0 : ℝ) < (t - u) * (1 - 2 * u) := by
    refine mul_pos (by linarith only [hut]) ?_
    linarith only [ht, hut]
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have ht0 : (0 : ℝ) < t := hu0.trans hut
  have hnum : (0 : ℝ) ≤ 36 * (d : ℝ) * t := by
    have : (0 : ℝ) ≤ 36 * (d : ℝ) := by linarith only [hdnn]
    exact mul_nonneg this ht0.le
  exact div_nonneg hnum hden.le

/-- **The constant at the printed slot** `(t,u) = (s/6, s/8)` of
`e.mathcalE.stability.applied`: a pure `C(d)`, with no `s`-power deviation.
For `s ∈ (0,1]` it is at most `192 d`. -/
theorem offGridStabilityConst_slot_le {d : ℕ} {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    offGridStabilityConst d (s / 6) (s / 8) ≤ 192 * (d : ℝ) := by
  have hden : (0 : ℝ) < (s / 6 - s / 8) * (1 - 2 * (s / 8)) := by
    refine mul_pos (by linarith only [hs0]) ?_
    linarith only [hs1]
  rw [offGridStabilityConst, div_le_iff₀ hden]
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hkey : (0 : ℝ) ≤ (d : ℝ) * s * (1 - s) :=
    mul_nonneg (mul_nonneg hdnn hs0.le) (by linarith only [hs1])
  nlinarith only [hkey]

variable {d : ℕ}

/-- The off-grid error factor is bounded uniformly when its scale exponent is at most one. -/
theorem offGridStabilityError_bound {s exponent E : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hexponent : exponent ≤ 1) (hE : 0 ≤ E) :
    0 ≤ Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
        ((3 : ℝ) ^ exponent * E) ∧
      Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
        ((3 : ℝ) ^ exponent * E) ≤ (Real.sqrt (192 * (d : ℝ)) * 3) * E := by
  have hpower : (3 : ℝ) ^ exponent ≤ 3 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexponent
  have hpositive : 0 ≤ (3 : ℝ) ^ exponent * E :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) hE
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) hpositive, ?_⟩
  calc
    Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) * ((3 : ℝ) ^ exponent * E) ≤
        Real.sqrt (192 * (d : ℝ)) * (3 * E) :=
      mul_le_mul (Real.sqrt_le_sqrt (offGridStabilityConst_slot_le hs hs1))
        (mul_le_mul_of_nonneg_right hpower hE) hpositive (Real.sqrt_nonneg _)
    _ = (Real.sqrt (192 * (d : ℝ)) * 3) * E := by ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
