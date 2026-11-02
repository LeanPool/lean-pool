/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.MultiscaleEstimate.BadEventIngredients
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.Finite
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.DiscountBounds

/-!
# BadEventMaxSplit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Provider: the max-first extraction of the bad-event fourth term

This is a *provider endpoint only*.  It is not a source node, it creates and
modifies no frozen declaration, and it closes no source node, no instance of a
source node and no fraction of a source node.

## 1. The order that works

The printed derivation reads as three steps: a per-scale ceiling, then the
single-term bound in the series defining `E^2_{s,infty,2}`, then a replacement
of the `l`-sum by its `l`-max.  Steps 2 and 3 each hide a factor `~ s^{-1}` and
they compound, so the literal reading yields one power of `s^{-1}` past the
printed `E^2_{s/4} max_l (.)` — and that power is not absorbable.

The admissible order, formalized here, extracts the `max` first and pays
the `l`-sum once, against the definition of `E^2_{s/4}`:

```
   sum_l c_{2s} 3^{-s(m-l)} (max_z max_e J_l) (avsum 1_{not Q})^{s/d}
 = (c_{2s}/c_{s/2}) sum_l [ c_{s/2} 3^{-s(m-l)/2} (max_z max_e J_l) ]
                        . [ 3^{-s(m-l)/2} (avsum 1_{not Q})^{s/d} ]
 <= (c_{2s}/c_{s/2}) . ( max_l 3^{-s(m-l)/2}(avsum 1_{not Q})^{s/d} ) . E^2_{s/4}
```

Two facts make this work, and both are verified here against the *proved*
carriers rather than assumed:

* **The seam.**  The bracketed left factor is the `j`-th summand of the series
  defining `E^2_{s/4,infty,2}(cu_m)`.  `geometricWeight_quarter_two_eq` records
  the identity `Ch02.geometricWeight (s/4) 2 j = c_{s/2}. 3^{-(s/4).2.j}` (as
  the `(s/4, 2)` specialization of the proved in-closure
  `ErrorComparison.geometricWeight_eq'`, `FiniteQTransfer.lean`, which is
  itself the definitional `rfl`), and the upstream
  `Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum` states
  `E_{s/4,infty,2}(Q)^2 = sum_j Ch02.geometricWeight (s/4) 2 j.
  maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - j) a a0`, whose
  per-scale factor is the printed `max_z max_e J(z + cu_{m-j})`.  The index
  seam `s/4` versus `s/2` is therefore *sound as printed*: the series of `E^2`
  at the parameter `s/4` and `q = 2` carries the weight `c_{(s/4).2}
  3^{-(s/4).2.j} = c_{s/2} 3^{-s j/2}`.  No index is adjusted.
* **The constant is a pure `C(d)` — in fact `4`, and `4` is sharp.**  With
  `q := 3^{-s/2}` one has `3^{-2s} = q^4`, hence
  `c_{2s} = 1 - q^4 = (1-q)(1+q+q^2+q^3) <= 4(1-q) = 4 c_{s/2}` for every
  `s >= 0`, by pure factorization and with no transcendental input at all
  (`geometricDiscount_two_le_four_mul_quarter`).  The ratio
  `c_{2s}/c_{s/2}` increases to `4` as `s -> 0+` (numerically `3.967` at
  `s = 0.01`, `3.691` at `s = 0.1`, `2.103` at `s = 1`), so `4` is the least
  uniform constant on `(0,1]`.

The honest sharp constant is `4`, it is what is proved here, and it needs no
upper bound on `s` at all (only `0 <= s`).  Nothing is forced to `5.2`.

## 2. The `[0,1]` ceiling is what makes the extracted factor free

records that the display's `max` is load-bearing: with the max, the extracted
second factor `max_l 3^{-s(m-l)/2}(avsum_z 1_{not Q})^{s/d}` is `[0,1]`-valued
(weight `<= 1`, average `<= 1`, power `<= 1`), so the cross terms of the crude
bound cost nothing; with the `l`-sum the same factor's ceiling is its total
weight mass `~ 36 s^{-1}` and the cross term gains an unabsorbable `s^{-1}`.

That ceiling is available at the exact development carrier by composing the
sibling `weightedIndicatorAverage_rpow_mem_Icc` (`BadEventCeiling.lean`) with
the weight `3^{-(s/4).2.j}`, which lies in `[0,1]` for `s >= 0`.

It is **not** what the downstream Orlicz composition `ceiling_product`
(`BadEventIngredients.lean`) consumes, and the earlier draft of this paragraph
said otherwise.  `ceiling_product` is *single-`l`* — one pair `(l, n)`, one
*scalar* weight `w`, no `j`-family and no `max_l` — and its seam is the pair
of scalar bounds `hw0 : 0 <= w`, `hw1 : w <= 1`; it re-derives the product
ceiling internally through `weightedIndicatorAverage_rpow_mem_Icc` and cannot
take a `mem_Icc` conclusion at all, whose shape is different.

## 3. What is delivered

*The abstract extraction engine*, over abstract reals, so that no
transcendental ever meets an arithmetic tactic:

* `tsum_weighted_square_mul_le` (countable, the reindexing `j = m - l`).

*The ratio*, at the honest sharp constant `4`:

* `geometricDiscount_two_le_four_mul_quarter`,
* `geometricDiscount_quarter_two_pos` (the single upstream wrapper kept, as the
  normal form the ratio's `div_le_iff₀` reads; the matching `c_{2s} >= 0` is
  consumed straight from `Ch02.book_geometricDiscount_nonneg` at its point of
  use and no wrapper for it is supplied),
* `geometricDiscount_two_div_quarter_le_four`.

*The `E^2`-series shape* and the extraction at the series weights:

* `geometricWeight_quarter_two_eq` (**the seam**),
* `three_rpow_quarter_two_mul_self`, `geometricWeight_quarter_two_nonneg`,
* `tsum_geometricDiscount_two_mul_le_four_mul`.

*The composed form*:

* `tsum_badMax_le_four_mul_homogenizationErrorOnCube_sq` — at the `E^2`
  carrier, with an abstract nonnegative second factor.

One `private` plumbing lemma (`three_rpow_mul_natCast_add`) absorbs the
`Real.rpow 3 x` / `(3 : ℝ) ^ x` spelling seam.

## 4. Hypotheses

The hypotheses are the display's own: `0 < s` (from the printed window
`8 cgamma <= s <= 1`; only positivity is used), the nonnegativity of the
printed factors, the positivity of the two geometric normalizations `c1`, `c2`,
and the domination `hW`, which says exactly that `W` — the printed `max_l` —
dominates the printed second factors.  `[NeZero d]` is carrier-forced:
`Ch02.HomogenizationErrorOnCube` and
`Ch02.maxDescendantNormalizedBlockResponseAtScale` carry it in their own
signatures.  The one remaining binder, `hsum : Summable ...`, is discussed next.

No `2 <= d` binder, no `NeZero d` binder beyond the two carriers that declare
it themselves, and no induction-state, `mStar`, `cstar` or `E` premise appears
anywhere in this file.

## 5. Where the summability obligation is genuine, and where it is not

**On the abstract engines the binder is genuine and load-bearing.** `Summable (fun
i => c1 . v i . f i)` is carried by `tsum_weighted_square_mul_le` and
`tsum_geometricDiscount_two_mul_le_four_mul` and cannot be dropped there:
Lean's `tsum` is `0` off summability, so the right side of the extraction
collapses while the left side does not.  The `hsum`-free abstract statement is
false: at `c1 = c2 = W = 1`, `v = f = 1`, `g i = (1/2)^i` its left side is `2`
and its right side is `0`.

**At the `E^2` carrier the binder is NOT a caller obligation, and is not
carried.**  The composed form
`tsum_badMax_le_four_mul_homogenizationErrorOnCube_sq` instantiates `f j` at
`Ch02.maxDescendantNormalizedBlockResponseAtScale (cu_m) (m - j) a a0`, and at
that instance the series is *unconditionally* summable from `0 < s` alone, by
the proved upstream

* `Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale`,
  at `Q := cu_m` (whose `.scale` is `m` by `rfl`) and at the parameter `s/4`,

which is inside this file's own three-import closure.  The composed form
discharges it inline, so nothing in the file is conditional at the concrete
carrier.

## 6. References

* ABK26: `e.mathcal.E.breakdown`, `e.localization.mathcalE.estimate`,
  `e.multGammasig`.
-/

namespace Algsuperdiff.Section3.Provider.MultiscaleEstimate

-- The `_root_` prefixes below are deliberate.  A bare `open Homogenization`
-- resolves to the sibling namespace `Algsuperdiff.Section3.Provider.Homogenization`
-- as soon as any module of it joins this file's import closure, at which point
-- `Mat`, `Vec` and `originCube` all become unknown identifiers.  The prefixes
-- keep the file robust against that.
open _root_.HCPolySupport
open _root_.HCPolySupport.Book

noncomputable section

/-! ## 1. Prefix/notation plumbing for the base-`3` powers

`Real.rpow 3 x` and `(3 : ℝ) ^ x` are `rfl`-equal but not syntactically equal,
and `rw` matches on the head symbol, so a `show` is required to move between
them.  Both lemmas below exist only to absorb that seam; they are `private`. -/

private theorem three_rpow_mul_natCast_add (x y : ℝ) (j : ℕ) :
    Real.rpow (3 : ℝ) (x * (j : ℝ)) * Real.rpow (3 : ℝ) (y * (j : ℝ)) =
      Real.rpow (3 : ℝ) ((x + y) * (j : ℝ)) := by
  change (3 : ℝ) ^ (x * (j : ℝ)) * (3 : ℝ) ^ (y * (j : ℝ)) = (3 : ℝ) ^ ((x + y) * (j : ℝ))
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-! ## 2. The abstract extraction engine

Everything here is about abstract reals: no transcendental function occurs, so
no arithmetic tactic ever meets one.  The shape is the mechanism display with
the two geometric normalizations named `c₁` (the series' own, `c_{s/2}`) and
`c₂` (the printed outer one, `c_{2s}`), and with `v i` the half-weight
`3^{-s(m-l)/2}`:

```
    sum_i c₂ (v i)^2 (f i . g i)
      = (c₂/c₁) sum_i (c₁ . v i . f i) . (v i . g i)
      <= (c₂/c₁) . W . sum_i c₁ . v i . f i ,     W >= v i . g i for all i.
```

The `W`-slot *is* the printed `max_l`. -/

/-- **The extraction engine, countable index set.**  The same statement for
`tsum`s over `ℕ`, which is the reindexing `j = m - l` of the manuscript's
`l`-sum over `(-infinity, m] cap ℤ`.

`hsum` is a caller obligation at this abstract level and is load-bearing here
(see §5 of the module docstring): it is what makes the right-hand series a genuine sum
rather than Lean's `0` default, and without it the statement is false — at `c₁
= c₂ = W = 1`, `v = f ≡ 1`, `g i = (1/2)^i` the left side is `2` and the right
side is `0`.  The summability of the left-hand series is then *derived*, not
assumed.  At the concrete `E^2` carrier of §5--§6 the same binder is
dischargeable upstream and is not carried. -/
theorem tsum_weighted_square_mul_le {c₁ c₂ W : ℝ} {v f g : ℕ → ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 ≤ c₂)
    (hv : ∀ i, 0 ≤ v i) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hW : ∀ i, v i * g i ≤ W)
    (hsum : Summable fun i : ℕ => c₁ * v i * f i) :
    ∑' i : ℕ, c₂ * (v i * v i) * (f i * g i) ≤
      c₂ / c₁ * W * ∑' i : ℕ, c₁ * v i * f i := by
  have hbase : ∀ i : ℕ, 0 ≤ c₁ * v i * f i := fun i =>
    mul_nonneg (mul_nonneg hc₁.le (hv i)) (hf i)
  have hterm : ∀ i : ℕ, c₂ * (v i * v i) * (f i * g i) ≤
      c₂ / c₁ * W * (c₁ * v i * f i) := by
    intro i
    have hnn : 0 ≤ c₂ / c₁ * (c₁ * v i * f i) :=
      mul_nonneg (div_nonneg hc₂ hc₁.le) (hbase i)
    have key : c₂ * (v i * v i) * (f i * g i)
        = c₂ / c₁ * (c₁ * v i * f i) * (v i * g i) := by
      field_simp
    rw [key]
    calc c₂ / c₁ * (c₁ * v i * f i) * (v i * g i)
        ≤ c₂ / c₁ * (c₁ * v i * f i) * W :=
          mul_le_mul_of_nonneg_left (hW i) hnn
      _ = c₂ / c₁ * W * (c₁ * v i * f i) := by ring
  have hnonneg : ∀ i : ℕ, 0 ≤ c₂ * (v i * v i) * (f i * g i) :=
    fun i => mul_nonneg (mul_nonneg hc₂ (mul_nonneg (hv i) (hv i)))
      (mul_nonneg (hf i) (hg i))
  have hmaj : Summable fun i : ℕ => c₂ / c₁ * W * (c₁ * v i * f i) :=
    hsum.mul_left _
  have hLsum : Summable fun i : ℕ => c₂ * (v i * v i) * (f i * g i) :=
    Summable.of_nonneg_of_le hnonneg hterm hmaj
  calc ∑' i : ℕ, c₂ * (v i * v i) * (f i * g i)
      ≤ ∑' i : ℕ, c₂ / c₁ * W * (c₁ * v i * f i) :=
        hLsum.tsum_le_tsum hterm hmaj
    _ = c₂ / c₁ * W * ∑' i : ℕ, c₁ * v i * f i := tsum_mul_left

/-! ## 3. The ratio `c_{2s}/c_{s/2}`, at the sharp constant `4` -/

/-- **`c_{2s} <= 4 c_{s/2}`, by factorization.**  With `q := 3^{-s/2}` one has
`3^{-2s} = q^4`, hence

```
    c_{2s} = 1 - q^4 = (1-q)(1 + q + q^2 + q^3) <= 4(1-q) = 4 c_{s/2} .
```

Only `0 <= s` is used (through `q <= 1`); no upper bound on `s`, no
`Real.log 3`, and no transcendental estimate of any kind enters.

`4` is the least uniform constant: the ratio `c_{2s}/c_{s/2}` tends to `4` as
`s -> 0+`.  prints `5.2`, which is true but not sharp; the sharp constant is
proved here and the printed one is not forced. -/
theorem geometricDiscount_two_le_four_mul_quarter {s : ℝ} (hs : 0 ≤ s) :
    Ch02.geometricDiscount s 2 ≤ 4 * Ch02.geometricDiscount (s / 4) 2 := by
  have hq0 : 0 ≤ (3 : ℝ) ^ (-(s / 4) * 2) := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hq1 : (3 : ℝ) ^ (-(s / 4) * 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hsq : ((3 : ℝ) ^ (-(s / 4) * 2)) ^ 2 ≤ 1 := pow_le_one₀ hq0 hq1
  have hcb : ((3 : ℝ) ^ (-(s / 4) * 2)) ^ 3 ≤ 1 := pow_le_one₀ hq0 hq1
  have hpow : ((3 : ℝ) ^ (-(s / 4) * 2)) ^ 4 = (3 : ℝ) ^ (-s * 2) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(s / 4) * 2)) 4,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    push_cast
    ring
  change 1 - (3 : ℝ) ^ (-s * 2) ≤ 4 * (1 - (3 : ℝ) ^ (-(s / 4) * 2))
  rw [← hpow]
  nlinarith [hq0, hq1, hsq, hcb]

/-- `c_{s/2} > 0` for `s > 0`, from the upstream `Ch02.book_geometricDiscount_pos`
(no in-repo copy of the `1 - 3^{-x} > 0` fact is added). -/
theorem geometricDiscount_quarter_two_pos {s : ℝ} (hs : 0 < s) :
    0 < Ch02.geometricDiscount (s / 4) 2 :=
  Ch02.book_geometricDiscount_pos (by linarith : (0 : ℝ) < s / 4 * 2)

/-- **The ratio, in division form.** `c_{2s}/c_{s/2} <= 4` on `s > 0` — a pure
`C(d)` with no `s^{-1}` anywhere. -/
theorem geometricDiscount_two_div_quarter_le_four {s : ℝ} (hs : 0 < s) :
    Ch02.geometricDiscount s 2 / Ch02.geometricDiscount (s / 4) 2 ≤ 4 := by
  rw [div_le_iff₀ (geometricDiscount_quarter_two_pos hs)]
  have := geometricDiscount_two_le_four_mul_quarter hs.le
  linarith

/-! ## 4. The `E^2_{s/4,infty,2}`-series shape

`Ch02.geometricWeight (s/4) 2 j = c_{s/2} . 3^{-s j/2}`: the parameter slot of
`E^2` is `s/4` and its exponent slot is `q = 2`, so the series weight carries
`c_{(s/4).2} = c_{s/2}` and `3^{-(s/4).2.j} = 3^{-s j/2}`.  This is the seam
requires, verified against the frozen carrier's own definition rather than
assumed. -/

/-- **The seam.**  The bracketed left factor of the mechanism display is
literally the `j`-th weight of the series defining `E^2_{s/4,infty,2}`.

Proved as the `(s/4, 2)` specialization of the proved in-closure public
`Provider.ErrorComparison.geometricWeight_eq'`
(`ErrorComparison/FiniteQTransfer.lean`), which is the general defining form; no
second `rfl` copy of the definition is added. -/
theorem geometricWeight_quarter_two_eq {s : ℝ} (j : ℕ) :
    Ch02.geometricWeight (s / 4) 2 j =
      Ch02.geometricDiscount (s / 4) 2 * Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) :=
  ErrorComparison.geometricWeight_eq' (s / 4) 2 j

/-- The half-weight squares to the printed outer weight:
`3^{-s(m-l)/2} . 3^{-s(m-l)/2} = 3^{-s(m-l)}`. -/
theorem three_rpow_quarter_two_mul_self {s : ℝ} (j : ℕ) :
    Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) *
        Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) =
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) := by
  rw [three_rpow_mul_natCast_add]
  congr 2
  ring

/-- `Ch02.geometricWeight (s/4) 2 j >= 0`, as the `(s/4, 2)` specialization of the
proved in-closure public `Provider.CoarseEllipticity.geometricWeight_nonneg'`
(`CoarseEllipticity/LambdaGridBridge.lean`); no third route through
`Ch02.geometricWeight_eq_old` is added here. -/
theorem geometricWeight_quarter_two_nonneg {s : ℝ} (hs : 0 ≤ s) (j : ℕ) :
    0 ≤ Ch02.geometricWeight (s / 4) 2 j :=
  CoarseEllipticity.geometricWeight_nonneg' (by linarith : (0 : ℝ) ≤ s / 4 * 2) j

/-- **The extraction at the `E^2`-series weights.**  The mechanism display, with
the abstract engine instantiated at `v j = 3^{-s j/2}`, `c₁ = c_{s/2}`, `c₂ =
c_{2s}`, and the ratio replaced by its sharp bound `4`:

```
    sum_j c_{2s} 3^{-s j} (f j . g j)
      <= 4 . W . sum_j c_{s/2} 3^{-s j/2} f j ,
```

for any `W` dominating the half-weighted second factors `3^{-s j/2} g j`. -/
theorem tsum_geometricDiscount_two_mul_le_four_mul {s W : ℝ} {f g : ℕ → ℝ}
    (hs : 0 < s) (hf : ∀ j, 0 ≤ f j) (hg : ∀ j, 0 ≤ g j)
    (hW : ∀ j : ℕ, Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) * g j ≤ W)
    (hsum : Summable fun j : ℕ => Ch02.geometricWeight (s / 4) 2 j * f j) :
    ∑' j : ℕ, Ch02.geometricDiscount s 2 * Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        (f j * g j) ≤
      4 * W * ∑' j : ℕ, Ch02.geometricWeight (s / 4) 2 j * f j := by
  have hc₁ := geometricDiscount_quarter_two_pos hs
  have hc₂ : (0 : ℝ) ≤ Ch02.geometricDiscount s 2 :=
    Ch02.book_geometricDiscount_nonneg (by linarith : (0 : ℝ) ≤ s * 2)
  have hv : ∀ j : ℕ, (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) :=
    fun j => (Real.rpow_pos_of_pos (by norm_num) _).le
  have hW0 : 0 ≤ W := le_trans (mul_nonneg (hv 0) (hg 0)) (hW 0)
  have hsum' : Summable fun j : ℕ =>
      Ch02.geometricDiscount (s / 4) 2 *
        Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) * f j := by
    refine hsum.congr fun j => ?_
    rw [geometricWeight_quarter_two_eq]
  have hbase := tsum_weighted_square_mul_le
    (c₁ := Ch02.geometricDiscount (s / 4) 2) (c₂ := Ch02.geometricDiscount s 2)
    (v := fun j : ℕ => Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ))) (f := f)
    (g := g) (W := W) hc₁ hc₂ hv hf hg hW hsum'
  have hleft : ∀ j : ℕ,
      Ch02.geometricDiscount s 2 *
          (Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) *
            Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ))) * (f j * g j) =
        Ch02.geometricDiscount s 2 * Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          (f j * g j) := by
    intro j
    rw [three_rpow_quarter_two_mul_self]
  have hright : ∀ j : ℕ,
      Ch02.geometricDiscount (s / 4) 2 *
          Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) * f j =
        Ch02.geometricWeight (s / 4) 2 j * f j := by
    intro j
    rw [geometricWeight_quarter_two_eq]
  rw [tsum_congr hleft, tsum_congr hright] at hbase
  have hS : 0 ≤ ∑' j : ℕ, Ch02.geometricWeight (s / 4) 2 j * f j :=
    tsum_nonneg fun j =>
      mul_nonneg (geometricWeight_quarter_two_nonneg hs.le j) (hf j)
  have hratio : Ch02.geometricDiscount s 2 / Ch02.geometricDiscount (s / 4) 2 * W ≤
      4 * W :=
    mul_le_mul_of_nonneg_right (geometricDiscount_two_div_quarter_le_four hs) hW0
  exact hbase.trans (mul_le_mul_of_nonneg_right hratio hS)

/-! ## 5. The composed form at the `E^2` carrier

`Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum` turns the right-hand
series into the frozen carrier `E^2_{s/4,infty,2}(cu_m; a, a0)` itself.  Its
per-scale factor `maxDescendantNormalizedBlockResponseAtScale (cu_m) (m - j)`
is the printed `max_{z in 3^{m-j} ℤ^d cap cu_m} max_{|e|=1} J(z + cu_{m-j};
a0^{-1/2} e, a0^{1/2} e; a)`.

At this carrier the abstract engine's summability binder is discharged INLINE,
from `0 < s` alone, by the proved upstream
`Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale`
(`EllipticityControl.lean`) at `Q := cu_m` and parameter `s/4` — note
`(originCube d m).scale = m` by `rfl`.  Everything below therefore carries no
summability hypothesis: the conditional A of the module docstring's §5 stops at
the abstract engines. -/

/-- **The max-first factorization at the `E^2` carrier.**

```
    sum_j c_{2s} 3^{-s j} ( max_z max_e J(z + cu_{m-j}) . g j )
      <= 4 . W . E^2_{s/4,infty,2}(cu_m; a, a0) ,
```

for any `W` dominating the half-weighted second factors `3^{-s j/2} g j`.  This
is the printed display's fourth summand, with its `C E^2_{s/4} max_l` shape
and the pure constant `4`. -/
theorem tsum_badMax_le_four_mul_homogenizationErrorOnCube_sq {d : ℕ} [NeZero d]
    (m : ℤ) {s W : ℝ} (hs : 0 < s) (a : Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {g : ℕ → ℝ} (hg : ∀ j, 0 ≤ g j)
    (hW : ∀ j : ℕ, Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) * g j ≤ W) :
    ∑' j : ℕ, Ch02.geometricDiscount s 2 * Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        (Ch02.maxDescendantNormalizedBlockResponseAtScale (originCube d m)
          (m - (j : ℤ)) a a0 * g j) ≤
      4 * W * (Ch02.HomogenizationErrorOnCube (originCube d m) (s / 4)
        Ch02.MultiscaleExponent.infinity (Ch02.MultiscaleExponent.finite 2) a a0) ^ 2 := by
  have hf : ∀ j : ℕ, 0 ≤ Ch02.maxDescendantNormalizedBlockResponseAtScale
      (originCube d m) (m - (j : ℤ)) a a0 := by
    intro j
    exact Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg (originCube d m)
      (show m - (j : ℤ) ≤ (originCube d m).scale from
        sub_le_self m (Int.natCast_nonneg j)) a a0
  have hsum : Summable fun j : ℕ => Ch02.geometricWeight (s / 4) 2 j *
      Ch02.maxDescendantNormalizedBlockResponseAtScale (originCube d m)
        (m - (j : ℤ)) a a0 :=
    Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
      (originCube d m) a a0 (by linarith : (0 : ℝ) < s / 4)
  rw [Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum (originCube d m)
    (by linarith : (0 : ℝ) < s / 4) a a0]
  exact tsum_geometricDiscount_two_mul_le_four_mul hs hf hg hW hsum

end

end Algsuperdiff.Section3.Provider.MultiscaleEstimate
