/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.GridWeights
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.DiscountBounds

/-!
# AggregationRemainder

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Provider: the remainder arithmetic of the localization good-event aggregation

After the `σ`-switch and the `δ = 1` sensitivity injection, the good-event leg
of `e.mathcal.E.breakdown` carries a *per-cube* additive remainder.  Summing it
over `z ∈ 3^l ℤ^d ∩ □_m` and over the localization weights `c_{2s} 3^{-s(m-l)}`
produces the fifth summand of `e.localization.mathcalE.estimate` --- the
printed

`C γ² (h² + s^{-2} + E⁴ |log γ|⁴)`.

**This module carries exactly that scalar collapse, and nothing else.**  It is
purely deterministic real analysis: no measures, no `Γ`-Orlicz layer, no
coefficient fields, no cubes.  Everything below is a statement about the real
series `Σ_{j ∈ ℕ} 3^{-s j} (…)` at `j = m - l`.

This is a *provider endpoint only*.  It is not a source node, not a frozen
declaration, and it closes no fraction of `l.localization.mathcalE`.

## The corrected per-cube remainder, and two divergences from the print

* The printed per-cube display ends with `C min{γ²Δ², 3^{2γΔ}} +⁴γ²|log γ|⁴` at
  `Δ = m - l + h`.  Since `u² ≤ 3^{2u}` for `u ≥ 0`, that minimum is
  identically `γ²Δ²`, which is strictly stronger than what the quoted input
  (`e.switchtheshoms.betterer.again`, whose right side carries an *uncancelled*
  `3^{γΔ}`, squared by the `e.shaking.lambda` remainder) yields, and it is
  false for large `Δ`.  The corrected per-cube remainder --- the one this
  module sums --- is `C min{γ²Δ², 1} · 3^{2γΔ} +⁴γ²|log γ|⁴ · 3^{2γΔ}`.  It is
  carried here by `switchRemainder`.  Note the manuscript *itself* uses the
  corrected `min` one display later.

* The fifth summand's constant is `C(d, c⋆)`, not a pure `C(d)`.  **That
  divergence does not arise here.**  The `c⋆`-dependence enters through the
  *per-cube* constant of the switch step (the `hpre`-style ellipticity
  witness), i.e. through the caller's `C` in
  `localization_remainder_series_le_of_termwise`; the collapse proved in this
  module multiplies that `C` through unchanged and contributes an **absolute**
  numerical factor `1024`, with no dependence on `d`, on `c⋆`, or on any
  coarse-grained ellipticity witness.  Callers must still record the
  `c⋆`-dependence they bring in.

## Honest arithmetic versus the printed proof

The printed target is `C γ²(h² + s^{-2} + E⁴|log γ|⁴)` and the printed device is

> Since `s ≥ 8γ` and `3^{-sγ^{-1}} ≤ C s^{-2} γ²`, we have
> `c_{2s} Σ_l 3^{-s(m-l)} min{γ²(m-l+h)², 1} 3^{2γ(m-l+h)} ≤ C(h² + s^{-2})γ²`.

**Achieved here: the printed shape, at the absolute constant `1024`, with the
`E`-leg included.**  Precisely, `localization_remainder_series_le` gives

`c_{2s} Σ_{j ≥ 0} 3^{-sj}(min{γ²(j+h)²,1} + E⁴γ²|log γ|⁴) 3^{2γ(j+h)}` ` ≤ 1024
γ² (h² + s^{-2} + E⁴|log γ|⁴)`,

for every `s ∈ [8γ, 1]`, `γ > 0`, `h ∈ ℕ` with `γ h ≤ 1`.  Two deviations from
the printed derivation are recorded, both in the direction of *less* loss:

1. Summed honestly it contributes `c_{2s} · E⁴γ²|log γ|⁴ · 3^{2γh} (1 -
   3^{-(s-2γ)})^{-1} ≤ 27 E⁴γ²|log γ|⁴`, the `27 = 3 × 9` coming from `c_{2s} ≤
   3 c_{s-2γ}` and `3^{2γh} ≤ 9` (`γ h ≤ 1`).  The amplitude carries the
   load-bearing `γ²` and **no** `s` power.

2. **The printed split is not needed.**  The printed proof splits the `min` at
   the index where `γ(j+h) ≥ 1` and absorbs the tail with
   `3^{-sγ^{-1}} ≤ C s^{-2} γ²`.  Reindexing exactly --- absorbing `3^{2γj}`
   into `3^{-sj}` to the *lossless* ratio `q = 3^{-(s-2γ)}`, which is `< 1`
   because `s ≥ 8γ` --- makes the quadratic series converge outright:
   `min{γ²(j+h)²,1} ≤ γ²(j+h)² ≤ 2γ²((j+1)² + h²)` and
   `Σ_j (j+1)² q^j ≤ 2(1-q)^{-3}`.  No case split, no cutoff index, no
   absorption inequality.  The printed device is therefore *sufficient but not
   necessary*, and is **not consumed** by the collapse.  This is
   a presentational observation about the printed proof, not a defect in it.

   The lossy alternative is real: replacing the `min` by the *linear* envelope
   `min{a²,1} ≤ a` (valid for `a ≥ 0`) collapses to `C(γ h + γ s^{-1})`.

   **That claim is false and is withdrawn.**  The frozen unit-M `Γ₂` amplitude
   is `Cms · E · s^{-1} · √(ε γ)`
   (`Algsuperdiff/Frozen/Section3/MultiscaleEstimate.lean`), which squares to
   `Cms² · ε · E² · γ · s^{-2}`; dividing the linear-envelope bound by it
   leaves `Cs · Cev · (h s² + s) ≤ Cms² ε E²`, and the frozen parameter window
   `(Disorder.cstar M)^{-1} · ε^{-Cms} ≤ E` gives `ε E² ≥ ε^{1-2Cms} c⋆^{-2}`,
   unboundedly large as `ε ↓ 0` for `Cms > 1/2`, against `h ≍ Cms |log ε|`.
   So the `γ¹` shape **clears** the budget as well: the `γ`-power heuristic
   silently dropped the `ε`/`E` factors that actually supply the margin.

   The genuine reason the quadratic route is required is **fidelity**: the
   printed fifth summand is `C γ²(h² + s^{-2} + E⁴|log γ|⁴)`, so a `γ¹` result
   would be a *different, weaker statement* than the one this module must
   deliver.  "The quadratic route is what buys the `γ²`" is the correct
   sentence; the budget justification for it is not.

## Where the constants come from

`c_{2s} = 1 - 3^{-2s} ≤ 3 (1 - 3^{-(s-2γ)}) = 3 c_{s-2γ}` (needs `s ≥ 6γ`; the
factorization `1 - q³ = (1-q)(1+q+q²)`), and `c_{s-2γ}^{-1} ≤ 2/(s-2γ) ≤ 3/s`
(needs `s ≥ 6γ` and `s - 2γ ≤ 1`).  One factor of `c_{s-2γ}` then cancels
against the poles, giving

`c_{2s} · Σ ≤ 108 γ² (1-q)^{-2} + 54 γ² h² + 27 E⁴γ²|log γ|⁴` `  ≤ 972 γ²
s^{-2} + 54 γ² h² + 27 E⁴γ²|log γ|⁴`,

and `max{972, 54, 27} ≤ 1024`.  The stated constant `1024` is an absolute
numeral chosen for roundness; the derivation supports `972`.

Only `s ≥ 6γ` is used.  The binder is stated at the source window `8γ ≤ s`
(tex `s ∈ [8γ, 1]`), which is what every caller has.

## Carriers and consumer fit

* The outer weight is spelled `Real.rpow (3 : ℝ) (-s * (j : ℝ))`,
  **byte-for-byte the spelling of `breakdownLegSum`**
  (`Provider/Localization/Breakdown.lean`), whose reindexing convention `j = m
  - l ∈ ℕ`, scale `m - (j: ℤ)`, this module adopts.
* `c_{2s}` is `Book.Ch02.geometricDiscount s 2` (CoarseGraining,
  `Homogenization/Book/Ch02/MultiscaleEllipticity.lean`), the carrier
  `Breakdown.lean` already identifies with the manuscript's `c_{2s}`.  Its
  unfolding is `geometricDiscount_two_eq`.
* The main consumer entry point is
  `localization_remainder_series_le_of_termwise`: it takes an arbitrary
  nonnegative per-scale remainder `f` dominated termwise by
  `C * switchRemainder γ E h j` and returns the collapsed amplitude at `1024 *
  C`. Its `Summable` obligation is discharged internally, so callers owe none.

## Main results

The 8 privates are `rpow_three`, `geometricDiscount_two_le_three_mul_shift`,
`inv_one_sub_shift_le`, `sq_succ_le_two_mul_choose`, `weight_reindex`,
`hasSum_envelope`, `weighted_switchRemainder_le`, `collapse_core`.  The 10
publics, in file order:

* `geometricDiscount_two_eq` --- the `c_{2s} = 1 - 3^{-2s}` normal form.
* `geometricDiscount_two_nonneg`, `geometricDiscount_two_le_four_mul` --- `q =
  2` wrappers of upstream CoarseGraining publics (see the retraction above),
  not new results.
* `switchRemainder`, `switchRemainder_nonneg` --- the corrected per-cube
  remainder envelope.
* An identity, not an estimate.
* `summable_weighted_switchRemainder` --- summability of the weighted family.
* `localization_remainder_series_le` --- the full remainder collapse.

## Import closure and layering

A consumer of this module no longer gets `Breakdown` transitively and must
-/

namespace Algsuperdiff.Section3.Provider.Localization

-- `_root_` is here, not presently load-bearing.
-- `Algsuperdiff.Section3.Provider.Homogenization` is a live sibling namespace, and a
-- bare `open Homogenization` resolves to it as soon as any `Provider.Homogenization`
-- module enters this file's import closure.
open _root_.HCPolySupport
open Algsuperdiff.Section3.Provider.CoarseEllipticity

noncomputable section

/-! ## The normalization `c_{2s}` -/

/-- `Real.rpow` and the power notation at base three agree definitionally.  The
bridge is needed only so that `ring`/`linarith` see one atom: `Breakdown.lean`
spells the localization weight `Real.rpow (3 : ℝ) (-s * (j : ℝ))`, while the
elementary `rpow` A is stated in notation. -/
private theorem rpow_three (y : ℝ) : Real.rpow (3 : ℝ) y = (3 : ℝ) ^ y := rfl

/-- The manuscript's `c_{2s} = 1 - 3^{-2s}` is `Book.Ch02.geometricDiscount s 2`. -/
theorem geometricDiscount_two_eq (s : ℝ) :
    Book.Ch02.geometricDiscount s 2 = 1 - (3 : ℝ) ^ (-(2 * s)) := by
  show 1 - Real.rpow (3 : ℝ) (-s * 2) = 1 - (3 : ℝ) ^ (-(2 * s))
  rw [rpow_three, show (-s * 2 : ℝ) = -(2 * s) by ring]

/-- `c_{2s}` is nonnegative for `s ≥ 0`.  A `q = 2` specialization of the
upstream public `Book.Ch02.book_geometricDiscount_nonneg`; kept only as the
normal form the collapse reads. -/
theorem geometricDiscount_two_nonneg {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ Book.Ch02.geometricDiscount s 2 :=
  Book.Ch02.book_geometricDiscount_nonneg (by linarith : (0 : ℝ) ≤ s * 2)

/-- **`c_{2s} = 1 - 3^{-2s} ≤ 4 s`.**  A `q = 2` specialization of the upstream
public `Book.Ch02.geometricDiscount_le_two_mul` (`c_{sq} ≤ 2 s q`), which is
strictly more general; kept only as the normal form the collapse reads.  Only
`0 ≤ s` is needed. -/
theorem geometricDiscount_two_le_four_mul {s : ℝ} (hs : 0 ≤ s) :
    Book.Ch02.geometricDiscount s 2 ≤ 4 * s := by
  have h := Book.Ch02.geometricDiscount_le_two_mul (by linarith : (0 : ℝ) ≤ s * 2)
  linarith

/-- **`c_{2s} ≤ 3 c_{s-2γ}`**, the sharp comparison the collapse uses.  Proof:
`3(s - 2γ) ≥ 2s` when `s ≥ 6γ`, so `q³ ≤ 3^{-2s}` at `q = 3^{-(s-2γ)}`, and
`1 - q³ = (1-q)(1 + q + q²) ≤ 3(1-q)`. -/
private theorem geometricDiscount_two_le_three_mul_shift {s gam : ℝ}
    (hgam : 0 < gam) (hsgam : 6 * gam ≤ s) :
    Book.Ch02.geometricDiscount s 2 ≤ 3 * (1 - (3 : ℝ) ^ (-(s - 2 * gam))) := by
  rw [geometricDiscount_two_eq]
  set q : ℝ := (3 : ℝ) ^ (-(s - 2 * gam)) with hq
  have hq0 : 0 ≤ q := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hqcube : q ^ 3 = (3 : ℝ) ^ (-(3 * (s - 2 * gam))) := by
    rw [hq, ← Real.rpow_natCast ((3 : ℝ) ^ (-(s - 2 * gam))) 3,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1; push_cast; ring
  have hmono : (3 : ℝ) ^ (-(3 * (s - 2 * gam))) ≤ (3 : ℝ) ^ (-(2 * s)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hq1 : q ≤ 1 := by
    rw [hq]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  calc 1 - (3 : ℝ) ^ (-(2 * s)) ≤ 1 - q ^ 3 := by rw [← hqcube] at hmono; linarith
    _ = (1 - q) * (1 + q + q ^ 2) := by ring
    _ ≤ (1 - q) * 3 := by
        apply mul_le_mul_of_nonneg_left _ (by nlinarith)
        nlinarith
    _ = 3 * (1 - q) := by ring

/-- **`c_{s-2γ}^{-1} ≤ 3/s`** at `0 < γ`, `6γ ≤ s ≤ 1`.

The earlier justification for declining it ("`half_le_one_sub_...` is already
in the import closure") was circular: WaveSizes was in the closure *only*
because of this one consumption.

**Sharpness, and why the conclusion is unchanged.**  At `ρ := s - 2γ ≤ 1` the
GridWeights pole is uniformly sharper (`1 + ρ^{-1} ≤ 2/ρ` always, since `ρ^{-1}
- 1 ≥ 0`): it supports `(1-q)^{-1} ≤ (7/3)/s` on this module's window and hence
a headline `588 γ²/s²` in place of `972 γ²/s²`.  The `3/s` conclusion is **kept
deliberately**, so that every public statement of this module — and in
particular the numeral `1024` — is unchanged; the sharper `588` is recorded,
not taken.  Any downstream numeral must still be read off the proved statement.

Route: `1 + (s-2γ)^{-1} ≤ 1 + 3/(2s) ≤ 3/s`, the first step from `6γ ≤ s` and
the second from `s ≤ 1`. -/
private theorem inv_one_sub_shift_le {s gam : ℝ} (hgam : 0 < gam)
    (hsgam : 6 * gam ≤ s) (hs1 : s ≤ 1) :
    (1 - (3 : ℝ) ^ (-(s - 2 * gam)))⁻¹ ≤ 3 / s := by
  have hs0 : 0 < s := lt_of_lt_of_le (by linarith) hsgam
  have ha0 : 0 < s - 2 * gam := by linarith
  have hpole : (1 - (3 : ℝ) ^ (-(s - 2 * gam)))⁻¹ ≤ 1 + (s - 2 * gam)⁻¹ :=
    one_sub_rpow_neg_inv_le ha0
  have hmid : (s - 2 * gam)⁻¹ ≤ 3 / (2 * s) := by
    rw [inv_eq_one_div, div_le_div_iff₀ ha0 (by linarith : (0 : ℝ) < 2 * s)]
    linarith
  have hlast : (1 : ℝ) + 3 / (2 * s) ≤ 3 / s := by
    rw [← sub_nonneg]
    have hid : 3 / s - (1 + 3 / (2 * s)) = (3 - 2 * s) / (2 * s) := by
      field_simp; ring
    rw [hid]
    exact div_nonneg (by linarith) (by linarith)
  linarith

/-! ## The corrected per-cube remainder -/

/-- **The corrected per-cube remainder of the localization `σ`-switch**, at gap `Δ
= j + h` (`j = m - l`):

`(min{γ²Δ², 1} + E⁴γ²|log γ|⁴) · 3^{2γΔ}`.

The `3^{2γΔ}` factor multiplies **both** summands: the input
`e.switchtheshoms.betterer.again` carries an uncancelled `3^{γΔ}`, and the
`e.shaking.lambda` remainder squares it. -/
def switchRemainder (gam E : ℝ) (h j : ℕ) : ℝ :=
  (min (gam ^ 2 * ((j : ℝ) + (h : ℝ)) ^ 2) 1 + E ^ 4 * gam ^ 2 * |Real.log gam| ^ 4)
    * (3 : ℝ) ^ (2 * gam * ((j : ℝ) + (h : ℝ)))

theorem switchRemainder_nonneg (gam E : ℝ) (h j : ℕ) :
    0 ≤ switchRemainder gam E h j := by
  have h1 : 0 ≤ min (gam ^ 2 * ((j : ℝ) + (h : ℝ)) ^ 2) 1 :=
    le_min (by positivity) zero_le_one
  have h2 : (0 : ℝ) ≤ E ^ 4 * gam ^ 2 * |Real.log gam| ^ 4 := by positivity
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * gam * ((j : ℝ) + (h : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  exact mul_nonneg (by linarith) h3

/-! ### The cross-file seam bridge

```
Cs Cev min 1 (γ²Δ²) 3^(2*(γ*Δ)) + Cs Cev (E⁴(γ²|log γ|⁴)) 3^(2*(γ*Δ))
```

**distributed**, with `min 1 (·)` (the argument order of the proved
`shom_continuity` display) and `Δ = (m:ℝ) - (n:ℝ)` at `m n : ℤ`, whereas
`switchRemainder` is **factored**, with `min (·) 1` (the order the tex carries)
and `(j:ℝ) + (h:ℝ)` at `j h : ℕ`.  The two are **equal, not merely comparable**
— no massaging, no loss, no absorbed constant — and the whole glue is
`min_comm` plus one `ring` normalization of the rpow exponent (`2*(γ*Δ)` is not
defeq to `2*γ*Δ` over `ℝ`) plus `push_cast` for the `ℤ → ℝ` reindex at `n:= m
- j - h`.

`C := Cs * Cev` then threads through `localization_remainder_series_le_of_termwise` by
plain distributivity, since the two summands factor exactly. -/

/-- **The seam bridge, at the gap `Δ = j + h`.**  The distributed two-summand
remainder of `SwitchNormalization.shom_switch` equals `(Cs * Cev)` times the
factored `switchRemainder` of this module.  An identity, not an estimate. -/
theorem switchRemainder_eq_of_gap (Cs Cev gam Eval : ℝ) (h j : ℕ) :
    Cs * Cev * min 1 (gam ^ 2 * ((j : ℝ) + (h : ℝ)) ^ 2) *
        (3 : ℝ) ^ (2 * (gam * ((j : ℝ) + (h : ℝ)))) +
      Cs * Cev * (Eval ^ 4 * (gam ^ 2 * |Real.log gam| ^ 4)) *
        (3 : ℝ) ^ (2 * (gam * ((j : ℝ) + (h : ℝ))))
      = Cs * Cev * switchRemainder gam Eval h j := by
  rw [switchRemainder, min_comm,
    show (2 : ℝ) * gam * ((j : ℝ) + (h : ℝ)) = 2 * (gam * ((j : ℝ) + (h : ℝ))) by
      ring]
  ring

/-- **The seam bridge at the integer scales, `n := m - j - h`.**  The `ℤ → ℝ`
cast the assembly owes, `(m:ℝ) - (n:ℝ) = (j:ℝ) + (h:ℝ)`, discharged inside the
identity: this is the form `SwitchNormalization.shom_switch` is instantiated at
(`m` the working scale, `n = l - h` the deep one, `j = m - l`). -/
theorem switchRemainder_eq_of_int_gap (Cs Cev gam Eval : ℝ) (m : ℤ) (h j : ℕ) :
    Cs * Cev *
        min 1 (gam ^ 2 * ((m : ℝ) - ((m - (j : ℤ) - (h : ℤ) : ℤ) : ℝ)) ^ 2) *
        (3 : ℝ) ^ (2 * (gam * ((m : ℝ) - ((m - (j : ℤ) - (h : ℤ) : ℤ) : ℝ)))) +
      Cs * Cev * (Eval ^ 4 * (gam ^ 2 * |Real.log gam| ^ 4)) *
        (3 : ℝ) ^ (2 * (gam * ((m : ℝ) - ((m - (j : ℤ) - (h : ℤ) : ℤ) : ℝ))))
      = Cs * Cev * switchRemainder gam Eval h j := by
  have hcast : (m : ℝ) - ((m - (j : ℤ) - (h : ℤ) : ℤ) : ℝ) = (j : ℝ) + (h : ℝ) := by
    push_cast
    ring
  rw [hcast]
  exact switchRemainder_eq_of_gap Cs Cev gam Eval h j

/-! ## Reindexing and the polynomial-geometric envelope -/

/-- `(n+1)² ≤ 2 (n+2).choose 2`: the bridge into Mathlib's closed form. -/
private theorem sq_succ_le_two_mul_choose (n : ℕ) :
    ((n : ℝ) + 1) ^ 2 ≤ 2 * (((n + 2).choose 2 : ℕ) : ℝ) := by
  rw [Nat.cast_choose_two]
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- **The exact reindexing.**  The `γ`-drift `3^{2γj}` is absorbed into the
localization weight `3^{-sj}` with no loss: the ratio is `q = 3^{-(s-2γ)}`. -/
private theorem weight_reindex (s gam : ℝ) (h j : ℕ) :
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) * (3 : ℝ) ^ (2 * gam * ((j : ℝ) + (h : ℝ)))
      = (3 : ℝ) ^ (2 * gam * (h : ℝ)) * ((3 : ℝ) ^ (-(s - 2 * gam))) ^ j := by
  rw [rpow_three, ← Real.rpow_natCast ((3 : ℝ) ^ (-(s - 2 * gam))) j,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1; ring

/-- The closed form of the polynomial-geometric envelope:
`Σ_j (A ((j+2).choose 2) + B) qʲ = A (1-q)^{-3} + B (1-q)^{-1}`. -/
private theorem hasSum_envelope {q A B : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun j : ℕ => A * (((j + 2).choose 2 : ℕ) : ℝ) * q ^ j + B * q ^ j)
      (A * (1 - q)⁻¹ ^ 3 + B * (1 - q)⁻¹) := by
  have hnorm : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1
  have hchoose : HasSum (fun j : ℕ => (((j + 2).choose 2 : ℕ) : ℝ) * q ^ j)
      ((1 - q)⁻¹ ^ 3) := by
    have h := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2 hnorm
    simpa [one_div, inv_pow] using h
  have hgeom : HasSum (fun j : ℕ => q ^ j) ((1 - q)⁻¹) :=
    hasSum_geometric_of_lt_one hq0 hq1
  have h := (hchoose.mul_left A).add (hgeom.mul_left B)
  simpa only [mul_assoc] using! h

/-- **The termwise envelope.**  `min{γ²Δ²,1} ≤ γ²Δ² ≤ 2γ²((j+1)² + h²)`,
`3^{2γh} ≤ 9` from `γ h ≤ 1`, and `(j+1)² ≤ 2 (j+2).choose 2`. -/
private theorem weighted_switchRemainder_le {s gam E : ℝ} {h : ℕ}
    (hgh : gam * (h : ℝ) ≤ 1) (j : ℕ) :
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) * switchRemainder gam E h j
      ≤ 36 * gam ^ 2 * (((j + 2).choose 2 : ℕ) : ℝ) *
            ((3 : ℝ) ^ (-(s - 2 * gam))) ^ j
        + (18 * gam ^ 2 * (h : ℝ) ^ 2 + 9 * (E ^ 4 * gam ^ 2 * |Real.log gam| ^ 4)) *
            ((3 : ℝ) ^ (-(s - 2 * gam))) ^ j := by
  set q : ℝ := (3 : ℝ) ^ (-(s - 2 * gam)) with hq
  have hq0 : (0 : ℝ) ≤ q := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hqj : (0 : ℝ) ≤ q ^ j := pow_nonneg hq0 j
  have hshift : (3 : ℝ) ^ (2 * gam * (h : ℝ)) ≤ 9 := by
    calc (3 : ℝ) ^ (2 * gam * (h : ℝ)) ≤ (3 : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
      _ = 9 := by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hbase : min (gam ^ 2 * ((j : ℝ) + (h : ℝ)) ^ 2) 1
        + E ^ 4 * gam ^ 2 * |Real.log gam| ^ 4
      ≤ 2 * gam ^ 2 * (2 * (((j + 2).choose 2 : ℕ) : ℝ))
        + (2 * gam ^ 2 * (h : ℝ) ^ 2 + E ^ 4 * gam ^ 2 * |Real.log gam| ^ 4) := by
    have hmin : min (gam ^ 2 * ((j : ℝ) + (h : ℝ)) ^ 2) 1
        ≤ gam ^ 2 * ((j : ℝ) + (h : ℝ)) ^ 2 := min_le_left _ _
    have hsplit : gam ^ 2 * ((j : ℝ) + (h : ℝ)) ^ 2
        ≤ 2 * gam ^ 2 * ((j : ℝ) + 1) ^ 2 + 2 * gam ^ 2 * (h : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((j : ℝ) - (h : ℝ)), Nat.cast_nonneg (α := ℝ) j,
        Nat.cast_nonneg (α := ℝ) h, sq_nonneg gam]
    have hch : ((j : ℝ) + 1) ^ 2 ≤ 2 * (((j + 2).choose 2 : ℕ) : ℝ) :=
      sq_succ_le_two_mul_choose j
    nlinarith [sq_nonneg gam]
  have hnn : (0 : ℝ) ≤ min (gam ^ 2 * ((j : ℝ) + (h : ℝ)) ^ 2) 1
      + E ^ 4 * gam ^ 2 * |Real.log gam| ^ 4 := by
    have h1 : 0 ≤ min (gam ^ 2 * ((j : ℝ) + (h : ℝ)) ^ 2) 1 :=
      le_min (by positivity) zero_le_one
    have h2 : (0 : ℝ) ≤ E ^ 4 * gam ^ 2 * |Real.log gam| ^ 4 := by positivity
    linarith
  have hrw : Real.rpow (3 : ℝ) (-s * (j : ℝ)) * switchRemainder gam E h j
      = (min (gam ^ 2 * ((j : ℝ) + (h : ℝ)) ^ 2) 1
          + E ^ 4 * gam ^ 2 * |Real.log gam| ^ 4)
        * ((3 : ℝ) ^ (2 * gam * (h : ℝ)) * q ^ j) := by
    rw [switchRemainder, hq, ← weight_reindex s gam h j]; ring
  rw [hrw]
  have hstep1 : (min (gam ^ 2 * ((j : ℝ) + (h : ℝ)) ^ 2) 1
        + E ^ 4 * gam ^ 2 * |Real.log gam| ^ 4)
      * ((3 : ℝ) ^ (2 * gam * (h : ℝ)) * q ^ j)
      ≤ (min (gam ^ 2 * ((j : ℝ) + (h : ℝ)) ^ 2) 1
        + E ^ 4 * gam ^ 2 * |Real.log gam| ^ 4) * (9 * q ^ j) := by
    apply mul_le_mul_of_nonneg_left _ hnn
    nlinarith
  refine hstep1.trans ?_
  refine (mul_le_mul_of_nonneg_right hbase (by positivity : (0 : ℝ) ≤ 9 * q ^ j)).trans ?_
  have hchnn : (0 : ℝ) ≤ (((j + 2).choose 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith [sq_nonneg gam]

/-! ## The collapse -/

/-- **The collapse core.**  Summability together with the collapsed amplitude.
-/
private theorem collapse_core {s gam E : ℝ} {h : ℕ} (hgam : 0 < gam)
    (hsgam : 8 * gam ≤ s) (hs1 : s ≤ 1) (hgh : gam * (h : ℝ) ≤ 1) :
    Summable (fun j : ℕ =>
        Real.rpow (3 : ℝ) (-s * (j : ℝ)) * switchRemainder gam E h j) ∧
      Book.Ch02.geometricDiscount s 2 *
          ∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) * switchRemainder gam E h j
        ≤ 1024 * gam ^ 2 *
            ((h : ℝ) ^ 2 + (s ^ 2)⁻¹ + E ^ 4 * |Real.log gam| ^ 4) := by
  have hs0 : 0 < s := lt_of_lt_of_le (by linarith) hsgam
  set q : ℝ := (3 : ℝ) ^ (-(s - 2 * gam)) with hq
  have hq0 : (0 : ℝ) ≤ q := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hq1 : q < 1 := by
    rw [hq]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hpos : (0 : ℝ) < 1 - q := by linarith
  set A : ℝ := 36 * gam ^ 2 with hA
  set B : ℝ := 18 * gam ^ 2 * (h : ℝ) ^ 2
      + 9 * (E ^ 4 * gam ^ 2 * |Real.log gam| ^ 4) with hB
  have hAnn : 0 ≤ A := by rw [hA]; positivity
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  have henv := hasSum_envelope (A := A) (B := B) hq0 hq1
  have hterm : ∀ j : ℕ,
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) * switchRemainder gam E h j
        ≤ A * (((j + 2).choose 2 : ℕ) : ℝ) * q ^ j + B * q ^ j := by
    intro j; rw [hA, hB, hq]; exact weighted_switchRemainder_le hgh j
  have hnn : ∀ j : ℕ,
      0 ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) * switchRemainder gam E h j := by
    intro j
    have h1 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    exact mul_nonneg h1 (switchRemainder_nonneg gam E h j)
  have hsummable : Summable (fun j : ℕ =>
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) * switchRemainder gam E h j) :=
    Summable.of_nonneg_of_le hnn hterm henv.summable
  refine ⟨hsummable, ?_⟩
  have hle : ∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) * switchRemainder gam E h j
      ≤ A * (1 - q)⁻¹ ^ 3 + B * (1 - q)⁻¹ := by
    calc ∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) * switchRemainder gam E h j
        ≤ ∑' j : ℕ, (A * (((j + 2).choose 2 : ℕ) : ℝ) * q ^ j + B * q ^ j) :=
          hsummable.tsum_le_tsum hterm henv.summable
      _ = A * (1 - q)⁻¹ ^ 3 + B * (1 - q)⁻¹ := henv.tsum_eq
  have hcnn : 0 ≤ Book.Ch02.geometricDiscount s 2 := geometricDiscount_two_nonneg hs0.le
  have hshift : Book.Ch02.geometricDiscount s 2 ≤ 3 * (1 - q) := by
    rw [hq]; exact geometricDiscount_two_le_three_mul_shift hgam (by linarith)
  have hinv0 : (0 : ℝ) ≤ (1 - q)⁻¹ := inv_nonneg.2 hpos.le
  have hbig0 : (0 : ℝ) ≤ A * (1 - q)⁻¹ ^ 3 + B * (1 - q)⁻¹ := by positivity
  have hident : 3 * (1 - q) * (A * (1 - q)⁻¹ ^ 3 + B * (1 - q)⁻¹)
      = 3 * A * (1 - q)⁻¹ ^ 2 + 3 * B := by
    field_simp
  have hinvle : (1 - q)⁻¹ ≤ 3 / s := by
    rw [hq]; exact inv_one_sub_shift_le hgam (by linarith) hs1
  have hinvsq : (1 - q)⁻¹ ^ 2 ≤ 9 * (s ^ 2)⁻¹ := by
    have h1 : (1 - q)⁻¹ ^ 2 ≤ (3 / s) ^ 2 := pow_le_pow_left₀ hinv0 hinvle 2
    have h2 : (3 / s : ℝ) ^ 2 = 9 * (s ^ 2)⁻¹ := by field_simp; norm_num
    linarith [h2 ▸ h1]
  have hfinal : 3 * A * (1 - q)⁻¹ ^ 2 + 3 * B
      ≤ 1024 * gam ^ 2 * ((h : ℝ) ^ 2 + (s ^ 2)⁻¹ + E ^ 4 * |Real.log gam| ^ 4) := by
    rw [hA, hB]
    have hg2 : (0 : ℝ) ≤ gam ^ 2 := sq_nonneg gam
    have hsinv : (0 : ℝ) ≤ (s ^ 2)⁻¹ := by positivity
    have hh2 : (0 : ℝ) ≤ (h : ℝ) ^ 2 := sq_nonneg _
    have hE4 : (0 : ℝ) ≤ E ^ 4 * |Real.log gam| ^ 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hinvsq (by positivity : (0 : ℝ) ≤ 108 * gam ^ 2),
      mul_nonneg hg2 hsinv, mul_nonneg hg2 hh2, mul_nonneg hg2 hE4]
  calc Book.Ch02.geometricDiscount s 2 *
        ∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) * switchRemainder gam E h j
      ≤ Book.Ch02.geometricDiscount s 2 * (A * (1 - q)⁻¹ ^ 3 + B * (1 - q)⁻¹) :=
        mul_le_mul_of_nonneg_left hle hcnn
    _ ≤ 3 * (1 - q) * (A * (1 - q)⁻¹ ^ 3 + B * (1 - q)⁻¹) :=
        mul_le_mul_of_nonneg_right hshift hbig0
    _ = 3 * A * (1 - q)⁻¹ ^ 2 + 3 * B := hident
    _ ≤ 1024 * gam ^ 2 *
          ((h : ℝ) ^ 2 + (s ^ 2)⁻¹ + E ^ 4 * |Real.log gam| ^ 4) := hfinal

/-- The weighted family of corrected per-cube remainders is summable. -/
theorem summable_weighted_switchRemainder {s gam E : ℝ} {h : ℕ} (hgam : 0 < gam)
    (hsgam : 8 * gam ≤ s) (hs1 : s ≤ 1) (hgh : gam * (h : ℝ) ≤ 1) :
    Summable (fun j : ℕ =>
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) * switchRemainder gam E h j) :=
  (collapse_core (E := E) hgam hsgam hs1 hgh).1

/-- **The remainder collapse of `l.localization.mathcalE`.**  For
`γ > 0`, `s ∈ [8γ, 1]` and `h ∈ ℕ` with `γ h ≤ 1`,

`c_{2s} Σ_{j ≥ 0} 3^{-sj} (min{γ²(j+h)²,1} + E⁴γ²|log γ|⁴) 3^{2γ(j+h)}` `  ≤
1024 γ² (h² + s^{-2} + E⁴|log γ|⁴)`,

at `j = m - l`.  The constant is absolute. -/
theorem localization_remainder_series_le {s gam E : ℝ} {h : ℕ} (hgam : 0 < gam)
    (hsgam : 8 * gam ≤ s) (hs1 : s ≤ 1) (hgh : gam * (h : ℝ) ≤ 1) :
    Book.Ch02.geometricDiscount s 2 *
        ∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) * switchRemainder gam E h j
      ≤ 1024 * gam ^ 2 *
          ((h : ℝ) ^ 2 + (s ^ 2)⁻¹ + E ^ 4 * |Real.log gam| ^ 4) :=
  (collapse_core hgam hsgam hs1 hgh).2

/-- **The consumer entry point.**  Any nonnegative per-scale remainder family
`f` dominated termwise by `C ·` the corrected per-cube remainder collapses to
the collapsed amplitude at `1024 C`.  The summability of the weighted family is
discharged internally, so callers owe no `Summable` obligation. -/
theorem localization_remainder_series_le_of_termwise {s gam E C : ℝ} {h : ℕ}
    {f : ℕ → ℝ} (hgam : 0 < gam) (hsgam : 8 * gam ≤ s) (hs1 : s ≤ 1)
    (hgh : gam * (h : ℝ) ≤ 1) (hC : 0 ≤ C) (hf0 : ∀ j, 0 ≤ f j)
    (hf : ∀ j, f j ≤ C * switchRemainder gam E h j) :
    Book.Ch02.geometricDiscount s 2 *
        ∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) * f j
      ≤ 1024 * C * gam ^ 2 *
          ((h : ℝ) ^ 2 + (s ^ 2)⁻¹ + E ^ 4 * |Real.log gam| ^ 4) := by
  have hs0 : 0 < s := lt_of_lt_of_le (by linarith) hsgam
  have hbase := summable_weighted_switchRemainder (E := E) hgam hsgam hs1 hgh
  have hmaj : Summable (fun j : ℕ =>
      C * (Real.rpow (3 : ℝ) (-s * (j : ℝ)) * switchRemainder gam E h j)) :=
    hbase.mul_left C
  have hwnn : ∀ j : ℕ, (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) := fun j =>
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hterm : ∀ j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) * f j
      ≤ C * (Real.rpow (3 : ℝ) (-s * (j : ℝ)) * switchRemainder gam E h j) := by
    intro j
    have := mul_le_mul_of_nonneg_left (hf j) (hwnn j)
    calc Real.rpow (3 : ℝ) (-s * (j : ℝ)) * f j
        ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) * (C * switchRemainder gam E h j) := this
      _ = C * (Real.rpow (3 : ℝ) (-s * (j : ℝ)) * switchRemainder gam E h j) := by ring
  have hnn : ∀ j : ℕ, 0 ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) * f j := fun j =>
    mul_nonneg (hwnn j) (hf0 j)
  have hsumf : Summable (fun j : ℕ => Real.rpow (3 : ℝ) (-s * (j : ℝ)) * f j) :=
    Summable.of_nonneg_of_le hnn hterm hmaj
  have hle : ∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) * f j
      ≤ C * ∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) * switchRemainder gam E h j := by
    calc ∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) * f j
        ≤ ∑' j : ℕ, C * (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            switchRemainder gam E h j) := hsumf.tsum_le_tsum hterm hmaj
      _ = C * ∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            switchRemainder gam E h j := hbase.tsum_mul_left C
  have hcnn : 0 ≤ Book.Ch02.geometricDiscount s 2 := geometricDiscount_two_nonneg hs0.le
  have hkey := localization_remainder_series_le (E := E) hgam hsgam hs1 hgh
  calc Book.Ch02.geometricDiscount s 2 *
        ∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) * f j
      ≤ Book.Ch02.geometricDiscount s 2 *
          (C * ∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            switchRemainder gam E h j) := mul_le_mul_of_nonneg_left hle hcnn
    _ = C * (Book.Ch02.geometricDiscount s 2 *
          ∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            switchRemainder gam E h j) := by ring
    _ ≤ C * (1024 * gam ^ 2 *
          ((h : ℝ) ^ 2 + (s ^ 2)⁻¹ + E ^ 4 * |Real.log gam| ^ 4)) :=
        mul_le_mul_of_nonneg_left hkey hC
    _ = 1024 * C * gam ^ 2 *
          ((h : ℝ) ^ 2 + (s ^ 2)⁻¹ + E ^ 4 * |Real.log gam| ^ 4) := by ring

end

end Algsuperdiff.Section3.Provider.Localization
