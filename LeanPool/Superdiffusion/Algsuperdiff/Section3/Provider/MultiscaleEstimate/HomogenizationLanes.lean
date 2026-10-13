/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Localization.GoodEventAggregation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.MultiscaleEstimate.ParameterWeb
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.AESummability
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.Maximum

/-!
# HomogenizationLanes

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the lane aggregation and corridor consumption of `e.what.homogenization.gives`

ABK26, §3.6.

```text
s * sum_{l = -infty}^{m} 3^{-s(m-l)}
      ( avsum_{z in 3^l Z^d cap cu_m}
          max_{|e| = 1} J(z + cu_l, shom_{l-h}^{-1/2} e, shom_{l-h}^{1/2} e; a_{l-h})^{d/s}
      )^{s/d}
  <= O_{Gamma_1}(C s^{-1} eps E^2 cgamma)
   + O_{Gamma_{1/4}}(C eps exp(-E^{-3} cgamma^{-1})) ,
```

proved in the manuscript in one sentence: *"an immediate consequence of
Proposition `p.homogenization.step`, the triangle inequality
`e.Gamma.sigma.triangle` and the fact that `s >= 8 cgamma`, provided that `h:=
C |log eps|` for `C` large enough"*.

**This module is the other half**: the `(l, z)` aggregation, the corridor
bookkeeping, and the a.e.-to-pointwise bridge.

## The route

Fix a depth `j`, write `l = m - j`, and let `N_j = 3^{dj}` be the depth-`j` grid cardinality.

1. **The grid maximum.**  The per-cube inputs at depth `j` share one amplitude
   pair, so the maximum over the `N_j` cubes is `Gamma_sigma` at `(3 max{1, log
   N_j})^{1/sigma} A` --- the manuscript's own `l.maximums.Gamma.s`, in the
   proved singleton-safe form
   `Orlicz.isBigOWith_gammaSigma_finset_sup'_of_nonempty`.
2. **The power-mean ceiling.**  A power mean is below the maximum of its
   arguments, so the printed `(avsum_z (.)^{d/s})^{s/d}` is below that grid
   maximum.  This is the proved `Breakdown.legScaleAverage_le_const`; it costs
   nothing.
3. **The depth sum.**  The per-depth amplitudes `3^{-sj} (3 max{1, d j log 3})^{1/sigma} A` are
   summable, with the closed forms of sections 3 and 4 below: `45 d s^{-2} A_1` on the
   `Gamma_1` lane and `12000000 d^4 s^{-5} A_2` on the `Gamma_{1/4}` lane.  The countable
   `Gamma_sigma` triangle inequality (`Orlicz.isBigOWith_gammaSigma_tsum_of_tsum_le`, constant
   `gammaTriangleConst sigma`) then produces one envelope per lane.

After the printed normalization by `s` the amplitudes are `C(d) s^{-1} A_1` and
`C(d) s^{-4} A_2`.  So this module delivers the best profile the manuscript's
own proof supports.

**A divergence of route.**  The printed one-line proof attributes the
`z`-aggregation to `e.Gamma.sigma.triangle`.  That route is not taken here, for
a formalization reason: the available `gammaTriangleConst sigma =
4 gammaGrowthConst sigma ^ 12` is not the sharp `M_sigma ~ sigma^{-1/sigma}`,
and at the index `sigma s/d` it inflates `s^{-4}` to `s^{-48}`.  This module
therefore routes through the Appendix's own `l.maximums.Gamma.s` per depth and
the triangle inequality across depths, where the index is fixed at `1` and
`1/4` and the constant is absolute.  Same displays, same exponents, different
mechanism.

## The amplitudes, and how they meet the frozen root

At `eps' := eps^2` the per-cube input carries `A_1 = eps^2 E^2 cgamma` and `A_2
= eps^2 exp(-2 E^{-3} cgamma^{-1})` (the sharp rate).  The two lanes therefore
read, after the printed normalization by `s`,

```text
Gamma_1      :  C_ord(d) s^{-1} eps^2 E^2 cgamma ,
Gamma_{1/4}  :  C_rare(d) s^{-4} eps^2 exp(-2 E^{-3} cgamma^{-1}) .
```

The first is **below the printed** `C s^{-1} eps E^2 cgamma` a fortiori (`eps
<= 1/2`).

## Deliverables

* ** the lane aggregation** --- `exists_envelope_gridScaleSeries_of_perCube`
  (abstract) and `exists_envelope_gridScaleSeries_homogenizationInput` (at the
  development's carriers, on the proved
  `GoodEventAggregation.gridScaleSeries`).  The domination is ONE almost-sure
  statement with the depth and cube quantifiers **inside** the event, so the
  per-cube input's common-event structure survives in the statement.  The
  concrete proof does take the countable intersection --- the per-cube producer emits
  one a.e. statement per `(j, R)` and section 8 collects them by
  `MeasureTheory.ae_all_iff` over depths and `Filter.eventually_all_finset`
  over each depth's finite grid --- which is harmless (countable intersection
  of full-measure sets) and exactly why the strong form is provable.
* **(c) the pointwise endpoint** --- `exists_witnesses_of_envelope`.  The
  device is the web's unconditional `exists_witnesses_ae_eq_of_ae_le`: the
  returned witnesses are almost everywhere equal to the envelopes, so a further
  tail of those envelopes transfers and the frozen conclusion's second conjunct
  survives on the same `Y`.

`geometricDiscount_two_mul_le_of_nonneg` is the seam to
`e.localization.mathcalE.estimate`'s own normalization: `c_{2s} <= 4 s` at the
localization side's own carrier from
`Provider.Localization.geometricDiscount_two_le_four_mul`, so the
`s`-normalized display dominates the localization lemma's first term at an
absolute cost.

## Named gaps, with owners

The `max_e` carrier and the measurability of the display are items 1 and 2
above.

## Sources

* ABK26: the `avsum` average; `e.what.homogenization.gives` (its one-line
  proof and the cutoff `h := C|log eps|`); `p.multiscale.estimate` and
  `e.param.conditions.in.main`; the Appendix's weak-Orlicz notation and
  `l.maximums.Gamma.s`, whose amplitude `(3 log N)^{1/sigma} A` is exactly the
  proved `Provider/Orlicz/Maximum.lean` engine's.
-/

namespace Algsuperdiff.Section3.Provider.MultiscaleEstimate

open _root_.MeasureTheory
open _root_.HCPolySupport
open _root_.HCPolySupport.IndependentSums
open _root_.Algsuperdiff.Section3.Cutoff
open _root_.Algsuperdiff.Section3.Provider.Localization

noncomputable section

variable {d : ℕ}

/-! ## 1. The depth series -/

/-- The depth series at the printed weight, against the printed algebraic pole.
Both inputs are proved publics; nothing is re-proved. -/
theorem tsum_three_rpow_neg_mul_nat_le {s : ℝ} (hs : 0 < s) :
    (∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ))) ≤ 1 + s⁻¹ := by
  rw [Book.Ch05.Section52.tsum_rpow_three_neg_mul_nat_eq_inv_geometricDiscount hs]
  have hg : geometricDiscount s 1 = 1 - (3 : ℝ) ^ (-s) := by
    simp [geometricDiscount]
  rw [hg]
  exact Provider.CoarseEllipticity.one_sub_rpow_neg_inv_le hs

/-- The form the two lanes of section 3 consume: on the window `s ≤ 1` the algebraic pole
`1 + (s/2)⁻¹` is below `3 s^{-1}`. -/
theorem tsum_three_rpow_neg_half_mul_nat_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    (∑' j : ℕ, Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ))) ≤ 3 / s := by
  have hs2 : (0 : ℝ) < s / 2 := by linarith
  have h := tsum_three_rpow_neg_mul_nat_le hs2
  have hinv : (1 : ℝ) ≤ s⁻¹ := (one_le_inv₀ hs).2 hs1
  have heq : (s / 2)⁻¹ = 2 * s⁻¹ := by field_simp
  rw [heq] at h
  have hdiv : (3 : ℝ) / s = 3 * s⁻¹ := by rw [div_eq_mul_inv]
  rw [hdiv]
  linarith

/-! ## 2. The polynomial factor of the grid maximum -/

/-- `Real.rpow` and the real power notation are the same function; the proved
`gridScaleSeries` writes the first, the `Real.rpow` A the second. -/
private theorem rpow_three_eq (e : ℝ) : Real.rpow (3 : ℝ) e = (3 : ℝ) ^ e := rfl

private theorem pow_mul_exp_neg_le (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ k * Real.exp (-x) ≤ (Nat.factorial k : ℝ) := by
  have hfac : (0 : ℝ) < (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.factorial_pos k
  have hterm : x ^ k / (Nat.factorial k : ℝ) ≤ Real.exp x :=
    Real.pow_div_factorial_le_exp (x := x) hx k
  have hxk : x ^ k ≤ (Nat.factorial k : ℝ) * Real.exp x := by
    rw [div_le_iff₀ hfac] at hterm
    linarith
  calc x ^ k * Real.exp (-x)
      ≤ ((Nat.factorial k : ℝ) * Real.exp x) * Real.exp (-x) :=
        mul_le_mul_of_nonneg_right hxk (Real.exp_pos _).le
    _ = (Nat.factorial k : ℝ) := by
        rw [mul_assoc, ← Real.exp_add]
        simp

private theorem nat_pow_mul_rpow_half_le {s : ℝ} (hs : 0 < s) (k j : ℕ) :
    ((j : ℝ)) ^ k * Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) ≤
      (Nat.factorial k : ℝ) * (2 / s) ^ k := by
  have hlog := Provider.CoarseEllipticity.one_lt_log_three
  set c : ℝ := s / 2 * Real.log 3 with hc
  have hcpos : 0 < c := by
    rw [hc]; positivity
  have hrpow : Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) = Real.exp (-(c * (j : ℝ))) := by
    rw [rpow_three_eq, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    congr 1
    rw [hc]; ring
  have hx : (0 : ℝ) ≤ c * (j : ℝ) := by positivity
  have hkey := pow_mul_exp_neg_le k hx
  rw [mul_pow] at hkey
  have hck : (0 : ℝ) < c ^ k := pow_pos hcpos k
  have hsplit : ((j : ℝ)) ^ k * Real.exp (-(c * (j : ℝ))) =
      (c ^ k * ((j : ℝ)) ^ k * Real.exp (-(c * (j : ℝ)))) * (c ^ k)⁻¹ := by
    field_simp
  have hcinv : c⁻¹ ≤ 2 / s := by
    have h1 : s / 2 ≤ c := by
      rw [hc]; nlinarith
    have h2 : (0 : ℝ) < s / 2 := by linarith
    have h3 : c⁻¹ ≤ (s / 2)⁻¹ := by
      rw [inv_le_inv₀ hcpos h2]
      exact h1
    calc c⁻¹ ≤ (s / 2)⁻¹ := h3
      _ = 2 / s := by field_simp
  have hstep : ((j : ℝ)) ^ k * Real.exp (-(c * (j : ℝ))) ≤
      (Nat.factorial k : ℝ) * (c⁻¹) ^ k := by
    rw [hsplit, ← inv_pow]
    exact mul_le_mul_of_nonneg_right hkey (by positivity)
  rw [hrpow]
  refine hstep.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact pow_le_pow_left₀ (by positivity) hcinv k

/-- The `a := 1` case of the proved
`Provider.Diffusivity.ApproximateRecurrence.add_pow_four_le_eight_mul`. -/
private theorem add_pow_four_le (u : ℝ) : (1 + u) ^ 4 ≤ 8 * (1 + u ^ 4) := by
  simpa using Provider.Diffusivity.ApproximateRecurrence.add_pow_four_le_eight_mul 1 u

private theorem weight_split (s : ℝ) (j : ℕ) :
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) =
      Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) * Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) := by
  simp only [rpow_three_eq]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

private theorem rpow_half_le_one {s : ℝ} (hs : 0 ≤ s) (j : ℕ) :
    Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) ≤ 1 := by
  simp only [rpow_three_eq]
  refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
  have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  nlinarith

private theorem rpow_half_nonneg (s : ℝ) (j : ℕ) :
    0 ≤ Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) :=
  Real.rpow_nonneg (by norm_num) _

/-- The ordinary-lane per-depth amplitude, discounted to a bare geometric term. -/
private theorem ordinary_term_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {d : ℕ} (hd : d ≠ 0)
    (j : ℕ) :
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) * (3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3))) ≤
      15 * (d : ℝ) / s * Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
  have hlog0 : (0 : ℝ) ≤ Real.log 3 := by
    linarith [Provider.CoarseEllipticity.one_lt_log_three]
  have hlog2 := Provider.Percolation.log_three_le_two
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hw := rpow_half_nonneg s j
  have hw1 := rpow_half_le_one hs.le j
  have hu0 : (0 : ℝ) ≤ (j : ℝ) * ((d : ℝ) * Real.log 3) := by positivity
  have hmax : max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3)) ≤
      1 + (j : ℝ) * ((d : ℝ) * Real.log 3) := max_le (by linarith) (by linarith)
  have hone := nat_pow_mul_rpow_half_le hs 1 j
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, one_mul] at hone
  have hkey : Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) *
      (3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3))) ≤ 15 * (d : ℝ) / s := by
    have hstep : Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) *
        (3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3))) ≤
          3 * Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) +
            3 * ((d : ℝ) * Real.log 3) *
              ((j : ℝ) * Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ))) := by
      nlinarith [mul_le_mul_of_nonneg_left hmax hw]
    have h1 : 3 * Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) ≤ 3 := by linarith
    have h2 : 3 * ((d : ℝ) * Real.log 3) *
        ((j : ℝ) * Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ))) ≤
          3 * ((d : ℝ) * Real.log 3) * (2 / s) :=
      mul_le_mul_of_nonneg_left hone (by positivity)
    have h3 : 3 * ((d : ℝ) * Real.log 3) * (2 / s) ≤ 12 * (d : ℝ) / s := by
      have heq : 3 * ((d : ℝ) * Real.log 3) * (2 / s) = (6 * (d : ℝ) * Real.log 3) / s := by
        ring
      rw [heq, div_le_div_iff_of_pos_right hs]
      nlinarith
    have h4 : (3 : ℝ) ≤ 3 * (d : ℝ) / s := by
      rw [le_div_iff₀ hs]
      nlinarith
    have h5 : 12 * (d : ℝ) / s + 3 * (d : ℝ) / s = 15 * (d : ℝ) / s := by ring
    linarith
  calc Real.rpow (3 : ℝ) (-s * (j : ℝ)) * (3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3)))
      = Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) *
          (Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) *
            (3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3)))) := by
        rw [weight_split s j]; ring
    _ ≤ Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) * (15 * (d : ℝ) / s) :=
        mul_le_mul_of_nonneg_left hkey hw
    _ = 15 * (d : ℝ) / s * Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) := by ring

/-- The rare-lane per-depth amplitude, discounted to a bare geometric term. -/
private theorem rare_term_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {d : ℕ} (hd : d ≠ 0)
    (j : ℕ) :
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        (3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3))) ^ 4 ≤
      4000000 * (d : ℝ) ^ 4 / s ^ 4 * Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
  have hlog0 : (0 : ℝ) ≤ Real.log 3 := by
    linarith [Provider.CoarseEllipticity.one_lt_log_three]
  have hlog2 := Provider.Percolation.log_three_le_two
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hw := rpow_half_nonneg s j
  have hw1 := rpow_half_le_one hs.le j
  have hu0 : (0 : ℝ) ≤ (j : ℝ) * ((d : ℝ) * Real.log 3) := by positivity
  have hmax0 : (0 : ℝ) ≤ max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3)) :=
    le_trans zero_le_one (le_max_left _ _)
  have hmax : max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3)) ≤
      1 + (j : ℝ) * ((d : ℝ) * Real.log 3) := max_le (by linarith) (by linarith)
  have hfour := nat_pow_mul_rpow_half_le hs 4 j
  have hfac4 : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hfac4] at hfour
  have hpow4 : ((2 : ℝ) / s) ^ 4 = 16 / s ^ 4 := by
    rw [div_pow]; norm_num
  rw [hpow4] at hfour
  have hjw : (j : ℝ) ^ 4 * Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) ≤ 384 / s ^ 4 := by
    have : (24 : ℝ) * (16 / s ^ 4) = 384 / s ^ 4 := by ring
    linarith [hfour, this.le, this.ge]
  have hjw0 : (0 : ℝ) ≤ (j : ℝ) ^ 4 * Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) := by
    positivity
  have hlogd : ((d : ℝ) * Real.log 3) ^ 4 ≤ 16 * (d : ℝ) ^ 4 := by
    have hl4 : (Real.log 3) ^ 4 ≤ 16 := by
      have := pow_le_pow_left₀ hlog0 hlog2 4
      norm_num at this
      linarith
    have hd4 : (0 : ℝ) ≤ (d : ℝ) ^ 4 := by positivity
    rw [mul_pow]
    nlinarith
  have hlogd0 : (0 : ℝ) ≤ ((d : ℝ) * Real.log 3) ^ 4 := by positivity
  have hprod : ((d : ℝ) * Real.log 3) ^ 4 *
      ((j : ℝ) ^ 4 * Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ))) ≤
        (16 * (d : ℝ) ^ 4) * (384 / s ^ 4) :=
    mul_le_mul hlogd hjw hjw0 (by positivity)
  have hT : (1 : ℝ) ≤ (d : ℝ) ^ 4 / s ^ 4 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [pow_le_one₀ hs.le hs1 (n := 4), one_le_pow₀ hd1 (n := 4)]
  have hchain : Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) *
      (3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3))) ^ 4 ≤
        648 * Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) +
          648 * (((d : ℝ) * Real.log 3) ^ 4 *
            ((j : ℝ) ^ 4 * Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)))) := by
    have e2 : (max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3))) ^ 4 ≤
        (1 + (j : ℝ) * ((d : ℝ) * Real.log 3)) ^ 4 :=
      pow_le_pow_left₀ hmax0 hmax 4
    have e3 := add_pow_four_le ((j : ℝ) * ((d : ℝ) * Real.log 3))
    have hle : Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) *
        (max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3))) ^ 4 ≤
          Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) *
            (8 * (1 + ((j : ℝ) * ((d : ℝ) * Real.log 3)) ^ 4)) :=
      mul_le_mul_of_nonneg_left (le_trans e2 e3) hw
    nlinarith [hle]
  have hfin : 648 * Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) +
      648 * (((d : ℝ) * Real.log 3) ^ 4 *
        ((j : ℝ) ^ 4 * Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)))) ≤
      4000000 * (d : ℝ) ^ 4 / s ^ 4 := by
    have hb : (16 * (d : ℝ) ^ 4) * (384 / s ^ 4) = 6144 * ((d : ℝ) ^ 4 / s ^ 4) := by
      ring
    have hgoal : 4000000 * (d : ℝ) ^ 4 / s ^ 4 = 4000000 * ((d : ℝ) ^ 4 / s ^ 4) := by
      ring
    rw [hgoal]
    nlinarith [hprod, hT, hw1, hb.le, hb.ge]
  calc Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        (3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3))) ^ 4
      = Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) *
          (Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) *
            (3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3))) ^ 4) := by
        rw [weight_split s j]; ring
    _ ≤ Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) * (4000000 * (d : ℝ) ^ 4 / s ^ 4) :=
        mul_le_mul_of_nonneg_left (le_trans hchain hfin) hw
    _ = 4000000 * (d : ℝ) ^ 4 / s ^ 4 * Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) := by ring

/-! ## 3. The two depth-series amplitudes -/

/-- **The ordinary lane's depth series.**  `Σ_j 3^{-sj} (3 max{1, log 3^{dj}})`, the amplitude
series of the `Γ₁` grid maxima, is `O(d s^{-2})`. -/
theorem tsum_ordinaryWeight_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {d : ℕ} (hd : d ≠ 0) :
    (∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        (3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3)))) ≤ 45 * (d : ℝ) * (s⁻¹) ^ 2 := by
  have hs2 : (0 : ℝ) < s / 2 := by linarith
  have hs21 : s / 2 ≤ 1 := by linarith
  have hmajSummable : Summable (fun j : ℕ =>
      15 * (d : ℝ) / s * Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ))) :=
    (Book.Ch05.Section52.summable_rpow_three_neg_mul_nat hs2).mul_left _
  have hterm := fun j : ℕ => ordinary_term_le hs hs1 hd j
  have hnn : ∀ j : ℕ, 0 ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      (3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3))) := by
    intro j
    refine mul_nonneg (Real.rpow_nonneg (by norm_num) _) ?_
    have := le_max_left (1 : ℝ) ((j : ℝ) * ((d : ℝ) * Real.log 3))
    linarith
  have hsum : Summable (fun j : ℕ => Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      (3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3)))) :=
    Summable.of_nonneg_of_le hnn hterm hmajSummable
  have hgeom : (∑' j : ℕ, Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ))) ≤ 3 / s :=
    tsum_three_rpow_neg_half_mul_nat_le hs hs1
  calc (∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        (3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3))))
      ≤ ∑' j : ℕ, 15 * (d : ℝ) / s * Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) :=
        hsum.tsum_le_tsum hterm hmajSummable
    _ = 15 * (d : ℝ) / s * ∑' j : ℕ, Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) :=
        tsum_mul_left
    _ ≤ 15 * (d : ℝ) / s * (3 / s) := by
        refine mul_le_mul_of_nonneg_left hgeom ?_
        have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
        positivity
    _ = 45 * (d : ℝ) * (s⁻¹) ^ 2 := by
        field_simp
        ring

theorem tsum_rareWeight_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {d : ℕ} (hd : d ≠ 0) :
    (∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        (3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3))) ^ 4) ≤
      12000000 * (d : ℝ) ^ 4 * (s⁻¹) ^ 5 := by
  have hs2 : (0 : ℝ) < s / 2 := by linarith
  have hs21 : s / 2 ≤ 1 := by linarith
  have hmajSummable : Summable (fun j : ℕ =>
      4000000 * (d : ℝ) ^ 4 / s ^ 4 * Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ))) :=
    (Book.Ch05.Section52.summable_rpow_three_neg_mul_nat hs2).mul_left _
  have hterm := fun j : ℕ => rare_term_le hs hs1 hd j
  have hnn : ∀ j : ℕ, 0 ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      (3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3))) ^ 4 := by
    intro j
    refine mul_nonneg (Real.rpow_nonneg (by norm_num) _) ?_
    have h1 := le_max_left (1 : ℝ) ((j : ℝ) * ((d : ℝ) * Real.log 3))
    positivity
  have hsum : Summable (fun j : ℕ => Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      (3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3))) ^ 4) :=
    Summable.of_nonneg_of_le hnn hterm hmajSummable
  have hgeom : (∑' j : ℕ, Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ))) ≤ 3 / s :=
    tsum_three_rpow_neg_half_mul_nat_le hs hs1
  calc (∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        (3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3))) ^ 4)
      ≤ ∑' j : ℕ, 4000000 * (d : ℝ) ^ 4 / s ^ 4 *
          Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) :=
        hsum.tsum_le_tsum hterm hmajSummable
    _ = 4000000 * (d : ℝ) ^ 4 / s ^ 4 *
          ∑' j : ℕ, Real.rpow (3 : ℝ) (-(s / 2) * (j : ℝ)) := tsum_mul_left
    _ ≤ 4000000 * (d : ℝ) ^ 4 / s ^ 4 * (3 / s) := by
        refine mul_le_mul_of_nonneg_left hgeom ?_
        have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
        positivity
    _ = 12000000 * (d : ℝ) ^ 4 * (s⁻¹) ^ 5 := by
        field_simp
        ring

/-! ## 4. Summability of the two depth series -/

theorem summable_ordinaryWeight {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {d : ℕ} (hd : d ≠ 0) :
    Summable (fun j : ℕ => Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      (3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3)))) := by
  have hs2 : (0 : ℝ) < s / 2 := by linarith
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ordinary_term_le hs hs1 hd j)
    ((Book.Ch05.Section52.summable_rpow_three_neg_mul_nat hs2).mul_left _)
  refine mul_nonneg (Real.rpow_nonneg (by norm_num) _) ?_
  have := le_max_left (1 : ℝ) ((j : ℝ) * ((d : ℝ) * Real.log 3))
  linarith

theorem summable_rareWeight {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {d : ℕ} (hd : d ≠ 0) :
    Summable (fun j : ℕ => Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      (3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3))) ^ 4) := by
  have hs2 : (0 : ℝ) < s / 2 := by linarith
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => rare_term_le hs hs1 hd j)
    ((Book.Ch05.Section52.summable_rpow_three_neg_mul_nat hs2).mul_left _)
  refine mul_nonneg (Real.rpow_nonneg (by norm_num) _) ?_
  have h1 := le_max_left (1 : ℝ) ((j : ℝ) * ((d : ℝ) * Real.log 3))
  positivity

/-! ## 5. The abstract lane aggregation -/

/-- Measurability of a countable sum of nonnegative measurable functions.  The
`Measurable` twin of the proved `A.aemeasurable_tsum_of_nonneg`
(`Provider/Orlicz/TsumTriangle.lean`), same `NNReal` route; that lemma returns
only `AEMeasurable`, while `IsTwoTermBigOWithWitnesses` and the witness upgrade demand
`Measurable`. -/
private theorem measurable_tsum_of_nonneg {Omega : Type*} [MeasurableSpace Omega]
    {X : ℕ → Omega → ℝ} (hXm : ∀ k, Measurable (X k)) (hX0 : ∀ k omega, 0 ≤ X k omega) :
    Measurable (fun omega => ∑' k : ℕ, X k omega) := by
  have hnn : Measurable (fun omega => ∑' k : ℕ, (X k omega).toNNReal) :=
    Measurable.tsum (L := SummationFilter.unconditional ℕ) fun k => (hXm k).real_toNNReal
  have hnn := hnn.coe_nnreal_real
  convert hnn using 1
  funext omega
  rw [NNReal.coe_tsum]
  refine tsum_congr fun k => ?_
  rw [Real.toNNReal_of_nonneg (hX0 k omega)]
  rfl

/-- **One lane of the aggregation.**  A per-`(depth, cube)` family of `Γ_σ` variables at one
common amplitude `A` is turned into a single measurable envelope for the whole weighted grid
series: the grid maximum at each depth (`Provider/Orlicz/Maximum.lean`, amplitude
`(3 max{1, log N})^{1/σ} A`), then the countable `Γ_σ` triangle inequality across depths
(`Provider/Orlicz/TsumTriangle.lean`, constant `gammaTriangleConst σ`).  The amplitude family
`alpha` is a parameter so that the caller supplies the closed-form depth-series bound of
section 3; nothing here is specific to `σ ∈ {1, 1/4}`. -/
private theorem exists_laneEnvelope {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (m : ℤ) {s : ℝ} {sigma : ℝ} (hsigma : 0 < sigma)
    (hne : ∀ j : ℕ, (descendantsAtScale (originCube d m) (m - (j : ℤ))).Nonempty)
    {W : ℕ → TriadicCube d → Omega → ℝ} {A B : ℝ} (hA : 0 < A)
    (hWm : ∀ (j : ℕ), ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      Measurable (W j R))
    (hWt : ∀ (j : ℕ), ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      IsBigOWith mu (gammaSigma sigma) (W j R) A)
    (alpha : ℕ → ℝ) (halphaPos : ∀ j, 0 < alpha j) (halphaSum : Summable alpha)
    (halphaB : (∑' j : ℕ, alpha j) ≤ B)
    (halphaBound : ∀ j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      ((3 * max 1 (Real.log
        (((descendantsAtScale (originCube d m) (m - (j : ℤ))).card : ℕ) : ℝ))) ^ sigma⁻¹ * A) ≤
        alpha j) :
    ∃ g : ℕ → Omega → ℝ,
      (∀ j omega, 0 ≤ g j omega) ∧
      (∀ (j : ℕ) (omega : Omega),
        ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)), W j R omega ≤ g j omega) ∧
      Measurable (fun omega => ∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) * g j omega) ∧
      IsBigOWith mu (gammaSigma sigma)
        (fun omega => ∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) * g j omega)
        (gammaTriangleConst sigma * B) ∧
      (∀ᵐ omega ∂mu,
        Summable (fun j : ℕ => Real.rpow (3 : ℝ) (-s * (j : ℝ)) * g j omega)) := by
  classical
  set g : ℕ → Omega → ℝ := fun j omega =>
    max 0 ((descendantsAtScale (originCube d m) (m - (j : ℤ))).sup' (hne j)
      fun R => W j R omega) with hg
  have hg0 : ∀ j omega, 0 ≤ g j omega := fun j omega => le_max_left _ _
  have hgle : ∀ (j : ℕ) (omega : Omega),
      ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)), W j R omega ≤ g j omega := by
    intro j omega R hR
    exact le_trans (Finset.le_sup' (f := fun R => W j R omega) hR) (le_max_right _ _)
  have hsupMeas : ∀ j : ℕ, Measurable (fun omega =>
      (descendantsAtScale (originCube d m) (m - (j : ℤ))).sup' (hne j)
        fun R => W j R omega) := by
    intro j
    have hfun : (fun omega =>
        (descendantsAtScale (originCube d m) (m - (j : ℤ))).sup' (hne j)
          fun R => W j R omega) =
        (descendantsAtScale (originCube d m) (m - (j : ℤ))).sup' (hne j) (fun R => W j R) := by
      funext omega
      rw [Finset.sup'_apply]
    rw [hfun]
    exact Finset.measurable_sup' (hne j) fun R hR => hWm j R hR
  have hgMeas : ∀ j : ℕ, Measurable (g j) := by
    intro j
    exact measurable_const.max (hsupMeas j)
  have hampPos : ∀ j : ℕ, (0 : ℝ) <
      (3 * max 1 (Real.log
        (((descendantsAtScale (originCube d m) (m - (j : ℤ))).card : ℕ) : ℝ))) ^ sigma⁻¹ * A := by
    intro j
    have hbase : (0 : ℝ) < 3 * max 1 (Real.log
        (((descendantsAtScale (originCube d m) (m - (j : ℤ))).card : ℕ) : ℝ)) := by
      have := le_max_left (1 : ℝ) (Real.log
        (((descendantsAtScale (originCube d m) (m - (j : ℤ))).card : ℕ) : ℝ))
      linarith
    exact mul_pos (Real.rpow_pos_of_pos hbase _) hA
  have hsupTail : ∀ j : ℕ, IsBigOWith mu (gammaSigma sigma) (g j)
      ((3 * max 1 (Real.log
        (((descendantsAtScale (originCube d m) (m - (j : ℤ))).card : ℕ) : ℝ))) ^ sigma⁻¹ * A) := by
    intro j
    have hsup := Provider.Orlicz.isBigOWith_gammaSigma_finset_sup'_of_nonempty
      (μ := mu) (descendantsAtScale (originCube d m) (m - (j : ℤ))) (hne j)
      (X := fun R omega => W j R omega) (A := A) (σ := sigma) hsigma hA.le
      (fun R hR => hWt j R hR)
    have hclamp := Provider.Tail.isBigOWith_max_zero (hampPos j) hsup
    exact hclamp
  have hweightNonneg : ∀ j : ℕ, (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) := fun j =>
    Real.rpow_nonneg (by norm_num) _
  have hX0 : ∀ (j : ℕ) (omega : Omega),
      0 ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) * g j omega := fun j omega =>
    mul_nonneg (hweightNonneg j) (hg0 j omega)
  have hXm : ∀ j : ℕ, Measurable (fun omega => Real.rpow (3 : ℝ) (-s * (j : ℝ)) * g j omega) :=
    fun j => (hgMeas j).const_mul _
  have hXt : ∀ j : ℕ, IsBigOWith mu (gammaSigma sigma)
      (fun omega => Real.rpow (3 : ℝ) (-s * (j : ℝ)) * g j omega) (alpha j) := by
    intro j
    exact (IsBigOWith.const_mul (hweightNonneg j) (hsupTail j)).mono_scale (halphaBound j)
  refine ⟨g, hg0, hgle, measurable_tsum_of_nonneg hXm hX0, ?_, ?_⟩
  · exact Provider.Orlicz.isBigOWith_gammaSigma_tsum_of_tsum_le hsigma hX0 hXm
      halphaPos halphaSum hXt halphaB
  · exact Provider.Orlicz.ae_summable_of_isBigOWith_gammaSigma hsigma hX0
      (fun j => (hXm j).aemeasurable) halphaPos halphaSum hXt

/-! ## 6. The lane aggregation -/

/-- The `Γ₁` constant of the aggregated ordinary lane. -/
def homLaneOrdinaryConst (d : ℕ) : ℝ := gammaTriangleConst 1 * (45 * (d : ℝ))

/-- The `Γ_{1/4}` constant of the aggregated rare lane. -/
def homLaneRareConst (d : ℕ) : ℝ :=
  gammaTriangleConst (1 / 4) * (12000000 * (d : ℝ) ^ 4)

theorem homLaneOrdinaryConst_pos {d : ℕ} (hd : d ≠ 0) : 0 < homLaneOrdinaryConst d := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
  have := gammaTriangleConst_pos (σ := (1 : ℝ))
  have h45 : (0 : ℝ) < 45 * (d : ℝ) := by linarith
  exact mul_pos this h45

theorem homLaneRareConst_pos {d : ℕ} (hd : d ≠ 0) : 0 < homLaneRareConst d := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
  have := gammaTriangleConst_pos (σ := (1 / 4 : ℝ))
  have h : (0 : ℝ) < 12000000 * (d : ℝ) ^ 4 := by positivity
  exact mul_pos this h

private theorem grid_nonempty (d : ℕ) (m : ℤ) (j : ℕ) :
    (descendantsAtScale (originCube d m) (m - (j : ℤ))).Nonempty :=
  descendantsAtScale_nonempty (originCube d m) (show m - (j : ℤ) ≤ m by omega)

/-- The union loss of the depth-`j` grid from the proved
`Provider.BadEvents.log_card_descendantsAtScale`. -/
private theorem log_grid_card (d : ℕ) (m : ℤ) (j : ℕ) :
    Real.log (((descendantsAtScale (originCube d m) (m - (j : ℤ))).card : ℕ) : ℝ) =
      (j : ℝ) * ((d : ℝ) * Real.log 3) := by
  have hk : m - (j : ℤ) ≤ (originCube d m).scale := show m - (j : ℤ) ≤ m by omega
  rw [Provider.BadEvents.log_card_descendantsAtScale (originCube d m) hk]
  show (d : ℝ) * ((m : ℝ) - ((m - (j : ℤ) : ℤ) : ℝ)) * Real.log 3 = _
  push_cast
  ring

/-- **The lane aggregation, abstractly.**  A per-`(depth, cube)` family of
two-term inputs at one common amplitude pair `(A₁, A₂)` — the shape the
`ε²`-route homogenization step delivers at every scale `l = m - j` and every
grid cube — is aggregated into a single measurable envelope pair for the whole
printed grid series

```text
Σ_{l ≤ m} 3^{-s(m-l)} ( ⨍_{z ∈ 3^l ℤ^d ∩ □_m} leg_l(z+□_l)^{d/s} )^{s/d} .
```

Both the hypothesis `hdom` and the conclusion are ONE almost-sure statement whose depth and
cube quantifiers sit inside the event, so this theorem takes no countable intersection at all:
the common-event structure of the per-cube input survives the aggregation.  (Section 8, whose
producer emits one a.e. statement per `(j, R)`, does take it, harmlessly, to build `hdom`.) -/
theorem exists_envelope_gridScaleSeries_of_perCube {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (m : ℤ) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hd : d ≠ 0)
    {leg Y Z : ℕ → TriadicCube d → Omega → ℝ} {A1 A2 : ℝ}
    (hA1 : 0 < A1) (hA2 : 0 < A2)
    (hYm : ∀ (j : ℕ), ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      Measurable (Y j R))
    (hZm : ∀ (j : ℕ), ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      Measurable (Z j R))
    (hYt : ∀ (j : ℕ), ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      IsBigOWith mu (gammaSigma 1) (Y j R) A1)
    (hZt : ∀ (j : ℕ), ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      IsBigOWith mu (gammaSigma (1 / 4)) (Z j R) A2)
    (hleg0 : ∀ (j : ℕ) (R : TriadicCube d) (omega : Omega), 0 ≤ leg j R omega)
    (hdom : ∀ᵐ omega ∂mu, ∀ j : ℕ,
      ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
        leg j R omega ≤ Y j R omega + Z j R omega) :
    ∃ U V : Omega → ℝ, Measurable U ∧ Measurable V ∧
      IsBigOWith mu (gammaSigma 1) U (homLaneOrdinaryConst d * (s⁻¹) ^ 2 * A1) ∧
      IsBigOWith mu (gammaSigma (1 / 4)) V (homLaneRareConst d * (s⁻¹) ^ 5 * A2) ∧
      ∀ᵐ omega ∂mu,
        gridScaleSeries m s (fun j R => leg j R omega) ≤ U omega + V omega := by
  classical
  have hne := grid_nonempty d m
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
  -- the ordinary lane
  have hordSum : Summable (fun j : ℕ => Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      (3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3))) * A1) :=
    (summable_ordinaryWeight hs hs1 hd).mul_right A1
  have hordPos : ∀ j : ℕ, (0 : ℝ) < Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      (3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3))) * A1 := by
    intro j
    have hw : (0 : ℝ) < Real.rpow (3 : ℝ) (-s * (j : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hm := le_max_left (1 : ℝ) ((j : ℝ) * ((d : ℝ) * Real.log 3))
    have : (0 : ℝ) < 3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3)) := by linarith
    exact mul_pos (mul_pos hw this) hA1
  have hordB : (∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      (3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3))) * A1) ≤
        45 * (d : ℝ) * (s⁻¹) ^ 2 * A1 := by
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right (tsum_ordinaryWeight_le hs hs1 hd) hA1.le
  have hordBound : ∀ j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      ((3 * max 1 (Real.log
        (((descendantsAtScale (originCube d m) (m - (j : ℤ))).card : ℕ) : ℝ))) ^ (1 : ℝ)⁻¹ *
        A1) ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          (3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3))) * A1 := by
    intro j
    rw [log_grid_card d m j, inv_one, Real.rpow_one]
    exact le_of_eq (by ring)
  obtain ⟨g1, hg10, hg1le, hg1meas, hg1tail, hg1sum⟩ :=
    exists_laneEnvelope (mu := mu) m (s := s) (sigma := 1) one_pos hne hA1 hYm hYt _
      hordPos hordSum hordB hordBound
  -- the rare lane
  have hrareSum : Summable (fun j : ℕ => Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      (3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3))) ^ 4 * A2) :=
    (summable_rareWeight hs hs1 hd).mul_right A2
  have hrarePos : ∀ j : ℕ, (0 : ℝ) < Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      (3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3))) ^ 4 * A2 := by
    intro j
    have hw : (0 : ℝ) < Real.rpow (3 : ℝ) (-s * (j : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hm := le_max_left (1 : ℝ) ((j : ℝ) * ((d : ℝ) * Real.log 3))
    have hb : (0 : ℝ) < 3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3)) := by linarith
    have : (0 : ℝ) < (3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3))) ^ 4 := by positivity
    exact mul_pos (mul_pos hw this) hA2
  have hrareB : (∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      (3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3))) ^ 4 * A2) ≤
        12000000 * (d : ℝ) ^ 4 * (s⁻¹) ^ 5 * A2 := by
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right (tsum_rareWeight_le hs hs1 hd) hA2.le
  have hrareBound : ∀ j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      ((3 * max 1 (Real.log
        (((descendantsAtScale (originCube d m) (m - (j : ℤ))).card : ℕ) : ℝ))) ^ (1 / 4 : ℝ)⁻¹ *
        A2) ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          (3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3))) ^ 4 * A2 := by
    intro j
    have hbase : (0 : ℝ) ≤ 3 * max 1 ((j : ℝ) * ((d : ℝ) * Real.log 3)) := by
      have := le_max_left (1 : ℝ) ((j : ℝ) * ((d : ℝ) * Real.log 3))
      linarith
    have hexp : ((1 / 4 : ℝ))⁻¹ = ((4 : ℕ) : ℝ) := by norm_num
    rw [log_grid_card d m j, hexp, Real.rpow_natCast]
    exact le_of_eq (by ring)
  obtain ⟨g2, hg20, hg2le, hg2meas, hg2tail, hg2sum⟩ :=
    exists_laneEnvelope (mu := mu) m (s := s) (sigma := 1 / 4) (by norm_num) hne hA2 hZm hZt _
      hrarePos hrareSum hrareB hrareBound
  refine ⟨fun omega => ∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) * g1 j omega,
    fun omega => ∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) * g2 j omega,
    hg1meas, hg2meas, ?_, ?_, ?_⟩
  · refine hg1tail.mono_scale (le_of_eq ?_)
    rw [homLaneOrdinaryConst]
    ring
  · refine hg2tail.mono_scale (le_of_eq ?_)
    rw [homLaneRareConst]
    ring
  · filter_upwards [hdom, hg1sum, hg2sum] with omega hdomega hsum1 hsum2
    have hweight : ∀ j : ℕ, (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) := fun j =>
      Real.rpow_nonneg (by norm_num) _
    have hterm : ∀ j : ℕ,
        Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            legScaleAverage (originCube d m) (m - (j : ℤ)) s (fun R => leg j R omega) ≤
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) * g1 j omega +
            Real.rpow (3 : ℝ) (-s * (j : ℝ)) * g2 j omega := by
      intro j
      have hD : (0 : ℝ) ≤ g1 j omega + g2 j omega := by
        have := hg10 j omega
        have := hg20 j omega
        linarith
      have hle : ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
          leg j R omega ≤ g1 j omega + g2 j omega := by
        intro R hR
        exact le_trans (hdomega j R hR)
          (add_le_add (hg1le j omega R hR) (hg2le j omega R hR))
      have hscale := legScaleAverage_le_const (originCube d m) (m - (j : ℤ)) hs hD
        (fun R _ => hleg0 j R omega) hle hd
      have := mul_le_mul_of_nonneg_left hscale (hweight j)
      linarith
    have hsumRHS : Summable (fun j : ℕ =>
        Real.rpow (3 : ℝ) (-s * (j : ℝ)) * g1 j omega +
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) * g2 j omega) := hsum1.add hsum2
    have hnn : ∀ j : ℕ, (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        legScaleAverage (originCube d m) (m - (j : ℤ)) s (fun R => leg j R omega) := by
      intro j
      exact mul_nonneg (hweight j)
        (legScaleAverage_nonneg _ _ _ fun R _ => hleg0 j R omega)
    have hsumLHS : Summable (fun j : ℕ =>
        Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          legScaleAverage (originCube d m) (m - (j : ℤ)) s (fun R => leg j R omega)) :=
      Summable.of_nonneg_of_le hnn hterm hsumRHS
    calc gridScaleSeries m s (fun j R => leg j R omega)
        = ∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            legScaleAverage (originCube d m) (m - (j : ℤ)) s (fun R => leg j R omega) := rfl
      _ ≤ ∑' j : ℕ, (Real.rpow (3 : ℝ) (-s * (j : ℝ)) * g1 j omega +
            Real.rpow (3 : ℝ) (-s * (j : ℝ)) * g2 j omega) :=
          hsumLHS.tsum_le_tsum hterm hsumRHS
      _ = (∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) * g1 j omega) +
            ∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) * g2 j omega := hsum1.tsum_add hsum2

/-! ## 8. The lane aggregation at the development's carriers -/

/-- **`e.what.homogenization.gives`, aggregated.**  With `h` any integer cutoff
meeting the corridor budget `h ≥ 2 Chom |log ε|`, the printed grid series of
the per-`(l, z)` responses at the deep coefficient family `a_{l-h}` and the
deep gauge `σ_{l-h}` admits one measurable envelope pair with the
homogenization step's own two lanes.  `leg` is the caller's carrier for the
printed `max_{|e|=1}`: the hypothesis `hlegub` says only that it is an U BOUND
of the unit-direction responses in the least-upper-bound sense, which every
`max`/`sSup` carrier satisfies. -/
theorem exists_envelope_gridScaleSeries_homogenizationInput
    (M : ABKModel d) {m : ℤ} (E : {E : ℝ // 1 ≤ E})
    (hE : 15 * (Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hgammaE : M.gamma ≤ ((E : ℝ)⁻¹) ^ 10)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {epsilon : ℝ} (hepsilon : epsilon ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hgate : M.gamma ≤ (homogenizationStepConst d)⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon ^ 2)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (h : ℕ) (hcorr : 2 * homogenizationStepConst d * |Real.log epsilon| ≤ (h : ℝ))
    {leg : ℕ → TriadicCube d → CutoffSample d → ℝ}
    (hleg0 : ∀ (j : ℕ) (R : TriadicCube d) (omega : CutoffSample d), 0 ≤ leg j R omega)
    (hlegub : ∀ (j : ℕ), ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      ∀ (omega : CutoffSample d) (c : ℝ),
        (∀ e : Vec d, Book.Ch02.vecNorm e = 1 →
          Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
              ((coefficientCutoffTriadicCoeffFamily M (m - (j : ℤ) - (h : ℤ)) omega).coeffOn R)
              (Observable.inverseSqrtLoad
                (Annealed.sigmaBar M (m - (j : ℤ) - (h : ℤ))) e)
              (Observable.sqrtLoad (Annealed.sigmaBar M (m - (j : ℤ) - (h : ℤ))) e) ≤ c) →
          leg j R omega ≤ c) :
    ∃ U V : CutoffSample d → ℝ, Measurable U ∧ Measurable V ∧
      IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma 1) U
        (homLaneOrdinaryConst d * (s⁻¹) ^ 2 * (epsilon ^ 2 * (E : ℝ) ^ 2 * M.gamma)) ∧
      IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma (1 / 4)) V
        (homLaneRareConst d * (s⁻¹) ^ 5 *
          (epsilon ^ 2 * Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)))) ∧
      ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
        gridScaleSeries m s (fun j R => leg j R omega) ≤ U omega + V omega := by
  classical
  have hd : d ≠ 0 := (Provider.Orlicz.dim_pos_of_model M).ne'
  have heps0 : 0 < epsilon := hepsilon.1
  have hgamma0 : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hEpos : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le zero_lt_one E.2
  have hA1 : (0 : ℝ) < epsilon ^ 2 * (E : ℝ) ^ 2 * M.gamma := by positivity
  have hA2 : (0 : ℝ) < epsilon ^ 2 * Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) := by
    positivity
  have hper : ∀ (j : ℕ), ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
      ∃ Y Z : CutoffSample d → ℝ,
        Measurable Y ∧ Measurable Z ∧
        IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma 1) Y
            (epsilon ^ 2 * (E : ℝ) ^ 2 * M.gamma) ∧
          IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma (1 / 4)) Z
              (epsilon ^ 2 * Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) ∧
            ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
              ∀ L : ℤ,
                (L : ℝ) ≤ ((m - (j : ℤ) : ℤ) : ℝ) -
                    2 * homogenizationStepConst d * |Real.log epsilon| →
                  ∀ e : Vec d, Book.Ch02.vecNorm e = 1 →
                    Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
                        ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn R)
                        (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
                        (Observable.sqrtLoad (Annealed.sigmaBar M L) e) ≤
                      Y omega + Z omega := by
    intro j R hR
    exact exists_envelope_responseJ_descendant_of_inductionState M
      (show m - (j : ℤ) ≤ m by omega) hR E hE hgammaE hS epsilon hepsilon hgate
  choose! Y Z hYm hZm hYt hZt hdomYZ using hper
  refine exists_envelope_gridScaleSeries_of_perCube (mu := (cutoffSampleLaw M).toMeasure)
    m hs hs1 hd (leg := leg) (Y := Y) (Z := Z) hA1 hA2 hYm hZm hYt hZt hleg0 ?_
  have hall : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure, ∀ j : ℕ,
      ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
        leg j R omega ≤ Y j R omega + Z j R omega := by
    rw [MeasureTheory.ae_all_iff]
    intro j
    rw [Filter.eventually_all_finset]
    intro R hR
    filter_upwards [hdomYZ j R hR] with omega homega
    have hL : ((m - (j : ℤ) - (h : ℤ) : ℤ) : ℝ) ≤ ((m - (j : ℤ) : ℤ) : ℝ) -
        2 * homogenizationStepConst d * |Real.log epsilon| := by
      push_cast
      linarith
    exact hlegub j R hR omega (Y j R omega + Z j R omega)
      (fun e he => homega (m - (j : ℤ) - (h : ℤ)) hL e he)
  exact hall

/-! ## 9. The two normalizations, the printed one and the localization one -/

/-- **The normalization seam, by consumption.**  `e.what.homogenization.gives` is
normalized by `s` and `e.localization.mathcalE.estimate`'s first term by `6
c_{2s}`; the two are compared by `c_{2s} = 1 - 3^{-2s} ≤ 4 s`, the proved
`Provider.Localization.geometricDiscount_two_le_four_mul`
(`AggregationRemainder.lean`).  The statement is at the localization side's
own carrier `Book.Ch02.geometricDiscount`; section 1's `geometricDiscount` is
the second name (`Homogenization.geometricDiscount`) of the same function `1 -
3^{-s q}`.

A first delivery re-proved the sharper `c_{2s} ≤ 2 log 3 s` from
`Real.add_one_le_exp` under a public named `geometricDiscount_two_le`.  The
sharpness is not load-bearing (the seam's cost is absolute either way) and the
name is already taken by `Provider.CoarseEllipticity.geometricDiscount_two_le`
(`ProfileClose.lean`, same `4 s`), so that public was D. -/
theorem geometricDiscount_two_mul_le_of_nonneg {s G : ℝ} (hs : 0 ≤ s) (hG : 0 ≤ G) :
    Book.Ch02.geometricDiscount s 2 * G ≤ 4 * (s * G) := by
  have h := geometricDiscount_two_le_four_mul hs
  nlinarith

/-! ## 10. The printed normalization and the pointwise endpoint -/

/-- **From an almost-everywhere domination to a pointwise one.**  A measurable
observable dominated almost everywhere by an envelope pair is a two-term
weak-Orlicz datum with named witnesses,
and the returned witnesses are almost everywhere equal to the given envelopes —
so every further tail of those envelopes transfers to the returned pair.  The
device is the web's unconditional `exists_witnesses_ae_eq_of_ae_le`, consumed,
not re-derived. -/
theorem exists_witnesses_of_envelope {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {X U V : Omega → ℝ} {A1 A2 : ℝ}
    (hA1 : 0 < A1) (hA2 : 0 < A2)
    (hXm : Measurable X) (hUm : Measurable U) (hVm : Measurable V)
    (hUt : IsBigOWith mu (gammaSigma 1) U A1)
    (hVt : IsBigOWith mu (gammaSigma (1 / 4)) V A2)
    (hle : ∀ᵐ omega ∂mu, X omega ≤ U omega + V omega) :
    ∃ U' V' : Omega → ℝ,
      Probability.IsTwoTermBigOWithWitnesses mu (gammaSigma 1) (gammaSigma (1 / 4))
          X U' V' A1 A2 ∧
        U' =ᵐ[mu] U ∧ V' =ᵐ[mu] V :=
  exists_witnesses_ae_eq_of_ae_le (Probability.isAdmissibleTail_gammaSigma one_pos)
    (Probability.isAdmissibleTail_gammaSigma (by norm_num)) hA1 hA2 hXm hUm hVm hle hUt hVt

end

end Algsuperdiff.Section3.Provider.MultiscaleEstimate
