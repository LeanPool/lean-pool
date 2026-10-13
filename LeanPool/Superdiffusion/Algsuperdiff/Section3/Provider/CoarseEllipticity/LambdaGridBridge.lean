/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.ScaleSummation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffMultiscaleEllipticity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Tail.TailSqrt

/-!
# LambdaGridBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The on-grid `lambdaSq` bridge: `Lambda_{s,q}` as a weighted grid series

`Provider/CoarseEllipticity/ScaleSummation.lean` and
`Provider/CoarseEllipticity/LowerLeg.lean` each retain the *same* conditional
analytic input, an explicit binder called `hgrid`: the domination of the
coarse-grained ellipticity constant by a weighted series of the per-scale
triadic grid maxima.  This module supplies the deterministic content of that
binder and pins, with machine-checked negative controls, exactly which part of
it can and cannot be transported to this repository's Section 3 observables.

## The two seams, and what happens to each

**(i) The index/pole seam.**  ABK26 defines

```
Lambda_{s,q}(cu_m;a) = ( c_{sq} sum_{k<=m} 3^{-sq(m-k)}
                             max_{z in 3^k Zd cap cu_m} |b(z+cu_k;a)|^{q/2} )^{2/q}
```

and CoarseGraining's `Ch02.LambdaSqFinite` is *literally* this, with `c_{sq} =
Ch02.geometricDiscount s q = 1 - 3^{-sq}` and gap index `n = m - k`.
CoarseGraining's own bridge to a *linear* grid series exists only at `q = 1`
and delivers the pole `s`, whereas the consumers need the summation performed
at the `q/2`-power level, **before** the outer `2/q` root.  That is what
`tsum_weighted_rpow_root_le` does, by countable subadditivity of the concave
power `x |-> x^{2/q}` at `q >= 2`; the resulting weight arithmetic is
`geometricWeight_rpow_succ`:

```
(c_{sq} 3^{-sq(k+1)})^{2/q} = gridSumConst s q * gridWeight (2 s) k
```

so the pole is `2s` **for every** `q >= 2`, not `sq`, and the collar absorption
`gridWeight_mul_rpow` of `GridWeights.lean` then moves it to the printed `(2s -
gamma)` (`geometricWeight_rpow_succ_collar`).  This settles the
weight-convention question flagged, and the "`s`-times-`gridWeight (2s-gamma)`"
reading of the printed deterministic pole is *recovered, not assumed*, through
`gridSumConst_two_le` (`gridSumConst s 2 = 1 - 3^{-2s} <= 4 s`).  At the ruled
exponent `q = 2` the two exponents `q/2` and `2/q` are both `1`, the
subadditivity step is vacuous, and the bridge is an **equality**
(`LambdaSqFinite_two_eq_top_add_gridSum`) needing no summability binder at all.

**The gap-`0` term is carried explicitly.**  `gridWeight` covers gaps `>= 1`
only (`GridWeights.lean`); the source series has a gap-`0` summand, the
one-cube quantity `|b(cu_m;a)|` at the top scale.  Every statement below
displays it as a separate summand `gridSumConst s q * (top-scale maximum)`;
nothing is silently dropped.

`A.mk` is `Classical.choose` of an existential and carries **no** pointwise
information about the literal observable, so the bridge proved here held
pathwise for the *literal* observables
(`cutoffUpperEllipticityLiteral_two_eq_top_add_gridSum` and its lower twin;
names corrected; the current conditional/A inventory describes the headline
families) and only almost everywhere for the representatives
(`cutoffUpperEllipticity_ae_le_top_add_gridSum`).  The route suggested by the
genuine centered-cube `rfl` between the two exported observables did **not**
extend: that equality identified two *representatives*, not a representative
with a literal, and two negative controls confirmed it (`cutoffUpperEllipticity
= cutoffUpperEllipticityLiteral` was not a definitional equality; neither was
`cubeUpperEllipticity M Q L ... = cutoffUpperEllipticity M m L ...` at an
arbitrary cube `Q`).

*How it was removed.*  Exactly that change was made.  On the source range `0 <
s` the clamp is inert (`Observable.cutoffLowerEllipticityInv_eq_literal`,
`Observable.cutoffUpperEllipticity_eq_literal`), so **every pathwise statement
of this module descends to the exported observables at every sample point.**
Both negative controls above are now vacuous: the first equality holds (not by
`rfl`, but by `max_eq_right` at `0 < s`), and the second holds whenever `Q =
originCube d m`.

The a.e. shadows below remain true, remain the statements the current consumers
are written against, and are now provable in one line from the pointwise forms.

*The leg-by-leg consequence, restated.*

* **Upper leg.**  Its payload's three witnesses are existential and its index
  set is a single scale, so even under the old bodies the null set could be
  absorbed *inside the witness*: `exists_pointwise_of_ae_threeTermSplit` takes
  the three-term bound only almost everywhere and returns a domination valid at
  **every** sample point, with everywhere-defined measurable witnesses.  No
  a.e. witness is produced or consumed anywhere; `IsBigOWith` is unchanged
  because it only sees the a.e. class (`Provider.Tail.isBigOWith_of_ae_eq`).
  That absorption is now optional rather than necessary.
* **Lower leg.**  Its payload needs *one* witness `Y` dominating the whole
  family `{X L}_{L >= m-1}` at every sample point.  Under the old bodies this
  was unreachable: on the null set the values `X L omega = max 0 (mk_L omega)`
  were uncontrolled for countably many `L` at once and `sup_L X L omega` was
  not known to be finite there, which is the obstruction recorded in
  `LowerLeg.lean` (point 1 of its module docstring) and in
  `Provider/Tail/TailSqrt.lean` (F-1).  **That obstruction is gone**: the
  deterministic content of the lower leg's `hgrid` conjunct is now available
  with the quantifier order `∀ omega, ∀ L`.  The analytic content of `hgrid`
  remains an input of the historical consumers (`ScaleSummation.lean`,
  `LowerLeg.lean`).  The concrete downstream theorem
  `superposedFlux_coarse_ellipticity_lower_leg` supplies the lower leg through
  a different finite-`q` pre-split route, so this conditional seam is no longer
  the global lower-leg status.  The separate downstream theorem
  `superposedFlux_coarse_ellipticity_upper_leg` supplies the upper leg.

## Main results

* `tsum_rpow_le_tsum_rpow`, `tsum_weighted_rpow_root_le` --- seam (i): the
  weighted `ell^{q/2}` aggregate that defines `Lambda_{s,q}` is dominated by
  the linear series with the reweighted coefficients `w^{2/q}`, for `q >= 2`.
* `gridSumConst`, `geometricWeight_rpow_zero`, `geometricWeight_rpow_succ` ---
  the weight arithmetic of the `2/q` root: the gap-`0` weight becomes the bare
  constant, and the gap-`(k+1)` weight becomes
  `gridSumConst s q * gridWeight (2 * s) k`, so the pole is `2s` uniformly in
  `q`.
* `lambdaSqFinite_inv_eq_rpow` --- `lambda_{s,q}^{-1}` unfolded as the positive
  `2/q` root of the source's weighted series, at every coefficient family and
  with no positivity side condition.
* `cutoffUpperEllipticityLiteral_eq_coeffField`,
  `cutoffLowerEllipticityInvLiteral_eq_coeffField` --- **the bridge at the
  Section 3 literal observables**: at the centered cube they are the Chapter 4
  ambient coefficient-field observables at the cutoff field.
* `exists_pointwise_of_ae_threeTermSplit` --- the pointwise-valid upgrade: an
  almost-everywhere three-term domination with a deterministic first slot
  becomes a domination valid at every sample point, with everywhere-defined
  measurable witnesses.

## References

* ABK26, coarse-grained ellipticity constants, (the definition and the
  normalizer `c_{sq}`).
* ABK26, `p.cg.ellipticity.bounds` from `p.bfA.multiscalebound`.
* `Provider/CoarseEllipticity/GridWeights.lean` (`gridWeight`, `gridSupAbs`,
  `maxDescendantBMatrixNormAtScale_eq_gridSupAbs`),
  `.../ScaleSummation.lean` and `.../LowerLeg.lean` (the two `hgrid` consumers),
  `Provider/BadEvents/CubeEllipticity.lean` (the centered-cube literal
  identities),
  `Provider/BadEvents/ObservableSwapPayoff.lean` (the pointwise upgrades of the
  a.e. shadows below, and the off-centre transport).
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## 1. The `q/2`-power level summation -/

/-- **Countable subadditivity of the concave power.**  For `0 < theta <= 1` and a
nonnegative summable `b` whose `theta`-powers are also summable,
`(sum b)^theta <= sum b^theta`.

This is the step the printed proof performs silently when it sums the per-scale
displays *inside* the `q/2`-power and only then takes the `2/q` root. -/
theorem tsum_rpow_le_tsum_rpow {b : ℕ → ℝ} {theta : ℝ} (htheta0 : 0 < theta)
    (htheta1 : theta ≤ 1) (hb : ∀ n, 0 ≤ b n) (hsum : Summable b)
    (hsumtheta : Summable fun n => b n ^ theta) :
    (∑' n, b n) ^ theta ≤ ∑' n, b n ^ theta := by
  set S : ℝ := ∑' n, b n with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg hb
  rcases eq_or_lt_of_le hS0 with hSz | hSpos
  · rw [← hSz, Real.zero_rpow (ne_of_gt htheta0)]
    exact tsum_nonneg fun n => Real.rpow_nonneg (hb n) _
  · have hterm : ∀ n, b n * S ^ (theta - 1) ≤ b n ^ theta := by
      intro n
      rcases eq_or_lt_of_le (hb n) with hz | hpos
      · rw [← hz, Real.zero_rpow (ne_of_gt htheta0)]
        simp
      · have hbS : b n ≤ S := hsum.le_tsum n fun m _ => hb m
        have hmono : S ^ (theta - 1) ≤ b n ^ (theta - 1) :=
          Real.rpow_le_rpow_of_nonpos hpos hbS (by linarith)
        have hsplit : b n ^ theta = b n * b n ^ (theta - 1) := by
          have hadd := Real.rpow_add hpos 1 (theta - 1)
          rw [Real.rpow_one, show (1 : ℝ) + (theta - 1) = theta by ring] at hadd
          exact hadd
        rw [hsplit]
        exact mul_le_mul_of_nonneg_left hmono hpos.le
    have hle := Summable.tsum_le_tsum hterm (hsum.mul_right (S ^ (theta - 1))) hsumtheta
    have hval : (∑' n, b n * S ^ (theta - 1)) = S ^ theta := by
      have hadd := Real.rpow_add hSpos 1 (theta - 1)
      rw [Real.rpow_one, show (1 : ℝ) + (theta - 1) = theta by ring] at hadd
      rw [tsum_mul_right, ← hSdef, hadd]
    rwa [hval] at hle

/-- **The `q/2`-power level summation** (seam (i)).  The weighted `ell^{q/2}`
aggregate that *defines* `Lambda_{s,q}` is dominated by the linear series with
the reweighted coefficients `w^{2/q}`, for every `q >= 2`. -/
theorem tsum_weighted_rpow_root_le {q : ℝ} {w f : ℕ → ℝ} (hq : 2 ≤ q)
    (hw : ∀ n, 0 ≤ w n) (hf : ∀ n, 0 ≤ f n)
    (hsum : Summable fun n => w n * f n ^ (q / 2))
    (hsumlin : Summable fun n => w n ^ (2 / q) * f n) :
    (∑' n, w n * f n ^ (q / 2)) ^ (2 / q) ≤ ∑' n, w n ^ (2 / q) * f n := by
  have hq0 : (0 : ℝ) < q := by linarith
  have htheta0 : (0 : ℝ) < 2 / q := by positivity
  have htheta1 : 2 / q ≤ 1 := by
    rw [div_le_one hq0]; linarith
  have hpow : ∀ n, (w n * f n ^ (q / 2)) ^ (2 / q) = w n ^ (2 / q) * f n := by
    intro n
    have hexp : q / 2 * (2 / q) = 1 := by field_simp
    rw [Real.mul_rpow (hw n) (Real.rpow_nonneg (hf n) _), ← Real.rpow_mul (hf n),
      hexp, Real.rpow_one]
  have hbnn : ∀ n, 0 ≤ w n * f n ^ (q / 2) := fun n =>
    mul_nonneg (hw n) (Real.rpow_nonneg (hf n) _)
  have hsumtheta : Summable fun n => (w n * f n ^ (q / 2)) ^ (2 / q) :=
    hsumlin.congr fun n => (hpow n).symm
  calc (∑' n, w n * f n ^ (q / 2)) ^ (2 / q)
      ≤ ∑' n, (w n * f n ^ (q / 2)) ^ (2 / q) :=
        tsum_rpow_le_tsum_rpow htheta0 htheta1 hbnn hsum hsumtheta
    _ = ∑' n, w n ^ (2 / q) * f n := tsum_congr hpow

/-! ## 2. The weight arithmetic of the `2/q` root -/

/-- The `k`-independent constant produced by the `2/q` root of the source's
normalizer: `c_{sq}^{2/q} = (1 - 3^{-sq})^{2/q}`. -/
noncomputable def gridSumConst (s q : ℝ) : ℝ :=
  Book.Ch02.geometricDiscount s q ^ (2 / q)

theorem geometricDiscount_nonneg' {s q : ℝ} (hsq : 0 ≤ s * q) :
    0 ≤ Book.Ch02.geometricDiscount s q :=
  Book.Ch02.book_geometricDiscount_nonneg hsq

theorem gridSumConst_nonneg {s q : ℝ} (hsq : 0 ≤ s * q) : 0 ≤ gridSumConst s q :=
  Real.rpow_nonneg (geometricDiscount_nonneg' hsq) _


theorem geometricWeight_nonneg' {s q : ℝ} (hsq : 0 ≤ s * q) (n : ℕ) :
    0 ≤ Book.Ch02.geometricWeight s q n :=
  mul_nonneg (Book.Ch02.book_geometricDiscount_nonneg hsq)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)

/-- The gap-`0` weight, after the `2/q` root, is the bare constant. -/
theorem geometricWeight_rpow_zero (s q : ℝ) :
    Book.Ch02.geometricWeight s q 0 ^ (2 / q) = gridSumConst s q := by
  rw [Book.Ch02.geometricWeight, gridSumConst]
  norm_num

/-- **The index/pole identity of seam (i).**  After the `2/q` root the source's
gap-`(k+1)` weight is the grid weight at pole `2s`, *uniformly in `q`*.  This is
why the printed poles are `(2s - gamma)`-type and not `(sq - gamma)`-type. -/
theorem geometricWeight_rpow_succ {s q : ℝ} (hsq : 0 ≤ s * q) (hq : q ≠ 0) (k : ℕ) :
    Book.Ch02.geometricWeight s q (k + 1) ^ (2 / q)
      = gridSumConst s q * gridWeight (2 * s) k := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hrw : ∀ y : ℝ, Real.rpow (3 : ℝ) y = (3 : ℝ) ^ y := fun _ => rfl
  have hexp : -s * q * ((k : ℝ) + 1) * (2 / q) = -(2 * s) * ((k : ℝ) + 1) := by
    field_simp
  have hgw : gridWeight (2 * s) k = (3 : ℝ) ^ (-(2 * s) * ((k : ℝ) + 1)) := by
    rw [gridWeight, ← Real.rpow_natCast ((3 : ℝ) ^ (-(2 * s))) (k + 1),
      ← Real.rpow_mul h3.le]
    push_cast
    ring_nf
  rw [Book.Ch02.geometricWeight, gridSumConst, hgw]
  simp only [hrw]
  rw [Real.mul_rpow (geometricDiscount_nonneg' hsq) (Real.rpow_nonneg h3.le _),
    ← Real.rpow_mul h3.le]
  push_cast
  rw [hexp]


/-! ## 3. The pathwise bridge at CoarseGraining's deterministic carriers -/


theorem maxSigmaStarInv_sub_nonneg (Q : TriadicCube d) (n : ℕ)
    (a : Book.Ch02.TriadicCoeffFamily d) :
    0 ≤ Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a :=
  Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q (by omega) a

/-- `lambda_{s,q}^{-1}` unfolded: the negative root of the source's series is
inverted to the positive root, at every coefficient family and with no
positivity side condition. -/
theorem lambdaSqFinite_inv_eq_rpow [NeZero d] (Q : TriadicCube d) {s q : ℝ}
    (hsq : 0 ≤ s * q) (a : Book.Ch02.TriadicCoeffFamily d) :
    (Book.Ch02.lambdaSqFinite Q s q a)⁻¹
      = (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
          Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a
            ^ (q / 2)) ^ (2 / q) := by
  have hS : (0 : ℝ) ≤ ∑' n : ℕ, Book.Ch02.geometricWeight s q n *
      Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a
        ^ (q / 2) :=
    tsum_nonneg fun n => mul_nonneg (geometricWeight_nonneg' hsq n)
      (Real.rpow_nonneg (maxSigmaStarInv_sub_nonneg Q n a) _)
  have hdef : Book.Ch02.lambdaSqFinite Q s q a
      = (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
          Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a
            ^ (q / 2)) ^ (-(2 / q)) := rfl
  rw [hdef, Real.rpow_neg hS, inv_inv]


/-! ## 7. The bridge at the Section 3 observables -/

/-- The Section 3 **literal** upper observable *is* the Chapter 4 ambient
observable at the cutoff field.  `NeZero d` is a `Prop` class, so the instance
carried inside the observable's definition and the one supplied here are
definitionally equal. -/
theorem cutoffUpperEllipticityLiteral_eq_coeffField (M : ABKModel d)
    (m L : ℤ) (s : ℝ) (q : CoarseEllipticityExponent)
    (omega : Cutoff.CutoffSample d) :
    Observable.cutoffUpperEllipticityLiteral M m L s q omega
      = Book.Ch04.LambdaSqCoeffField (originCube d m) s q.1
          (Cutoff.coefficientCutoff M.nu L omega) :=
  rfl

/-- The Section 3 **literal** lower observable is the inverse of the Chapter 4
ambient observable at the cutoff field. -/
theorem cutoffLowerEllipticityInvLiteral_eq_coeffField (M : ABKModel d)
    (m L : ℤ) (s : ℝ) (q : CoarseEllipticityExponent)
    (omega : Cutoff.CutoffSample d) :
    Observable.cutoffLowerEllipticityInvLiteral M m L s q omega
      = (Book.Ch04.lambdaSqCoeffField (originCube d m) s q.1
          (Cutoff.coefficientCutoff M.nu L omega))⁻¹ :=
  rfl


/-! ## 8. The pointwise-valid upgrade, and the upper leg's summation -/

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- **The pointwise-valid null-set upgrade.**  An almost-everywhere three-term
domination with a *deterministic* first slot upgrades to a domination valid at
**every** sample point, by moving the defect into the ordinary lane on a
measurable null set.

Nothing produced here is an almost-everywhere witness: `U1'` is an
everywhere-defined measurable function, the domination is `forall omega`, and
the `Gamma` tail is unchanged because `IsBigOWith` only sees the
almost-everywhere class (`Provider.Tail.isBigOWith_of_ae_eq`).  This upgrade is
available to the **upper** leg only; the lower leg's single witness must
majorize a whole `L`-indexed family at once, and on the null set that supremum
is not known to be finite (see the module docstring). -/
theorem exists_pointwise_of_ae_threeTermSplit
    {X U1 Uexp : Omega → ℝ} {b A1 A2 sigma1 sigma2 : ℝ}
    (hXmeas : Measurable X) (hU1meas : Measurable U1) (hUexpmeas : Measurable Uexp)
    (h1 : IsBigOWith mu (gammaSigma sigma1) U1 A1)
    (hexp : IsBigOWith mu (gammaSigma sigma2) Uexp A2)
    (hae : ∀ᵐ omega ∂mu, X omega ≤ b + U1 omega + Uexp omega) :
    ∃ Udet U1' Uexp' : Omega → ℝ,
      (∀ omega, X omega ≤ Udet omega + U1' omega + Uexp' omega) ∧
      (∀ omega, Udet omega ≤ b) ∧
      Measurable U1' ∧ Measurable Uexp' ∧
      IsBigOWith mu (gammaSigma sigma1) U1' A1 ∧
      IsBigOWith mu (gammaSigma sigma2) Uexp' A2 := by
  classical
  obtain ⟨N, hsubN, hNmeas, hN0⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hae)
  set g : Omega → ℝ := fun omega => max 0 (X omega - b - U1 omega - Uexp omega) with hg
  have hgmeas : Measurable g :=
    measurable_const.max (((hXmeas.sub measurable_const).sub hU1meas).sub hUexpmeas)
  refine ⟨fun _ => b, fun omega => U1 omega + N.indicator g omega, Uexp, ?_, fun _ => le_rfl,
    hU1meas.add (hgmeas.indicator hNmeas), hUexpmeas, ?_, hexp⟩
  · intro omega
    change X omega ≤ b + (U1 omega + N.indicator g omega) + Uexp omega
    by_cases hmem : omega ∈ N
    · have hind : N.indicator g omega = g omega := Set.indicator_of_mem hmem g
      have hge : X omega - b - U1 omega - Uexp omega ≤ g omega := le_max_right _ _
      rw [hind]
      linarith
    · have hgood : X omega ≤ b + U1 omega + Uexp omega := by
        by_contra hcon
        exact hmem (hsubN hcon)
      have hind : N.indicator g omega = 0 := Set.indicator_of_notMem hmem g
      rw [hind]
      linarith
  · refine Provider.Tail.isBigOWith_of_ae_eq ?_ h1
    have hnmem : ∀ᵐ omega ∂mu, omega ∉ N := measure_eq_zero_iff_ae_notMem.mp hN0
    filter_upwards [hnmem] with omega homega
    show U1 omega = U1 omega + N.indicator g omega
    rw [Set.indicator_of_notMem homega g, add_zero]


end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
