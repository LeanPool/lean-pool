/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.BadEventLemmaOscillation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.TranslatedLargeCubeW1Inf

/-!
# OscillationBranchLow

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The oscillation branch of `l.bad.event.lemma` at `n < m`

`BadEventLemmaOscillation.lean` supplies a local result associated with ABK26's
`e.oscillation.bound` on the branch `m <= n`, where the increment base sits at
or above the cube scale.  This module supplies a local result for the *other*
branch, `n < m`, on which

* the increment `k_L - k_n` contains shells `k in (n, m)` strictly below the
  cube scale, and
* the displayed exponent carries the factor `3^{-5 (m-n)_+}`.

The conclusion is the manuscript's own display at `(n-m)_+ = 0`,

```
P[ sensitivity clause of Q(m,n,z) fails ]  <=  exp( - c c_star gamma^{-1} 3^{-5(m-n)} ) .
```

## The two corrections this branch runs under

* The printed wave/shell inclusion is *invalid* on this branch: for `L in [n,
  m)` the partial increment `k_L - k_n` is dominated neither by `k_m - k_n` nor
  by any shell above `m`.  The correction recorded there is to price the shell
  sum `sum_{k = n+1}^{m} ||grad j_k||` instead, which is what `e.W.1.inf.bound`
  bounds.
* On this branch the printed bound is not derivable from the cited inputs at
  the printed admissibility for unrestricted `m`; the correction is the
  *self-consistent* restriction

  ```
  3^{5 (m-n)_+}  <=  c c_star gamma^{-1} ,
  ```

  i.e. the display's own exponent is at least one.  It is carried here by the
  binder `hrestrict : 1 <= badEventOscFullRate M Ccg Q n`, which is literally
  that inequality, and it is the *only* hypothesis of this module beyond the
  manuscript's own data.  Every manuscript use satisfies it.

## The two ingredients

1. **The weight conversion** `shellOscGauge_le_translatedLargeCubeDerivGauge`:
   for `k <= m`,

   ```
   3^{2m} ||grad j_k||_{W^{1,infinity}(z+square_m)}
     <=  3^{2(m-k)} ( 3^k ||grad j_k||_{L^infinity(z+square_m)}
                      + 3^{2k} ||grad^2 j_k||_{L^infinity(z+square_m)} ) ,
   ```

   the intrinsic factor between the `e.BoscL.def` gauge at cube scale `m` and
   the `e.W.1.inf.bound` summand of a shell at scale `k < m`.
2. **The translated `e.W1inf.jL.bound.smaller`**
   `Provider.Stream.isBigOWith_gammaSigma_largeCubeDerivGauge_lt_translate`.

Above the cube scale the proved per-shell tail
`isBigOWith_gammaSigma_shellOscGauge` (`e.nabla.jk.O` at the base point of `Q`)
is used, exactly as on the branch `m <= n`.

## The constant

`c` of the display is chosen as `badEventOscLowConst d Ccg`, the constant of
the branch `m <= n` further divided by `(1 or
C_{(e.W1inf.jL.bound.smaller)})^2`, where the latter is the dimension-only
covering constant `Provider.Stream.shellW1InfSmallerConst d`.  Both factors are
dimension-only, so the manuscript's requirement that `c` depends only on `d` is respected.

## Main definitions

* `badEventOscLowConst`: the constant of `e.oscillation.bound` on this branch.
* `badEventOscFullRate`: the exponent of `e.oscillation.bound` over the *whole*
  range, `c c_star gamma^{-1} 3^{-5(m-n)_+} 3^{(n-m)_+}`.

## Main results

* `shellOscGauge_le_translatedLargeCubeDerivGauge` (the weight conversion).
* `measureReal_shellSensitivityFailure_le_low` (one shell, either regime).
* `measureReal_goodLocalSensitivityFailure_le_low` (the branch `n < m`).

## References

* ABK26, `l.bad.event.lemma`; `e.oscillation.bound`; the wave decomposition.
* ABK26, `e.W.1.inf.bound`; `e.nabla.jk.O`.
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Stream

noncomputable section

variable {d : ℕ}

/-! ## Elementary numerics -/

private theorem three_rpow_posL (x : ℝ) : (0 : ℝ) < (3 : ℝ) ^ x :=
  Real.rpow_pos_of_pos (by norm_num) x

private theorem three_rpow_addL (x y : ℝ) :
    (3 : ℝ) ^ x * (3 : ℝ) ^ y = (3 : ℝ) ^ (x + y) :=
  (Real.rpow_add (by norm_num) x y).symm

private theorem three_rpow_half_sqL (x : ℝ) :
    ((3 : ℝ) ^ ((1 / 2 : ℝ) * x)) ^ 2 = (3 : ℝ) ^ x := by
  rw [← Real.rpow_natCast ((3 : ℝ) ^ ((1 / 2 : ℝ) * x)) 2,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  push_cast
  ring

private theorem one_le_mul_one_leL {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    1 ≤ a * b := by nlinarith

private theorem one_le_of_one_le_sqL {B : ℝ} (hB : 0 < B) (h : 1 ≤ B ^ 2) :
    1 ≤ B := by nlinarith

private theorem sqrt_le_self_of_one_leL {a : ℝ} (h : 1 ≤ a) :
    Real.sqrt a ≤ a := by
  have h0 : (0 : ℝ) ≤ a := le_trans zero_le_one h
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt h0
  nlinarith [Real.sqrt_nonneg a, hsq, sq_nonneg (Real.sqrt a - 1)]

/-- `x <= 3^{x/2}` for `x >= 0`: the elementary bound that lets the covering
factor `(m-k)^{1/2}` of `e.W1inf.jL.bound.smaller` be absorbed by the geometric
decay `3^{-(m-n)/2}` of the shell budget. -/
private theorem self_le_three_rpow_halfL {x : ℝ} (hx : 0 ≤ x) :
    x ≤ (3 : ℝ) ^ (x / 2) := by
  have hlog : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hhalf : x ≤ Real.exp (x / 2) := by
    have h := Real.add_one_le_exp (x / 4)
    have hexp : Real.exp (x / 2) = Real.exp (x / 4) * Real.exp (x / 4) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    nlinarith [h, sq_nonneg (x - 4), hx,
      mul_le_mul h h (by linarith : (0 : ℝ) ≤ x / 4 + 1)
        (le_of_lt (Real.exp_pos (x / 4)))]
  have hmono : Real.exp (x / 2) ≤ (3 : ℝ) ^ (x / 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_le_exp.2 (by nlinarith [hlog, hx])
  linarith

private theorem exp_pow_eqL (x : ℝ) (w : ℕ) :
    Real.exp x ^ w = Real.exp ((w : ℝ) * x) := by
  induction w with
  | zero => simp
  | succ k ih =>
      have hcast : ((k + 1 : ℕ) : ℝ) * x = (k : ℝ) * x + x := by push_cast; ring
      rw [pow_succ, ih, hcast, Real.exp_add]

private theorem two_le_exp_oneL : (2 : ℝ) ≤ Real.exp 1 := by
  linarith [Real.add_one_le_exp (1 : ℝ)]

private theorem three_mul_succ_le_three_powL (w : ℕ) : 3 * (w + 1) ≤ 3 ^ (w + 1) := by
  induction w with
  | zero => norm_num
  | succ k ih =>
      have h3 : (3 : ℕ) ^ (k + 1 + 1) = 3 * 3 ^ (k + 1) := by ring
      omega

/-- The geometric summation `sum_{i >= 1} exp(-3 kappa)^i <= exp(-kappa)` for
`kappa >= 1`. -/
private theorem tsum_exp_pow_leL {kappa : ℝ} (hk : 1 ≤ kappa) :
    ∑' w : ℕ, Real.exp (-(3 * kappa)) ^ (w + 1) ≤ Real.exp (-kappa) := by
  have ha0 : (0 : ℝ) < Real.exp (-kappa) := Real.exp_pos _
  have hahalf : Real.exp (-kappa) ≤ 1 / 2 := by
    have h1 : Real.exp 1 ≤ Real.exp kappa := Real.exp_le_exp.2 hk
    have h2 : (2 : ℝ) ≤ Real.exp kappa := le_trans two_le_exp_oneL h1
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos kappa)]
    linarith
  have hcube : Real.exp (-(3 * kappa)) = Real.exp (-kappa) ^ 3 := by
    rw [exp_pow_eqL]
    congr 1
    push_cast
    ring
  have hq0 : (0 : ℝ) ≤ Real.exp (-(3 * kappa)) := (Real.exp_pos _).le
  have hq1 : Real.exp (-(3 * kappa)) < 1 := by
    have hlt : Real.exp (-(3 * kappa)) < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
    simpa using hlt
  have hsum : ∑' w : ℕ, Real.exp (-(3 * kappa)) ^ (w + 1) =
      (1 - Real.exp (-(3 * kappa)))⁻¹ * Real.exp (-(3 * kappa)) := by
    have hpow : ∀ w : ℕ, Real.exp (-(3 * kappa)) ^ (w + 1) =
        Real.exp (-(3 * kappa)) ^ w * Real.exp (-(3 * kappa)) := fun w => pow_succ _ w
    rw [tsum_congr hpow, tsum_mul_right, tsum_geometric_of_lt_one hq0 hq1]
  have hden : (0 : ℝ) < 1 - Real.exp (-kappa) ^ 3 := by
    rw [hcube] at hq1
    linarith
  have ha2 : Real.exp (-kappa) ^ 2 ≤ 1 / 4 := by nlinarith [ha0, hahalf]
  have ha3 : Real.exp (-kappa) ^ 3 ≤ 1 / 8 := by nlinarith [ha0, hahalf, ha2]
  rw [hsum, hcube, inv_mul_eq_div, div_le_iff₀ hden]
  nlinarith [ha0, ha2, ha3, mul_le_mul_of_nonneg_left ha2 ha0.le,
    mul_le_mul_of_nonneg_left ha3 ha0.le]

/-- The weak-Orlicz tail, read at the threshold-to-amplitude ratio. -/
private theorem measureReal_upperTail_le_expL {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega} {X : Omega → ℝ}
    {A B thr rate : ℝ} (hA : 0 < A) (hB : 0 < B) (hBA : B * A ≤ thr)
    (hBsq : B ^ 2 = rate) (hrate : 1 ≤ rate)
    (htail : HCPolySupport.IndependentSums.IsBigOWith mu
      (HCPolySupport.IndependentSums.gammaSigma 2) X A) :
    mu.real {omega | thr < X omega} ≤ Real.exp (-rate) := by
  have hB1 : 1 ≤ B := one_le_of_one_le_sqL hB (by rw [hBsq]; exact hrate)
  have hBt : B ≤ thr / A := (le_div_iff₀ hA).2 hBA
  have ht1 : (1 : ℝ) ≤ thr / A := le_trans hB1 hBt
  have h := htail ht1
  have hAt : A * (thr / A) = thr := by field_simp
  rw [hAt] at h
  refine le_trans h ?_
  rw [HCPolySupport.IndependentSums.gammaSigma_inv]
  refine Real.exp_le_exp.2 (neg_le_neg ?_)
  have htt : (thr / A) ^ (2 : ℝ) = (thr / A) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (thr / A) 2]
    norm_num
  rw [htt, ← hBsq]
  nlinarith [hBt, hB]

/-- The geometric union bound. -/
private theorem measureReal_le_exp_of_iUnionL {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega) [IsFiniteMeasure mu]
    {S : Set Omega} {T : ℕ → Set Omega} {kappa : ℝ} (hk : 1 ≤ kappa)
    (hsub : S ⊆ ⋃ w : ℕ, T w)
    (hterm : ∀ w : ℕ,
      mu.real (T w) ≤ Real.exp (-(kappa * (3 : ℝ) ^ ((w : ℝ) + 1)))) :
    mu.real S ≤ Real.exp (-kappa) := by
  classical
  have hk0 : (0 : ℝ) < kappa := lt_of_lt_of_le zero_lt_one hk
  have hgeom : ∀ w : ℕ,
      mu.real (T w) ≤ Real.exp (-(3 * kappa)) ^ (w + 1) := by
    intro w
    refine le_trans (hterm w) ?_
    rw [exp_pow_eqL]
    refine Real.exp_le_exp.2 ?_
    have hN : (3 * (w + 1) : ℕ) ≤ 3 ^ (w + 1) := three_mul_succ_le_three_powL w
    have hR : ((3 * (w + 1) : ℕ) : ℝ) ≤ ((3 ^ (w + 1) : ℕ) : ℝ) := by
      exact_mod_cast hN
    have hid : (3 : ℝ) ^ ((w : ℝ) + 1) = (3 : ℝ) ^ (w + 1 : ℕ) := by
      rw [show ((w : ℝ) + 1) = ((w + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    have hpow : (3 : ℝ) * ((w : ℝ) + 1) ≤ (3 : ℝ) ^ ((w : ℝ) + 1) := by
      rw [hid]
      push_cast at hR
      linarith
    have hmul : 3 * kappa * ((w : ℝ) + 1) ≤ kappa * (3 : ℝ) ^ ((w : ℝ) + 1) := by
      calc 3 * kappa * ((w : ℝ) + 1) = kappa * (3 * ((w : ℝ) + 1)) := by ring
        _ ≤ kappa * (3 : ℝ) ^ ((w : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hpow hk0.le
    push_cast
    linarith
  have hsummable : Summable fun w : ℕ => Real.exp (-(3 * kappa)) ^ (w + 1) := by
    have hq1 : Real.exp (-(3 * kappa)) < 1 := by
      have hlt : Real.exp (-(3 * kappa)) < Real.exp 0 :=
        Real.exp_lt_exp.2 (by linarith)
      simpa using hlt
    exact ((summable_geometric_of_lt_one (Real.exp_pos _).le hq1).mul_right _).congr
      fun w => (pow_succ _ w).symm
  have hbound : mu S ≤
      ENNReal.ofReal (∑' w : ℕ, Real.exp (-(3 * kappa)) ^ (w + 1)) := by
    rw [ENNReal.ofReal_tsum_of_nonneg
      (fun w => pow_nonneg (Real.exp_pos _).le _) hsummable]
    refine le_trans (measure_mono hsub) ?_
    refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun w => ?_)
    have hfin : mu (T w) ≠ ⊤ := measure_ne_top _ _
    rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal (hgeom w)
  calc mu.real S = (mu S).toReal := rfl
    _ ≤ (ENNReal.ofReal (∑' w : ℕ, Real.exp (-(3 * kappa)) ^ (w + 1))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    _ = ∑' w : ℕ, Real.exp (-(3 * kappa)) ^ (w + 1) :=
        ENNReal.toReal_ofReal
          (tsum_nonneg fun w => pow_nonneg (Real.exp_pos _).le _)
    _ ≤ Real.exp (-kappa) := tsum_exp_pow_leL hk

/-! ## The weight conversion (`e.BoscL.def` gauge versus the `e.W.1.inf.bound`
summand) -/

/-- **The weight conversion.**  For a shell at or below the cube scale, the
`e.BoscL.def` gauge `3^{2m} ||grad j_k||_{W^{1,infinity}(z+square_m)}` is
dominated by `3^{2(m-k)}` times the summand
`3^k ||grad j_k||_{L^infinity(z+square_m)} + 3^{2k} ||grad^2 j_k||_{L^infinity(z+square_m)}`
of `e.W.1.inf.bound` on the *same* (translated) cube.

This is the intrinsic factor identified: the oscillation gauge is normalized at
the cube scale `m`, the stream summand at the shell scale `k`. -/
theorem shellOscGauge_le_translatedLargeCubeDerivGauge (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) (omega : CutoffSample d) :
    shellOscGauge Q k omega ≤
      (3 : ℝ) ^ (2 * (Q.scale - k)) *
        largeCubeDerivGauge Q.scale k
          (ShellField.translate (cubeBasePoint Q) (omega.1 k)) := by
  have hne : (3 : ℝ) ≠ 0 := by norm_num
  have hD : (0 : ℝ) ≤ localCubeDerivNorm Q.scale
      (ShellField.translate (cubeBasePoint Q) (omega.1 k)) :=
    localCubeDerivNorm_nonneg _ _
  have hS : (0 : ℝ) ≤ localCubeSecondDerivNorm Q.scale
      (ShellField.translate (cubeBasePoint Q) (omega.1 k)) :=
    localCubeSecondDerivNorm_nonneg _ _
  have e1 : (3 : ℝ) ^ (2 * (Q.scale - k)) * (3 : ℝ) ^ k =
      (3 : ℝ) ^ (2 * Q.scale - k) := by
    rw [← zpow_add₀ hne]
    congr 1
    ring
  have e2 : (3 : ℝ) ^ (2 * (Q.scale - k)) * (3 : ℝ) ^ (2 * k) =
      (3 : ℝ) ^ (2 * Q.scale) := by
    rw [← zpow_add₀ hne]
    congr 1
    ring
  have hmul : (3 : ℝ) ^ (2 * (Q.scale - k)) *
      largeCubeDerivGauge Q.scale k
        (ShellField.translate (cubeBasePoint Q) (omega.1 k)) =
      (3 : ℝ) ^ (2 * Q.scale - k) *
          localCubeDerivNorm Q.scale
            (ShellField.translate (cubeBasePoint Q) (omega.1 k)) +
        (3 : ℝ) ^ (2 * Q.scale) *
          localCubeSecondDerivNorm Q.scale
            (ShellField.translate (cubeBasePoint Q) (omega.1 k)) := by
    rw [largeCubeDerivGauge, mul_add, ← mul_assoc, ← mul_assoc, e1, e2]
  rw [hmul]
  have hbig : (3 : ℝ) ^ Q.scale ≤ (3 : ℝ) ^ (2 * Q.scale - k) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hpos1 : (0 : ℝ) < (3 : ℝ) ^ (2 * Q.scale - k) := zpow_pos (by norm_num) _
  have hpos2 : (0 : ℝ) < (3 : ℝ) ^ (2 * Q.scale) := zpow_pos (by norm_num) _
  refine max_le ?_ ?_
  · nlinarith [hpos1, hD]
  · nlinarith [hpos2, hS, hbig, hD]

/-! ## The constant and the exponent -/

/-- The local choice of the manuscript's `c` in `e.oscillation.bound` valid on
*both* branches: the constant `badEventOscConst` of the branch `m <= n`, divided
by the square of the dimension-only covering constant
`(1 or C_{(e.W1inf.jL.bound.smaller)})` that the shells below the cube scale
cost. -/
def badEventOscLowConst (d : ℕ) (Ccg : ℝ) : ℝ :=
  (1 / 3600 : ℝ) * ((sensitivityConstMax d)⁻¹) ^ 2 * (Ccg⁻¹) ^ 2 *
    ((max 1 (shellW1InfSmallerConst d))⁻¹) ^ 2

theorem badEventOscLowConst_pos {Ccg : ℝ} (hCcg : 0 < Ccg) (d : ℕ) :
    0 < badEventOscLowConst d Ccg := by
  have hC : (0 : ℝ) < sensitivityConstMax d := sensitivityConstMax_pos d
  have hmax : (0 : ℝ) < max 1 (shellW1InfSmallerConst d) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have h1 : (0 : ℝ) < ((sensitivityConstMax d)⁻¹) ^ 2 := by positivity
  have h2 : (0 : ℝ) < (Ccg⁻¹) ^ 2 := by positivity
  have h3 : (0 : ℝ) < ((max 1 (shellW1InfSmallerConst d))⁻¹) ^ 2 := by positivity
  unfold badEventOscLowConst
  positivity

/-- The branch constant is below the constant of the branch `m <= n`, so the proved
bound on that branch implies the same bound at this constant. -/
theorem badEventOscLowConst_le_badEventOscConst {Ccg : ℝ} (hCcg : 0 < Ccg)
    (d : ℕ) : badEventOscLowConst d Ccg ≤ badEventOscConst d Ccg := by
  have hC : (0 : ℝ) < sensitivityConstMax d := sensitivityConstMax_pos d
  have hmax : (1 : ℝ) ≤ max 1 (shellW1InfSmallerConst d) := le_max_left _ _
  have hmaxpos : (0 : ℝ) < max 1 (shellW1InfSmallerConst d) :=
    lt_of_lt_of_le zero_lt_one hmax
  have hinv : (max 1 (shellW1InfSmallerConst d))⁻¹ ≤ 1 := by
    have h := inv_anti₀ (zero_lt_one (α := ℝ)) hmax
    rwa [inv_one] at h
  have hinv0 : (0 : ℝ) < (max 1 (shellW1InfSmallerConst d))⁻¹ := inv_pos.2 hmaxpos
  have hsq : ((max 1 (shellW1InfSmallerConst d))⁻¹) ^ 2 ≤ 1 := by nlinarith
  have hbase : (0 : ℝ) < (1 / 3600 : ℝ) * ((sensitivityConstMax d)⁻¹) ^ 2 *
      (Ccg⁻¹) ^ 2 := by positivity
  unfold badEventOscLowConst badEventOscConst
  nlinarith [hbase, hsq]

/-- **The exponent of `e.oscillation.bound` over the whole range of `m, n`**
(ABK26): `c c_star gamma^{-1} 3^{-5 (m-n)_+} 3^{(n-m)_+}`. -/
def badEventOscFullRate (M : ABKModel d) (Ccg : ℝ) (Q : TriadicCube d) (n : ℤ) :
    ℝ :=
  badEventOscLowConst d Ccg * Algsuperdiff.Section3.Disorder.cstar M *
    M.gamma⁻¹ *
    (3 : ℝ) ^ (scaleGapPos Q.scale n - 5 * scaleGapPos n Q.scale)

/-- On the branch `n < m` the full exponent is the printed
`c c_star gamma^{-1} 3^{-5(m-n)}`. -/
theorem badEventOscFullRate_of_lt (M : ABKModel d) (Ccg : ℝ) (Q : TriadicCube d)
    {n : ℤ} (h : n < Q.scale) :
    badEventOscFullRate M Ccg Q n =
      badEventOscLowConst d Ccg * Algsuperdiff.Section3.Disorder.cstar M *
        M.gamma⁻¹ * (3 : ℝ) ^ (-(5 : ℝ) * ((Q.scale : ℝ) - (n : ℝ))) := by
  rw [badEventOscFullRate, scaleGapPos_of_lt h, scaleGapPos_of_le h.le]
  congr 2
  ring

/-- On the branch `m <= n` the full exponent is below the proved rate
`badEventOscRate`. -/
theorem badEventOscFullRate_le_badEventOscRate (M : ABKModel d) {Ccg : ℝ}
    (hCcg : 0 < Ccg) (Q : TriadicCube d) {n : ℤ} (h : Q.scale ≤ n) :
    badEventOscFullRate M Ccg Q n ≤ badEventOscRate M Ccg Q n := by
  have hc : (0 : ℝ) < Algsuperdiff.Section3.Disorder.cstar M :=
    (Algsuperdiff.Section3.Disorder.cstar_characterization M).1
  have hg : (0 : ℝ) < M.gamma⁻¹ := inv_pos.2 M.shellPrefix.gamma_pos
  have hzero : scaleGapPos n Q.scale = 0 := by
    have hle : ((Q.scale : ℝ)) - (n : ℝ) ≤ 0 := by
      have : ((Q.scale : ℝ)) ≤ (n : ℝ) := by exact_mod_cast h
      linarith
    rw [scaleGapPos]
    exact max_eq_right hle
  have hcst := badEventOscLowConst_le_badEventOscConst hCcg d
  have hpow : (0 : ℝ) < (3 : ℝ) ^ scaleGapPos Q.scale n := three_rpow_posL _
  rw [badEventOscFullRate, badEventOscRate, hzero]
  rw [show scaleGapPos Q.scale n - 5 * (0 : ℝ) = scaleGapPos Q.scale n by ring]
  have hprod : badEventOscLowConst d Ccg *
      Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ ≤
      badEventOscConst d Ccg * Algsuperdiff.Section3.Disorder.cstar M *
        M.gamma⁻¹ := by
    have hstep : badEventOscLowConst d Ccg *
        Algsuperdiff.Section3.Disorder.cstar M ≤
        badEventOscConst d Ccg * Algsuperdiff.Section3.Disorder.cstar M :=
      mul_le_mul_of_nonneg_right hcst hc.le
    exact mul_le_mul_of_nonneg_right hstep hg.le
  exact mul_le_mul_of_nonneg_right hprod hpow.le

/-! ## The two abstract threshold comparisons -/

/-- The exponent comparison for a shell at or above the cube scale, on the
branch `n < m`. -/
private theorem high_exponent_leL {gamma pm pn pk : ℝ} (hgq : gamma ≤ 1 / 4)
    (hnk : pn + 1 ≤ pk) (hnm : pn + 1 ≤ pm) :
    (1 / 2 : ℝ) * (-(5 : ℝ) * (pm - pn)) + (1 / 2 : ℝ) * (pk - pn) + pm +
        (gamma - 1) * pk ≤
      1 + (gamma * (pn - 1) + -(1 / 5 : ℝ) * (pk - pn)) := by
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ pk - pn - 1)
    (by linarith : (0 : ℝ) ≤ 3 / 10 - gamma), hnm]

/-- **The threshold comparison for a shell at or above the cube scale.** -/
private theorem high_threshold_comparisonL {kap w pm pn pk gamma : ℝ}
    (hkap : 0 ≤ kap) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hgq : gamma ≤ 1 / 4)
    (hnk : pn + 1 ≤ pk) (hnm : pn + 1 ≤ pm) :
    (1 / 60 : ℝ) * kap * w * (3 : ℝ) ^ ((1 / 2 : ℝ) * (-(5 : ℝ) * (pm - pn))) *
        (3 : ℝ) ^ ((1 / 2 : ℝ) * (pk - pn)) *
        ((3 : ℝ) ^ pm * (3 : ℝ) ^ ((gamma - 1) * pk)) ≤
      (1 / 20 : ℝ) * kap *
        ((3 : ℝ) ^ (gamma * (pn - 1)) * (3 : ℝ) ^ (-(1 / 5 : ℝ) * (pk - pn))) := by
  have hL : (3 : ℝ) ^ ((1 / 2 : ℝ) * (-(5 : ℝ) * (pm - pn))) *
      (3 : ℝ) ^ ((1 / 2 : ℝ) * (pk - pn)) *
      ((3 : ℝ) ^ pm * (3 : ℝ) ^ ((gamma - 1) * pk)) =
      (3 : ℝ) ^ ((1 / 2 : ℝ) * (-(5 : ℝ) * (pm - pn)) + (1 / 2 : ℝ) * (pk - pn) +
        pm + (gamma - 1) * pk) := by
    simp only [three_rpow_addL]
    congr 1
    ring
  have hR : (3 : ℝ) ^ (gamma * (pn - 1)) * (3 : ℝ) ^ (-(1 / 5 : ℝ) * (pk - pn)) =
      (3 : ℝ) ^ (gamma * (pn - 1) + -(1 / 5 : ℝ) * (pk - pn)) := three_rpow_addL _ _
  have hstep : (3 : ℝ) ^ ((1 / 2 : ℝ) * (-(5 : ℝ) * (pm - pn)) +
        (1 / 2 : ℝ) * (pk - pn) + pm + (gamma - 1) * pk) ≤
      3 * (3 : ℝ) ^ (gamma * (pn - 1) + -(1 / 5 : ℝ) * (pk - pn)) := by
    have hmerge : (3 : ℝ) *
        (3 : ℝ) ^ (gamma * (pn - 1) + -(1 / 5 : ℝ) * (pk - pn)) =
        (3 : ℝ) ^ (1 + (gamma * (pn - 1) + -(1 / 5 : ℝ) * (pk - pn))) := by
      have hone := three_rpow_addL (1 : ℝ)
        (gamma * (pn - 1) + -(1 / 5 : ℝ) * (pk - pn))
      rwa [Real.rpow_one] at hone
    rw [hmerge]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (high_exponent_leL hgq hnk hnm)
  have hRpos : (0 : ℝ) <
      (3 : ℝ) ^ (gamma * (pn - 1) + -(1 / 5 : ℝ) * (pk - pn)) := three_rpow_posL _
  calc (1 / 60 : ℝ) * kap * w *
        (3 : ℝ) ^ ((1 / 2 : ℝ) * (-(5 : ℝ) * (pm - pn))) *
        (3 : ℝ) ^ ((1 / 2 : ℝ) * (pk - pn)) *
        ((3 : ℝ) ^ pm * (3 : ℝ) ^ ((gamma - 1) * pk))
      = ((1 / 60 : ℝ) * kap * w) *
          ((3 : ℝ) ^ ((1 / 2 : ℝ) * (-(5 : ℝ) * (pm - pn))) *
            (3 : ℝ) ^ ((1 / 2 : ℝ) * (pk - pn)) *
            ((3 : ℝ) ^ pm * (3 : ℝ) ^ ((gamma - 1) * pk))) := by ring
    _ = ((1 / 60 : ℝ) * kap * w) *
          (3 : ℝ) ^ ((1 / 2 : ℝ) * (-(5 : ℝ) * (pm - pn)) +
            (1 / 2 : ℝ) * (pk - pn) + pm + (gamma - 1) * pk) := by rw [hL]
    _ ≤ ((1 / 60 : ℝ) * kap * w) *
          (3 * (3 : ℝ) ^ (gamma * (pn - 1) + -(1 / 5 : ℝ) * (pk - pn))) := by
        refine mul_le_mul_of_nonneg_left hstep ?_
        positivity
    _ = ((1 / 20 : ℝ) * kap * w) *
          (3 : ℝ) ^ (gamma * (pn - 1) + -(1 / 5 : ℝ) * (pk - pn)) := by ring
    _ ≤ ((1 / 20 : ℝ) * kap * 1) *
          (3 : ℝ) ^ (gamma * (pn - 1) + -(1 / 5 : ℝ) * (pk - pn)) := by
        refine mul_le_mul_of_nonneg_right ?_ hRpos.le
        nlinarith [hkap, hw1]
    _ = (1 / 20 : ℝ) * kap *
          (3 : ℝ) ^ (gamma * (pn - 1) + -(1 / 5 : ℝ) * (pk - pn)) := by ring
    _ = (1 / 20 : ℝ) * kap *
          ((3 : ℝ) ^ (gamma * (pn - 1)) *
            (3 : ℝ) ^ (-(1 / 5 : ℝ) * (pk - pn))) := by rw [hR]

/-- **The threshold comparison for a shell strictly below the cube scale.**
The covering factor `sq` of `e.W1inf.jL.bound.smaller` and the intrinsic weight
`3^{2(m-k)}` of the gauge conversion are both absorbed: the first by the
geometric decay `3^{-(m-n)/2}` left over from the branch's own exponent
`3^{-5(m-n)/2}`, the second by `3^{2(m-n)}` of the same. -/
private theorem wave_threshold_comparisonL {kap w cw sq pm pn pk gamma : ℝ}
    (hkap : 0 ≤ kap) (hw0 : 0 ≤ w) (hcw : 0 ≤ cw) (hwcw : cw * w ≤ 1)
    (hsqle : sq ≤ (3 : ℝ) ^ ((pm - pn) / 2))
    (hg0 : 0 < gamma) (hgq : gamma ≤ 1 / 4) (hnk : pn + 1 ≤ pk) :
    (1 / 60 : ℝ) * kap * w * (3 : ℝ) ^ ((1 / 2 : ℝ) * (-(5 : ℝ) * (pm - pn))) *
        (3 : ℝ) ^ ((1 / 2 : ℝ) * (pk - pn)) *
        ((3 : ℝ) ^ ((2 : ℝ) * (pm - pk)) * (cw * sq * (3 : ℝ) ^ (gamma * pk))) ≤
      (1 / 20 : ℝ) * kap *
        ((3 : ℝ) ^ (gamma * (pn - 1)) * (3 : ℝ) ^ (-(1 / 5 : ℝ) * (pk - pn))) := by
  have hz1 : sq * (3 : ℝ) ^ (-((pm - pn) / 2)) ≤ 1 := by
    calc sq * (3 : ℝ) ^ (-((pm - pn) / 2))
        ≤ (3 : ℝ) ^ ((pm - pn) / 2) * (3 : ℝ) ^ (-((pm - pn) / 2)) :=
          mul_le_mul_of_nonneg_right hsqle (three_rpow_posL _).le
      _ = 1 := by
          rw [three_rpow_addL,
            show (pm - pn) / 2 + -((pm - pn) / 2) = (0 : ℝ) by ring,
            Real.rpow_zero]
  have hz2 : (3 : ℝ) ^ ((pk - pn) * (gamma - 13 / 10) + gamma) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ pk - pn - 1)
      (by linarith : (0 : ℝ) ≤ 13 / 10 - gamma)]
  have hkey : (3 : ℝ) ^ ((1 / 2 : ℝ) * (-(5 : ℝ) * (pm - pn))) *
      (3 : ℝ) ^ ((1 / 2 : ℝ) * (pk - pn)) *
      ((3 : ℝ) ^ ((2 : ℝ) * (pm - pk)) * (3 : ℝ) ^ (gamma * pk)) =
      ((3 : ℝ) ^ (-((pm - pn) / 2)) *
          (3 : ℝ) ^ ((pk - pn) * (gamma - 13 / 10) + gamma)) *
        ((3 : ℝ) ^ (gamma * (pn - 1)) *
          (3 : ℝ) ^ (-(1 / 5 : ℝ) * (pk - pn))) := by
    simp only [three_rpow_addL]
    congr 1
    ring
  have hXpos : (0 : ℝ) < (3 : ℝ) ^ (gamma * (pn - 1)) *
      (3 : ℝ) ^ (-(1 / 5 : ℝ) * (pk - pn)) :=
    mul_pos (three_rpow_posL _) (three_rpow_posL _)
  have hbc : (sq * (3 : ℝ) ^ (-((pm - pn) / 2))) *
      (3 : ℝ) ^ ((pk - pn) * (gamma - 13 / 10) + gamma) ≤ 1 := by
    calc (sq * (3 : ℝ) ^ (-((pm - pn) / 2))) *
          (3 : ℝ) ^ ((pk - pn) * (gamma - 13 / 10) + gamma)
        ≤ 1 * (3 : ℝ) ^ ((pk - pn) * (gamma - 13 / 10) + gamma) :=
          mul_le_mul_of_nonneg_right hz1 (three_rpow_posL _).le
      _ = (3 : ℝ) ^ ((pk - pn) * (gamma - 13 / 10) + gamma) := one_mul _
      _ ≤ 1 := hz2
  have habc : (cw * w) * ((sq * (3 : ℝ) ^ (-((pm - pn) / 2))) *
      (3 : ℝ) ^ ((pk - pn) * (gamma - 13 / 10) + gamma)) ≤ 1 := by
    calc (cw * w) * ((sq * (3 : ℝ) ^ (-((pm - pn) / 2))) *
          (3 : ℝ) ^ ((pk - pn) * (gamma - 13 / 10) + gamma))
        ≤ (cw * w) * 1 := mul_le_mul_of_nonneg_left hbc (mul_nonneg hcw hw0)
      _ = cw * w := mul_one _
      _ ≤ 1 := hwcw
  calc (1 / 60 : ℝ) * kap * w *
        (3 : ℝ) ^ ((1 / 2 : ℝ) * (-(5 : ℝ) * (pm - pn))) *
        (3 : ℝ) ^ ((1 / 2 : ℝ) * (pk - pn)) *
        ((3 : ℝ) ^ ((2 : ℝ) * (pm - pk)) * (cw * sq * (3 : ℝ) ^ (gamma * pk)))
      = ((1 / 60 : ℝ) * kap) * ((cw * w) * sq) *
          ((3 : ℝ) ^ ((1 / 2 : ℝ) * (-(5 : ℝ) * (pm - pn))) *
            (3 : ℝ) ^ ((1 / 2 : ℝ) * (pk - pn)) *
            ((3 : ℝ) ^ ((2 : ℝ) * (pm - pk)) * (3 : ℝ) ^ (gamma * pk))) := by
        ring
    _ = ((1 / 60 : ℝ) * kap) * ((cw * w) * sq) *
          (((3 : ℝ) ^ (-((pm - pn) / 2)) *
              (3 : ℝ) ^ ((pk - pn) * (gamma - 13 / 10) + gamma)) *
            ((3 : ℝ) ^ (gamma * (pn - 1)) *
              (3 : ℝ) ^ (-(1 / 5 : ℝ) * (pk - pn)))) := by rw [hkey]
    _ = ((1 / 60 : ℝ) * kap) *
          ((cw * w) * ((sq * (3 : ℝ) ^ (-((pm - pn) / 2))) *
            (3 : ℝ) ^ ((pk - pn) * (gamma - 13 / 10) + gamma))) *
          ((3 : ℝ) ^ (gamma * (pn - 1)) *
            (3 : ℝ) ^ (-(1 / 5 : ℝ) * (pk - pn))) := by ring
    _ ≤ ((1 / 60 : ℝ) * kap) * 1 *
          ((3 : ℝ) ^ (gamma * (pn - 1)) *
            (3 : ℝ) ^ (-(1 / 5 : ℝ) * (pk - pn))) := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left habc (by positivity)) hXpos.le
    _ = ((3 : ℝ) ^ (gamma * (pn - 1)) *
          (3 : ℝ) ^ (-(1 / 5 : ℝ) * (pk - pn))) * kap * (1 / 60 : ℝ) := by ring
    _ ≤ ((3 : ℝ) ^ (gamma * (pn - 1)) *
          (3 : ℝ) ^ (-(1 / 5 : ℝ) * (pk - pn))) * kap * (1 / 20 : ℝ) :=
        mul_le_mul_of_nonneg_left (by norm_num) (mul_nonneg hXpos.le hkap)
    _ = (1 / 20 : ℝ) * kap *
          ((3 : ℝ) ^ (gamma * (pn - 1)) *
            (3 : ℝ) ^ (-(1 / 5 : ℝ) * (pk - pn))) := by ring

/-! ## The per-shell probability bound on the branch `n < m` -/

/-- **One shell of the oscillation branch at `n < m`.**  For every shell `k > n`
the probability that `j_k` exceeds its share of the `e.good.local.events`
threshold is at most `exp(- rate 3^{k-n})`, where `rate` is the exponent
`badEventOscFullRate` of `e.oscillation.bound`.

Shells at or above the cube scale are priced by the proved translated
`e.nabla.jk.O` tail `isBigOWith_gammaSigma_shellOscGauge`; shells strictly
below it are priced by the translated `e.W1inf.jL.bound.smaller`
(`Provider.Stream.isBigOWith_gammaSigma_largeCubeDerivGauge_lt_translate`)
after the weight conversion `shellOscGauge_le_translatedLargeCubeDerivGauge` —
this is the shell-sum pricing.

`hrestrict` is the restriction. -/
theorem measureReal_shellSensitivityFailure_le_low (M : ABKModel d) {Ccg : ℝ}
    (hCcg : 0 < Ccg) (Q : TriadicCube d) {n k m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E)
    (hn : n ≤ m0 - 1) (hmn : n < Q.scale) (hnk : n < k)
    (hrestrict : 1 ≤ badEventOscFullRate M Ccg Q n) :
    (cutoffSampleLaw M).toMeasure.real (shellSensitivityFailure M Ccg Q n k) ≤
      Real.exp (-(badEventOscFullRate M Ccg Q n *
        (3 : ℝ) ^ ((k : ℝ) - (n : ℝ)))) := by
  have hC : (0 : ℝ) < sensitivityConstMax d := sensitivityConstMax_pos d
  have hc : (0 : ℝ) < Algsuperdiff.Section3.Disorder.cstar M :=
    (Algsuperdiff.Section3.Disorder.cstar_characterization M).1
  have hg : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hgq : M.gamma ≤ 1 / 4 := M.shellPrefix.gamma_le_quarter
  have hnkR : (n : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hnk
  have hnmR : (n : ℝ) + 1 ≤ (Q.scale : ℝ) := by exact_mod_cast hmn
  have hsqc : (0 : ℝ) < Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) :=
    Real.sqrt_pos.2 hc
  have hsqg : (0 : ℝ) < (Real.sqrt M.gamma)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hg)
  have hkappos : (0 : ℝ) < (sensitivityConstMax d)⁻¹ * Ccg⁻¹ *
      Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
      (Real.sqrt M.gamma)⁻¹ := by positivity
  -- the covering constant and its normalization
  have hmax1 : (1 : ℝ) ≤ max 1 (shellW1InfSmallerConst d) := le_max_left _ _
  have hmaxpos : (0 : ℝ) < max 1 (shellW1InfSmallerConst d) :=
    lt_of_lt_of_le zero_lt_one hmax1
  have hwpos : (0 : ℝ) < (max 1 (shellW1InfSmallerConst d))⁻¹ := inv_pos.2 hmaxpos
  have hw1 : (max 1 (shellW1InfSmallerConst d))⁻¹ ≤ 1 := by
    have h := inv_anti₀ (zero_lt_one (α := ℝ)) hmax1
    rwa [inv_one] at h
  have hwcw : shellW1InfSmallerConst d *
      (max 1 (shellW1InfSmallerConst d))⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hmaxpos]
    exact le_max_right _ _
  -- the square root of the rate
  have hBpos : (0 : ℝ) < (1 / 60 : ℝ) *
      ((sensitivityConstMax d)⁻¹ * Ccg⁻¹ *
        Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
        (Real.sqrt M.gamma)⁻¹) *
      (max 1 (shellW1InfSmallerConst d))⁻¹ *
      (3 : ℝ) ^ ((1 / 2 : ℝ) * (-(5 : ℝ) * ((Q.scale : ℝ) - (n : ℝ)))) *
      (3 : ℝ) ^ ((1 / 2 : ℝ) * ((k : ℝ) - (n : ℝ))) := by
    have h1 := three_rpow_posL
      ((1 / 2 : ℝ) * (-(5 : ℝ) * ((Q.scale : ℝ) - (n : ℝ))))
    have h2 := three_rpow_posL ((1 / 2 : ℝ) * ((k : ℝ) - (n : ℝ)))
    positivity
  have hBsq : ((1 / 60 : ℝ) *
      ((sensitivityConstMax d)⁻¹ * Ccg⁻¹ *
        Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
        (Real.sqrt M.gamma)⁻¹) *
      (max 1 (shellW1InfSmallerConst d))⁻¹ *
      (3 : ℝ) ^ ((1 / 2 : ℝ) * (-(5 : ℝ) * ((Q.scale : ℝ) - (n : ℝ)))) *
      (3 : ℝ) ^ ((1 / 2 : ℝ) * ((k : ℝ) - (n : ℝ)))) ^ 2 =
      badEventOscFullRate M Ccg Q n * (3 : ℝ) ^ ((k : ℝ) - (n : ℝ)) := by
    have hcs : Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) ^ 2 =
        Algsuperdiff.Section3.Disorder.cstar M := Real.sq_sqrt hc.le
    have hgs : Real.sqrt M.gamma ^ 2 = M.gamma := Real.sq_sqrt hg.le
    have hexpand : ((1 / 60 : ℝ) *
        ((sensitivityConstMax d)⁻¹ * Ccg⁻¹ *
          Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
          (Real.sqrt M.gamma)⁻¹) *
        (max 1 (shellW1InfSmallerConst d))⁻¹ *
        (3 : ℝ) ^ ((1 / 2 : ℝ) * (-(5 : ℝ) * ((Q.scale : ℝ) - (n : ℝ)))) *
        (3 : ℝ) ^ ((1 / 2 : ℝ) * ((k : ℝ) - (n : ℝ)))) ^ 2 =
        (1 / 3600 : ℝ) * ((sensitivityConstMax d)⁻¹) ^ 2 * (Ccg⁻¹) ^ 2 *
          ((max 1 (shellW1InfSmallerConst d))⁻¹) ^ 2 *
          (Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) ^ 2) *
          ((Real.sqrt M.gamma) ^ 2)⁻¹ *
          (((3 : ℝ) ^ ((1 / 2 : ℝ) *
            (-(5 : ℝ) * ((Q.scale : ℝ) - (n : ℝ))))) ^ 2) *
          (((3 : ℝ) ^ ((1 / 2 : ℝ) * ((k : ℝ) - (n : ℝ)))) ^ 2) := by
      rw [← inv_pow]
      ring
    rw [hexpand, hcs, hgs, three_rpow_half_sqL, three_rpow_half_sqL,
      badEventOscFullRate_of_lt M Ccg Q hmn, badEventOscLowConst]
  have hrate3 : (1 : ℝ) ≤
      badEventOscFullRate M Ccg Q n * (3 : ℝ) ^ ((k : ℝ) - (n : ℝ)) :=
    one_le_mul_one_leL hrestrict
      (Real.one_le_rpow (by norm_num) (by linarith))
  -- the shell threshold, relaxed through the induction state
  have hgapzero : scaleGapPos Q.scale n = 0 := scaleGapPos_of_lt hmn
  have hsigma := sqrt_cstar_mul_inv_sqrt_gamma_mul_rpow_le_two_mul_sigmaBar M hS
    (m := n - 1) (by omega)
  have hcast : (((n - 1 : ℤ) : ℝ)) = (n : ℝ) - 1 := by push_cast; ring
  rw [hcast] at hsigma
  have hthrlow : (1 / 20 : ℝ) *
      ((sensitivityConstMax d)⁻¹ * Ccg⁻¹ *
        Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
        (Real.sqrt M.gamma)⁻¹) *
      ((3 : ℝ) ^ (M.gamma * ((n : ℝ) - 1)) *
        (3 : ℝ) ^ (-(1 / 5 : ℝ) * ((k : ℝ) - (n : ℝ)))) ≤
      shellSensitivityThreshold M Ccg Q.scale n k := by
    have hfacpos : (0 : ℝ) ≤ (1 / 20 : ℝ) * ((sensitivityConstMax d)⁻¹ * Ccg⁻¹) *
        (3 : ℝ) ^ (-(1 / 5 : ℝ) * ((k : ℝ) - (n : ℝ))) := by
      have h1 := three_rpow_posL (-(1 / 5 : ℝ) * ((k : ℝ) - (n : ℝ)))
      have h3 : (0 : ℝ) < (sensitivityConstMax d)⁻¹ * Ccg⁻¹ := by positivity
      positivity
    rw [shellSensitivityThreshold, goodLocalThreshold, hgapzero, mul_zero,
      Real.rpow_zero]
    calc (1 / 20 : ℝ) *
          ((sensitivityConstMax d)⁻¹ * Ccg⁻¹ *
            Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
            (Real.sqrt M.gamma)⁻¹) *
          ((3 : ℝ) ^ (M.gamma * ((n : ℝ) - 1)) *
            (3 : ℝ) ^ (-(1 / 5 : ℝ) * ((k : ℝ) - (n : ℝ))))
        = (1 / 20 : ℝ) * ((sensitivityConstMax d)⁻¹ * Ccg⁻¹) *
            (3 : ℝ) ^ (-(1 / 5 : ℝ) * ((k : ℝ) - (n : ℝ))) *
            (Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
              (Real.sqrt M.gamma)⁻¹ *
              (3 : ℝ) ^ (M.gamma * ((n : ℝ) - 1))) := by ring
      _ ≤ (1 / 20 : ℝ) * ((sensitivityConstMax d)⁻¹ * Ccg⁻¹) *
            (3 : ℝ) ^ (-(1 / 5 : ℝ) * ((k : ℝ) - (n : ℝ))) *
            (2 * (Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ)) :=
          mul_le_mul_of_nonneg_left hsigma hfacpos
      _ = (1 / 5 : ℝ) *
            ((sensitivityConstMax d)⁻¹ *
              ((1 / 2 : ℝ) * Ccg⁻¹ * 1 *
                (Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ))) *
            (3 : ℝ) ^ (-(1 / 5 : ℝ) * ((k : ℝ) - (n : ℝ))) := by ring
  change (cutoffSampleLaw M).toMeasure.real
      {omega | shellSensitivityThreshold M Ccg Q.scale n k <
        shellOscGauge Q k omega} ≤ _
  rcases lt_or_ge k Q.scale with hkm | hmk
  · -- the wave regime: a shell strictly below the cube scale
    have hkmR : (k : ℝ) + 1 ≤ (Q.scale : ℝ) := by exact_mod_cast hkm
    have hd2 : (2 : ℕ) ≤ d := M.shellPrefix.dimension
    have hdR : (0 : ℝ) < (d : ℝ) := by
      have : (0 : ℕ) < d := by omega
      exact_mod_cast this
    have hCW : (0 : ℝ) < shellW1InfSmallerConst d := by
      have hL : (0 : ℝ) < largeCubeLogConst * (d : ℝ) :=
        mul_pos largeCubeLogConst_pos hdR
      have hs := Real.sqrt_pos.2 hL
      rw [shellW1InfSmallerConst]
      linarith
    have hsqrtpos : (0 : ℝ) < Real.sqrt ((Q.scale : ℝ) - (k : ℝ)) :=
      Real.sqrt_pos.2 (by linarith)
    have hApos : (0 : ℝ) < (3 : ℝ) ^ ((2 : ℝ) * ((Q.scale : ℝ) - (k : ℝ))) *
        (shellW1InfSmallerConst d * Real.sqrt ((Q.scale : ℝ) - (k : ℝ)) *
          (3 : ℝ) ^ (M.gamma * (k : ℝ))) := by
      have h1 := three_rpow_posL ((2 : ℝ) * ((Q.scale : ℝ) - (k : ℝ)))
      have h2 := three_rpow_posL (M.gamma * (k : ℝ))
      positivity
    have hsqle : Real.sqrt ((Q.scale : ℝ) - (k : ℝ)) ≤
        (3 : ℝ) ^ (((Q.scale : ℝ) - (n : ℝ)) / 2) := by
      have h1 : Real.sqrt ((Q.scale : ℝ) - (k : ℝ)) ≤ (Q.scale : ℝ) - (k : ℝ) :=
        sqrt_le_self_of_one_leL (by linarith)
      have h2 : (Q.scale : ℝ) - (n : ℝ) ≤
          (3 : ℝ) ^ (((Q.scale : ℝ) - (n : ℝ)) / 2) :=
        self_le_three_rpow_halfL (by linarith)
      linarith
    have htail : HCPolySupport.IndependentSums.IsBigOWith
        (cutoffSampleLaw M).toMeasure
        (HCPolySupport.IndependentSums.gammaSigma 2) (shellOscGauge Q k)
        ((3 : ℝ) ^ ((2 : ℝ) * ((Q.scale : ℝ) - (k : ℝ))) *
          (shellW1InfSmallerConst d * Real.sqrt ((Q.scale : ℝ) - (k : ℝ)) *
            (3 : ℝ) ^ (M.gamma * (k : ℝ)))) := by
      have hbase := isBigOWith_gammaSigma_largeCubeDerivGauge_lt_translate M hkm
        (cubeBasePoint Q)
      have hcut := isBigOWith_cutoffSampleLaw_comp_val hbase
      have hscaled := hcut.const_mul
        (c := (3 : ℝ) ^ ((2 : ℝ) * ((Q.scale : ℝ) - (k : ℝ))))
        (Real.rpow_nonneg (by norm_num) _)
      refine hscaled.of_le fun omega => ?_
      have hz : (3 : ℝ) ^ ((2 : ℝ) * ((Q.scale : ℝ) - (k : ℝ))) =
          (3 : ℝ) ^ (2 * (Q.scale - k)) := by
        rw [← Real.rpow_intCast (3 : ℝ) (2 * (Q.scale - k))]
        congr 1
        push_cast
        ring
      rw [hz]
      exact shellOscGauge_le_translatedLargeCubeDerivGauge Q hkm.le omega
    refine measureReal_upperTail_le_expL hApos hBpos ?_ hBsq hrate3 htail
    refine le_trans ?_ hthrlow
    exact wave_threshold_comparisonL hkappos.le hwpos.le hCW.le hwcw
      hsqle hg hgq hnkR
  · -- the own-scale regime: a shell at or above the cube scale
    have hApos : (0 : ℝ) < (3 : ℝ) ^ ((Q.scale : ℝ)) *
        (3 : ℝ) ^ ((M.gamma - 1) * (k : ℝ)) :=
      mul_pos (three_rpow_posL _) (three_rpow_posL _)
    have htail := isBigOWith_gammaSigma_shellOscGauge M Q hmk
    refine measureReal_upperTail_le_expL hApos hBpos ?_ hBsq hrate3 htail
    refine le_trans ?_ hthrlow
    exact high_threshold_comparisonL hkappos.le hwpos.le hw1 hgq hnkR hnmR

/-! ## The oscillation branch at `n < m` -/

/-- **The oscillation branch of `l.bad.event.lemma` at `n < m`** (ABK26,
`e.oscillation.bound`), where `(n-m)_+ = 0`:

```
P[ sensitivity clause of Q(m,n,z) fails ]
  <= exp( - c c_star gamma^{-1} 3^{-5(m-n)} ) ,
```

with `c = badEventOscLowConst d Ccg`, dimension-only.

It is the only hypothesis beyond the manuscript's own data, and it is also
exactly the gate that the weak-Orlicz tail and the geometric summation need. -/
theorem measureReal_goodLocalSensitivityFailure_le_low (M : ABKModel d)
    {Ccg : ℝ} (hCcg : 0 < Ccg) (Q : TriadicCube d) {n m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E)
    (hn : n ≤ m0 - 1) (hmn : n < Q.scale)
    (hrestrict : 1 ≤ badEventOscFullRate M Ccg Q n) :
    (cutoffSampleLaw M).toMeasure.real (goodLocalSensitivityFailure M Ccg Q n) ≤
      Real.exp (-(badEventOscFullRate M Ccg Q n)) := by
  refine measureReal_le_exp_of_iUnionL _ hrestrict
    (goodLocalSensitivityFailure_subset_iUnion M hCcg Q n) fun w => ?_
  have hle := measureReal_shellSensitivityFailure_le_low M hCcg Q hS hn hmn
    (k := n + 1 + (w : ℤ)) (by omega) hrestrict
  have hcast : (((n + 1 + (w : ℤ) : ℤ) : ℝ) - (n : ℝ)) = (w : ℝ) + 1 := by
    push_cast
    ring
  rwa [hcast] at hle

end

end Algsuperdiff.Section3.Provider.BadEvents
