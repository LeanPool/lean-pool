/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.FiniteQAggregateBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.LowerLegProfile

/-!
# FiniteQLtTwoPresplit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The conditional finite-`q < 2` pre-split producer

This file implements the corrected sublinear route for the finite lower
coarse-ellipticity aggregate when `1 <= q < 2`.  At each depth, the random
remainder is written as `a n * V n`, where `a n` is its deterministic Orlicz
amplitude and `V n = O_{Gamma_sigma}(1)` is normalized.  The probability
weights

```text
c n = w n * (a n)^(q/2) / sum_k w k * (a k)^(q/2)
```

then permit Jensen's inequality without replacing the source weight by a
slower one.  This is essential: direct linearization against `w n` would need
the stronger, non-source restriction `s * q > gamma`.  The normalized route
uses only `2 * s > gamma` and retains the corrected pole of order `2 / q`.

## Main results

* `tsum_weighted_rpow_root_le_of_one_le_of_le_two`: countable weighted Jensen
  for exponents `1 <= q <= 2` and subprobability weights.
* `twoTermFamilySplit_cutoffLowerEllipticityInv_of_finiteQLtTwoPresplit`: the
  exact finite-`q` cutoff aggregate split into its corrected deterministic
  profile and a normalized random lane.
* `coarse_ellipticity_lower_branchPayload_lt_two_of_finiteQPresplit`: the
  corresponding `payloadLtTwo` interface of `LowerLegProfile.lean`.

## Conditional status and A inventory

This file proves only a local aggregation result.  It does not itself prove the
analytic producer `finiteQPresplit`, and carries no source-node status.  The
concrete downstream superposed-flux provider supplies that producer and proves
the lower leg; a separate downstream provider proves the upper leg.  In the
main theorem, `hdepth`, `hVO`, and `hbudget` are explicit analytic A
obligations: the per-depth deterministic-plus-random estimate and its Orlicz
control.  The wrapper's `finiteQPresplit` input is the same conditional
analytic producer, uniformly over the induction data.  Relative to an exact
source-facing theorem these are proof obligations to discharge, not source
premises.  The other inputs record the standing model, dimension, positivity,
measurability, and summability; the corrected `2 / q` pole and random
depth-zero lane are the adopted mathematical form.  No induction hypothesis is
altered or unpacked here.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-- Countable weighted Jensen for the sublinear power `q / 2`.  The weights
may have total mass at most one; this is the form used after normalizing the
per-depth Orlicz amplitudes. -/
theorem tsum_weighted_rpow_root_le_of_one_le_of_le_two
    {q : ℝ} {w H : ℕ → ℝ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (hw : ∀ n, 0 ≤ w n) (hH : ∀ n, 0 ≤ H n)
    (hwsum : Summable w) (hwone : (∑' n : ℕ, w n) ≤ 1)
    (hWHsum : Summable fun n : ℕ => w n * H n)
    (hWqsum : Summable fun n : ℕ => w n * H n ^ (q / 2)) :
    (∑' n : ℕ, w n * H n ^ (q / 2)) ^ (2 / q) ≤
      ∑' n : ℕ, w n * H n := by
  classical
  let B : ℝ := ∑' n : ℕ, w n * H n
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq1
  have hp1 : 1 ≤ 2 / q := by
    rw [le_div_iff₀ hq0]
    simpa using hq2
  have hp0 : 0 ≤ 2 / q := by positivity
  have ht0 : 0 ≤ q / 2 := by positivity
  have hpinv : (2 / q)⁻¹ = q / 2 := by
    rw [inv_div]
  have hcancel : q / 2 * (2 / q) = 1 := by
    simp only [div_eq_mul_inv]
    calc
      (q * (2 : ℝ)⁻¹) * (2 * q⁻¹) =
          (q * q⁻¹) * (2 * (2 : ℝ)⁻¹) := by ring_nf
      _ = 1 := by rw [mul_inv_cancel₀ hq0.ne']; norm_num
  have hB : 0 ≤ B := by
    dsimp [B]
    exact tsum_nonneg fun n => mul_nonneg (hw n) (hH n)
  have hfinite : ∀ s : Finset ℕ,
      ∑ n ∈ s, w n * H n ^ (q / 2) ≤ B ^ (q / 2) := by
    intro s
    have hholder :
        ∑ n ∈ s, w n * H n ^ (q / 2) ≤
          (∑ n ∈ s, w n) ^ (1 - (2 / q)⁻¹) *
            (∑ n ∈ s, w n * (H n ^ (q / 2)) ^ (2 / q)) ^
              (2 / q)⁻¹ :=
      Real.inner_le_weight_mul_Lp_of_nonneg
        (s := s) (p := 2 / q) (w := w) (f := fun n => H n ^ (q / 2))
        hp1 hw fun n => Real.rpow_nonneg (hH n) _
    have hpower : (∑ n ∈ s, w n * (H n ^ (q / 2)) ^ (2 / q)) =
        ∑ n ∈ s, w n * H n := by
      refine Finset.sum_congr rfl ?_
      intro n _hn
      congr 1
      rw [← Real.rpow_mul (hH n), hcancel, Real.rpow_one]
    have hsumw0 : 0 ≤ ∑ n ∈ s, w n :=
      Finset.sum_nonneg fun n _hn => hw n
    have hsumw1 : ∑ n ∈ s, w n ≤ 1 :=
      (hwsum.sum_le_tsum s fun n _hn => hw n).trans hwone
    have hexp0 : 0 ≤ 1 - (2 / q)⁻¹ := by
      rw [hpinv]
      linarith
    have hweight : (∑ n ∈ s, w n) ^ (1 - (2 / q)⁻¹) ≤ 1 := by
      have hmono := Real.rpow_le_rpow hsumw0 hsumw1 hexp0
      simpa using hmono
    have hsumH0 : 0 ≤ ∑ n ∈ s, w n * H n :=
      Finset.sum_nonneg fun n _hn => mul_nonneg (hw n) (hH n)
    have hsumHB : ∑ n ∈ s, w n * H n ≤ B := by
      dsimp [B]
      exact hWHsum.sum_le_tsum s fun n _hn => mul_nonneg (hw n) (hH n)
    have hmoment : (∑ n ∈ s, w n * H n) ^ (q / 2) ≤ B ^ (q / 2) :=
      Real.rpow_le_rpow hsumH0 hsumHB ht0
    calc
      ∑ n ∈ s, w n * H n ^ (q / 2) ≤
          (∑ n ∈ s, w n) ^ (1 - (2 / q)⁻¹) *
            (∑ n ∈ s, w n * (H n ^ (q / 2)) ^ (2 / q)) ^
              (2 / q)⁻¹ := hholder
      _ = (∑ n ∈ s, w n) ^ (1 - (2 / q)⁻¹) *
          (∑ n ∈ s, w n * H n) ^ (q / 2) := by
            rw [hpower, hpinv]
      _ ≤ 1 * B ^ (q / 2) :=
        mul_le_mul hweight hmoment (Real.rpow_nonneg hsumH0 _) (by norm_num)
      _ = B ^ (q / 2) := one_mul _
  have hsum0 : 0 ≤ ∑' n : ℕ, w n * H n ^ (q / 2) :=
    tsum_nonneg fun n => mul_nonneg (hw n) (Real.rpow_nonneg (hH n) _)
  have hsumle : (∑' n : ℕ, w n * H n ^ (q / 2)) ≤ B ^ (q / 2) :=
    hWqsum.tsum_le_of_sum_le hfinite
  calc
    (∑' n : ℕ, w n * H n ^ (q / 2)) ^ (2 / q) ≤
        (B ^ (q / 2)) ^ (2 / q) :=
      Real.rpow_le_rpow hsum0 hsumle hp0
    _ = B := by rw [← Real.rpow_mul hB, hcancel, Real.rpow_one]

/-- The root exponent `2 / q` is at most two when `1 <= q`; hence its
two-term convexity loss is bounded by the fixed factor two. -/
private theorem rpow_add_le_two_mul_add_rpow {a b q : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) :
    (a + b) ^ (2 / q) ≤ 2 * (a ^ (2 / q) + b ^ (2 / q)) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq1
  have hp1 : 1 ≤ 2 / q := by
    rw [le_div_iff₀ hq0]
    simpa using hq2
  have hp2 : 2 / q ≤ 2 := by
    rw [div_le_iff₀ hq0]
    linarith
  have hcoeff : (2 : ℝ) ^ (2 / q - 1) ≤ 2 := by
    calc
      (2 : ℝ) ^ (2 / q - 1) ≤ (2 : ℝ) ^ (1 : ℝ) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        linarith
      _ = 2 := Real.rpow_one 2
  calc
    (a + b) ^ (2 / q) ≤
        (2 : ℝ) ^ (2 / q - 1) * (a ^ (2 / q) + b ^ (2 / q)) :=
      rpow_add_le_mul_rpow_add_rpow ha hb hp1
    _ ≤ 2 * (a ^ (2 / q) + b ^ (2 / q)) :=
      mul_le_mul_of_nonneg_right hcoeff
        (add_nonneg (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _))

/-- A normalized per-depth finite-`q < 2` split produces the lower
coarse-ellipticity two-slot payload.  The amplitude profile stays inside the
exact `ell^(q/2)` aggregate; only its normalized probability weights are
linearized. -/
theorem twoTermFamilySplit_cutoffLowerEllipticityInv_of_finiteQLtTwoPresplit
    [NeZero d] (M : ABKModel d) (m : ℤ)
    (r : {r : ℝ // 1 ≤ r}) (hr : (r : ℝ) < 2)
    {s Cprof scaling sigmaTail B : ℝ} (hs : 0 < s)
    (hgap : 0 < 2 * s - M.gamma) (hCprof : 0 ≤ Cprof)
    (hscaling : 0 ≤ scaling) (hsigmaTail : 0 < sigmaTail)
    {L0 : ℤ} {V : ℕ → Cutoff.CutoffSample d → ℝ} {a : ℕ → ℝ}
    (hVnonneg : ∀ n omega, 0 ≤ V n omega)
    (hVmeas : ∀ n, Measurable (V n))
    (ha : ∀ n, 0 < a n)
    (hasum : Summable fun n : ℕ =>
      Book.Ch02.geometricWeight s (r : ℝ) n * a n ^ ((r : ℝ) / 2))
    (hVlinsum : ∀ omega, Summable fun n : ℕ =>
      Book.Ch02.geometricWeight s (r : ℝ) n *
        a n ^ ((r : ℝ) / 2) * V n omega)
    (hVO : ∀ n, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma sigmaTail) (V n) 1)
    (hbudget :
      (2 * (∑' n : ℕ, Book.Ch02.geometricWeight s (r : ℝ) n *
          a n ^ ((r : ℝ) / 2)) ^ (2 / (r : ℝ))) *
        gammaTriangleConst sigmaTail ≤ B)
    (hdepth : ∀ omega, ∀ L : ℤ, L0 ≤ L → ∀ n : ℕ,
      scaling *
          Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
            (originCube d m) (m - (n : ℤ))
            (Cutoff.coefficientCutoff M.nu L omega) ≤
        finiteQGeometricProfile Cprof M.gamma n + a n * V n omega) :
    ∃ Ydet Y : Cutoff.CutoffSample d → ℝ,
      (∀ omega, ∀ L : ℤ, L0 ≤ L →
        Observable.cutoffLowerEllipticityInv M m L s hs
              (CoarseEllipticityExponent.finite r) omega * scaling ≤
          Ydet omega + Y omega) ∧
      (∀ omega, Ydet omega ≤
        8 * Cprof * (s / (2 * s - M.gamma)) ^ (2 / (r : ℝ))) ∧
      Measurable Y ∧
      IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
        (gammaSigma sigmaTail) Y B := by
  let w : ℕ → ℝ := fun n => Book.Ch02.geometricWeight s (r : ℝ) n
  let D : ℕ → ℝ := finiteQGeometricProfile Cprof M.gamma
  let R : ℕ → Cutoff.CutoffSample d → ℝ := fun n omega => a n * V n omega
  let Z : ℤ → Cutoff.CutoffSample d → ℕ → ℝ := fun L omega n =>
    scaling *
      Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
        (originCube d m) (m - (n : ℤ))
        (Cutoff.coefficientCutoff M.nu L omega)
  let S : ℝ := ∑' n : ℕ, w n * a n ^ ((r : ℝ) / 2)
  let c : ℕ → ℝ := fun n => S⁻¹ * (w n * a n ^ ((r : ℝ) / 2))
  have hr0 : (0 : ℝ) < (r : ℝ) :=
    lt_of_lt_of_le zero_lt_one r.property
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := r.property
  have hr2 : (r : ℝ) ≤ 2 := hr.le
  have ht0 : (0 : ℝ) ≤ (r : ℝ) / 2 := by positivity
  have ht1 : (r : ℝ) / 2 ≤ 1 := by linarith
  have hroot0 : (0 : ℝ) ≤ 2 / (r : ℝ) := by positivity
  have hsr : (0 : ℝ) < s * (r : ℝ) := mul_pos hs hr0
  have hwpos : ∀ n, 0 < w n := fun n =>
    HCPolySupport.geometricWeight_pos n hsr
  have hw : ∀ n, 0 ≤ w n := fun n => (hwpos n).le
  have hD : ∀ n, 0 ≤ D n := fun n =>
    finiteQGeometricProfile_nonneg hCprof M.gamma n
  have hR : ∀ n omega, 0 ≤ R n omega := fun n omega =>
    mul_nonneg (ha n).le (hVnonneg n omega)
  have hDqsum : Summable fun n : ℕ => w n * D n ^ ((r : ℝ) / 2) := by
    simpa [w, D] using
      summable_geometricWeight_mul_finiteQGeometricProfile_rpow hCprof hgap hr0
  have hVlinsum' : ∀ omega, Summable fun n : ℕ =>
      w n * a n ^ ((r : ℝ) / 2) * V n omega := by
    intro omega
    simpa [w] using hVlinsum omega
  have hSpos : 0 < S := by
    have hterm : 0 < w 0 * a 0 ^ ((r : ℝ) / 2) :=
      mul_pos (hwpos 0) (Real.rpow_pos_of_pos (ha 0) _)
    have hterm_le : w 0 * a 0 ^ ((r : ℝ) / 2) ≤ S := by
      dsimp [S]
      have hfinite := hasum.sum_le_tsum {0} fun n _hn =>
        mul_nonneg (hw n) (Real.rpow_nonneg (ha n).le _)
      simpa using hfinite
    exact hterm.trans_le hterm_le
  have hcpos : ∀ n, 0 < c n := fun n => by
    exact mul_pos (inv_pos.mpr hSpos)
      (mul_pos (hwpos n) (Real.rpow_pos_of_pos (ha n) _))
  have hc : ∀ n, 0 ≤ c n := fun n => (hcpos n).le
  have hcsum : Summable c := by
    simpa [c] using hasum.mul_left S⁻¹
  have hctsum : (∑' n : ℕ, c n) = 1 := by
    change (∑' n : ℕ, S⁻¹ * (w n * a n ^ ((r : ℝ) / 2))) = 1
    rw [tsum_mul_left]
    change S⁻¹ * S = 1
    exact inv_mul_cancel₀ hSpos.ne'
  have hVqweighted : ∀ omega, Summable fun n : ℕ =>
      w n * a n ^ ((r : ℝ) / 2) * V n omega ^ ((r : ℝ) / 2) := by
    intro omega
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg
        (mul_nonneg (hw n) (Real.rpow_nonneg (ha n).le _))
        (Real.rpow_nonneg (hVnonneg n omega) _))
      (fun n => ?_) (hasum.add (hVlinsum' omega))
    have hpower : V n omega ^ ((r : ℝ) / 2) ≤ 1 + V n omega := by
      by_cases hVone : V n omega ≤ 1
      · calc
          V n omega ^ ((r : ℝ) / 2) ≤ (1 : ℝ) ^ ((r : ℝ) / 2) :=
            Real.rpow_le_rpow (hVnonneg n omega) hVone ht0
          _ = 1 := Real.one_rpow _
          _ ≤ 1 + V n omega := by linarith [hVnonneg n omega]
      · have hle : V n omega ^ ((r : ℝ) / 2) ≤ V n omega :=
          Real.rpow_le_self_of_one_le (le_of_not_ge hVone) ht1
        linarith
    calc
      w n * a n ^ ((r : ℝ) / 2) * V n omega ^ ((r : ℝ) / 2) ≤
          w n * a n ^ ((r : ℝ) / 2) * (1 + V n omega) :=
        mul_le_mul_of_nonneg_left hpower
          (mul_nonneg (hw n) (Real.rpow_nonneg (ha n).le _))
      _ = w n * a n ^ ((r : ℝ) / 2) +
          w n * a n ^ ((r : ℝ) / 2) * V n omega := by ring_nf
  have hRqsum : ∀ omega, Summable fun n : ℕ =>
      w n * R n omega ^ ((r : ℝ) / 2) := by
    intro omega
    refine (hVqweighted omega).congr fun n => ?_
    change w n * a n ^ ((r : ℝ) / 2) * V n omega ^ ((r : ℝ) / 2) =
      w n * (a n * V n omega) ^ ((r : ℝ) / 2)
    rw [Real.mul_rpow (ha n).le (hVnonneg n omega)]
    ring_nf
  have hVqnorm : ∀ omega, Summable fun n : ℕ =>
      c n * V n omega ^ ((r : ℝ) / 2) := by
    intro omega
    simpa [c, mul_assoc] using (hVqweighted omega).mul_left S⁻¹
  have hVlinnorm : ∀ omega, Summable fun n : ℕ => c n * V n omega := by
    intro omega
    simpa [c, mul_assoc] using (hVlinsum' omega).mul_left S⁻¹
  have hRseries : ∀ omega,
      (∑' n : ℕ, w n * R n omega ^ ((r : ℝ) / 2)) =
        S * ∑' n : ℕ, c n * V n omega ^ ((r : ℝ) / 2) := by
    intro omega
    calc
      (∑' n : ℕ, w n * R n omega ^ ((r : ℝ) / 2)) =
          ∑' n : ℕ,
            w n * a n ^ ((r : ℝ) / 2) * V n omega ^ ((r : ℝ) / 2) := by
        refine tsum_congr fun n => ?_
        change w n * (a n * V n omega) ^ ((r : ℝ) / 2) = _
        rw [Real.mul_rpow (ha n).le (hVnonneg n omega)]
        ring_nf
      _ = S * ∑' n : ℕ, c n * V n omega ^ ((r : ℝ) / 2) := by
        rw [← tsum_mul_left]
        refine tsum_congr fun n => ?_
        dsimp [c]
        calc
          w n * a n ^ ((r : ℝ) / 2) * V n omega ^ ((r : ℝ) / 2) =
              1 * (w n * a n ^ ((r : ℝ) / 2)) *
                V n omega ^ ((r : ℝ) / 2) := by ring_nf
          _ = (S * S⁻¹) * (w n * a n ^ ((r : ℝ) / 2)) *
                V n omega ^ ((r : ℝ) / 2) := by
            rw [mul_inv_cancel₀ hSpos.ne']
          _ = S * (S⁻¹ * (w n * a n ^ ((r : ℝ) / 2)) *
                V n omega ^ ((r : ℝ) / 2)) := by ring_nf
  have hRroot : ∀ omega,
      (∑' n : ℕ, w n * R n omega ^ ((r : ℝ) / 2)) ^ (2 / (r : ℝ)) ≤
        S ^ (2 / (r : ℝ)) * ∑' n : ℕ, c n * V n omega := by
    intro omega
    have hqsum0 : 0 ≤ ∑' n : ℕ, c n * V n omega ^ ((r : ℝ) / 2) :=
      tsum_nonneg fun n => mul_nonneg (hc n)
        (Real.rpow_nonneg (hVnonneg n omega) _)
    have hjensen := tsum_weighted_rpow_root_le_of_one_le_of_le_two
      hr1 hr2 hc (fun n => hVnonneg n omega) hcsum hctsum.le
      (hVlinnorm omega) (hVqnorm omega)
    rw [hRseries omega, Real.mul_rpow hSpos.le hqsum0]
    exact mul_le_mul_of_nonneg_left hjensen
      (Real.rpow_nonneg hSpos.le _)
  have hDroot :
      (∑' n : ℕ, w n * D n ^ ((r : ℝ) / 2)) ^ (2 / (r : ℝ)) ≤
        4 * Cprof * (s / (2 * s - M.gamma)) ^ (2 / (r : ℝ)) := by
    have hx : 0 ≤ s / (2 * s - M.gamma) :=
      div_nonneg hs.le hgap.le
    calc
      (∑' n : ℕ, w n * D n ^ ((r : ℝ) / 2)) ^ (2 / (r : ℝ)) ≤
          Cprof * (2 * s / (2 * s - M.gamma)) ^ (2 / (r : ℝ)) := by
        simpa [w, D] using finiteQGeometricProfile_aggregate_le
          hCprof M.shellPrefix.gamma_pos.le hs hr0 hgap
      _ = Cprof * (2 * (s / (2 * s - M.gamma))) ^ (2 / (r : ℝ)) := by
        ring_nf
      _ ≤ Cprof * (4 * (s / (2 * s - M.gamma)) ^ (2 / (r : ℝ))) :=
        mul_le_mul_of_nonneg_left (rpow_two_mul_div_le hx hr1) hCprof
      _ = 4 * Cprof * (s / (2 * s - M.gamma)) ^ (2 / (r : ℝ)) := by
        ring_nf
  have htotalSum : ∀ omega, Summable fun n : ℕ =>
      w n * (D n + R n omega) ^ ((r : ℝ) / 2) := by
    intro omega
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (hw n)
        (Real.rpow_nonneg (add_nonneg (hD n) (hR n omega)) _))
      (fun n => ?_) (hDqsum.add (hRqsum omega))
    calc
      w n * (D n + R n omega) ^ ((r : ℝ) / 2) ≤
          w n * (D n ^ ((r : ℝ) / 2) +
            R n omega ^ ((r : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_add_le_add_rpow (hD n) (hR n omega) ht0 ht1) (hw n)
      _ = w n * D n ^ ((r : ℝ) / 2) +
          w n * R n omega ^ ((r : ℝ) / 2) := by ring_nf
  refine ⟨fun _ =>
      8 * Cprof * (s / (2 * s - M.gamma)) ^ (2 / (r : ℝ)),
    fun omega =>
      (2 * S ^ (2 / (r : ℝ))) * ∑' n : ℕ, c n * V n omega,
    ?_, fun _ => le_rfl, ?_, ?_⟩
  · intro omega L hL
    have hscale : (originCube d m).scale = m := rfl
    have hZ : ∀ n, 0 ≤ Z L omega n := by
      intro n
      refine mul_nonneg hscaling ?_
      exact Book.Ch05.Section52.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_nonneg_of_le
        (originCube d m) (Cutoff.coefficientCutoff M.nu L omega)
        (by rw [hscale]; omega)
    have hZR : ∀ n, Z L omega n ≤ D n + R n omega := by
      intro n
      simpa [Z, D, R] using hdepth omega L hL n
    have hZqsum : Summable fun n : ℕ =>
        w n * Z L omega n ^ ((r : ℝ) / 2) := by
      refine Summable.of_nonneg_of_le
        (fun n => mul_nonneg (hw n) (Real.rpow_nonneg (hZ n) _))
        (fun n => mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (hZ n) (hZR n) ht0) (hw n))
        (htotalSum omega)
    have hsumZR :
        (∑' n : ℕ, w n * Z L omega n ^ ((r : ℝ) / 2)) ≤
          ∑' n : ℕ, w n * (D n + R n omega) ^ ((r : ℝ) / 2) :=
      hZqsum.tsum_le_tsum
        (fun n => mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (hZ n) (hZR n) ht0) (hw n))
        (htotalSum omega)
    have hZaggregate :
        (∑' n : ℕ, w n * Z L omega n ^ ((r : ℝ) / 2)) ^
              (2 / (r : ℝ)) ≤
          (∑' n : ℕ, w n * (D n + R n omega) ^ ((r : ℝ) / 2)) ^
              (2 / (r : ℝ)) :=
      Real.rpow_le_rpow
        (tsum_nonneg fun n => mul_nonneg (hw n) (Real.rpow_nonneg (hZ n) _))
        hsumZR hroot0
    have hpresplit :
        (∑' n : ℕ, w n * (D n + R n omega) ^ ((r : ℝ) / 2)) ≤
          (∑' n : ℕ, w n * D n ^ ((r : ℝ) / 2)) +
            ∑' n : ℕ, w n * R n omega ^ ((r : ℝ) / 2) := by
      have hstep := (htotalSum omega).tsum_le_tsum
        (fun n => by
          calc
            w n * (D n + R n omega) ^ ((r : ℝ) / 2) ≤
                w n * (D n ^ ((r : ℝ) / 2) +
                  R n omega ^ ((r : ℝ) / 2)) :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_add_le_add_rpow (hD n) (hR n omega) ht0 ht1) (hw n)
            _ = w n * D n ^ ((r : ℝ) / 2) +
                w n * R n omega ^ ((r : ℝ) / 2) := by ring_nf)
        (hDqsum.add (hRqsum omega))
      rwa [hDqsum.tsum_add (hRqsum omega)] at hstep
    have hDsum0 : 0 ≤ ∑' n : ℕ, w n * D n ^ ((r : ℝ) / 2) :=
      tsum_nonneg fun n => mul_nonneg (hw n) (Real.rpow_nonneg (hD n) _)
    have hRsum0 : 0 ≤ ∑' n : ℕ, w n * R n omega ^ ((r : ℝ) / 2) :=
      tsum_nonneg fun n => mul_nonneg (hw n) (Real.rpow_nonneg (hR n omega) _)
    have hcombined :
        (∑' n : ℕ, w n * (D n + R n omega) ^ ((r : ℝ) / 2)) ^
              (2 / (r : ℝ)) ≤
          2 * ((∑' n : ℕ, w n * D n ^ ((r : ℝ) / 2)) ^
                (2 / (r : ℝ)) +
              (∑' n : ℕ, w n * R n omega ^ ((r : ℝ) / 2)) ^
                (2 / (r : ℝ))) := by
      calc
        (∑' n : ℕ, w n * (D n + R n omega) ^ ((r : ℝ) / 2)) ^
              (2 / (r : ℝ)) ≤
            ((∑' n : ℕ, w n * D n ^ ((r : ℝ) / 2)) +
              ∑' n : ℕ, w n * R n omega ^ ((r : ℝ) / 2)) ^
                (2 / (r : ℝ)) :=
          Real.rpow_le_rpow
            (tsum_nonneg fun n => mul_nonneg (hw n)
              (Real.rpow_nonneg (add_nonneg (hD n) (hR n omega)) _))
            hpresplit hroot0
        _ ≤ 2 * ((∑' n : ℕ, w n * D n ^ ((r : ℝ) / 2)) ^
                (2 / (r : ℝ)) +
              (∑' n : ℕ, w n * R n omega ^ ((r : ℝ) / 2)) ^
                (2 / (r : ℝ))) :=
          rpow_add_le_two_mul_add_rpow hDsum0 hRsum0 hr1 hr2
    rw [cutoffLowerEllipticityInv_mul_eq_rpow M m L hs rfl hr0 hscaling omega]
    change
      (∑' n : ℕ, w n * Z L omega n ^ ((r : ℝ) / 2)) ^
          (2 / (r : ℝ)) ≤
        8 * Cprof * (s / (2 * s - M.gamma)) ^ (2 / (r : ℝ)) +
          (2 * S ^ (2 / (r : ℝ))) * ∑' n : ℕ, c n * V n omega
    calc
      (∑' n : ℕ, w n * Z L omega n ^ ((r : ℝ) / 2)) ^
            (2 / (r : ℝ)) ≤
          (∑' n : ℕ, w n * (D n + R n omega) ^ ((r : ℝ) / 2)) ^
            (2 / (r : ℝ)) := hZaggregate
      _ ≤ 2 * ((∑' n : ℕ, w n * D n ^ ((r : ℝ) / 2)) ^
              (2 / (r : ℝ)) +
            (∑' n : ℕ, w n * R n omega ^ ((r : ℝ) / 2)) ^
              (2 / (r : ℝ))) := hcombined
      _ ≤ 2 * (4 * Cprof *
              (s / (2 * s - M.gamma)) ^ (2 / (r : ℝ)) +
            S ^ (2 / (r : ℝ)) * ∑' n : ℕ, c n * V n omega) :=
        mul_le_mul_of_nonneg_left
          (add_le_add hDroot (hRroot omega)) (by norm_num)
      _ = 8 * Cprof *
            (s / (2 * s - M.gamma)) ^ (2 / (r : ℝ)) +
          (2 * S ^ (2 / (r : ℝ))) * ∑' n : ℕ, c n * V n omega := by
        ring_nf
  · exact (measurable_tsum_of_nonneg
      (fun n => (hVmeas n).const_mul (c n))
      (fun n omega => mul_nonneg (hc n) (hVnonneg n omega))
      hVlinnorm).const_mul (2 * S ^ (2 / (r : ℝ)))
  · have honesum : Summable fun n : ℕ => c n * (1 : ℝ) := by
      simpa using hcsum
    have honetsum : (∑' n : ℕ, c n * (1 : ℝ)) = 1 := by
      simpa using hctsum
    have hsumO : IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
        (gammaSigma sigmaTail) (fun omega => ∑' n : ℕ, c n * V n omega)
        (gammaTriangleConst sigmaTail) := by
      refine isBigOWith_gammaSigma_tsum_weighted hsigmaTail hcpos hVnonneg hVmeas
        (fun _ => one_pos) honesum hVO ?_
      rw [honetsum]
      simp
    have hfactor : 0 ≤ 2 * S ^ (2 / (r : ℝ)) :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg hSpos.le _)
    exact (IsBigOWith.const_mul hfactor hsumO).mono_scale
      (by simpa [w, S] using hbudget)

/-- The normalized finite-`q < 2` pre-split interface discharges exactly the
`payloadLtTwo` argument of
`coarse_ellipticity_lower_payload_of_branchPayloads`.

The gate `8 * Cprof <= Clow` absorbs the factor four reconciling the exact
geometric profile with the frozen base and the factor two from taking the
convex outer root.  The analytic producer remains explicit in this helper; the
downstream superposed-flux caller supplies the per-depth normalized remainders
and their Orlicz amplitude profile. -/
theorem coarse_ellipticity_lower_branchPayload_lt_two_of_finiteQPresplit
    (d : ℕ) [NeZero d] {Clow Cprof : ℝ} (hCprof : 0 ≤ Cprof)
    (habsorb : 8 * Cprof ≤ Clow)
    (finiteQPresplit :
      ∀ (M : ABKModel d) (m : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        ∀ sigma : ℝ, sigma ∈ Set.Ioc 0 (1 / 2) →
          max (Real.exp (Clow / sigma)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
          (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
          ∀ r : {r : ℝ // 1 ≤ r}, (r : ℝ) < 2 →
            ∀ s : ℝ,
              ∀ hsWindow : s ∈ Set.Icc
                (M.gamma / 2 +
                  Real.exp
                    (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) 1,
              ∃ (V : ℕ → Cutoff.CutoffSample d → ℝ) (a : ℕ → ℝ),
                (∀ n omega, 0 ≤ V n omega) ∧
                (∀ n, Measurable (V n)) ∧
                (∀ n, 0 < a n) ∧
                (Summable fun n : ℕ =>
                  Book.Ch02.geometricWeight s (r : ℝ) n *
                    a n ^ ((r : ℝ) / 2)) ∧
                (∀ omega, Summable fun n : ℕ =>
                  Book.Ch02.geometricWeight s (r : ℝ) n *
                    a n ^ ((r : ℝ) / 2) * V n omega) ∧
                (∀ n, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
                  (gammaSigma ((1 - sigma) / 2)) (V n) 1) ∧
                ((2 * (∑' n : ℕ,
                    Book.Ch02.geometricWeight s (r : ℝ) n *
                      a n ^ ((r : ℝ) / 2)) ^ (2 / (r : ℝ))) *
                    gammaTriangleConst ((1 - sigma) / 2) ≤
                  Real.exp
                    (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) ∧
                (∀ omega, ∀ L : ℤ, m - 1 ≤ L → ∀ n : ℕ,
                  (Annealed.sigmaBar M (m - 1) : ℝ) *
                      Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
                        (originCube d m) (m - (n : ℤ))
                        (Cutoff.coefficientCutoff M.nu L omega) ≤
                    finiteQGeometricProfile Cprof M.gamma n +
                      a n * V n omega)) :
      ∀ (M : ABKModel d) (m : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        ∀ sigma : ℝ, sigma ∈ Set.Ioc 0 (1 / 2) →
          max (Real.exp (Clow / sigma)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
          (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
          ∀ r : {r : ℝ // 1 ≤ r}, (r : ℝ) < 2 →
            ∀ s : ℝ,
              ∀ hsWindow : s ∈ Set.Icc
                (M.gamma / 2 +
                  Real.exp
                    (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) 1,
              ∃ Ydet Y : Cutoff.CutoffSample d → ℝ,
                (∀ omega, ∀ L : ℤ, m - 1 ≤ L →
                    Observable.cutoffLowerEllipticityInv
                          M m L s
                          (by
                            exact
                              (add_pos
                                (div_pos M.shellPrefix.gamma_pos (by norm_num))
                              (Real.exp_pos
                                (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 *
                                    M.gamma⁻¹)))).trans_le hsWindow.1)
                          (CoarseEllipticityExponent.finite r) omega *
                        (Annealed.sigmaBar M (m - 1) : ℝ) ≤
                      Ydet omega + Y omega) ∧
                (∀ omega, Ydet omega ≤
                  Clow * Real.rpow (s / (2 * s - M.gamma))
                    (2 / (r : ℝ))) ∧
                Measurable Y ∧
                IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
                  (gammaSigma ((1 - sigma) / 2)) Y
                  (Real.exp
                    (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) := by
  intro M m E hstate sigma hsigma hE1 hE2 r hr s hsWindow
  obtain ⟨V, a, hVnonneg, hVmeas, ha, hasum, hVlinsum, hVO, hbudget,
    hdepth⟩ :=
    finiteQPresplit M m E hstate sigma hsigma hE1 hE2 r hr s hsWindow
  have hexppos : (0 : ℝ) <
      Real.exp (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) :=
    Real.exp_pos _
  have hwin : M.gamma / 2 +
      Real.exp (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤ s :=
    hsWindow.1
  have hs : (0 : ℝ) < s := by
    linarith [M.shellPrefix.gamma_pos]
  have hgap : (0 : ℝ) < 2 * s - M.gamma := by
    linarith
  have hsigmaTail : (0 : ℝ) < (1 - sigma) / 2 := by
    linarith [hsigma.2]
  obtain ⟨Ydet, Y, hdom, hdet, hYmeas, htail⟩ :=
    twoTermFamilySplit_cutoffLowerEllipticityInv_of_finiteQLtTwoPresplit
      M m r hr hs hgap hCprof (Annealed.sigmaBar M (m - 1)).2.le
      hsigmaTail hVnonneg hVmeas ha hasum hVlinsum hVO hbudget hdepth
  refine ⟨Ydet, Y, hdom, ?_, hYmeas, htail⟩
  intro omega
  have hfactor : (0 : ℝ) ≤
      (s / (2 * s - M.gamma)) ^ (2 / (r : ℝ)) :=
    Real.rpow_nonneg (div_nonneg hs.le hgap.le) _
  calc
    Ydet omega ≤
        8 * Cprof * (s / (2 * s - M.gamma)) ^ (2 / (r : ℝ)) :=
      hdet omega
    _ = (8 * Cprof) *
        (s / (2 * s - M.gamma)) ^ (2 / (r : ℝ)) := by ring_nf
    _ ≤ Clow * (s / (2 * s - M.gamma)) ^ (2 / (r : ℝ)) :=
      mul_le_mul_of_nonneg_right habsorb hfactor

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
