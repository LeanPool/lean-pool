/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.FiniteQLtTwoPresplit

/-!
# UpperFiniteQLtTwo

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Finite upper coarse ellipticity below exponent two

This module keeps the finite upper observable in its defining weighted
`ell^(q / 2)` aggregate when `1 <= q < 2`.  At that exponent the inner power
is concave, while the outer power is convex.  Each random depth remainder is
therefore normalized by its own deterministic amplitude before countable
weak-Orlicz summation.  In particular, no comparison between a finite carrier
and the `q = infinity` carrier is used.

The final theorem accepts an almost-everywhere per-depth split of the actual
Chapter 4 descendant maximum into a deterministic profile and two normalized
random lanes.  It returns the everywhere-defined three-term witness consumed
by `UpperLeg.lean`; the null-set defect is absorbed inside the ordinary lane.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## The exact finite upper carrier -/

/-- The Chapter 4 finite upper ellipticity is its defining weighted
`ell^(q / 2)` aggregate, including the totalized non-elliptic branch. -/
theorem LambdaSqCoeffField_finite_eq_rpow (Q : TriadicCube d)
    (a : RegCoeffField d) (s : ℝ) {q : ℝ} (hq : 0 < q) :
    Book.Ch04.LambdaSqCoeffField Q s (.finite q) a =
      (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
        Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q
            (Q.scale - (n : ℤ)) a ^ (q / 2)) ^ (2 / q) := by
  classical
  by_cases ha : Book.Ch04.AELocallyUniformlyEllipticField a
  · simp only [Book.Ch04.LambdaSqCoeffField,
      Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale, ha, dite_eq_left,
      Book.Ch02.LambdaSq_finite, Book.Ch02.LambdaSqFinite]
    rfl
  · simp [Book.Ch04.LambdaSqCoeffField,
      Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale, ha,
      Real.zero_rpow (by positivity : q / 2 ≠ 0),
      Real.zero_rpow (by positivity : 2 / q ≠ 0)]

/-- Multiplication of the exported finite upper observable by a nonnegative
scalar can be moved inside every depth before taking the outer root. -/
theorem cutoffUpperEllipticity_mul_eq_rpow (M : ABKModel d)
    (m L : ℤ) {s r : ℝ} (hs : 0 < s) {q : CoarseEllipticityExponent}
    (hqval : q.1 = Book.Ch02.MultiscaleExponent.finite r) (hr : 0 < r)
    {scaling : ℝ} (hscaling : 0 ≤ scaling) (omega : Cutoff.CutoffSample d) :
    Observable.cutoffUpperEllipticity M m L s hs q omega * scaling =
      (∑' n : ℕ, Book.Ch02.geometricWeight s r n *
        (scaling *
          Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
            (originCube d m) (m - (n : ℤ))
            (Cutoff.coefficientCutoff M.nu L omega)) ^ (r / 2)) ^ (2 / r) := by
  let a : RegCoeffField d := Cutoff.coefficientCutoff M.nu L omega
  let H : ℕ → ℝ := fun n =>
    Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
      (originCube d m) (m - (n : ℤ)) a
  have hscale : (originCube d m).scale = m := rfl
  have hsr : 0 ≤ s * r := (mul_pos hs hr).le
  have hH : ∀ n, 0 ≤ H n := by
    intro n
    exact Book.Ch05.Section52.maxDescendantBMatrixNormCoeffFieldAtScale_nonneg_of_le
      (originCube d m) a (by rw [hscale]; omega)
  have hS : 0 ≤ ∑' n : ℕ,
      Book.Ch02.geometricWeight s r n * H n ^ (r / 2) :=
    tsum_nonneg fun n => mul_nonneg (geometricWeight_nonneg' hsr n)
      (Real.rpow_nonneg (hH n) _)
  have hseries :
      (∑' n : ℕ, Book.Ch02.geometricWeight s r n *
          (scaling * H n) ^ (r / 2)) =
        scaling ^ (r / 2) *
          ∑' n : ℕ, Book.Ch02.geometricWeight s r n * H n ^ (r / 2) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [Real.mul_rpow hscaling (hH n)]
    ring
  have hcancel : r / 2 * (2 / r) = 1 := by
    field_simp
  rw [congrFun (Observable.cutoffUpperEllipticity_eq_literal M m L s hs q) omega,
    cutoffUpperEllipticityLiteral_eq_coeffField, hqval,
    LambdaSqCoeffField_finite_eq_rpow (q := r) (originCube d m) a s hr]
  change
    (∑' n : ℕ, Book.Ch02.geometricWeight s r n * H n ^ (r / 2)) ^ (2 / r) *
        scaling =
      (∑' n : ℕ, Book.Ch02.geometricWeight s r n *
        (scaling * H n) ^ (r / 2)) ^ (2 / r)
  rw [hseries, Real.mul_rpow (Real.rpow_nonneg hscaling _) hS,
    ← Real.rpow_mul hscaling, hcancel, Real.rpow_one]
  ring

/-! ## A normalized random lane -/

/-- A normalized family of nonnegative depth remainders produces one
measurable weak-Orlicz lane.  The returned summability clause is the exact
input needed to combine several such lanes before taking the outer root. -/
theorem exists_normalized_finite_q_lt_two_lane
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsFiniteMeasure mu] {r sigma K B : ℝ} {w a : ℕ → ℝ}
    {V : ℕ → Omega → ℝ}
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (hsigma : 0 < sigma)
    (hw : ∀ n, 0 < w n) (ha : ∀ n, 0 < a n)
    (hVnonneg : ∀ n omega, 0 ≤ V n omega)
    (hVmeas : ∀ n, Measurable (V n))
    (hasum : Summable fun n : ℕ => w n * a n ^ (r / 2))
    (hVlinsum : ∀ omega, Summable fun n : ℕ =>
      w n * a n ^ (r / 2) * V n omega)
    (hVO : ∀ n, IsBigOWith mu (gammaSigma sigma) (V n) 1)
    (hK : 0 ≤ K)
    (hbudget :
      (K * (∑' n : ℕ, w n * a n ^ (r / 2)) ^ (2 / r)) *
          gammaTriangleConst sigma ≤ B) :
    ∃ Y : Omega → ℝ,
      (∀ omega, Summable fun n : ℕ =>
        w n * (a n * V n omega) ^ (r / 2)) ∧
      Measurable Y ∧
      IsBigOWith mu (gammaSigma sigma) Y B ∧
      ∀ omega,
        K * (∑' n : ℕ, w n * (a n * V n omega) ^ (r / 2)) ^ (2 / r) ≤
          Y omega := by
  let S : ℝ := ∑' n : ℕ, w n * a n ^ (r / 2)
  let c : ℕ → ℝ := fun n => S⁻¹ * (w n * a n ^ (r / 2))
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have ht0 : 0 ≤ r / 2 := by positivity
  have ht1 : r / 2 ≤ 1 := by linarith
  have hSpos : 0 < S := by
    have hterm : 0 < w 0 * a 0 ^ (r / 2) :=
      mul_pos (hw 0) (Real.rpow_pos_of_pos (ha 0) _)
    have hterm_le : w 0 * a 0 ^ (r / 2) ≤ S := by
      dsimp [S]
      have hfinite := hasum.sum_le_tsum {0} fun n _hn =>
        mul_nonneg (hw n).le (Real.rpow_nonneg (ha n).le _)
      simpa using hfinite
    exact hterm.trans_le hterm_le
  have hcpos : ∀ n, 0 < c n := fun n =>
    mul_pos (inv_pos.mpr hSpos)
      (mul_pos (hw n) (Real.rpow_pos_of_pos (ha n) _))
  have hc : ∀ n, 0 ≤ c n := fun n => (hcpos n).le
  have hcsum : Summable c := by
    simpa [c] using hasum.mul_left S⁻¹
  have hctsum : (∑' n : ℕ, c n) = 1 := by
    change (∑' n : ℕ, S⁻¹ * (w n * a n ^ (r / 2))) = 1
    rw [tsum_mul_left]
    change S⁻¹ * S = 1
    exact inv_mul_cancel₀ hSpos.ne'
  have hVqweighted : ∀ omega, Summable fun n : ℕ =>
      w n * a n ^ (r / 2) * V n omega ^ (r / 2) := by
    intro omega
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg
        (mul_nonneg (hw n).le (Real.rpow_nonneg (ha n).le _))
        (Real.rpow_nonneg (hVnonneg n omega) _))
      (fun n => ?_) (hasum.add (hVlinsum omega))
    have hpower : V n omega ^ (r / 2) ≤ 1 + V n omega := by
      by_cases hVone : V n omega ≤ 1
      · calc
          V n omega ^ (r / 2) ≤ (1 : ℝ) ^ (r / 2) :=
            Real.rpow_le_rpow (hVnonneg n omega) hVone ht0
          _ = 1 := Real.one_rpow _
          _ ≤ 1 + V n omega := by linarith [hVnonneg n omega]
      · have hle : V n omega ^ (r / 2) ≤ V n omega :=
          Real.rpow_le_self_of_one_le (le_of_not_ge hVone) ht1
        linarith
    calc
      w n * a n ^ (r / 2) * V n omega ^ (r / 2) ≤
          w n * a n ^ (r / 2) * (1 + V n omega) :=
        mul_le_mul_of_nonneg_left hpower
          (mul_nonneg (hw n).le (Real.rpow_nonneg (ha n).le _))
      _ = w n * a n ^ (r / 2) +
          w n * a n ^ (r / 2) * V n omega := by ring
  have hRqsum : ∀ omega, Summable fun n : ℕ =>
      w n * (a n * V n omega) ^ (r / 2) := by
    intro omega
    refine (hVqweighted omega).congr fun n => ?_
    rw [Real.mul_rpow (ha n).le (hVnonneg n omega)]
    ring
  have hVqnorm : ∀ omega, Summable fun n : ℕ =>
      c n * V n omega ^ (r / 2) := by
    intro omega
    simpa [c, mul_assoc] using (hVqweighted omega).mul_left S⁻¹
  have hVlinnorm : ∀ omega, Summable fun n : ℕ => c n * V n omega := by
    intro omega
    simpa [c, mul_assoc] using (hVlinsum omega).mul_left S⁻¹
  have hRseries : ∀ omega,
      (∑' n : ℕ, w n * (a n * V n omega) ^ (r / 2)) =
        S * ∑' n : ℕ, c n * V n omega ^ (r / 2) := by
    intro omega
    calc
      (∑' n : ℕ, w n * (a n * V n omega) ^ (r / 2)) =
          ∑' n : ℕ, w n * a n ^ (r / 2) * V n omega ^ (r / 2) := by
        refine tsum_congr fun n => ?_
        rw [Real.mul_rpow (ha n).le (hVnonneg n omega)]
        ring
      _ = S * ∑' n : ℕ, c n * V n omega ^ (r / 2) := by
        rw [← tsum_mul_left]
        refine tsum_congr fun n => ?_
        dsimp [c]
        calc
          w n * a n ^ (r / 2) * V n omega ^ (r / 2) =
              1 * (w n * a n ^ (r / 2)) * V n omega ^ (r / 2) := by ring
          _ = (S * S⁻¹) * (w n * a n ^ (r / 2)) *
                V n omega ^ (r / 2) := by
            rw [mul_inv_cancel₀ hSpos.ne']
          _ = S * (S⁻¹ * (w n * a n ^ (r / 2)) *
                V n omega ^ (r / 2)) := by ring
  have hRroot : ∀ omega,
      (∑' n : ℕ, w n * (a n * V n omega) ^ (r / 2)) ^ (2 / r) ≤
        S ^ (2 / r) * ∑' n : ℕ, c n * V n omega := by
    intro omega
    have hqsum0 : 0 ≤ ∑' n : ℕ, c n * V n omega ^ (r / 2) :=
      tsum_nonneg fun n => mul_nonneg (hc n)
        (Real.rpow_nonneg (hVnonneg n omega) _)
    have hjensen := tsum_weighted_rpow_root_le_of_one_le_of_le_two
      hr1 hr2 hc (fun n => hVnonneg n omega) hcsum hctsum.le
      (hVlinnorm omega) (hVqnorm omega)
    rw [hRseries omega, Real.mul_rpow hSpos.le hqsum0]
    exact mul_le_mul_of_nonneg_left hjensen (Real.rpow_nonneg hSpos.le _)
  let Y : Omega → ℝ := fun omega =>
    (K * S ^ (2 / r)) * ∑' n : ℕ, c n * V n omega
  refine ⟨Y, hRqsum, ?_, ?_, ?_⟩
  · exact (Measurable.tsum (L := SummationFilter.unconditional ℕ)
      (fun n => (hVmeas n).const_mul (c n))).const_mul (K * S ^ (2 / r))
  · have honesum : Summable fun n : ℕ => c n * (1 : ℝ) := by
      simpa using hcsum
    have honetsum : (∑' n : ℕ, c n * (1 : ℝ)) = 1 := by
      simpa using hctsum
    have hsumO : IsBigOWith mu (gammaSigma sigma)
        (fun omega => ∑' n : ℕ, c n * V n omega)
        (gammaTriangleConst sigma) := by
      refine isBigOWith_gammaSigma_tsum_weighted hsigma hcpos hVnonneg hVmeas
        (fun _ => one_pos) honesum hVO ?_
      rw [honetsum]
      simp
    have hfactor : 0 ≤ K * S ^ (2 / r) :=
      mul_nonneg hK (Real.rpow_nonneg hSpos.le _)
    exact (IsBigOWith.const_mul hfactor hsumO).mono_scale (by
      simpa [S] using hbudget)
  · intro omega
    dsimp [Y]
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left (hRroot omega) hK

private theorem rpow_three_le_four_mul_sum {x y z r : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2) :
    (x + y + z) ^ (2 / r) ≤
      4 * (x ^ (2 / r) + y ^ (2 / r) + z ^ (2 / r)) := by
  have hxy : 0 ≤ x + y := add_nonneg hx hy
  have hfirst := rpow_add_le_two_mul_add_rpow hxy hz hr1 hr2
  have hsecond := rpow_add_le_two_mul_add_rpow hx hy hr1 hr2
  calc
    (x + y + z) ^ (2 / r) ≤
        2 * ((x + y) ^ (2 / r) + z ^ (2 / r)) := hfirst
    _ ≤ 2 * (2 * (x ^ (2 / r) + y ^ (2 / r)) + z ^ (2 / r)) := by
      gcongr
    _ ≤ 4 * (x ^ (2 / r) + y ^ (2 / r) + z ^ (2 / r)) := by
      have hxpow := Real.rpow_nonneg hx (2 / r)
      have hypow := Real.rpow_nonneg hy (2 / r)
      have hzpow := Real.rpow_nonneg hz (2 / r)
      linarith

/-! ## The actual upper observable -/

/-- An almost-everywhere normalized per-depth split of the actual finite upper
carrier yields the everywhere three-term witness required by the upper leg.
The factor four is the uniform convexity loss for the three outer-root slots
when `1 <= q < 2`. -/
theorem threeTermSplit_cutoffUpperEllipticity_of_finiteQLtTwoPresplit (M : ABKModel d) (m L : ℤ)
    (r : {r : ℝ // 1 ≤ r}) (hr : (r : ℝ) < 2)
    {s scaling Bdet B1 Bexp sigma1 sigmaExp : ℝ} (hs : 0 < s)
    (hscaling : 0 ≤ scaling) (hsigma1 : 0 < sigma1)
    (hsigmaExp : 0 < sigmaExp)
    {D a1 aexp : ℕ → ℝ}
    {Vone Vexp : ℕ → Cutoff.CutoffSample d → ℝ}
    (hD : ∀ n, 0 ≤ D n) (ha1 : ∀ n, 0 < a1 n)
    (haexp : ∀ n, 0 < aexp n)
    (hVoneNonneg : ∀ n omega, 0 ≤ Vone n omega)
    (hVexpNonneg : ∀ n omega, 0 ≤ Vexp n omega)
    (hVoneMeas : ∀ n, Measurable (Vone n))
    (hVexpMeas : ∀ n, Measurable (Vexp n))
    (hDsum : Summable fun n : ℕ =>
      Book.Ch02.geometricWeight s (r : ℝ) n * D n ^ ((r : ℝ) / 2))
    (ha1sum : Summable fun n : ℕ =>
      Book.Ch02.geometricWeight s (r : ℝ) n * a1 n ^ ((r : ℝ) / 2))
    (haexpsum : Summable fun n : ℕ =>
      Book.Ch02.geometricWeight s (r : ℝ) n * aexp n ^ ((r : ℝ) / 2))
    (hVoneLinSum : ∀ omega, Summable fun n : ℕ =>
      Book.Ch02.geometricWeight s (r : ℝ) n * a1 n ^ ((r : ℝ) / 2) *
        Vone n omega)
    (hVexpLinSum : ∀ omega, Summable fun n : ℕ =>
      Book.Ch02.geometricWeight s (r : ℝ) n * aexp n ^ ((r : ℝ) / 2) *
        Vexp n omega)
    (hVoneO : ∀ n, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma sigma1) (Vone n) 1)
    (hVexpO : ∀ n, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma sigmaExp) (Vexp n) 1)
    (hdetBudget :
      4 * (∑' n : ℕ, Book.Ch02.geometricWeight s (r : ℝ) n *
          D n ^ ((r : ℝ) / 2)) ^ (2 / (r : ℝ)) ≤ Bdet)
    (honeBudget :
      (4 * (∑' n : ℕ, Book.Ch02.geometricWeight s (r : ℝ) n *
          a1 n ^ ((r : ℝ) / 2)) ^ (2 / (r : ℝ))) *
          gammaTriangleConst sigma1 ≤ B1)
    (hexpBudget :
      (4 * (∑' n : ℕ, Book.Ch02.geometricWeight s (r : ℝ) n *
          aexp n ^ ((r : ℝ) / 2)) ^ (2 / (r : ℝ))) *
          gammaTriangleConst sigmaExp ≤ Bexp)
    (hdepth : ∀ n : ℕ, ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      scaling *
          Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
            (originCube d m) (m - (n : ℤ))
            (Cutoff.coefficientCutoff M.nu L omega) ≤
        D n + a1 n * Vone n omega + aexp n * Vexp n omega) :
    ∃ Udet Uone Utail : Cutoff.CutoffSample d → ℝ,
      (∀ omega,
        Observable.cutoffUpperEllipticity M m L s hs
              (CoarseEllipticityExponent.finite r) omega * scaling ≤
          Udet omega + Uone omega + Utail omega) ∧
      (∀ omega, Udet omega ≤ Bdet) ∧
      Measurable Uone ∧ Measurable Utail ∧
      IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
        (gammaSigma sigma1) Uone B1 ∧
      IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
        (gammaSigma sigmaExp) Utail Bexp := by
  let w : ℕ → ℝ := fun n => Book.Ch02.geometricWeight s (r : ℝ) n
  let Rone : ℕ → Cutoff.CutoffSample d → ℝ := fun n omega => a1 n * Vone n omega
  let Rexp : ℕ → Cutoff.CutoffSample d → ℝ := fun n omega => aexp n * Vexp n omega
  let Z : ℕ → Cutoff.CutoffSample d → ℝ := fun n omega =>
    scaling *
      Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
        (originCube d m) (m - (n : ℤ))
        (Cutoff.coefficientCutoff M.nu L omega)
  have hr0 : (0 : ℝ) < (r : ℝ) :=
    lt_of_lt_of_le zero_lt_one r.property
  have hr2 : (r : ℝ) ≤ 2 := hr.le
  have ht0 : (0 : ℝ) ≤ (r : ℝ) / 2 := by positivity
  have ht1 : (r : ℝ) / 2 ≤ 1 := by linarith
  have hroot0 : (0 : ℝ) ≤ 2 / (r : ℝ) := by positivity
  have hsr : (0 : ℝ) < s * (r : ℝ) := mul_pos hs hr0
  have hwpos : ∀ n, 0 < w n := fun n =>
    HCPolySupport.geometricWeight_pos n hsr
  obtain ⟨Yone, hRoneSum, hYoneMeas, hYoneO, hYoneDom⟩ :=
    exists_normalized_finite_q_lt_two_lane
      (mu := (Cutoff.cutoffSampleLaw M).toMeasure) r.property hr2 hsigma1
      hwpos ha1 hVoneNonneg hVoneMeas (by simpa [w] using ha1sum)
      (by intro omega; simpa [w] using hVoneLinSum omega) hVoneO
      (by norm_num : (0 : ℝ) ≤ 4) (by simpa [w] using honeBudget)
  obtain ⟨Yexp, hRexpSum, hYexpMeas, hYexpO, hYexpDom⟩ :=
    exists_normalized_finite_q_lt_two_lane
      (mu := (Cutoff.cutoffSampleLaw M).toMeasure) r.property hr2 hsigmaExp
      hwpos haexp hVexpNonneg hVexpMeas (by simpa [w] using haexpsum)
      (by intro omega; simpa [w] using hVexpLinSum omega) hVexpO
      (by norm_num : (0 : ℝ) ≤ 4) (by simpa [w] using hexpBudget)
  have hdepthAll : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ n, Z n omega ≤
      D n + Rone n omega + Rexp n omega := by
    rw [ae_all_iff]
    intro n
    simpa [Z, Rone, Rexp] using hdepth n
  have hDsum' : Summable fun n : ℕ => w n * D n ^ ((r : ℝ) / 2) := by
    simpa [w] using hDsum
  have hae : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Observable.cutoffUpperEllipticity M m L s hs
            (CoarseEllipticityExponent.finite r) omega * scaling ≤
        Bdet + Yone omega + Yexp omega := by
    filter_upwards [hdepthAll] with omega homega
    have hscale : (originCube d m).scale = m := rfl
    have hZ : ∀ n, 0 ≤ Z n omega := by
      intro n
      refine mul_nonneg hscaling ?_
      exact Book.Ch05.Section52.maxDescendantBMatrixNormCoeffFieldAtScale_nonneg_of_le
        (originCube d m) (Cutoff.coefficientCutoff M.nu L omega)
        (by rw [hscale]; omega)
    have hRone : ∀ n, 0 ≤ Rone n omega := fun n =>
      mul_nonneg (ha1 n).le (hVoneNonneg n omega)
    have hRexp : ∀ n, 0 ≤ Rexp n omega := fun n =>
      mul_nonneg (haexp n).le (hVexpNonneg n omega)
    have hw : ∀ n, 0 ≤ w n := fun n => (hwpos n).le
    have hRoneSum' : Summable fun n : ℕ =>
        w n * Rone n omega ^ ((r : ℝ) / 2) := by
      simpa [Rone] using hRoneSum omega
    have hRexpSum' : Summable fun n : ℕ =>
        w n * Rexp n omega ^ ((r : ℝ) / 2) := by
      simpa [Rexp] using hRexpSum omega
    have htotalSum : Summable fun n : ℕ =>
        w n * (D n + Rone n omega + Rexp n omega) ^ ((r : ℝ) / 2) := by
      refine Summable.of_nonneg_of_le
        (fun n => mul_nonneg (hw n)
          (Real.rpow_nonneg (add_nonneg (add_nonneg (hD n) (hRone n)) (hRexp n)) _))
        (fun n => ?_)
        ((hDsum'.add hRoneSum').add hRexpSum')
      have hfirst : (D n + Rone n omega + Rexp n omega) ^ ((r : ℝ) / 2) ≤
          (D n + Rone n omega) ^ ((r : ℝ) / 2) +
            Rexp n omega ^ ((r : ℝ) / 2) :=
        Real.rpow_add_le_add_rpow (add_nonneg (hD n) (hRone n)) (hRexp n) ht0 ht1
      have hsecond : (D n + Rone n omega) ^ ((r : ℝ) / 2) ≤
          D n ^ ((r : ℝ) / 2) + Rone n omega ^ ((r : ℝ) / 2) :=
        Real.rpow_add_le_add_rpow (hD n) (hRone n) ht0 ht1
      have hpower : (D n + Rone n omega + Rexp n omega) ^ ((r : ℝ) / 2) ≤
          D n ^ ((r : ℝ) / 2) + Rone n omega ^ ((r : ℝ) / 2) +
            Rexp n omega ^ ((r : ℝ) / 2) :=
        hfirst.trans (add_le_add hsecond le_rfl)
      calc
        w n * (D n + Rone n omega + Rexp n omega) ^ ((r : ℝ) / 2) ≤
            w n * (D n ^ ((r : ℝ) / 2) + Rone n omega ^ ((r : ℝ) / 2) +
              Rexp n omega ^ ((r : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left hpower (hw n)
        _ = w n * D n ^ ((r : ℝ) / 2) +
            w n * Rone n omega ^ ((r : ℝ) / 2) +
            w n * Rexp n omega ^ ((r : ℝ) / 2) := by ring
    have hZsum : Summable fun n : ℕ => w n * Z n omega ^ ((r : ℝ) / 2) := by
      refine Summable.of_nonneg_of_le
        (fun n => mul_nonneg (hw n) (Real.rpow_nonneg (hZ n) _))
        (fun n => mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (hZ n) (homega n) ht0) (hw n))
        htotalSum
    have hsumMajor :
        (∑' n : ℕ, w n * Z n omega ^ ((r : ℝ) / 2)) ≤
          (∑' n : ℕ, w n * D n ^ ((r : ℝ) / 2)) +
          (∑' n : ℕ, w n * Rone n omega ^ ((r : ℝ) / 2)) +
          (∑' n : ℕ, w n * Rexp n omega ^ ((r : ℝ) / 2)) := by
      have hterm : ∀ n,
          w n * Z n omega ^ ((r : ℝ) / 2) ≤
            w n * D n ^ ((r : ℝ) / 2) +
            w n * Rone n omega ^ ((r : ℝ) / 2) +
            w n * Rexp n omega ^ ((r : ℝ) / 2) := by
        intro n
        have hfirst : (D n + Rone n omega + Rexp n omega) ^ ((r : ℝ) / 2) ≤
            (D n + Rone n omega) ^ ((r : ℝ) / 2) +
              Rexp n omega ^ ((r : ℝ) / 2) :=
          Real.rpow_add_le_add_rpow (add_nonneg (hD n) (hRone n)) (hRexp n) ht0 ht1
        have hsecond : (D n + Rone n omega) ^ ((r : ℝ) / 2) ≤
            D n ^ ((r : ℝ) / 2) + Rone n omega ^ ((r : ℝ) / 2) :=
          Real.rpow_add_le_add_rpow (hD n) (hRone n) ht0 ht1
        have hpower : (D n + Rone n omega + Rexp n omega) ^ ((r : ℝ) / 2) ≤
            D n ^ ((r : ℝ) / 2) + Rone n omega ^ ((r : ℝ) / 2) +
              Rexp n omega ^ ((r : ℝ) / 2) :=
          hfirst.trans (add_le_add hsecond le_rfl)
        calc
          w n * Z n omega ^ ((r : ℝ) / 2) ≤
              w n * (D n + Rone n omega + Rexp n omega) ^ ((r : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (hZ n) (homega n) ht0) (hw n)
          _ ≤ w n * (D n ^ ((r : ℝ) / 2) + Rone n omega ^ ((r : ℝ) / 2) +
                Rexp n omega ^ ((r : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left hpower (hw n)
          _ = _ := by ring
      have hmajorSum : Summable fun n : ℕ =>
          w n * D n ^ ((r : ℝ) / 2) + w n * Rone n omega ^ ((r : ℝ) / 2) +
            w n * Rexp n omega ^ ((r : ℝ) / 2) :=
        ((hDsum'.add hRoneSum').add hRexpSum')
      have hle := hZsum.tsum_le_tsum hterm hmajorSum
      rw [(hDsum'.add hRoneSum').tsum_add hRexpSum',
        hDsum'.tsum_add hRoneSum'] at hle
      exact hle
    have hDsum0 : 0 ≤ ∑' n : ℕ, w n * D n ^ ((r : ℝ) / 2) :=
      tsum_nonneg fun n => mul_nonneg (hw n) (Real.rpow_nonneg (hD n) _)
    have hRoneSum0 : 0 ≤ ∑' n : ℕ, w n * Rone n omega ^ ((r : ℝ) / 2) :=
      tsum_nonneg fun n => mul_nonneg (hw n) (Real.rpow_nonneg (hRone n) _)
    have hRexpSum0 : 0 ≤ ∑' n : ℕ, w n * Rexp n omega ^ ((r : ℝ) / 2) :=
      tsum_nonneg fun n => mul_nonneg (hw n) (Real.rpow_nonneg (hRexp n) _)
    rw [cutoffUpperEllipticity_mul_eq_rpow M m L hs rfl hr0 hscaling omega]
    change (∑' n : ℕ, w n * Z n omega ^ ((r : ℝ) / 2)) ^ (2 / (r : ℝ)) ≤
      Bdet + Yone omega + Yexp omega
    calc
      (∑' n : ℕ, w n * Z n omega ^ ((r : ℝ) / 2)) ^ (2 / (r : ℝ)) ≤
          ((∑' n : ℕ, w n * D n ^ ((r : ℝ) / 2)) +
            (∑' n : ℕ, w n * Rone n omega ^ ((r : ℝ) / 2)) +
            (∑' n : ℕ, w n * Rexp n omega ^ ((r : ℝ) / 2))) ^
              (2 / (r : ℝ)) :=
        Real.rpow_le_rpow
          (tsum_nonneg fun n => mul_nonneg (hw n) (Real.rpow_nonneg (hZ n) _))
          hsumMajor hroot0
      _ ≤ 4 * ((∑' n : ℕ, w n * D n ^ ((r : ℝ) / 2)) ^ (2 / (r : ℝ)) +
            (∑' n : ℕ, w n * Rone n omega ^ ((r : ℝ) / 2)) ^ (2 / (r : ℝ)) +
            (∑' n : ℕ, w n * Rexp n omega ^ ((r : ℝ) / 2)) ^ (2 / (r : ℝ))) :=
        rpow_three_le_four_mul_sum hDsum0 hRoneSum0 hRexpSum0 r.property hr2
      _ ≤ Bdet + Yone omega + Yexp omega := by
        have h1 := hYoneDom omega
        have h2 := hYexpDom omega
        linarith
  exact exists_pointwise_of_ae_threeTermSplit
    ((Observable.measurable_cutoffUpperEllipticity M m L s hs
      (CoarseEllipticityExponent.finite r)).mul_const scaling)
    hYoneMeas hYexpMeas hYoneO hYexpO hae

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
