/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.JCarrierRescale

/-!
# LambdaSensitivityTwin

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The `lambda`-sensitivity twin of the response-`J` switch

`LambdaTransfer.lean` proves the frozen `lambda`-sensitivity switch on the good
local event, and `ResponseCongruence.lean` proves the identification

```
unitCubeLambda s q (perturbCoeffOn (square_0) (a_n rescaled) (k_L - k_n) 1)
  =  unitCubeLambda s q (a_L rescaled) .
```

Composing the two turns the frozen conclusion, which is stated about the
*perturbed* coefficient object, into the manuscript's own statement about the
honest field `a_L`.  That is what the localization consumer of ABK26 reads:

```
lambda^{-1}_{1/8,2}(z + square_l; a_m) 1_{Q(l,l-h,z)}
   <= 2 lambda^{-1}_{1/8,2}(z + square_l; a_{l-h}) 1_{Q(l,l-h,z)} ,
```

the factor `2` being the manuscript's rendering of `(1 + C |grad(k_m - k_{l-h})|
lambda^{-1}_{3/8,2})` under the good event.  This module keeps the factor
explicit rather than relaxing it to `2`, so nothing is lost.

## The bad-event half, and why it is here

The mirror is exact: the threshold `delta_osc` is normalized against
`sensitivityConstMax`, which dominates *both* frozen constants
(`DeltaOsc.lean`), so the same constant chain `2^{-9} . 10 < 1` holds with
`lambdaSensitivityConst` in place of `responseSensitivityConst`.

## Main results

* `unitCubeLambda_inv_le_of_mem_goodLocalEvent_ae`,
  `lambdaSq_inv_le_of_mem_goodLocalEvent_ae`: **the twin** — the good-event
  `lambda`-switch read at the honest field `a_L`, at the unit-cube carrier and
  at the manuscript's cube carrier.
* `oscThreshold_le_two_pow_neg_nine_mul_inv_lambdaSensitivityConst_mul_sigmaBar`,
  `gradientW1Infinity_incrementUnitCube_le_lambdaGate_notMem_bad_ae`: the
  `lambda`-constant mirror of the `e.we.can.apply.cg` chain.

## References

* ABK26 (the localization consumer).
* ABK26 (`p.bfA.multiscalebound`, Step 1).
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents

noncomputable section

variable {d : ℕ}

/-! ## The twin on the good local event -/

/-- **The `lambda`-sensitivity twin** (ABK26).  On the good local event `Q(m, n,
z)`, the multiscale lower ellipticity of the *later* field `a_L` is comparable
to that of `a_n`, at the unit-cube carrier:

```
lambda^{-1}_{s,q}(a_L rescaled)
  <= (1 + C |grad(k_L - k_n)| lambda^{-1}_{3/8,2}(a_n rescaled))
       lambda^{-1}_{s,q}(a_n rescaled) .
```

This is the frozen `lambda`-sensitivity conclusion of `LambdaTransfer.lean` with
its perturbed carrier rewritten as the honest rescaled `a_L`, exactly as
`responseJ_le_of_notMem_bad_ae` does on the response side. -/
theorem unitCubeLambda_inv_le_of_mem_goodLocalEvent_ae (M : ABKModel d) (Ccg : ℝ)
    (Q : TriadicCube d) {n L : ℤ} (hL : n ≤ L) (s : ℝ)
    (q : Ch02.MultiscaleExponent) (hs : 0 < s) (hs2 : s ≤ 1 / 2)
    (hq : q.IsAdmissible) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∈ goodLocalEvent M Ccg Q n →
        (unitCubeLambda s q (unitRescaledCutoffCoeff M Q L omega))⁻¹
          ≤ (1 + lambdaSensitivityConst d *
              (incrementUnitCube₂ Q n L omega).gradientW1Infinity *
              (unitCubeLambda (3 / 8) (.finite 2)
                (unitRescaledCutoffCoeff M Q n omega))⁻¹) *
            (unitCubeLambda s q (unitRescaledCutoffCoeff M Q n omega))⁻¹ := by
  filter_upwards [lambda_sensitivity_of_mem_goodLocalEvent_ae M Ccg Q n L hL s q hs
    hs2 hq] with omega hswitch hmem
  rw [← unitCubeLambda_perturbCoeffOn_unitRescaledCutoffCoeff M Q hL omega s q]
  exact hswitch hmem

/-- The twin at the manuscript's carrier: the same comparison read at
`lambda_{s,q}(z + square_m; .)` itself. -/
theorem lambdaSq_inv_le_of_mem_goodLocalEvent_ae (hd : 2 ≤ d) (M : ABKModel d)
    (Ccg : ℝ) (Q : TriadicCube d) {n L : ℤ} (hL : n ≤ L) (s : ℝ)
    (q : Ch02.MultiscaleExponent) (hs : 0 < s) (hs2 : s ≤ 1 / 2)
    (hq : q.IsAdmissible) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∈ goodLocalEvent M Ccg Q n →
        (Ch02.lambdaSq Q s q (coefficientCutoffTriadicCoeffFamily M L omega))⁻¹
          ≤ (1 + lambdaSensitivityConst d *
              (incrementUnitCube₂ Q n L omega).gradientW1Infinity *
              (Ch02.lambdaSq Q (3 / 8) (.finite 2)
                (coefficientCutoffTriadicCoeffFamily M n omega))⁻¹) *
            (Ch02.lambdaSq Q s q
              (coefficientCutoffTriadicCoeffFamily M n omega))⁻¹ := by
  let : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) hd)⟩
  filter_upwards [unitCubeLambda_inv_le_of_mem_goodLocalEvent_ae M Ccg Q hL s q hs
    hs2 hq] with omega hswitch hmem
  have h := hswitch hmem
  rwa [unitCubeLambda_unitRescaledCutoffCoeff M Q L s q omega,
    unitCubeLambda_unitRescaledCutoffCoeff M Q n s q omega,
    unitCubeLambda_unitRescaledCutoffCoeff M Q n (3 / 8) (.finite 2) omega] at h

/-! ## The `lambda`-constant mirror of `e.we.can.apply.cg` -/

/-- The constant chain of ABK26, at the `lambda`-sensitivity constant:
the `e.Bosc.def` threshold is below
`2^{-9} C_{(e.lambda.sensitivity)}^{-1} sigmabar_j`.  This is the mirror of
`oscThreshold_le_two_pow_neg_nine_mul_inv_responseSensitivityConst_mul_sigmaBar`,
available because `delta_osc` is normalized against the maximum of the two
frozen constants. -/
theorem oscThreshold_le_two_pow_neg_nine_mul_inv_lambdaSensitivityConst_mul_sigmaBar
    (hd : 2 ≤ d) (M : ABKModel d) {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) {m : ℤ}
    (hm : m ≤ m0) :
    oscThreshold M m ≤
      (2 : ℝ) ^ (-9 : ℤ) * (lambdaSensitivityConst d)⁻¹ *
        (Algsuperdiff.Section3.Annealed.sigmaBar M m : ℝ) := by
  have hsigma : 0 < (Algsuperdiff.Section3.Annealed.sigmaBar M m : ℝ) :=
    (Algsuperdiff.Section3.Annealed.sigmaBar_characterization M m).1
  have hkey := sqrt_cstar_mul_inv_sqrt_gamma_mul_rpow_le_two_mul_sigmaBar M hS hm
  have hdelta := deltaOsc_le_two_pow_neg_ten_mul_inv_lambdaSensitivityConst hd
  have hdeltapos : 0 < deltaOsc d := deltaOsc_pos d
  have hinv : 0 < (lambdaSensitivityConst d)⁻¹ :=
    inv_pos.2 (lambdaSensitivityConst_pos hd)
  have hthr : oscThreshold M m =
      deltaOsc d * (Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
        (Real.sqrt M.gamma)⁻¹ * (3 : ℝ) ^ (M.gamma * (m : ℝ))) := by
    rw [oscThreshold]
    ring
  have hstep : oscThreshold M m ≤
      deltaOsc d * (2 * (Algsuperdiff.Section3.Annealed.sigmaBar M m : ℝ)) := by
    rw [hthr]
    exact mul_le_mul_of_nonneg_left hkey hdeltapos.le
  refine hstep.trans ?_
  nlinarith [hdelta, hsigma, hinv, hdeltapos]

/-- **The `lambda`-gate on a good cube**: the mirror of
`gradientW1Infinity_incrementUnitCube_le_responseGate_ae` at the
`lambda`-sensitivity constant.  Almost surely, on `not B_osc(z + square_j)` and
`not B_loc(z + square_j)` and under the induction state, the frozen gate
quantity of the rescaled increment `k_L - k_j` satisfies the
`e.lambda.sensitivity.smallness.condition` at the gauge
`lambda_{3/8,2}` of the rescaled `a_j`, for every `L >= j`. -/
theorem gradientW1Infinity_incrementUnitCube_le_lambdaGate_notMem_bad_ae
    (hd : 2 ≤ d) (M : ABKModel d) {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) (Q : TriadicCube d)
    (hm : Q.scale ≤ m0) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∉ badOsc M Q → omega ∉ badLoc M Q → ∀ L : ℤ, Q.scale ≤ L →
        (incrementUnitCube₂ Q Q.scale L omega).gradientW1Infinity ≤
          (lambdaSensitivityConst d)⁻¹ *
            unitCubeLambda (3 / 8) (.finite 2)
              (unitRescaledCutoffCoeff M Q Q.scale omega) := by
  filter_upwards [cubeLowerEllipticityInv_pos_ae M Q Q.scale (1 / 4) (by norm_num)
      exponentTwo, lambda_transfer_quarter_ae M Q Q.scale]
    with omega hpos htransfer hosc hloc L hL
  have hCinv : (0 : ℝ) < (lambdaSensitivityConst d)⁻¹ :=
    inv_pos.2 (lambdaSensitivityConst_pos hd)
  have hlam : (0 : ℝ) ≤ cubeLowerEllipticity M Q Q.scale (1 / 4) (by norm_num)
      exponentTwo omega :=
    cubeLowerEllipticity_nonneg M Q Q.scale (1 / 4) (by norm_num) exponentTwo omega
  have hloc' := sigmaBar_le_ten_mul_cubeLowerEllipticity_of_notMem_badLoc M Q hloc
    hpos
  have hchain : incrementOscGauge Q L omega ≤
      (lambdaSensitivityConst d)⁻¹ *
        cubeLowerEllipticity M Q Q.scale (1 / 4) (by norm_num) exponentTwo
          omega := by
    calc incrementOscGauge Q L omega
        ≤ oscThreshold M Q.scale := incrementOscGauge_le_oscThreshold M Q hosc hL
      _ ≤ (2 : ℝ) ^ (-9 : ℤ) * (lambdaSensitivityConst d)⁻¹ *
            ((Algsuperdiff.Section3.Annealed.sigmaBar M Q.scale : ℝ)) :=
          oscThreshold_le_two_pow_neg_nine_mul_inv_lambdaSensitivityConst_mul_sigmaBar
            hd M hS hm
      _ ≤ (2 : ℝ) ^ (-9 : ℤ) * (lambdaSensitivityConst d)⁻¹ *
            (10 * cubeLowerEllipticity M Q Q.scale (1 / 4) (by norm_num)
              exponentTwo omega) :=
          mul_le_mul_of_nonneg_left hloc' (mul_nonneg (by positivity) hCinv.le)
      _ ≤ (lambdaSensitivityConst d)⁻¹ *
            cubeLowerEllipticity M Q Q.scale (1 / 4) (by norm_num) exponentTwo
              omega := by
          rw [show ((2 : ℝ) ^ (-9 : ℤ)) = 1 / 512 by norm_num]
          nlinarith [mul_nonneg hCinv.le hlam]
  refine (gradientW1Infinity_incrementUnitCube₂_le Q Q.scale L omega).trans ?_
  exact hchain.trans (mul_le_mul_of_nonneg_left htransfer hCinv.le)

/-! ## The transfer on the bad-event complement -/

/-- Almost surely, on `not B_osc(z + square_j)` and `not B_loc(z + square_j)` and
under the induction state,

```
lambda^{-1}_{s,q}(a_L rescaled)
  <= (1 + C |grad(k_L - k_j)| lambda^{-1}_{3/8,2}(a_j rescaled))
       lambda^{-1}_{s,q}(a_j rescaled)
```

for every `L >= j` and every admissible `(s, q)` with `s in (0, 1/2]`. -/
theorem unitCubeLambda_inv_le_of_notMem_bad_ae (hd : 2 ≤ d) (M : ABKModel d)
    {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) (Q : TriadicCube d)
    (hm : Q.scale ≤ m0) (s : ℝ) (q : Ch02.MultiscaleExponent) (hs : 0 < s)
    (hs2 : s ≤ 1 / 2) (hq : q.IsAdmissible) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∉ badOsc M Q → omega ∉ badLoc M Q → ∀ L : ℤ, Q.scale ≤ L →
        (unitCubeLambda s q (unitRescaledCutoffCoeff M Q L omega))⁻¹
          ≤ (1 + lambdaSensitivityConst d *
              (incrementUnitCube₂ Q Q.scale L omega).gradientW1Infinity *
              (unitCubeLambda (3 / 8) (.finite 2)
                (unitRescaledCutoffCoeff M Q Q.scale omega))⁻¹) *
            (unitCubeLambda s q
              (unitRescaledCutoffCoeff M Q Q.scale omega))⁻¹ := by
  filter_upwards [gradientW1Infinity_incrementUnitCube_le_lambdaGate_notMem_bad_ae
    hd M hS Q hm] with omega hgate hosc hloc L hL
  have hswitch := (lambda_sensitivity_const hd).2
    (unitRescaledCutoffCoeff M Q Q.scale omega)
    (incrementUnitCube₂ Q Q.scale L omega) (hgate hosc hloc L hL) s q hs hs2 hq
  rwa [unitCubeLambda_perturbCoeffOn_unitRescaledCutoffCoeff M Q hL omega s q]
    at hswitch

/-- The same transfer at the manuscript's carrier `lambda_{s,q}(z + square_j; .)`. -/
theorem lambdaSq_inv_le_of_notMem_bad_ae (hd : 2 ≤ d) (M : ABKModel d) {m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) (Q : TriadicCube d)
    (hm : Q.scale ≤ m0) (s : ℝ) (q : Ch02.MultiscaleExponent) (hs : 0 < s)
    (hs2 : s ≤ 1 / 2) (hq : q.IsAdmissible) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∉ badOsc M Q → omega ∉ badLoc M Q → ∀ L : ℤ, Q.scale ≤ L →
        (Ch02.lambdaSq Q s q (coefficientCutoffTriadicCoeffFamily M L omega))⁻¹
          ≤ (1 + lambdaSensitivityConst d *
              (incrementUnitCube₂ Q Q.scale L omega).gradientW1Infinity *
              (Ch02.lambdaSq Q (3 / 8) (.finite 2)
                (coefficientCutoffTriadicCoeffFamily M Q.scale omega))⁻¹) *
            (Ch02.lambdaSq Q s q
              (coefficientCutoffTriadicCoeffFamily M Q.scale omega))⁻¹ := by
  let : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) hd)⟩
  filter_upwards [unitCubeLambda_inv_le_of_notMem_bad_ae hd M hS Q hm s q hs hs2 hq]
    with omega hswitch hosc hloc L hL
  have h := hswitch hosc hloc L hL
  rwa [unitCubeLambda_unitRescaledCutoffCoeff M Q L s q omega,
    unitCubeLambda_unitRescaledCutoffCoeff M Q Q.scale s q omega,
    unitCubeLambda_unitRescaledCutoffCoeff M Q Q.scale (3 / 8) (.finite 2)
      omega] at h

end

end Algsuperdiff.Section3.Provider.Multiscale
