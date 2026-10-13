/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.JSmallness
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.ResponseCongruence
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.UnitCubeMultiscale.BigLambda.Characterization
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.UnitCubeMultiscale.CompatibleFamily
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.BigLambdaSensitivity
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.BigLambdaSensitivityAtDelta

/-!
# BigLambdaSensitivity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The `Lambda`-half of the coefficient switch, at the manuscript's cube

`LambdaCovariance.lean` transports the multiscale *lower* ellipticity from the
frozen unit-cube gauge to the manuscript's cube `z + square_m`, and
`LambdaTransfer.lean` / `LambdaSensitivityTwin.lean` read the frozen
`lambda`-sensitivity switch there.  This module is the exact `Lambda`
counterpart: it transports `Lambda_{s,q}` to the same carrier and reads the
frozen `e.big.Lambda.sensitivity` (ABK26) at it.

The consumer is the middle of Step 1 of `p.bfA.multiscalebound`, which passes

```
Lambda_{1/4,2}(z + square_j; a_L)
  <=  C Lambda_{1/4,2}(z + square_j; a_j)
      + C (|(k_L - k_j)| + 3^j ||grad (k_L - k_j)||)^2
          lambda^{-1}_{1/4,2}(z + square_j; a_j) ,
```

i.e. `e.big.Lambda.sensitivity` at the cube `z + square_j`.

## The smallness gate, and how it is discharged

`e.big.Lambda.sensitivity` is the second display of Lemma `l.J.sensitivity`: in
the manuscript it carries the *same* constant `C` and the *same* smallness
condition `e.J.sensitivity.smallness.condition` as `e.J.sensitivity`.  In the
Lean rendering the two displays are two frozen theorems,
`Algsuperdiff.Frozen.Section24.responseJ_sensitivity` and
`Algsuperdiff.Frozen.Section24.bigLambda_sensitivity`, each with its own
existential constant.

`DeltaOsc.lean` therefore normalizes the manuscript's `delta_osc` against
`sensitivityConstMax d = max 1 (max (max C_lambda C_J) C_BigLambda)`, the
three-way maximum that restores the manuscript's single-constant reading.  The
bad-event chain `not B_osc and not B_loc ==> gate` of `JSmallness.lean` and
`LambdaSensitivityTwin.lean` consequently opens the `Lambda` gate too, and the
`..._of_notMem_bad_ae` conclusions below carry no gate hypothesis at all.  The
`..._of_gate` forms are kept as the deterministic, `omega`-free core: their
hypothesis *is* the manuscript's own `e.J.sensitivity.smallness.condition`,
read at the cube, so no proof step has migrated into a hypothesis either way.

## Main results

* `coarseBMatrixNorm_cutoff_translateCutoffSample`,
  `LambdaSq_cutoff_translateCutoffSample`, `LambdaSq_originCube_dilate`: the
  translation and dilation covariance of `Lambda_{s,q}` for the actual
  coefficient cutoff.
* `unitCubeBigLambda_unitRescaledCutoffCoeff`: **the `Lambda`-transfer**,
  `unitCubeBigLambda s q (a_n rescaled) = Lambda_{s,q}(z + square_m; a_n)`.
* `unitCubeBigLambda_eq_of_aeeq`,
  `unitCubeBigLambda_perturbCoeffOn_unitRescaledCutoffCoeff`: the frozen
  `Lambda` gauge is an a.e. invariant, and the perturbed rescaled `a_n` is the
  rescaled `a_L` inside it.
* `LambdaSq_le_of_gate`: `e.big.Lambda.sensitivity` at the manuscript's cube
  and at the honest field `a_L`, from the smallness gate, with the
  dimension-only constant `bigLambdaSensitivityConst d`.
* `oscThreshold_le_two_pow_neg_nine_mul_inv_bigLambdaSensitivityConst_mul_sigmaBar`,
  `gradientW1Infinity_incrementUnitCube_le_bigLambdaGate_notMem_bad_ae`: the
  `Lambda`-constant mirror of the `e.we.can.apply.cg` chain.
* `LambdaSq_le_of_notMem_bad_ae`, `LambdaSq_quarter_le_of_notMem_bad_ae`:
  **the gate discharged** — `e.big.Lambda.sensitivity` at the manuscript's cube
  holds almost surely on `not B_osc and not B_loc`, with no smallness
  hypothesis.

## References

* ABK26 (`l.J.sensitivity`, one constant and one smallness condition for both
  displays; second display `e.big.Lambda.sensitivity`).
* ABK26, `e.Bosc.def`, `e.delta.osc.choice`.
* ABK26, `p.bfA.multiscalebound`, `e.we.can.apply.cg`.
* ABK26 (`p.bfA.multiscalebound`, Step 1).
* ABK26 (the definitions (2.22)--(2.23)).
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents

noncomputable section

variable {d : ℕ}

/-! ## One-cube translation covariance of `|b|` -/

/-- One-cube translation covariance of `|b(Q; a)|` for the actual coefficient
cutoff.  This is the `b`-half of
`coarseSigmaStarInvMatrixNorm_cutoff_translateCutoffSample`, read off the same
covariance of the coarse block matrix. -/
theorem coarseBMatrixNorm_cutoff_translateCutoffSample [NeZero d] (M : ABKModel d)
    (m : ℤ) (v : Vec d) {R T : TriadicCube d}
    (hset : cubeSet T = translateSet v (cubeSet R)) (omega : CutoffSample d) :
    Ch02.coarseBMatrixNorm T (coefficientCutoffTriadicCoeffFamily M m omega) =
      Ch02.coarseBMatrixNorm R
        (coefficientCutoffTriadicCoeffFamily M m
          (translateCutoffSample v omega)) := by
  have hleft : Ch02.TriadicCoeffFamily.AEEq
      (coefficientCutoffTriadicCoeffFamily M m omega)
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (coefficientCutoff M.nu m omega)
        (coefficientCutoff_aeLocallyUniformlyEllipticField M m omega)) :=
    fun _ => Filter.EventuallyEq.rfl
  have hright : Ch02.TriadicCoeffFamily.AEEq
      (coefficientCutoffTriadicCoeffFamily M m (translateCutoffSample v omega))
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (coefficientCutoff M.nu m (translateCutoffSample v omega))
        (coefficientCutoff_aeLocallyUniformlyEllipticField M m
          (translateCutoffSample v omega))) :=
    fun _ => Filter.EventuallyEq.rfl
  rw [Ch02.coarseBMatrixNorm_eq_ofAEEq hleft T,
    Ch02.coarseBMatrixNorm_eq_ofAEEq hright R]
  have hmat := coarseBlockMatrix_cutoff_translateCutoffSample M m v hset omega
  have hupper := congrArg (fun A : BlockMat d => Ch02.matrixNorm A.upperLeft) hmat
  simpa [Ch02.coarseBMatrixNorm] using hupper

/-! ## Translation covariance of the multiscale upper ellipticity -/

/-- **Deterministic translation covariance of `Lambda_{s,q}`.**  For the actual
coefficient cutoff, the multiscale upper ellipticity on an arbitrary triadic
cube `Q` equals the one on the centered cube of the same scale, evaluated at the
sample translated by the base point `triadicCubeShift Q` of `Q`. -/
theorem LambdaSq_cutoff_translateCutoffSample [NeZero d] (M : ABKModel d) (m : ℤ)
    (Q : TriadicCube d) (s : ℝ) (q : Ch02.MultiscaleExponent)
    (omega : CutoffSample d) :
    Ch02.LambdaSq Q s q (coefficientCutoffTriadicCoeffFamily M m omega) =
      Ch02.LambdaSq (originCube d Q.scale) s q
        (coefficientCutoffTriadicCoeffFamily M m
          (translateCutoffSample (triadicCubeShift Q) omega)) := by
  have hQ : translateCube Q.index (originCube d Q.scale) = Q := by
    cases Q with
    | mk scale index => simp [translateCube, originCube]
  have hrw : Ch02.LambdaSq Q s q (coefficientCutoffTriadicCoeffFamily M m omega) =
      Ch02.LambdaSq (translateCube Q.index (originCube d Q.scale)) s q
        (coefficientCutoffTriadicCoeffFamily M m omega) := by
    rw [hQ]
  rw [hrw]
  refine Ch02.LambdaSq_translateCube_of_coarseBMatrixNorm _ _ Q.index
    (originCube d Q.scale) s q ?_
  intro l R hR
  have hk : (originCube d Q.scale).scale - (l : ℤ) ≤ (originCube d Q.scale).scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le l)
  have hscale : R.scale = Q.scale - (l : ℤ) := by
    have h := scale_eq_sub_of_mem_descendantsAtScale hk hR
    have hred : ((originCube d Q.scale).scale -
        ((originCube d Q.scale).scale - (l : ℤ))).toNat = l := by
      simp [originCube]
    rw [hred] at h
    simpa [originCube] using h
  refine coarseBMatrixNorm_cutoff_translateCutoffSample M m (triadicCubeShift Q) ?_
    omega
  rw [cubeSet_translateCube_descendantTranslationShift Q.index l hscale]
  rfl

/-! ## Dilation to the unit cube -/

/-- **Scale normalization of `Lambda_{s,q}`.**  The multiscale upper ellipticity
of a family on the centered scale-`m` cube is that of its `3^{-m}`-dilation on
the unit cube. -/
theorem LambdaSq_originCube_dilate (F : Ch02.TriadicCoeffFamily d) (m : ℤ) (s : ℝ)
    (q : Ch02.MultiscaleExponent) :
    Ch02.LambdaSq (originCube d 0) s q (Ch02.TriadicCoeffFamily.dilate (-m) F) =
      Ch02.LambdaSq (originCube d m) s q F := by
  have h := Ch02.LambdaSq_dilate
    (Ch02.TriadicCoeffFamily.isDilation_dilate (-m) F) (originCube d m) s q
  rwa [dilateCube_neg_originCube m] at h

/-! ## The `Lambda`-transfer -/

/-- **The `Lambda`-transfer identity.**  The multiscale upper ellipticity of the
cutoff `a_n` on the cube `Q = z + square_m` is the frozen unit-cube gauge
`unitCubeBigLambda` of the rescaled coefficient object.  This is the exact
analogue of the proved `unitCubeLambda_unitRescaledCutoffCoeff`. -/
theorem unitCubeBigLambda_unitRescaledCutoffCoeff [NeZero d] (M : ABKModel d)
    (Q : TriadicCube d) (cutoffScale : ℤ) (s : ℝ) (q : Ch02.MultiscaleExponent)
    (omega : CutoffSample d) :
    unitCubeBigLambda s q (unitRescaledCutoffCoeff M Q cutoffScale omega) =
      Ch02.LambdaSq Q s q
        (coefficientCutoffTriadicCoeffFamily M cutoffScale omega) := by
  rw [unitRescaledCutoffCoeff,
    Algsuperdiff.Section24.UnitCubeMultiscale.BigLambda.characterization s q _ _
      (Ch02.CoeffOn.AEEq.refl _),
    LambdaSq_originCube_dilate]
  exact (LambdaSq_cutoff_translateCutoffSample M cutoffScale Q s q omega).symm

/-- The frozen scalar `unitCubeBigLambda` only depends on the coefficient field
up to a.e. equality.  This is the `Lambda`-mirror of
`Section24.Sensitivity.Provider.Lambda.unitCubeLambda_eq_of_aeeq`. -/
theorem unitCubeBigLambda_eq_of_aeeq (s : ℝ) (q : Ch02.MultiscaleExponent)
    {a b : Ch02.CoeffOn (Ch02.cubeDomain (originCube d 0))}
    (hab : Ch02.CoeffOn.AEEq a b) :
    unitCubeBigLambda s q a = unitCubeBigLambda s q b := by
  obtain ⟨F, hF⟩ :=
    Algsuperdiff.Section24.UnitCubeMultiscale.exists_compatibleTriadicCoeffFamily a
  rw [Algsuperdiff.Section24.UnitCubeMultiscale.BigLambda.characterization s q a F hF,
    Algsuperdiff.Section24.UnitCubeMultiscale.BigLambda.characterization s q b F
      (hF.trans hab)]

/-- The `#J`-smallness identification, read at the frozen unit-cube upper gauge:
the frozen perturbation of the rescaled `a_n` by the rescaled literal increment
`k_L - k_n` has the same `Lambda_{s,q}` as the rescaled `a_L`. -/
theorem unitCubeBigLambda_perturbCoeffOn_unitRescaledCutoffCoeff (M : ABKModel d)
    (Q : TriadicCube d) {n L : ℤ} (hnL : n ≤ L) (omega : CutoffSample d) (s : ℝ)
    (q : Ch02.MultiscaleExponent) :
    unitCubeBigLambda s q
        (perturbCoeffOn (Ch02.cubeDomain (originCube d 0))
          (unitRescaledCutoffCoeff M Q n omega)
          (incrementUnitCube₂ Q n L omega).toLInfSkewMatrixFieldOn 1) =
      unitCubeBigLambda s q (unitRescaledCutoffCoeff M Q L omega) :=
  unitCubeBigLambda_eq_of_aeeq s q
    (perturbCoeffOn_unitRescaledCutoffCoeff_aeEq M Q hnL omega)

/-! ## The frozen constant of `e.big.Lambda.sensitivity`

The fixed-factor constant of `e.big.Lambda.sensitivity` is
`Algsuperdiff.Section3.Provider.BadEvents.bigLambdaSensitivityConst`, extracted
in `DeltaOsc.lean` next to the `lambda`- and `J`-sensitivity constants and
merged with them into `sensitivityConstMax`; its frozen conclusion is
`bigLambda_sensitivity_const` there.  Only the free-`delta` variant, which has
no counterpart among the manuscript's displays, is extracted here. -/


/-! ## `e.big.Lambda.sensitivity` at the manuscript's cube -/

/-- Nonzero dimension, from the paper-wide assumption `2 <= d`. -/
private theorem neZero_of_two_le_bigLambda {d : ℕ} (hd : 2 ≤ d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) hd)⟩

/-- **`e.big.Lambda.sensitivity` at the translated triadic cube** (ABK26, the
statement display; its proof is; consumed).  If the increment `k_L - k_n`
satisfies the manuscript's smallness condition
`e.J.sensitivity.smallness.condition` at the cube `Q = z + square_m`, then for
every `s in (0, 3/8)`,

```
Lambda_{s,2}(Q; a_L)
  <=  4 Lambda_{s,2}(Q; a_n)
      + C (3/8 - s)^{-1} ||k_L - k_n||^2 lambda_{s,2}^{-1}(Q; a_n) ,
```

with `C = bigLambdaSensitivityConst d` the dimension-only frozen constant.
Every carrier is the manuscript's own cube, and the field on the left is the
honest `a_L`, not a perturbed object; the increment gauges are the normalized
quantities of `IncrementBridge.lean`. -/
theorem LambdaSq_le_of_gate (hd : 2 ≤ d) (M : ABKModel d) (Q : TriadicCube d)
    {n L : ℤ} (hnL : n ≤ L) (omega : CutoffSample d)
    (hgate : (incrementUnitCube₂ Q n L omega).gradientW1Infinity ≤
      (bigLambdaSensitivityConst d)⁻¹ *
        Ch02.lambdaSq Q (3 / 8) (.finite 2)
          (coefficientCutoffTriadicCoeffFamily M n omega))
    {s : ℝ} (hs : 0 < s) (hs38 : s < 3 / 8) :
    Ch02.LambdaSq Q s (.finite 2)
        (coefficientCutoffTriadicCoeffFamily M L omega) ≤
      4 * Ch02.LambdaSq Q s (.finite 2)
          (coefficientCutoffTriadicCoeffFamily M n omega) +
        bigLambdaSensitivityConst d * (3 / 8 - s)⁻¹ *
          (incrementUnitCube₂ Q n L omega).w1Infinity ^ 2 *
          (Ch02.lambdaSq Q s (.finite 2)
            (coefficientCutoffTriadicCoeffFamily M n omega))⁻¹ := by
  let : NeZero d := neZero_of_two_le_bigLambda hd
  have hgate' : (incrementUnitCube₂ Q n L omega).gradientW1Infinity ≤
      (bigLambdaSensitivityConst d)⁻¹ *
        unitCubeLambda (3 / 8) (.finite 2)
          (unitRescaledCutoffCoeff M Q n omega) := by
    rwa [unitCubeLambda_unitRescaledCutoffCoeff M Q n (3 / 8) (.finite 2) omega]
  have hswitch := (bigLambda_sensitivity_const hd).2
    (unitRescaledCutoffCoeff M Q n omega) (incrementUnitCube₂ Q n L omega) hgate'
    s hs hs38
  rw [unitCubeBigLambda_perturbCoeffOn_unitRescaledCutoffCoeff M Q hnL omega s
      (.finite 2),
    unitCubeBigLambda_unitRescaledCutoffCoeff M Q L s (.finite 2) omega,
    unitCubeBigLambda_unitRescaledCutoffCoeff M Q n s (.finite 2) omega,
    unitCubeLambda_unitRescaledCutoffCoeff M Q n s (.finite 2) omega] at hswitch
  exact hswitch


/-! ## The gate discharged on the bad-event complement -/

/-- The constant chain of ABK26, at the `Lambda`-sensitivity constant: the
`e.Bosc.def` threshold is below `2^{-9} C_{(e.big.Lambda.sensitivity)}^{-1}
sigmabar_j`.  This is the mirror of
`oscThreshold_le_two_pow_neg_nine_mul_inv_responseSensitivityConst_mul_sigmaBar`
and of its `lambda` twin, available because `delta_osc` is normalized against
the maximum of the three frozen constants — which is what ABK26's single
constant `C_{(e.J.sensitivity.smallness.condition)}` (label) says. -/
theorem oscThreshold_le_two_pow_neg_nine_mul_inv_bigLambdaSensitivityConst_mul_sigmaBar
    (hd : 2 ≤ d) (M : ABKModel d) {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) {m : ℤ}
    (hm : m ≤ m0) :
    oscThreshold M m ≤
      (2 : ℝ) ^ (-9 : ℤ) * (bigLambdaSensitivityConst d)⁻¹ *
        (Algsuperdiff.Section3.Annealed.sigmaBar M m : ℝ) := by
  have hsigma : 0 < (Algsuperdiff.Section3.Annealed.sigmaBar M m : ℝ) :=
    (Algsuperdiff.Section3.Annealed.sigmaBar_characterization M m).1
  have hkey := sqrt_cstar_mul_inv_sqrt_gamma_mul_rpow_le_two_mul_sigmaBar M hS hm
  have hdelta := deltaOsc_le_two_pow_neg_ten_mul_inv_bigLambdaSensitivityConst hd
  have hdeltapos : 0 < deltaOsc d := deltaOsc_pos d
  have hinv : 0 < (bigLambdaSensitivityConst d)⁻¹ :=
    inv_pos.2 (bigLambdaSensitivityConst_pos hd)
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

/-- **The `Lambda`-gate on a good cube**: the mirror of
`gradientW1Infinity_incrementUnitCube_le_responseGate_ae` at the
`Lambda`-sensitivity constant.  Almost surely, on `not B_osc(z + square_j)` and
`not B_loc(z + square_j)` and under the induction state, the frozen gate
quantity of the rescaled increment `k_L - k_j` satisfies the manuscript's
`e.J.sensitivity.smallness.condition` at the approved gauge `lambda_{3/8,2}` of
the rescaled `a_j`, for every `L >= j`. -/
theorem gradientW1Infinity_incrementUnitCube_le_bigLambdaGate_notMem_bad_ae
    (hd : 2 ≤ d) (M : ABKModel d) {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) (Q : TriadicCube d)
    (hm : Q.scale ≤ m0) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∉ badOsc M Q → omega ∉ badLoc M Q → ∀ L : ℤ, Q.scale ≤ L →
        (incrementUnitCube₂ Q Q.scale L omega).gradientW1Infinity ≤
          (bigLambdaSensitivityConst d)⁻¹ *
            unitCubeLambda (3 / 8) (.finite 2)
              (unitRescaledCutoffCoeff M Q Q.scale omega) := by
  filter_upwards [cubeLowerEllipticityInv_pos_ae M Q Q.scale (1 / 4) (by norm_num)
      exponentTwo, lambda_transfer_quarter_ae M Q Q.scale]
    with omega hpos htransfer hosc hloc L hL
  have hCinv : (0 : ℝ) < (bigLambdaSensitivityConst d)⁻¹ :=
    inv_pos.2 (bigLambdaSensitivityConst_pos hd)
  have hlam : (0 : ℝ) ≤ cubeLowerEllipticity M Q Q.scale (1 / 4) (by norm_num)
      exponentTwo omega :=
    cubeLowerEllipticity_nonneg M Q Q.scale (1 / 4) (by norm_num) exponentTwo omega
  have hloc' := sigmaBar_le_ten_mul_cubeLowerEllipticity_of_notMem_badLoc M Q hloc
    hpos
  have hchain : incrementOscGauge Q L omega ≤
      (bigLambdaSensitivityConst d)⁻¹ *
        cubeLowerEllipticity M Q Q.scale (1 / 4) (by norm_num) exponentTwo
          omega := by
    calc incrementOscGauge Q L omega
        ≤ oscThreshold M Q.scale := incrementOscGauge_le_oscThreshold M Q hosc hL
      _ ≤ (2 : ℝ) ^ (-9 : ℤ) * (bigLambdaSensitivityConst d)⁻¹ *
            ((Algsuperdiff.Section3.Annealed.sigmaBar M Q.scale : ℝ)) :=
          oscThreshold_le_two_pow_neg_nine_mul_inv_bigLambdaSensitivityConst_mul_sigmaBar
            hd M hS hm
      _ ≤ (2 : ℝ) ^ (-9 : ℤ) * (bigLambdaSensitivityConst d)⁻¹ *
            (10 * cubeLowerEllipticity M Q Q.scale (1 / 4) (by norm_num)
              exponentTwo omega) :=
          mul_le_mul_of_nonneg_left hloc' (mul_nonneg (by positivity) hCinv.le)
      _ ≤ (bigLambdaSensitivityConst d)⁻¹ *
            cubeLowerEllipticity M Q Q.scale (1 / 4) (by norm_num) exponentTwo
              omega := by
          rw [show ((2 : ℝ) ^ (-9 : ℤ)) = 1 / 512 by norm_num]
          nlinarith [mul_nonneg hCinv.le hlam]
  refine (gradientW1Infinity_incrementUnitCube₂_le Q Q.scale L omega).trans ?_
  exact hchain.trans (mul_le_mul_of_nonneg_left htransfer hCinv.le)

/-- **`e.big.Lambda.sensitivity` on the bad-event complement** (ABK26,
consumed).  Almost surely, on `not B_osc(z + square_j)` and `not B_loc(z +
square_j)` and under the induction state at a scale above `j = Q.scale`, for
every `L >= j` and every `s in (0, 3/8)`,

```
Lambda_{s,2}(z + square_j; a_L)
  <=  4 Lambda_{s,2}(z + square_j; a_j)
      + C (3/8 - s)^{-1} ||k_L - k_j||^2 lambda_{s,2}^{-1}(z + square_j; a_j) .
```

This is `LambdaSq_le_of_gate` with its smallness hypothesis discharged by
`gradientW1Infinity_incrementUnitCube_le_bigLambdaGate_notMem_bad_ae`, exactly
as `responseJ_le_of_notMem_bad_ae` discharges the response half. -/
theorem LambdaSq_le_of_notMem_bad_ae (hd : 2 ≤ d) (M : ABKModel d) {m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) (Q : TriadicCube d)
    (hm : Q.scale ≤ m0) {s : ℝ} (hs : 0 < s) (hs38 : s < 3 / 8) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∉ badOsc M Q → omega ∉ badLoc M Q → ∀ L : ℤ, Q.scale ≤ L →
        Ch02.LambdaSq Q s (.finite 2)
            (coefficientCutoffTriadicCoeffFamily M L omega) ≤
          4 * Ch02.LambdaSq Q s (.finite 2)
              (coefficientCutoffTriadicCoeffFamily M Q.scale omega) +
            bigLambdaSensitivityConst d * (3 / 8 - s)⁻¹ *
              (incrementUnitCube₂ Q Q.scale L omega).w1Infinity ^ 2 *
              (Ch02.lambdaSq Q s (.finite 2)
                (coefficientCutoffTriadicCoeffFamily M Q.scale omega))⁻¹ := by
  let : NeZero d := neZero_of_two_le_bigLambda hd
  filter_upwards [gradientW1Infinity_incrementUnitCube_le_bigLambdaGate_notMem_bad_ae
    hd M hS Q hm] with omega hgate hosc hloc L hL
  refine LambdaSq_le_of_gate hd M Q hL omega ?_ hs hs38
  have h := hgate hosc hloc L hL
  rwa [unitCubeLambda_unitRescaledCutoffCoeff M Q Q.scale (3 / 8) (.finite 2)
    omega] at h

/-- **The instance on the bad-event complement**: `s = 1/4`, `q = 2`, at the cube
`Q = z + square_j`, with no smallness hypothesis. -/
theorem LambdaSq_quarter_le_of_notMem_bad_ae (hd : 2 ≤ d) (M : ABKModel d)
    {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) (Q : TriadicCube d)
    (hm : Q.scale ≤ m0) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∉ badOsc M Q → omega ∉ badLoc M Q → ∀ L : ℤ, Q.scale ≤ L →
        Ch02.LambdaSq Q (1 / 4) (.finite 2)
            (coefficientCutoffTriadicCoeffFamily M L omega) ≤
          4 * Ch02.LambdaSq Q (1 / 4) (.finite 2)
              (coefficientCutoffTriadicCoeffFamily M Q.scale omega) +
            bigLambdaSensitivityConst d * 8 *
              (incrementUnitCube₂ Q Q.scale L omega).w1Infinity ^ 2 *
              (Ch02.lambdaSq Q (1 / 4) (.finite 2)
                (coefficientCutoffTriadicCoeffFamily M Q.scale omega))⁻¹ := by
  filter_upwards [LambdaSq_le_of_notMem_bad_ae hd M hS Q hm (s := 1 / 4)
    (by norm_num) (by norm_num)] with omega h hosc hloc L hL
  have h' := h hosc hloc L hL
  rwa [show ((3 : ℝ) / 8 - 1 / 4)⁻¹ = 8 by norm_num] at h'

end

end Algsuperdiff.Section3.Provider.Multiscale
