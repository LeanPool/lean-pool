/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.GoodLocalEllipticity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.IncrementGaugeTwoIndex

/-!
# GoodLocalEvents

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The good local sensitivity event `e.good.local.events`

ABK26 defines, in `e.good.local.events`, for `m, n` integers and a centre `z`,
the event

```
Q(m,n,z) := { C_sens sup_{L >= n} 3^{2m} ||grad (k_L - k_n)||_{W^{1,infinity}(z+square_m)}
              <= (1/2) C_{(e.cg.ellip.lower)}^{-1} 3^{-(1/2)(n-m)_+} sigmaBar_{n-1}
              <= 3^{-(1/4)(n-m)_+} lambda_{1/8,2}(z+square_m; a_n) } ,
```

a chain of two inequalities around the common middle threshold
`goodLocalThreshold M Ccg m n`.  Its stated purpose is that it "allows us to
switch from the field `a_L` to `a_n` in the cube `z+square_m` for any `L >= n`,
using the coarse-grained sensitivity estimates".

This module assembles the event from its two proved clauses and proves that
switch, i.e. that on the event the rescaled literal increment `k_L - k_n` meets
the smallness gate of the frozen Section 2.4 sensitivity lemmas.

* the **sensitivity clause** `goodLocalSensitivity` is the first inequality,
  measured by the two-index gauge `incrementOscGauge₂` of
  `IncrementGaugeTwoIndex`;
* the **coarse-ellipticity clause** is the proved `goodLocalEllipticity` of
  `GoodLocalEllipticity`;
* `goodLocalEvent` is their intersection, which is the displayed chain.

## Reading conventions (recorded; none of them is a manuscript defect)

* **The supremum.**  The manuscript's `sup_{L >= n} ... <= T` is denoted by the
  equivalent universally quantified form `forall L >= n, ... <= T`: a supremum
  is below `T` exactly when every member of the family is.  Membership in the
  event unfolds to exactly that quantified form
  (`mem_goodLocalSensitivity_iff`), and the event is correspondingly the
  intersection over `L >= n` of the one-index gates
  (`goodLocalSensitivity_eq_iInter`).  The `iSup` of an unbounded real family
  is a junk value, so the universally quantified form is the faithful
  denotation, not a weakening.
* **The centre.**  `z` is carried by a `TriadicCube d`: `m = Q.scale` and
  `cubeSet Q = z + square_m` with `z` in `3^m Z^d`.  The manuscript writes `z
  in R^d`; every consumer of `e.good.local.events` instantiates `z` in a
  triadic lattice, and this repository has no multiscale ellipticity
  observable on off-grid translates.
* **The two constants.**  `C_{(e.cg.ellip.lower)}` is the explicit real
  parameter `Ccg` of `GoodLocalEllipticity` (the now-proved frozen
  `coarse_ellipticity_bounds` supplies it to downstream consumers, while this
  conditional A remains parametrized).  The joint smallness constant
  `C_{(e.J.sensitivity.smallness.condition)&(e.lambda.sensitivity.smallness.condition)}`
  is `sensitivityConstMax d` of `DeltaOsc`, the single dimension-only constant
  that dominates both frozen sensitivity constants.
* **No positivity of `Ccg` is used** by the gate opening: the chain
  `C_sens * gauge <= threshold <= 3^{-(1/4)(n-m)_+} lambda` passes through the
  threshold without inspecting it.

## The remaining input: the lambda-transfer

The frozen Section 2.4 gates are stated at the *unit cube*, against
`unitCubeLambda (3/8) (.finite 2) a`; the event is stated at `z + square_m`,
against `lambda_{1/8,2}(z+square_m; a_n)`.  Bridging the two needs

```
lambda_{1/8,2}(z+square_m; a_n)  <=  lambda_{3/8,2}(unit cube; a_rescaled) ,
```

which is the composition of

1. the exponent monotonicity `e.ellipticities.monotone.ordered` (ABK26):
   `lambda_{t,q} <= lambda_{s,q}` for `0 < t < s`, here at `t = 1/8 < 3/8 = s`;
   and
2. the scale-and-translation covariance of the multiscale lower ellipticity,
   `lambda_{s,q}(z + square_m; a) = unitCubeLambda s q (a rescaled by `y |-> z
   + 3^m y`)`.  CoarseGraining has a dilation interface
   (`Homogenization.Book.Ch02.MultiscaleDilationTheory.lambdaSq_dilate`) but no
   translation counterpart, and neither is instantiated here.

The downstream provider `LambdaTransfer.lean` now supplies this comparison in
the forms `lambda_transfer_literal` and `lambda_transfer_ae`.  To keep the
dependency direction acyclic, this base module deliberately exposes the gate
opening in two layers: the **unconditional** cube-level gate
`gradientW1Infinity_incrementUnitCube₂_le_of_mem_goodLocalEvent` (and its two
frozen-constant variants), and the **conditional** helpers named
`..._of_lambdaTransfer`, which take exactly the displayed comparison above as an
explicit hypothesis.  This module alone assigns no source-node status.

## Main definitions

* `goodLocalSensitivity`: the first inequality of `e.good.local.events`.
* `goodLocalEvent`: the displayed event `Q(m,n,z)`.
* `goodLocalSensitivityFailure`: the complement of the sensitivity clause, in
  the scale-resolved union form used by the proof of `l.bad.event.lemma`.

## Main results

* `mem_goodLocalEvent_iff`, `mem_goodLocalSensitivity_iff`: the
  characterizations, the sensitivity clause read as the threshold bound holding
  at every scale `L >= n`.
* `measurableSet_goodLocalEvent`.
* `compl_goodLocalEvent_eq`, `measureReal_compl_goodLocalEvent_le`: the
  decomposition of `not Q(m,n,z)` used at ABK26.
* `gradientW1Infinity_incrementUnitCube₂_le_of_mem_goodLocalEvent` and its two
  frozen-constant variants: the gate opening at the cube level.
* `lambda_sensitivity_of_mem_goodLocalEvent_of_lambdaTransfer`,
  `responseJ_sensitivity_of_mem_goodLocalEvent_of_lambdaTransfer`: the two
  frozen sensitivity conclusions for the rescaled increment `k_L - k_n`,
  conditional on the lambda-transfer.

## References

* ABK26, `e.good.local.events`.
* ABK26, `l.bad.event.lemma`.
* ABK26 (the two consumers).
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The sensitivity clause -/

/-- The first inequality of `e.good.local.events` (ABK26), as an event: the
joint sensitivity constant times the two-index increment gauge `3^{2m} ||grad
(k_L - k_n)||_{W^{1,infinity}(z+square_m)}` stays below the middle threshold
`(1/2) Ccg^{-1} 3^{-(1/2)(n-m)_+} sigmaBar_{n-1}`, uniformly in `L >= n`. -/
def goodLocalSensitivity (M : ABKModel d) (Ccg : ℝ) (Q : TriadicCube d) (n : ℤ) :
    Set (CutoffSample d) :=
  {omega | ∀ L : ℤ, n ≤ L →
    sensitivityConstMax d * incrementOscGauge₂ Q n L omega ≤
      goodLocalThreshold M Ccg Q.scale n}

theorem mem_goodLocalSensitivity_iff (M : ABKModel d) (Ccg : ℝ)
    (Q : TriadicCube d) (n : ℤ) (omega : CutoffSample d) :
    omega ∈ goodLocalSensitivity M Ccg Q n ↔
      ∀ L : ℤ, n ≤ L →
        sensitivityConstMax d * incrementOscGauge₂ Q n L omega ≤
          goodLocalThreshold M Ccg Q.scale n :=
  Iff.rfl

theorem goodLocalSensitivity_eq_iInter (M : ABKModel d) (Ccg : ℝ)
    (Q : TriadicCube d) (n : ℤ) :
    goodLocalSensitivity M Ccg Q n =
      ⋂ L ∈ Set.Ici n,
        {omega : CutoffSample d |
          sensitivityConstMax d * incrementOscGauge₂ Q n L omega ≤
            goodLocalThreshold M Ccg Q.scale n} := by
  ext omega
  simp only [goodLocalSensitivity, Set.mem_ofPred_eq, Set.mem_iInter₂, Set.mem_Ici]

theorem measurableSet_goodLocalSensitivity (M : ABKModel d) (Ccg : ℝ)
    (Q : TriadicCube d) (n : ℤ) :
    MeasurableSet (goodLocalSensitivity M Ccg Q n) := by
  rw [goodLocalSensitivity_eq_iInter]
  refine MeasurableSet.iInter fun L => MeasurableSet.iInter fun _ => ?_
  exact measurableSet_le
    ((measurable_incrementOscGauge₂ Q n L).const_mul _) measurable_const

/-! ## The event -/

/-- **The good local sensitivity event `Q(m,n,z)`** of ABK26,
`e.good.local.events`, at the triadic cube `Q` of scale `m = Q.scale` and base
point `z = cubeBasePoint Q`, and the cutoff scale `n`: the conjunction of the
two displayed inequalities. -/
def goodLocalEvent (M : ABKModel d) (Ccg : ℝ) (Q : TriadicCube d) (n : ℤ) :
    Set (CutoffSample d) :=
  goodLocalSensitivity M Ccg Q n ∩ goodLocalEllipticity M Ccg Q n

/-- The displayed chain, verbatim. -/
theorem mem_goodLocalEvent_iff (M : ABKModel d) (Ccg : ℝ) (Q : TriadicCube d)
    (n : ℤ) (omega : CutoffSample d) :
    omega ∈ goodLocalEvent M Ccg Q n ↔
      (∀ L : ℤ, n ≤ L →
          sensitivityConstMax d * incrementOscGauge₂ Q n L omega ≤
            goodLocalThreshold M Ccg Q.scale n) ∧
        goodLocalThreshold M Ccg Q.scale n ≤
          (3 : ℝ) ^ (-(1 / 4 : ℝ) * scaleGapPos Q.scale n) *
            cubeLowerEllipticity M Q n (1 / 8) (by norm_num) exponentTwo omega :=
  Iff.rfl

theorem measurableSet_goodLocalEvent (M : ABKModel d) (Ccg : ℝ)
    (Q : TriadicCube d) (n : ℤ) :
    MeasurableSet (goodLocalEvent M Ccg Q n) :=
  (measurableSet_goodLocalSensitivity M Ccg Q n).inter
    (measurableSet_goodLocalEllipticity M Ccg Q n)

/-! ## The complement decomposition of `l.bad.event.lemma` -/

/-- The failure of the sensitivity clause, in the scale-resolved union form:
this is the event `B_osc(m,n)` of the proof of `l.bad.event.lemma` (ABK26),
stated at the event's own threshold rather than at the manuscript's relaxation
of it through the induction-state lower bound on `sigmaBar_{n-1}`. -/
def goodLocalSensitivityFailure (M : ABKModel d) (Ccg : ℝ) (Q : TriadicCube d)
    (n : ℤ) : Set (CutoffSample d) :=
  ⋃ L ∈ Set.Ici n,
    {omega : CutoffSample d |
      goodLocalThreshold M Ccg Q.scale n <
        sensitivityConstMax d * incrementOscGauge₂ Q n L omega}

theorem compl_goodLocalSensitivity_eq (M : ABKModel d) (Ccg : ℝ)
    (Q : TriadicCube d) (n : ℤ) :
    (goodLocalSensitivity M Ccg Q n)ᶜ = goodLocalSensitivityFailure M Ccg Q n := by
  ext omega
  constructor
  · intro h
    rw [Set.mem_compl_iff, mem_goodLocalSensitivity_iff] at h
    push Not at h
    obtain ⟨L, hL, hlt⟩ := h
    exact Set.mem_biUnion hL hlt
  · intro h hmem
    obtain ⟨L, hL, hlt⟩ := Set.mem_iUnion₂.1 h
    exact absurd (hmem L hL) (not_le.2 hlt)

/-- **The decomposition of `not Q(m,n,z)`** used at ABK26: the complement of the
good event is the union of the scale-resolved sensitivity failure and the
failure of the coarse-ellipticity clause. -/
theorem compl_goodLocalEvent_eq (M : ABKModel d) (Ccg : ℝ) (Q : TriadicCube d)
    (n : ℤ) :
    (goodLocalEvent M Ccg Q n)ᶜ =
      goodLocalSensitivityFailure M Ccg Q n ∪ (goodLocalEllipticity M Ccg Q n)ᶜ := by
  rw [goodLocalEvent, Set.compl_inter, compl_goodLocalSensitivity_eq]

/-- The same decomposition with the coarse-ellipticity half replaced by the
manuscript's own failure event of ABK26, using the almost-sure identification
`compl_goodLocalEllipticity_ae_eq`. -/
theorem measureReal_compl_goodLocalEvent_le (M : ABKModel d) {Ccg : ℝ}
    (hCcg : 0 < Ccg) (Q : TriadicCube d) (n : ℤ) :
    (Cutoff.cutoffSampleLaw M).toMeasure.real (goodLocalEvent M Ccg Q n)ᶜ ≤
      (Cutoff.cutoffSampleLaw M).toMeasure.real
          (goodLocalSensitivityFailure M Ccg Q n) +
        (Cutoff.cutoffSampleLaw M).toMeasure.real
          (coarseEllipticityFailure M Ccg Q n) := by
  rw [compl_goodLocalEvent_eq]
  refine le_trans (measureReal_union_le _ _) ?_
  rw [measureReal_compl_goodLocalEllipticity M hCcg Q n]

/-! ## The gate opening (ABK26)

On the event, the rescaled literal increment `k_L - k_n` meets the smallness
gate of the frozen Section 2.4 sensitivity lemmas, which is what "allows us to
switch from the field `a_L` to `a_n` in the cube `z + square_m` for any
`L >= n`". -/

/-- The chained inequality of `e.good.local.events`, read on the event: the
gauged increment is below the coarse-grained lower ellipticity of `a_n`,
discounted by `3^{-(1/4)(n-m)_+}`. -/
theorem incrementOscGauge₂_le_of_mem_goodLocalEvent (M : ABKModel d) {Ccg : ℝ}
    (Q : TriadicCube d) {n : ℤ} {omega : CutoffSample d}
    (homega : omega ∈ goodLocalEvent M Ccg Q n) {L : ℤ} (hL : n ≤ L) :
    sensitivityConstMax d * incrementOscGauge₂ Q n L omega ≤
      (3 : ℝ) ^ (-(1 / 4 : ℝ) * scaleGapPos Q.scale n) *
        cubeLowerEllipticity M Q n (1 / 8) (by norm_num) exponentTwo omega :=
  le_trans (homega.1 L hL) homega.2

/-- The smallness condition `e.J.sensitivity.smallness.condition` /
`e.lambda.sensitivity.smallness.condition` at the cube, after discarding the
discount `3^{-(1/4)(n-m)_+} <= 1`. -/
theorem incrementOscGauge₂_le_inv_sensitivityConstMax_mul_cubeLowerEllipticity
    (M : ABKModel d) {Ccg : ℝ} (Q : TriadicCube d) {n : ℤ}
    {omega : CutoffSample d} (homega : omega ∈ goodLocalEvent M Ccg Q n) {L : ℤ}
    (hL : n ≤ L) :
    incrementOscGauge₂ Q n L omega ≤
      (sensitivityConstMax d)⁻¹ *
        cubeLowerEllipticity M Q n (1 / 8) (by norm_num) exponentTwo omega := by
  have hC : (0 : ℝ) < sensitivityConstMax d := sensitivityConstMax_pos d
  have hlam : 0 ≤ cubeLowerEllipticity M Q n (1 / 8) (by norm_num) exponentTwo omega :=
    cubeLowerEllipticity_nonneg M Q n (1 / 8) (by norm_num) exponentTwo omega
  have hA : (3 : ℝ) ^ (-(1 / 4 : ℝ) * scaleGapPos Q.scale n) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by linarith [scaleGapPos_nonneg Q.scale n])
  have hstep : sensitivityConstMax d * incrementOscGauge₂ Q n L omega ≤
      cubeLowerEllipticity M Q n (1 / 8) (by norm_num) exponentTwo omega := by
    refine (incrementOscGauge₂_le_of_mem_goodLocalEvent M Q homega hL).trans ?_
    calc (3 : ℝ) ^ (-(1 / 4 : ℝ) * scaleGapPos Q.scale n) *
            cubeLowerEllipticity M Q n (1 / 8) (by norm_num) exponentTwo omega
        ≤ 1 * cubeLowerEllipticity M Q n (1 / 8) (by norm_num) exponentTwo omega :=
          mul_le_mul_of_nonneg_right hA hlam
      _ = cubeLowerEllipticity M Q n (1 / 8) (by norm_num) exponentTwo omega :=
          one_mul _
  refine le_of_mul_le_mul_left ?_ hC
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hC), one_mul]
  exact hstep

/-- **The gate opening at the cube level** (ABK26).  On the good event, the
frozen Section 2.4 gate quantity of the rescaled literal increment `k_L -
k_n` is below `C_sens^{-1} lambda_{1/8,2}(z+square_m; a_n)` for every `L >=
n`.  The rescaled increment is the literal one, by
`incrementUnitCube₂_value`. -/
theorem gradientW1Infinity_incrementUnitCube₂_le_of_mem_goodLocalEvent
    (M : ABKModel d) {Ccg : ℝ} (Q : TriadicCube d) {n : ℤ}
    {omega : CutoffSample d} (homega : omega ∈ goodLocalEvent M Ccg Q n) {L : ℤ}
    (hL : n ≤ L) :
    (incrementUnitCube₂ Q n L omega).gradientW1Infinity ≤
      (sensitivityConstMax d)⁻¹ *
        cubeLowerEllipticity M Q n (1 / 8) (by norm_num) exponentTwo omega :=
  (gradientW1Infinity_incrementUnitCube₂_le Q n L omega).trans
    (incrementOscGauge₂_le_inv_sensitivityConstMax_mul_cubeLowerEllipticity
      M Q homega hL)

/-- The same gate at the constant of the frozen `lambda`-sensitivity lemma. -/
theorem gradientW1Infinity_incrementUnitCube₂_le_inv_lambdaSensitivityConst_mul
    (M : ABKModel d) {Ccg : ℝ} (Q : TriadicCube d) {n : ℤ}
    {omega : CutoffSample d} (homega : omega ∈ goodLocalEvent M Ccg Q n) {L : ℤ}
    (hL : n ≤ L) :
    (incrementUnitCube₂ Q n L omega).gradientW1Infinity ≤
      (lambdaSensitivityConst d)⁻¹ *
        cubeLowerEllipticity M Q n (1 / 8) (by norm_num) exponentTwo omega := by
  refine (gradientW1Infinity_incrementUnitCube₂_le_of_mem_goodLocalEvent
    M Q homega hL).trans ?_
  refine mul_le_mul_of_nonneg_right ?_
    (cubeLowerEllipticity_nonneg M Q n (1 / 8) (by norm_num) exponentTwo omega)
  exact inv_anti₀ (lambdaSensitivityConst_pos M.shellPrefix.dimension)
    (lambdaSensitivityConst_le_sensitivityConstMax d)

/-- The same gate at the constant of the frozen response-sensitivity lemma. -/
theorem gradientW1Infinity_incrementUnitCube₂_le_inv_responseSensitivityConst_mul
    (M : ABKModel d) {Ccg : ℝ} (Q : TriadicCube d) {n : ℤ}
    {omega : CutoffSample d} (homega : omega ∈ goodLocalEvent M Ccg Q n) {L : ℤ}
    (hL : n ≤ L) :
    (incrementUnitCube₂ Q n L omega).gradientW1Infinity ≤
      (responseSensitivityConst d)⁻¹ *
        cubeLowerEllipticity M Q n (1 / 8) (by norm_num) exponentTwo omega := by
  refine (gradientW1Infinity_incrementUnitCube₂_le_of_mem_goodLocalEvent
    M Q homega hL).trans ?_
  refine mul_le_mul_of_nonneg_right ?_
    (cubeLowerEllipticity_nonneg M Q n (1 / 8) (by norm_num) exponentTwo omega)
  exact inv_anti₀ (responseSensitivityConst_pos M.shellPrefix.dimension)
    (responseSensitivityConst_le_sensitivityConstMax d)

/-! ## Conditional on the lambda-transfer: the two frozen sensitivity gates

The hypothesis `hlam` below is exactly the missing input described in the module
header: the comparison of the event's own coarse-grained lower ellipticity
`lambda_{1/8,2}(z+square_m; a_n)` with the frozen Section 2.4 unit-cube gauge
`lambda_{3/8,2}` of the rescaled coefficient field.  It is an explicit binder,
never a hidden one; these four declarations are conditional helpers and are not
the local event equality corresponding to `e.good.local.events`. -/

/-- The frozen `lambda`-sensitivity gate for the rescaled increment,
conditional on the lambda-transfer. -/
theorem gradientW1Infinity_incrementUnitCube₂_le_lambdaGate_of_lambdaTransfer
    (M : ABKModel d) {Ccg : ℝ} (Q : TriadicCube d) {n : ℤ}
    {omega : CutoffSample d} (homega : omega ∈ goodLocalEvent M Ccg Q n) {L : ℤ}
    (hL : n ≤ L) (a : CoeffOn (cubeDomain (originCube d 0)))
    (hlam : cubeLowerEllipticity M Q n (1 / 8) (by norm_num) exponentTwo omega ≤
      unitCubeLambda (3 / 8) (.finite 2) a) :
    (incrementUnitCube₂ Q n L omega).gradientW1Infinity ≤
      (lambdaSensitivityConst d)⁻¹ * unitCubeLambda (3 / 8) (.finite 2) a := by
  refine (gradientW1Infinity_incrementUnitCube₂_le_inv_lambdaSensitivityConst_mul
    M Q homega hL).trans ?_
  exact mul_le_mul_of_nonneg_left hlam
    (inv_nonneg.2 (lambdaSensitivityConst_pos M.shellPrefix.dimension).le)

/-- The frozen response-sensitivity gate for the rescaled increment,
conditional on the lambda-transfer. -/
theorem gradientW1Infinity_incrementUnitCube₂_le_responseGate_of_lambdaTransfer
    (M : ABKModel d) {Ccg : ℝ} (Q : TriadicCube d) {n : ℤ}
    {omega : CutoffSample d} (homega : omega ∈ goodLocalEvent M Ccg Q n) {L : ℤ}
    (hL : n ≤ L) (a : CoeffOn (cubeDomain (originCube d 0)))
    (hlam : cubeLowerEllipticity M Q n (1 / 8) (by norm_num) exponentTwo omega ≤
      unitCubeLambda (3 / 8) (.finite 2) a) :
    (incrementUnitCube₂ Q n L omega).gradientW1Infinity ≤
      (responseSensitivityConst d)⁻¹ * unitCubeLambda (3 / 8) (.finite 2) a := by
  refine (gradientW1Infinity_incrementUnitCube₂_le_inv_responseSensitivityConst_mul
    M Q homega hL).trans ?_
  exact mul_le_mul_of_nonneg_left hlam
    (inv_nonneg.2 (responseSensitivityConst_pos M.shellPrefix.dimension).le)

/-- **The `lambda`-sensitivity switch on the good event**, conditional on the
lambda-transfer: the coefficient switch of ABK26, in the form used. -/
theorem lambda_sensitivity_of_mem_goodLocalEvent_of_lambdaTransfer
    (M : ABKModel d) {Ccg : ℝ} (Q : TriadicCube d) {n : ℤ}
    {omega : CutoffSample d} (homega : omega ∈ goodLocalEvent M Ccg Q n) {L : ℤ}
    (hL : n ≤ L) (a : CoeffOn (cubeDomain (originCube d 0)))
    (hlam : cubeLowerEllipticity M Q n (1 / 8) (by norm_num) exponentTwo omega ≤
      unitCubeLambda (3 / 8) (.finite 2) a)
    (s : ℝ) (q : Ch02.MultiscaleExponent) (hs : 0 < s) (hs2 : s ≤ 1 / 2)
    (hq : q.IsAdmissible) :
    (unitCubeLambda s q
      (perturbCoeffOn (cubeDomain (originCube d 0)) a
        (incrementUnitCube₂ Q n L omega).toLInfSkewMatrixFieldOn 1))⁻¹
      ≤ (1 + lambdaSensitivityConst d *
          (incrementUnitCube₂ Q n L omega).gradientW1Infinity *
          (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
        (unitCubeLambda s q a)⁻¹ :=
  (lambda_sensitivity_const M.shellPrefix.dimension).2 a _
    (gradientW1Infinity_incrementUnitCube₂_le_lambdaGate_of_lambdaTransfer
      M Q homega hL a hlam) s q hs hs2 hq

/-- **The response-`J` sensitivity switch on the good event**, conditional on the
lambda-transfer: the coefficient switch of ABK26, in the form used. -/
theorem responseJ_sensitivity_of_mem_goodLocalEvent_of_lambdaTransfer
    (M : ABKModel d) {Ccg : ℝ} (Q : TriadicCube d) {n : ℤ}
    {omega : CutoffSample d} (homega : omega ∈ goodLocalEvent M Ccg Q n) {L : ℤ}
    (hL : n ≤ L) (a : CoeffOn (cubeDomain (originCube d 0)))
    (hlam : cubeLowerEllipticity M Q n (1 / 8) (by norm_num) exponentTwo omega ≤
      unitCubeLambda (3 / 8) (.finite 2) a)
    (p q : Vec d) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    responseJ (cubeDomain (originCube d 0))
        (perturbCoeffOn (cubeDomain (originCube d 0)) a
          (incrementUnitCube₂ Q n L omega).toLInfSkewMatrixFieldOn 1) p q
      ≤ (1 + δ + responseSensitivityConst d *
          (incrementUnitCube₂ Q n L omega).gradientW1Infinity *
          (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
          responseJ (cubeDomain (originCube d 0)) a p q +
        responseSensitivityConst d * δ⁻¹ *
          (vecNormSq p * (incrementUnitCube₂ Q n L omega).w1Infinity ^ 2 *
              (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ +
            |vecDot p q| *
                (incrementUnitCube₂ Q n L omega).gradientW1Infinity ^ 2 *
              (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ ^ 2) :=
  (responseJ_sensitivity_const M.shellPrefix.dimension).2 a _
    (gradientW1Infinity_incrementUnitCube₂_le_responseGate_of_lambdaTransfer
      M Q homega hL a hlam) p q δ hδ hδ1

end

end Algsuperdiff.Section3.Provider.BadEvents
