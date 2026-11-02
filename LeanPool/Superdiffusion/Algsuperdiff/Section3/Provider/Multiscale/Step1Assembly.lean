/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.CrudeResponseBound

/-!
# Step1Assembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The assembly of Step 1: `e.good.simplex.consequence` at the cube carrier

`CrudeResponseBound.lean` proves the middle of Step 1 of
`p.bfA.multiscalebound` (ABK26): the two crude response legs at `a_L`,
transported to the multiscale gauges `Lambda_{1/4,2}(z + square_j; a_j)` and
`lambda^{-1}_{1/4,2}(z + square_j; a_j)` of the containing cube.
`JResponseApplication.lean` proves the polarization split and the
running-diffusivity comparison.  This module proves local cube-carrier results
by supplying the two missing links and running the final arithmetic:

2. **the arithmetic**, with the `cstar^{-1}` correction.

## The manuscript's unnamed `C`s, made explicit

Every constant below is explicit and dimension-free except the one frozen
`Lambda`-sensitivity constant `bigLambdaSensitivityConst d`:

* `p̂` leg:  `80. 3^{(j-k)/2} (1 + 8 C_{Lambda} cstar^{-1} gamma 3^{-2 gamma j}
  ||k_L - k_j||^2)`;
* `q̂` leg:  `40 . 3^{(j-k)/2} . 3^{gamma (i - j)}`;
* assembled:  four times each, by the polarization split.

The `q̂` leg's factor `(1 + C_lambda |grad (k_L - k_j)| lambda^{-1}_{3/8,2})`,
which the manuscript hides inside `C`, is collapsed to `2` by the proved
`e.we.can.apply.cg` gate (`lambdaGateFactor_le_one_of_notMem_bad_ae`); the `p̂`
leg's `Lambda` and `lambda^{-1}` gauges are collapsed by the two halves of `not
B_loc`; the two `sigmabar` ratios are the proved
`sigmaBar_le_four_mul_sigmaBar` and `sigmaBar_le_four_mul_rpow_mul_sigmaBar`
(constant `4` each).

## Why the statements are almost-sure

`e.Bloc.def` is stated against the measurable representatives
`cubeLowerEllipticityInv` / `cubeUpperEllipticity` built by `A.mk`, of which no
pointwise information is available; transporting either to the Chapter 2 gauge
`Ch02.lambdaSq` / `Ch02.LambdaSq` that the sensitivity conclusions carry
therefore costs one null set.  This is the same carrier phenomenon as in
`LambdaTransfer.lean` and `JSmallness.lean`, and all proved smallness gates are
already discharged, so no gate hypothesis appears anywhere below (reading,
for the `q̂` leg).

## Main results

* `cubeUpperEllipticityLiteral_eq_LambdaSq`: **the `Lambda`-half literal
  identification**, the mirror of `cubeLowerEllipticityInvLiteral_inv_eq_lambdaSq`.
* `cubeUpperEllipticity_le_ten_mul_sigmaBar_of_notMem_badLoc`,
  `LambdaSq_quarter_le_ten_mul_sigmaBar_of_notMem_badLoc_ae`: **the `Lambda`-half
  of `not B_loc`**, at the representative and at the Chapter 2 gauge.
* `lambdaSq_quarter_inv_le_ten_mul_inv_sigmaBar_of_notMem_badLoc_ae`: its
  `lambda`-mirror at the same carrier.
* `inv_sigmaBar_sq_le_four_mul_inv_cstar_mul_gamma_mul_rpow`: **the
  `cstar^{-1}` correction**.
* `lambdaGateFactor_le_one_of_notMem_bad_ae`: the `e.we.can.apply.cg` gate as the
  factor bound the `q̂` leg consumes.
* `cubeLowerEllipticityInvLiteral_eq_lambdaSq_inv`: the `lambda`-half literal
  identification, reading the literal lower observable as
  `lambda^{-1}_{s,q}` of the Chapter 2 family.

## References

* ABK26, `e.good.simplex.consequence`, Step 1 of `p.bfA.multiscalebound`,
  `e.shom.h.bounds`, `e.Bloc.def`, `e.SW.def`.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents

noncomputable section

variable {d : ℕ}

/-- Nonzero dimension, from the paper-wide assumption `2 <= d` stored in the
model. -/
private theorem neZero_of_model_step1 (M : ABKModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩

/-! ## The `Lambda`-half literal identification -/

/-- **The `Lambda`-half literal identification.**  The literal upper observable of
`CubeEllipticity.lean` is CoarseGraining's `Ch02.LambdaSq` of the compatible
triadic family of the actual cutoff.  This is the exact mirror of the proved
`cubeLowerEllipticityInvLiteral_inv_eq_lambdaSq` of `LambdaTransfer.lean`, and
it is what moves the second disjunct of `e.Bloc.def` onto the carrier at which
`e.big.Lambda.sensitivity` is stated. -/
theorem cubeUpperEllipticityLiteral_eq_LambdaSq (M : ABKModel d)
    (Q : TriadicCube d) (cutoffScale : ℤ) (s : ℝ)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent)
    (omega : CutoffSample d) :
    cubeUpperEllipticityLiteral M Q cutoffScale s q omega =
      Ch02.LambdaSq Q s q.1
        (coefficientCutoffTriadicCoeffFamily M cutoffScale omega) := by
  let : NeZero d := neZero_of_model_step1 M
  unfold cubeUpperEllipticityLiteral
  rw [Ch04.LambdaSqCoeffField]
  simp only [dite_eq_left
    (coefficientCutoff_aeLocallyUniformlyEllipticField M cutoffScale omega)]
  exact Ch02.LambdaSq_eq_ofAEEq (fun _ => Filter.EventuallyEq.rfl) Q s q.1

/-- The literal lower observable, read directly as `lambda^{-1}_{s,q}` of the
Chapter 2 family.  This is the proved
`cubeLowerEllipticityInvLiteral_inv_eq_lambdaSq` with the inverse moved to the
right side. -/
theorem cubeLowerEllipticityInvLiteral_eq_lambdaSq_inv (M : ABKModel d)
    (Q : TriadicCube d) (cutoffScale : ℤ) (s : ℝ)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent)
    (omega : CutoffSample d) :
    cubeLowerEllipticityInvLiteral M Q cutoffScale s q omega =
      (Ch02.lambdaSq Q s q.1
        (coefficientCutoffTriadicCoeffFamily M cutoffScale omega))⁻¹ := by
  rw [← cubeLowerEllipticityInvLiteral_inv_eq_lambdaSq, inv_inv]

/-! ## The two halves of `not B_loc` -/

/-- **The `Lambda`-half of `not B_loc`, at the representative** (ABK26, the
second disjunct of `e.Bloc.def`): off `B_loc(z + square_j)` the coarse-grained
upper ellipticity of `a_j` on the cube is at most `10 sigmabar_j`.  This is the
exact mirror of the proved
`sigmaBar_le_ten_mul_cubeLowerEllipticity_of_notMem_badLoc` of
`JSmallness.lean`; no positivity binder is needed on this side, because nothing
is inverted. -/
theorem cubeUpperEllipticity_le_ten_mul_sigmaBar_of_notMem_badLoc (M : ABKModel d)
    (Q : TriadicCube d) {omega : CutoffSample d} (homega : omega ∉ badLoc M Q) :
    cubeUpperEllipticity M Q Q.scale (1 / 4) (by norm_num) exponentTwo omega ≤
      10 * ((Algsuperdiff.Section3.Annealed.sigmaBar M Q.scale : ℝ)) :=
  not_lt.1 fun hcon => homega (Set.mem_union_right _ hcon)

/-- **The `Lambda`-half of `not B_loc`, at the Chapter 2 gauge.**  Almost surely,
off `B_loc(z + square_j)`,

```
Lambda_{1/4,2}(z + square_j; a_j)  <=  10 sigmabar_j .
```

The transport from the measurable representative to `Ch02.LambdaSq` is
`cubeUpperEllipticity_ae_eq_literal` composed with
`cubeUpperEllipticityLiteral_eq_LambdaSq`; the null set is the representative's
own, exactly as for the `lambda` half. -/
theorem LambdaSq_quarter_le_ten_mul_sigmaBar_of_notMem_badLoc_ae (M : ABKModel d)
    (Q : TriadicCube d) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∉ badLoc M Q →
        Ch02.LambdaSq Q (1 / 4) (.finite 2)
            (coefficientCutoffTriadicCoeffFamily M Q.scale omega) ≤
          10 * ((Algsuperdiff.Section3.Annealed.sigmaBar M Q.scale : ℝ)) := by
  filter_upwards [cubeUpperEllipticity_ae_eq_literal M Q Q.scale (1 / 4)
    (by norm_num) exponentTwo] with omega homega hloc
  have hle := cubeUpperEllipticity_le_ten_mul_sigmaBar_of_notMem_badLoc M Q hloc
  rwa [homega, cubeUpperEllipticityLiteral_eq_LambdaSq, exponentTwo_val] at hle

/-- **The `lambda`-half of `not B_loc`, at the Chapter 2 gauge** (ABK26, the
first disjunct of `e.Bloc.def`).  Almost surely, off `B_loc(z + square_j)`,

```
lambda^{-1}_{1/4,2}(z + square_j; a_j)  <=  10 sigmabar_j^{-1} .
```

(The proved `sigmaBar_le_ten_mul_cubeLowerEllipticity_of_notMem_badLoc` is a
cousin at the representative `cubeLowerEllipticity`; this proof does NOT use it
— it negates `badLoc`'s first disjunct directly;.) -/
theorem lambdaSq_quarter_inv_le_ten_mul_inv_sigmaBar_of_notMem_badLoc_ae
    (M : ABKModel d) (Q : TriadicCube d) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∉ badLoc M Q →
        (Ch02.lambdaSq Q (1 / 4) (.finite 2)
            (coefficientCutoffTriadicCoeffFamily M Q.scale omega))⁻¹ ≤
          10 * ((Algsuperdiff.Section3.Annealed.sigmaBar M Q.scale : ℝ))⁻¹ := by
  filter_upwards [cubeLowerEllipticityInv_ae_eq_literal M Q Q.scale (1 / 4)
    (by norm_num) exponentTwo] with omega homega hloc
  have hle : cubeLowerEllipticityInv M Q Q.scale (1 / 4) (by norm_num) exponentTwo
      omega ≤ 10 * ((Algsuperdiff.Section3.Annealed.sigmaBar M Q.scale : ℝ))⁻¹ :=
    not_lt.1 fun hcon => hloc (Set.mem_union_left _ hcon)
  rwa [homega, cubeLowerEllipticityInvLiteral_eq_lambdaSq_inv, exponentTwo_val]
    at hle

/-! ## The `cstar^{-1}` correction -/

/-- The lower branch of `e.shom.h.bounds` (ABK26) gives `sigmabar_m^2 >= (1/4)
cstar gamma^{-1} 3^{2 gamma m}`, hence

```
sigmabar_m^{-2}  <=  4 cstar^{-1} gamma 3^{-2 gamma m} ,
```

for every scale `m <= m0`.  The factor `cstar^{-1}`, absent from the printed
display, cannot be absorbed into a dimension-only constant: the standing
assumptions bound `cstar` only from above. -/
theorem inv_sigmaBar_sq_le_four_mul_inv_cstar_mul_gamma_mul_rpow (M : ABKModel d)
    {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) {m : ℤ}
    (hm : m ≤ m0) :
    (((Algsuperdiff.Section3.Annealed.sigmaBar M m : ℝ)) ^ 2)⁻¹ ≤
      4 * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
        (3 : ℝ) ^ (-(2 * M.gamma * (m : ℝ))) := by
  have hc : 0 < Algsuperdiff.Section3.Disorder.cstar M :=
    (Algsuperdiff.Section3.Disorder.cstar_characterization M).1
  have hg : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hpow : (0 : ℝ) < (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hlow : (1 / 4 : ℝ) *
      max (Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) (M.nu ^ 2)
      ≤ ((Algsuperdiff.Section3.Annealed.sigmaBar M m : ℝ)) ^ 2 := (hS.1 m hm).1
  have hstep : (1 / 4 : ℝ) * (Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
      (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))
      ≤ ((Algsuperdiff.Section3.Annealed.sigmaBar M m : ℝ)) ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)) hlow
  have hrhs : 4 * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
      (3 : ℝ) ^ (-(2 * M.gamma * (m : ℝ))) =
      ((1 / 4 : ℝ) * (Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))))⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
    field_simp
  rw [hrhs]
  exact inv_anti₀ (by positivity) hstep

/-! ## The `e.we.can.apply.cg` gate as a factor bound -/

/-- **The gate of `e.we.can.apply.cg`, read as a factor bound** (ABK26).  Almost
surely, on `not B_osc(z + square_j)` and `not B_loc(z + square_j)` and under the
induction state, the multiplicative sensitivity defect of the `q̂` leg is at
most `1`, for every `L >= j`:

```
C_{(e.lambda.sensitivity)} |grad (k_L - k_j)| lambda^{-1}_{3/8,2}(z+square_j;a_j)
  <=  1 .
```

This is the proved
`gradientW1Infinity_incrementUnitCube_le_lambdaGate_notMem_bad_ae` divided by
the (strictly positive) gauge; it is what collapses the manuscript's hidden `C`
on the `q̂` leg to the explicit factor `2`. -/
theorem lambdaGateFactor_le_one_of_notMem_bad_ae (hd : 2 ≤ d) (M : ABKModel d)
    {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) (Q : TriadicCube d)
    (hm : Q.scale ≤ m0) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∉ badOsc M Q → omega ∉ badLoc M Q → ∀ L : ℤ, Q.scale ≤ L →
        lambdaSensitivityConst d *
            (incrementUnitCube₂ Q Q.scale L omega).gradientW1Infinity *
            (Ch02.lambdaSq Q (3 / 8) (.finite 2)
              (coefficientCutoffTriadicCoeffFamily M Q.scale omega))⁻¹ ≤ 1 := by
  let : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) hd)⟩
  filter_upwards [gradientW1Infinity_incrementUnitCube_le_lambdaGate_notMem_bad_ae
    hd M hS Q hm] with omega hgate hosc hloc L hL
  have h := hgate hosc hloc L hL
  rw [unitCubeLambda_unitRescaledCutoffCoeff M Q Q.scale (3 / 8) (.finite 2)
    omega] at h
  have hpos : (0 : ℝ) < Ch02.lambdaSq Q (3 / 8) (.finite 2)
      (coefficientCutoffTriadicCoeffFamily M Q.scale omega) :=
    Ch02.lambdaSq_pos Q _ (by norm_num) (by norm_num)
  have hC : (0 : ℝ) < lambdaSensitivityConst d := lambdaSensitivityConst_pos hd
  have hmul := mul_le_mul_of_nonneg_left h
    (le_of_lt (mul_pos hC (inv_pos.2 hpos)))
  calc lambdaSensitivityConst d *
        (incrementUnitCube₂ Q Q.scale L omega).gradientW1Infinity *
        (Ch02.lambdaSq Q (3 / 8) (.finite 2)
          (coefficientCutoffTriadicCoeffFamily M Q.scale omega))⁻¹
      = lambdaSensitivityConst d *
          (Ch02.lambdaSq Q (3 / 8) (.finite 2)
            (coefficientCutoffTriadicCoeffFamily M Q.scale omega))⁻¹ *
          (incrementUnitCube₂ Q Q.scale L omega).gradientW1Infinity := by ring
    _ ≤ lambdaSensitivityConst d *
          (Ch02.lambdaSq Q (3 / 8) (.finite 2)
            (coefficientCutoffTriadicCoeffFamily M Q.scale omega))⁻¹ *
          ((lambdaSensitivityConst d)⁻¹ *
            Ch02.lambdaSq Q (3 / 8) (.finite 2)
              (coefficientCutoffTriadicCoeffFamily M Q.scale omega)) := hmul
    _ = 1 := by field_simp

/-! ## The two normalized legs -/


/-! ## The arithmetic -/


/-! ## The manuscript's Whitney reading of the `q̂` exponent -/


end

end Algsuperdiff.Section3.Provider.Multiscale
