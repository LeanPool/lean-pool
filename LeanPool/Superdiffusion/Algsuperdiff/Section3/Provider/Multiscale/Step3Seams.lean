/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.LayerMass
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SimplexResponseBound
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.Step1Assembly

/-!
# Step3Seams

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The Step-3 seams of `p.bfA.multiscalebound`: Step 1 at the simplex carrier,
and the per-layer majorant

This module supplies the two halves of that hypothesis that are provable below
the competitor construction:

1. **Step 1 at the manuscript's own simplex carrier.**  `Step1Assembly` proves
   `e.good.simplex.consequence` (assembled) at a *triadic descendant cube*
   `R` of the Whitney cube `Q = z + square_j`; the manuscript states it at a
   **simplex** `spx` of `SW(square_n)` contained in `Q`.
   `SimplexResponseBound` proves the corresponding local estimates for the two
   *crude* legs, at the cost of the explicit dissection constant
   `simplexCrudeConst d s = 6 d (d+1)/(1-3^{2s-1})` in place of the
   cube-carrier `1/2`.  Below, that substitution is run through the whole of
   Step 1: the two normalized legs and the polarization assembly are re-derived
   **at the simplex carrier**, with the same `sigmabar` arithmetic, the same
   correction `cstar^{-1}`, and the constants `80 -> 160 C(d,s)`, `40 -> 80
   C(d,s)`, `320 -> 640 C(d,s)`, `160 -> 320 C(d,s)`.

   The `1/2 -> C(d,s)` substitution is isolated in two **abstract-real** cores
   (`normalized_flux_core`, `normalized_slope_core`) which carry no cube, no
   sample and no `rpow`: they take the four proved inequalities (`Lambda <= 10
   sigmabar_j`, `lambda^{-1} <= 10 sigmabar_j^{-1}`, `sigmabar_j <= 4
   sigmabar_i`, `sigmabar_j^{-2} <= T`) and the crude base bound at an
   arbitrary nonnegative constant `c`, and return the assembled leg.
   Instantiated at `c = 1/2` they reproduce `Step1Assembly`'s own constants
   (machine-checked by the two `example`s following the cores).

2. The sub-family `S` of the statement is the good part of the layer for the
   first leg of `layerContrib` and the collar part for the second.

3. **The `4 gamma <= 1 - b` gate, discharged**.
   `ConclusionAssembly`/`LayerMass` carry `hgamma : 4 * gamma <= 1 - b` as an
   explicit numeric A input.  Wherever the printed admissibility `C(d) <= E
   cstar` (or just `4 <= E`) and the printed scale restriction `gamma <=
   E^{-5}` are in scope, the gate is a **consequence**, not a new assumption:
   `AdmissibleGates.gamma_le_one_div_twenty_of_four_le` gives `gamma <= 1/20`'s
   own `9 b <= 1` gives `b <= 1/9`, so `4 gamma <= 1/5 <= 8/9 <= 1 - b` with a
   factor `~228` of slack.  This module is the first consumer with both in
   scope and proves the discharge.

## What is not proved in this file

* The collar leg's *slope* input `e.bounds.on.slopes.when.bad`, `|(grad.
  hatD_q)(spx)|^2/|q|^2 + |grad hatlinear_p(spx)|^2/|p|^2 <=^{2 b (k+h_k)}`, is
  a statement about the piecewise-affine competitor `(hatlinear_p, hatD_q)` of
  `l.piecewise.affine.approx`, not about `bfA`.  It is not proved or assumed
  here: `sum_sum_ofReal_cellWeight_le_ofReal_mul` takes the per-cell bound of
  *whichever* leg as its own abstract datum `C`.  `LayerUniform.lean` and the
  later affine envelope providers supply concrete versions downstream.
* The instantiation of `sum_of_a_decomp`'s `aS` at
  `simplexCoeffOn (coefficientCutoffTriadicCoeffFamily M L omega)` — i.e. the
  at-consumer wiring with the competitor pair `(F, G)` — is downstream of the
  competitor construction and is not performed here;
  `ConclusionCompetitor.lean` later performs that instantiation.
* Seams 2 (the squared three-term composition) and 3 (the Orlicz half of the
  `3^{gamma hsep}` reduction) are untouched in this file; see
  `ConclusionSeam2*.lean`, `ConclusionSeam3*.lean`, and
  `ConclusionAssemblyFinal.lean` for the later route.

## Main results

* `responseJ_simplexDomain_normalized_flux_le_of_notMem_bad_ae`,
  `responseJ_simplexDomain_normalized_slope_le_of_notMem_bad_ae`: the two legs
  at the **simplex** carrier.
* `blockVecDot_coarseBlockMatrix_simplexDomain_normalized_le_of_notMem_bad_ae`:
  **`e.good.simplex.consequence` at the manuscript's own carrier**.
* `sum_cellWeight_whitneySimplexCells_le`: the cells of a Whitney cube carry at
  most the cube's mass.
* `sum_sum_ofReal_cellWeight_le_ofReal_mul`: one Whitney layer of
  `e.sum-of-a-decomp`, majorized in the shape of one leg of `layerContrib`.

## References

* ABK26, `e.sum-of-a-decomp`, `e.good.simplex.consequence`, Step 1, Step 3,
  `e.SW.def`.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Whitney

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The `4 gamma <= 1 - b` gate, discharged -/


/-! ## The two abstract-real cores of the Step-1 assembly -/

/-- **The `p̂`-leg arithmetic, with the crude constant free.**  No cube, no sample,
no `rpow`: `c` is the constant of the crude response bound at whatever carrier
it is proved on (`1/2` at a triadic descendant cube, `simplexCrudeConst d s` at
a Kuhn cell), `A = Lambda_{1/4,2}(Q;a_j)`, `B = lambda^{-1}_{1/4,2}(Q;a_j)`,
`sj = sigmabar_j`, `si = sigmabar_i`, `T` any majorant of `sigmabar_j^{-2}`,
`w` the increment gauge and `np = |p̂|^2`.  The conclusion is
`Step1Assembly.responseJ_normalized_flux_le_of_notMem_bad_ae` with `80`
replaced by `160 c`. -/
private theorem normalized_flux_core {J c W A B si sj Cb w T np : ℝ}
    (hc : 0 ≤ c) (hW : 0 ≤ W) (hsj : 0 < sj) (hsi : 0 < si) (hCb : 0 ≤ Cb)
    (hnp : 0 ≤ np) (hA : A ≤ 10 * sj) (hB : B ≤ 10 * sj⁻¹) (hratio : sj ≤ 4 * si)
    (hT : (sj ^ 2)⁻¹ ≤ T)
    (hbase : J ≤ c * (W * (4 * A + Cb * 8 * w ^ 2 * B)) * (si⁻¹ * np)) :
    J ≤ 160 * c * W * (1 + 2 * Cb * T * w ^ 2) * np := by
  have hsiinv : (0 : ℝ) < si⁻¹ := inv_pos.2 hsi
  have hsjinv : (0 : ℝ) < sj⁻¹ := inv_pos.2 hsj
  have hw2 : (0 : ℝ) ≤ w ^ 2 := sq_nonneg w
  have hstep1 : 2 * A * si⁻¹ ≤ 80 := by
    have h1 : A * si⁻¹ ≤ 10 * sj * si⁻¹ := mul_le_mul_of_nonneg_right hA hsiinv.le
    have h2 : sj * si⁻¹ ≤ 4 := by
      have h := mul_le_mul_of_nonneg_right hratio hsiinv.le
      rwa [mul_assoc, mul_inv_cancel₀ (ne_of_gt hsi), mul_one] at h
    nlinarith [h1, h2]
  have hinvle : si⁻¹ ≤ 4 * sj⁻¹ := by
    have h := inv_anti₀ hsj hratio
    have hrw : (4 * si)⁻¹ = 4⁻¹ * si⁻¹ := by rw [mul_inv]
    rw [hrw] at h
    linarith [h]
  have hstep2 : 4 * Cb * w ^ 2 * B * si⁻¹ ≤ 160 * Cb * T * w ^ 2 := by
    have h1 : B * si⁻¹ ≤ 10 * sj⁻¹ * si⁻¹ := mul_le_mul_of_nonneg_right hB hsiinv.le
    have h2 : sj⁻¹ * si⁻¹ ≤ 4 * (sj ^ 2)⁻¹ := by
      have h := mul_le_mul_of_nonneg_left hinvle hsjinv.le
      have hid : sj⁻¹ * (4 * sj⁻¹) = 4 * (sj ^ 2)⁻¹ := by field_simp
      rwa [hid] at h
    have h3 : B * si⁻¹ ≤ 40 * T := by
      calc B * si⁻¹ ≤ 10 * sj⁻¹ * si⁻¹ := h1
        _ = 10 * (sj⁻¹ * si⁻¹) := by ring
        _ ≤ 10 * (4 * (sj ^ 2)⁻¹) := by linarith [h2]
        _ ≤ 10 * (4 * T) := by linarith [hT]
        _ = 40 * T := by ring
    have hk : (0 : ℝ) ≤ 4 * Cb * w ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) hCb) hw2
    calc 4 * Cb * w ^ 2 * B * si⁻¹ = 4 * Cb * w ^ 2 * (B * si⁻¹) := by ring
      _ ≤ 4 * Cb * w ^ 2 * (40 * T) := mul_le_mul_of_nonneg_left h3 hk
      _ = 160 * Cb * T * w ^ 2 := by ring
  have hinner : c * (4 * A + Cb * 8 * w ^ 2 * B) * si⁻¹ ≤
      160 * c * (1 + 2 * Cb * T * w ^ 2) := by
    have hsum : 2 * A * si⁻¹ + 4 * Cb * w ^ 2 * B * si⁻¹ ≤
        80 + 160 * Cb * T * w ^ 2 := by linarith [hstep1, hstep2]
    calc c * (4 * A + Cb * 8 * w ^ 2 * B) * si⁻¹
        = 2 * c * (2 * A * si⁻¹ + 4 * Cb * w ^ 2 * B * si⁻¹) := by ring
      _ ≤ 2 * c * (80 + 160 * Cb * T * w ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (by linarith)
      _ = 160 * c * (1 + 2 * Cb * T * w ^ 2) := by ring
  refine hbase.trans ?_
  calc c * (W * (4 * A + Cb * 8 * w ^ 2 * B)) * (si⁻¹ * np)
      = W * (c * (4 * A + Cb * 8 * w ^ 2 * B) * si⁻¹) * np := by ring
    _ ≤ W * (160 * c * (1 + 2 * Cb * T * w ^ 2)) * np :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinner hW) hnp
    _ = 160 * c * W * (1 + 2 * Cb * T * w ^ 2) * np := by ring

/-- **The `q̂`-leg arithmetic, with the crude constant free.**  `G` is the
multiplicative sensitivity defect of `e.we.can.apply.cg` (collapsed to `<= 1`
upstream), `R` any majorant of `sigmabar_i sigmabar_j^{-1}/4`.  The conclusion
is `Step1Assembly.responseJ_normalized_slope_le_of_notMem_bad_ae` with `40`
replaced by `80 c`. -/
private theorem normalized_slope_core {J c W B G si sj R nq : ℝ}
    (hc : 0 ≤ c) (hW : 0 ≤ W) (hsi : 0 < si) (hnq : 0 ≤ nq) (hB0 : 0 ≤ B)
    (hG : G ≤ 1) (hB : B ≤ 10 * sj⁻¹) (hrat : si * sj⁻¹ ≤ 4 * R)
    (hbase : J ≤ c * (W * ((1 + G) * B)) * (si * nq)) :
    J ≤ 80 * c * W * R * nq := by
  have hinner : (1 + G) * B * si ≤ 80 * R := by
    have hstep1 : (1 + G) * B ≤ 2 * B := by nlinarith [hG, hB0]
    calc (1 + G) * B * si ≤ 2 * B * si := mul_le_mul_of_nonneg_right hstep1 hsi.le
      _ ≤ 2 * (10 * sj⁻¹) * si :=
          mul_le_mul_of_nonneg_right (by linarith [hB]) hsi.le
      _ = 20 * (si * sj⁻¹) := by ring
      _ ≤ 20 * (4 * R) := by linarith [hrat]
      _ = 80 * R := by ring
  refine hbase.trans ?_
  calc c * (W * ((1 + G) * B)) * (si * nq)
      = W * (c * ((1 + G) * B * si)) * nq := by ring
    _ ≤ W * (c * (80 * R)) * nq :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinner hc) hW) hnq
    _ = 80 * c * W * R * nq := by ring

/-! ## The two normalized legs at the simplex carrier -/

/-- Almost surely, on `not B_osc(z + square_j)` and `not B_loc(z + square_j)` and
under the induction state, for every `L >= j`, every scale `i` with `j <= i <=
m0`, every Kuhn cell `spx` whose support cube is a triadic descendant of `z +
square_j` at scale `k`, and every `p̂`,

```
J(spx, sigmabar_i^{-1/2} p̂, 0; a_L)
  <=  160 C(d,1/4) . 3^{(j-k)/2}
        ( 1 + 8 C_{(e.big.Lambda.sensitivity)} cstar^{-1} gamma 3^{-2 gamma j}
              ||k_L - k_j||^2 ) |p̂|^2 ,
```

with `C(d,1/4) = simplexCrudeConst d (1/4) = 6 d (d+1)/(1 - 3^{-1/2})`.  This is
`Step1Assembly.responseJ_normalized_flux_le_of_notMem_bad_ae` with the
cube-carrier crude constant `1/2` replaced by the dissection constant of
`SimplexResponseBound.responseJ_simplexDomain_zero_flux_le_LambdaSq`; the rest
of the chain (`Lambda <= 10 sigmabar_j`, `lambda^{-1} <= 10 sigmabar_j^{-1}`,
`sigmabar_j sigmabar_i^{-1} <= 4`, the `cstar^{-1}` correction) is verbatim the
same. -/
theorem responseJ_simplexDomain_normalized_flux_le_of_notMem_bad_ae (hd : 2 ≤ d)
    (M : ABKModel d) {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) (Q : TriadicCube d)
    (hm : Q.scale ≤ m0) (k : ℤ) {i : ℤ} (hji : Q.scale ≤ i) (hi : i ≤ m0) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∉ badOsc M Q → omega ∉ badLoc M Q → ∀ L : ℤ, Q.scale ≤ L →
        ∀ T : KuhnCell d, T.supportCube ∈ descendantsAtScale Q k → ∀ p : Vec d,
          Ch02.responseJ (simplexDomain T)
              (simplexCoeffOn (coefficientCutoffTriadicCoeffFamily M L omega) T)
              ((Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • p)
              0 ≤
            160 * simplexCrudeConst d (1 / 4) *
                Ch02.multiscaleDescendantWeight Q k (1 / 4) *
                (1 + 8 * bigLambdaSensitivityConst d *
                    (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
                    (3 : ℝ) ^ (-(2 * M.gamma * (Q.scale : ℝ))) *
                    (incrementUnitCube₂ Q Q.scale L omega).w1Infinity ^ 2) *
                vecNormSq p := by
  let : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) hd)⟩
  have hinvSq := inv_sigmaBar_sq_le_four_mul_inv_cstar_mul_gamma_mul_rpow M hS
    (le_trans hji hi)
  filter_upwards [LambdaSq_quarter_le_of_notMem_bad_ae hd M hS Q hm,
    LambdaSq_quarter_le_ten_mul_sigmaBar_of_notMem_badLoc_ae M Q,
    lambdaSq_quarter_inv_le_ten_mul_inv_sigmaBar_of_notMem_badLoc_ae M Q]
    with omega hLamL hLam hlam hosc hloc L hL T hT p
  set sj : ℝ := ((Algsuperdiff.Section3.Annealed.sigmaBar M Q.scale : ℝ)) with hsjdef
  set si : ℝ := ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) with hsidef
  have hsj : 0 < sj := (Algsuperdiff.Section3.Annealed.sigmaBar M Q.scale).2
  have hsi : 0 < si := (Algsuperdiff.Section3.Annealed.sigmaBar M i).2
  set W : ℝ := Ch02.multiscaleDescendantWeight Q k (1 / 4) with hWdef
  have hW : 0 ≤ W := multiscaleDescendantWeight_nonneg Q k (1 / 4)
  set S : ℝ := simplexCrudeConst d (1 / 4) with hSdef
  have hSnn : 0 ≤ S := simplexCrudeConst_nonneg d (by norm_num)
  set A : ℝ := Ch02.LambdaSq Q (1 / 4) (.finite 2)
    (coefficientCutoffTriadicCoeffFamily M Q.scale omega) with hAdef
  set B : ℝ := (Ch02.lambdaSq Q (1 / 4) (.finite 2)
    (coefficientCutoffTriadicCoeffFamily M Q.scale omega))⁻¹ with hBdef
  set Cb : ℝ := bigLambdaSensitivityConst d with hCdef
  have hCb : 0 ≤ Cb := (bigLambdaSensitivityConst_pos hd).le
  set w : ℝ := (incrementUnitCube₂ Q Q.scale L omega).w1Infinity with hwdef
  set Tm : ℝ := 4 * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
    (3 : ℝ) ^ (-(2 * M.gamma * (Q.scale : ℝ))) with hTdef
  have hnp : (0 : ℝ) ≤ vecNormSq p := vecNormSq_nonneg p
  have hcrude := responseJ_simplexDomain_zero_flux_le_LambdaSq hT
    (coefficientCutoffTriadicCoeffFamily M L omega) (s := 1 / 4) (qe := .finite 2)
    (by norm_num) (by norm_num) (by norm_num) ((Real.sqrt si)⁻¹ • p)
  have hscal : vecNormSq ((Real.sqrt si)⁻¹ • p) = si⁻¹ * vecNormSq p := by
    rw [vecNormSq_smul, inv_pow, Real.sq_sqrt hsi.le]
  rw [hscal] at hcrude
  have hmul : Ch02.LambdaSq Q (1 / 4) (.finite 2)
      (coefficientCutoffTriadicCoeffFamily M L omega) ≤
      4 * A + Cb * 8 * w ^ 2 * B := hLamL hosc hloc L hL
  have hbase : Ch02.responseJ (simplexDomain T)
      (simplexCoeffOn (coefficientCutoffTriadicCoeffFamily M L omega) T)
      ((Real.sqrt si)⁻¹ • p) 0 ≤
      S * (W * (4 * A + Cb * 8 * w ^ 2 * B)) * (si⁻¹ * vecNormSq p) := by
    refine hcrude.trans ?_
    have hSW : (0 : ℝ) ≤ S * W := mul_nonneg hSnn hW
    have hfac : (0 : ℝ) ≤ si⁻¹ * vecNormSq p :=
      mul_nonneg (inv_pos.2 hsi).le hnp
    have h1 : S * (W * Ch02.LambdaSq Q (1 / 4) (.finite 2)
        (coefficientCutoffTriadicCoeffFamily M L omega)) ≤
        S * (W * (4 * A + Cb * 8 * w ^ 2 * B)) := by
      rw [← mul_assoc, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left hmul hSW
    exact mul_le_mul_of_nonneg_right h1 hfac
  have hcore := normalized_flux_core (J := Ch02.responseJ (simplexDomain T)
      (simplexCoeffOn (coefficientCutoffTriadicCoeffFamily M L omega) T)
      ((Real.sqrt si)⁻¹ • p) 0) (T := Tm)
    hSnn hW hsj hsi hCb hnp (hLam hloc) (hlam hloc)
    (sigmaBar_le_four_mul_sigmaBar M hS hji hi) hinvSq hbase
  refine hcore.trans (le_of_eq ?_)
  rw [hTdef]
  ring

/-- Almost surely, on `not B_osc` and `not B_loc` and under the induction state,

```
J(spx, 0, sigmabar_i^{1/2} q̂; a_L)
  <=  80 C(d,1/4) . 3^{(j-k)/2} . 3^{gamma (i - j)} |q̂|^2 .
```

`Step1Assembly.responseJ_normalized_slope_le_of_notMem_bad_ae` with `40`
replaced by `80 C(d,1/4)`. -/
theorem responseJ_simplexDomain_normalized_slope_le_of_notMem_bad_ae (hd : 2 ≤ d)
    (M : ABKModel d) {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) (Q : TriadicCube d)
    (hm : Q.scale ≤ m0) (k : ℤ) {i : ℤ} (hji : Q.scale ≤ i) (hi : i ≤ m0) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∉ badOsc M Q → omega ∉ badLoc M Q → ∀ L : ℤ, Q.scale ≤ L →
        ∀ T : KuhnCell d, T.supportCube ∈ descendantsAtScale Q k → ∀ q : Vec d,
          Ch02.responseJ (simplexDomain T)
              (simplexCoeffOn (coefficientCutoffTriadicCoeffFamily M L omega) T) 0
              (Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • q) ≤
            80 * simplexCrudeConst d (1 / 4) *
                Ch02.multiscaleDescendantWeight Q k (1 / 4) *
                (3 : ℝ) ^ (M.gamma * ((i : ℝ) - (Q.scale : ℝ))) * vecNormSq q := by
  let : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) hd)⟩
  filter_upwards [lambdaSq_inv_le_of_notMem_bad_ae hd M hS Q hm (1 / 4) (.finite 2)
      (by norm_num) (by norm_num) (by norm_num),
    lambdaSq_quarter_inv_le_ten_mul_inv_sigmaBar_of_notMem_badLoc_ae M Q,
    lambdaGateFactor_le_one_of_notMem_bad_ae hd M hS Q hm]
    with omega hlamL hlam hgate hosc hloc L hL T hT q
  set sj : ℝ := ((Algsuperdiff.Section3.Annealed.sigmaBar M Q.scale : ℝ)) with hsjdef
  set si : ℝ := ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) with hsidef
  have hsj : 0 < sj := (Algsuperdiff.Section3.Annealed.sigmaBar M Q.scale).2
  have hsi : 0 < si := (Algsuperdiff.Section3.Annealed.sigmaBar M i).2
  set W : ℝ := Ch02.multiscaleDescendantWeight Q k (1 / 4) with hWdef
  have hW : 0 ≤ W := multiscaleDescendantWeight_nonneg Q k (1 / 4)
  set S : ℝ := simplexCrudeConst d (1 / 4) with hSdef
  have hSnn : 0 ≤ S := simplexCrudeConst_nonneg d (by norm_num)
  set B : ℝ := (Ch02.lambdaSq Q (1 / 4) (.finite 2)
    (coefficientCutoffTriadicCoeffFamily M Q.scale omega))⁻¹ with hBdef
  set G : ℝ := lambdaSensitivityConst d *
      (incrementUnitCube₂ Q Q.scale L omega).gradientW1Infinity *
      (Ch02.lambdaSq Q (3 / 8) (.finite 2)
        (coefficientCutoffTriadicCoeffFamily M Q.scale omega))⁻¹ with hGdef
  have hB0 : (0 : ℝ) ≤ B :=
    inv_nonneg.2 (Ch02.lambdaSq_nonneg Q _ (by norm_num) (by norm_num))
  have hnq : (0 : ℝ) ≤ vecNormSq q := vecNormSq_nonneg q
  have hcrude := responseJ_simplexDomain_zero_slope_le_lambdaSq_inv hT
    (coefficientCutoffTriadicCoeffFamily M L omega) (s := 1 / 4) (qe := .finite 2)
    (by norm_num) (by norm_num) (by norm_num) (Real.sqrt si • q)
  have hscal : vecNormSq (Real.sqrt si • q) = si * vecNormSq q := by
    rw [vecNormSq_smul, Real.sq_sqrt hsi.le]
  rw [hscal] at hcrude
  have hmul : (Ch02.lambdaSq Q (1 / 4) (.finite 2)
      (coefficientCutoffTriadicCoeffFamily M L omega))⁻¹ ≤ (1 + G) * B :=
    hlamL hosc hloc L hL
  have hbase : Ch02.responseJ (simplexDomain T)
      (simplexCoeffOn (coefficientCutoffTriadicCoeffFamily M L omega) T) 0
      (Real.sqrt si • q) ≤ S * (W * ((1 + G) * B)) * (si * vecNormSq q) := by
    refine hcrude.trans ?_
    have hSW : (0 : ℝ) ≤ S * W := mul_nonneg hSnn hW
    have hfac : (0 : ℝ) ≤ si * vecNormSq q := mul_nonneg hsi.le hnq
    have h1 : S * (W * (Ch02.lambdaSq Q (1 / 4) (.finite 2)
        (coefficientCutoffTriadicCoeffFamily M L omega))⁻¹) ≤
        S * (W * ((1 + G) * B)) := by
      rw [← mul_assoc, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left hmul hSW
    exact mul_le_mul_of_nonneg_right h1 hfac
  have hrat : si * sj⁻¹ ≤ 4 * (3 : ℝ) ^ (M.gamma * ((i : ℝ) - (Q.scale : ℝ))) := by
    have h := sigmaBar_le_four_mul_rpow_mul_sigmaBar M hS hji hi
    have h2 := mul_le_mul_of_nonneg_right h (inv_pos.2 hsj).le
    rwa [mul_assoc, mul_inv_cancel₀ (ne_of_gt hsj), mul_one] at h2
  exact normalized_slope_core hSnn hW hsi hnq hB0 (hgate hosc hloc L hL)
    (hlam hloc) hrat hbase

/-! ## `e.good.simplex.consequence` at the manuscript's own carrier -/

/-- Almost surely, on `not B_osc(z + square_j)` and `not B_loc(z + square_j)` and
under the induction state, for every `L >= j`, every scale `i` with `j <= i <=
m0`, every Kuhn cell `spx` whose support cube is a triadic descendant of `z +
square_j` at scale `k` and every `P̂ = (p̂, q̂)`,

```
| bfA_L^{1/2}(spx) bfAhom_i^{-1/2} P̂ |^2
  <=  640 C(d,1/4) . 3^{(j-k)/2}
        ( 1 + 8 C_{(e.big.Lambda.sensitivity)} cstar^{-1} gamma 3^{-2 gamma j}
              ||k_L - k_j||^2 ) |p̂|^2
      + 320 C(d,1/4) . 3^{(j-k)/2} . 3^{gamma (i - j)} |q̂|^2 .
```

This is the local response-leg shape estimate for the simplex carrier: the
manuscript's `spx` is a genuine Kuhn simplex of `SW(square_n)`, not a triadic
descendant cube, and the price of the carrier is exactly the explicit
dissection constant `simplexCrudeConst d (1/4)`.  At `i = n - 1` and `Q` a
layer-`k` Whitney cube the `q̂` exponent is the manuscript's `gamma (k + h_k)`
by `Step1Assembly.rpow_gamma_mul_sub_scale_le_of_mem_whitneyLayer`; that
instantiation is the consumer's. -/
theorem blockVecDot_coarseBlockMatrix_simplexDomain_normalized_le_of_notMem_bad_ae
    (hd : 2 ≤ d) (M : ABKModel d) {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) (Q : TriadicCube d)
    (hm : Q.scale ≤ m0) (k : ℤ) {i : ℤ} (hji : Q.scale ≤ i) (hi : i ≤ m0) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∉ badOsc M Q → omega ∉ badLoc M Q → ∀ L : ℤ, Q.scale ≤ L →
        ∀ T : KuhnCell d, T.supportCube ∈ descendantsAtScale Q k →
          ∀ p q : Vec d,
            blockVecDot
                ((Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • p,
                  Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • q)
                (blockMatVecMul
                  (Ch02.coarseBlockMatrix (simplexDomain T)
                    (simplexCoeffOn (coefficientCutoffTriadicCoeffFamily M L omega) T))
                  ((Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • p,
                    Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • q)) ≤
              640 * simplexCrudeConst d (1 / 4) *
                  Ch02.multiscaleDescendantWeight Q k (1 / 4) *
                  (1 + 8 * bigLambdaSensitivityConst d *
                      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
                      (3 : ℝ) ^ (-(2 * M.gamma * (Q.scale : ℝ))) *
                      (incrementUnitCube₂ Q Q.scale L omega).w1Infinity ^ 2) *
                  vecNormSq p +
                320 * simplexCrudeConst d (1 / 4) *
                  Ch02.multiscaleDescendantWeight Q k (1 / 4) *
                  (3 : ℝ) ^ (M.gamma * ((i : ℝ) - (Q.scale : ℝ))) * vecNormSq q := by
  filter_upwards
    [responseJ_simplexDomain_normalized_flux_le_of_notMem_bad_ae hd M hS Q hm k hji hi,
      responseJ_simplexDomain_normalized_slope_le_of_notMem_bad_ae hd M hS Q hm k hji hi]
    with omega hp hq hosc hloc L hL T hT p q
  have hsplit := blockVecDot_coarseBlockMatrix_le_four_responseJ_add
    (simplexDomain T)
    (simplexCoeffOn (coefficientCutoffTriadicCoeffFamily M L omega) T)
    ((Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • p)
    (Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) • q)
  have hpleg := hp hosc hloc L hL T hT p
  have hqleg := hq hosc hloc L hL T hT q
  refine hsplit.trans ?_
  linarith [hpleg, hqleg]

/-! ## The mass carried by the cells of one Whitney cube -/

theorem cellWeight_nonneg (m : ℤ) (T : KuhnCell d) : 0 ≤ cellWeight m T :=
  div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- `|R| / |square_m|` in volume form. -/
theorem cubeMassRatio_originCube_eq_div (m : ℤ) (Q : TriadicCube d) :
    cubeMassRatio (originCube d m) Q = cubeVolume Q / cubeVolume (originCube d m) := by
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  have hpow : ∀ z : ℤ, ((3 : ℝ) ^ z) ^ d = (3 : ℝ) ^ (z * (d : ℤ)) := fun z => by
    rw [← zpow_natCast ((3 : ℝ) ^ z) d, ← zpow_mul]
  have hL : cubeMassRatio (originCube d m) Q = (3 : ℝ) ^ ((d : ℤ) * (Q.scale - m)) := by
    rw [cubeMassRatio, ← zpow_natCast (3 : ℝ) d, ← zpow_mul]
    rfl
  have hR : cubeVolume Q / cubeVolume (originCube d m)
      = (3 : ℝ) ^ (Q.scale * (d : ℤ) - m * (d : ℤ)) := by
    rw [cubeVolume_eq_pow_scale, cubeVolume_eq_pow_scale, hpow, hpow, ← zpow_sub₀ h3]
    rfl
  rw [hL, hR]
  congr 1
  ring

/-- **The cells of a Whitney cube carry at most the cube's mass.**  The open
carriers of the cells of `S_{m-(n+1)-h_{n+1}}(square)` are pairwise disjoint
subsets of the cube, so their `e.sum-of-a-decomp` weights `|spx| / |square_m|`
sum to at most `|square| / |square_m|`.  (Equality holds --- the cells tile the
cube --- but only the upper bound is consumed.) -/
theorem sum_cellWeight_whitneySimplexCells_le (m : ℤ) (hn : ℕ → ℕ) (n : ℕ)
    (Q : TriadicCube d) :
    ∑ T ∈ whitneySimplexCells (d := d) m hn n Q, cellWeight m T
      ≤ cubeMassRatio (originCube d m) Q := by
  classical
  have hvol : ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
      (volume T.openCarrier).toReal ≤ cubeVolume Q := by
    by_cases hj : simplexScale m hn n ≤ Q.scale
    · have hsub : ∀ T ∈ whitneySimplexCells (d := d) m hn n Q,
          T.openCarrier ⊆ openCubeSet Q := by
        intro T hT
        have hTd : T.supportCube ∈
            descendantsAtDepth Q (Q.scale - simplexScale m hn n).toNat := by
          rw [← descendantsAtScale_eq_descendantsAtDepth Q hj]
          exact mem_whitneySimplexCells_iff.mp hT
        exact T.openCarrier_subset_openCubeSet.trans
          (openCubeSet_subset_of_mem_descendantsAtDepth hTd)
      have hdisj : (↑(whitneySimplexCells (d := d) m hn n Q) :
          Set (KuhnCell d)).PairwiseDisjoint KuhnCell.openCarrier :=
        triadicSimplexPartition_openCarrier_pairwiseDisjoint Q (simplexScale m hn n)
      have hmeas : ∀ T ∈ whitneySimplexCells (d := d) m hn n Q,
          MeasurableSet T.openCarrier := fun T _ => (isOpen_openCarrier T).measurableSet
      have hunion : ∑ T ∈ whitneySimplexCells (d := d) m hn n Q, volume T.openCarrier
          = volume (⋃ T ∈ whitneySimplexCells (d := d) m hn n Q, T.openCarrier) :=
        (measure_biUnion_finset hdisj hmeas).symm
      have hmono : volume (⋃ T ∈ whitneySimplexCells (d := d) m hn n Q, T.openCarrier)
          ≤ volume (openCubeSet Q) :=
        measure_mono (Set.iUnion₂_subset hsub)
      have hfin : ∀ T ∈ whitneySimplexCells (d := d) m hn n Q,
          volume T.openCarrier ≠ ⊤ := fun T _ =>
        (isBoundedDomain_openCarrier T).volume_lt_top.ne
      have hsum : (∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
          volume T.openCarrier).toReal
          = ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
            (volume T.openCarrier).toReal := ENNReal.toReal_sum hfin
      rw [← hsum, hunion]
      calc (volume (⋃ T ∈ whitneySimplexCells (d := d) m hn n Q, T.openCarrier)).toReal
          ≤ (volume (openCubeSet Q)).toReal :=
            ENNReal.toReal_mono (volume_openCubeSet_lt_top Q).ne hmono
        _ = cubeVolume Q := volume_openCubeSet_toReal Q
    · have hempty : whitneySimplexCells (d := d) m hn n Q = ∅ := by
        rw [whitneySimplexCells]
        exact triadicSimplexPartition_eq_empty (by omega)
      rw [hempty, Finset.sum_empty]
      exact (cubeVolume_nonneg Q)
  have hden : (0 : ℝ) < cubeVolume (originCube d m) := cubeVolume_pos _
  have hrw : ∑ T ∈ whitneySimplexCells (d := d) m hn n Q, cellWeight m T
      = (∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
          (volume T.openCarrier).toReal) / cubeVolume (originCube d m) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [cellWeight, volume_openCubeSet_toReal]
  rw [hrw, cubeMassRatio_originCube_eq_div]
  gcongr

/-! ## One Whitney layer of `e.sum-of-a-decomp`, in the `layerContrib` shape -/

/-- **The per-layer majorant, from a uniform per-cell bound.**  Let `g` be a
nonnegative cell functional which is bounded by `C` on the cells of the cubes of
a sub-family `S` of the layer, and vanishes on the cells of the layer's other
cubes.  Then the layer's `e.sum-of-a-decomp` total is majorized by
`C` times the mass of `S`:

```
∑_{□ ∈ 𝒲(□_m,n)} ∑_{𝔰 ∈ S(□)} ofReal(|𝔰|/|□_m| . g 𝔰)
  ≤ ofReal( C . ∑_{□ ∈ S} |□|/|□_m| ) .
```

This is exactly the shape of one leg of `ConclusionAssembly.layerContrib`: for
the good leg `S` is the layer minus its bad cubes, `g` the quadratic form times
`1_{¬𝓑}`, and `C = Ktot 3^{gamma(k+h_k)}` (the layer reading of
`e.good.simplex.consequence`); for the collar leg `S` is the collar part of
the layer, `g` the competitor's quadratic form times `1_{¬𝓑} 1_{𝒩(ℐ)}`, and `C
= Ccol 3^{2b(k+h_k)}` (`e.bounds.on.slopes.when.bad`).  The mass of `S` is
then weakened to the layer mass (good leg) or to the bad mass (collar leg) by
`Finset.sum_le_sum_of_subset_of_nonneg`, giving `hlayer` of
`LayerMass.toReal_tsum_simplexPartition_le_payload`. -/
theorem sum_sum_ofReal_cellWeight_le_ofReal_mul {m : ℤ} {hn : ℕ → ℕ} {n : ℕ}
    {g : KuhnCell d → ℝ} {C : ℝ} {S : Finset (TriadicCube d)}
    (hS : S ⊆ whitneyLayer (d := d) m hn n) (hC : 0 ≤ C)
    (hgS : ∀ Q ∈ S, ∀ T ∈ whitneySimplexCells (d := d) m hn n Q, g T ≤ C)
    (hgz : ∀ Q ∈ whitneyLayer (d := d) m hn n, Q ∉ S →
      ∀ T ∈ whitneySimplexCells (d := d) m hn n Q, g T = 0) :
    ∑ Q ∈ whitneyLayer (d := d) m hn n,
        ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
          ENNReal.ofReal (cellWeight m T * g T)
      ≤ ENNReal.ofReal (C * ∑ Q ∈ S, cubeMassRatio (originCube d m) Q) := by
  classical
  have hzero : ∀ Q ∈ whitneyLayer (d := d) m hn n, Q ∉ S →
      ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
        ENNReal.ofReal (cellWeight m T * g T) = 0 := by
    intro Q hQ hQS
    refine Finset.sum_eq_zero fun T hT => ?_
    rw [hgz Q hQ hQS T hT, mul_zero, ENNReal.ofReal_zero]
  have hrestrict : ∑ Q ∈ whitneyLayer (d := d) m hn n,
      ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
        ENNReal.ofReal (cellWeight m T * g T)
      = ∑ Q ∈ S, ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
        ENNReal.ofReal (cellWeight m T * g T) :=
    (Finset.sum_subset hS hzero).symm
  have hcube : ∀ Q ∈ S, ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
      ENNReal.ofReal (cellWeight m T * g T)
      ≤ ENNReal.ofReal (C * cubeMassRatio (originCube d m) Q) := by
    intro Q hQ
    have hterm : ∀ T ∈ whitneySimplexCells (d := d) m hn n Q,
        ENNReal.ofReal (cellWeight m T * g T)
        ≤ ENNReal.ofReal (C * cellWeight m T) := by
      intro T hT
      refine ENNReal.ofReal_le_ofReal ?_
      have h := hgS Q hQ T hT
      have hw := cellWeight_nonneg m T
      nlinarith [h, hw]
    calc ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
            ENNReal.ofReal (cellWeight m T * g T)
        ≤ ∑ T ∈ whitneySimplexCells (d := d) m hn n Q,
            ENNReal.ofReal (C * cellWeight m T) := Finset.sum_le_sum hterm
      _ = ENNReal.ofReal
            (C * ∑ T ∈ whitneySimplexCells (d := d) m hn n Q, cellWeight m T) := by
          rw [← ENNReal.ofReal_sum_of_nonneg
            (fun T _ => mul_nonneg hC (cellWeight_nonneg m T)), ← Finset.mul_sum]
      _ ≤ ENNReal.ofReal (C * cubeMassRatio (originCube d m) Q) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
            (sum_cellWeight_whitneySimplexCells_le m hn n Q) hC)
  rw [hrestrict]
  refine le_trans (Finset.sum_le_sum hcube) (le_of_eq ?_)
  rw [← ENNReal.ofReal_sum_of_nonneg
      (fun Q _ => mul_nonneg hC (cubeMassRatio_nonneg _ Q)), ← Finset.mul_sum]

end

end Algsuperdiff.Section3.Provider.Multiscale
