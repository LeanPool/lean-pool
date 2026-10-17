/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpGlobalFrame
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpSimplexMean

/-!
# SharpFramedSimplexMean

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The framed upper Step-1 simplex estimate

This file retains the factor `3^(-gamma * (i - j))` when the normalized
potential response is estimated at a fine cube of scale `j` and observation
scale `i`.  The factor comes from applying the growth branch of the induction
window at both running-diffusivity indices.

The results below are internal conditional proof obligations.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Whitney
open scoped ENNReal Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-- Arithmetic form of the normalized potential-response estimate when the
product of reciprocal running diffusivities retains its scale frame. -/
private theorem normalized_flux_framed_core
    {J c W A B si sj Cb w K np : ℝ}
    (hc : 0 ≤ c) (hW : 0 ≤ W) (hsj : 0 < sj) (hsi : 0 < si)
    (hCb : 0 ≤ Cb) (hK : 0 ≤ K) (hnp : 0 ≤ np)
    (hA : A ≤ 10 * sj) (hB : B ≤ 10 * sj⁻¹) (hratio : sj ≤ 4 * si)
    (hprod : si⁻¹ * sj⁻¹ ≤ 4 * K)
    (hbase : J ≤ c * (W * (4 * A + Cb * 8 * w ^ 2 * B)) * (si⁻¹ * np)) :
    J ≤ 160 * c * W * (1 + 8 * Cb * K * w ^ 2) * np := by
  have hsiinv : (0 : ℝ) < si⁻¹ := inv_pos.2 hsi
  have hsjinv : (0 : ℝ) < sj⁻¹ := inv_pos.2 hsj
  have hw2 : (0 : ℝ) ≤ w ^ 2 := sq_nonneg w
  have hstep1 : 2 * A * si⁻¹ ≤ 80 := by
    have h1 : A * si⁻¹ ≤ 10 * sj * si⁻¹ :=
      mul_le_mul_of_nonneg_right hA hsiinv.le
    have h2 : sj * si⁻¹ ≤ 4 := by
      have h := mul_le_mul_of_nonneg_right hratio hsiinv.le
      rwa [mul_assoc, mul_inv_cancel₀ (ne_of_gt hsi), mul_one] at h
    nlinarith [h1, h2]
  have hprod' : sj⁻¹ * si⁻¹ ≤ 4 * K := by
    simpa [mul_comm] using hprod
  have hBinv : B * si⁻¹ ≤ 40 * K := by
    calc
      B * si⁻¹ ≤ 10 * sj⁻¹ * si⁻¹ :=
        mul_le_mul_of_nonneg_right hB hsiinv.le
      _ = 10 * (sj⁻¹ * si⁻¹) := by ring
      _ ≤ 10 * (4 * K) := mul_le_mul_of_nonneg_left hprod' (by norm_num)
      _ = 40 * K := by ring
  have hcoeff : (0 : ℝ) ≤ 4 * Cb * w ^ 2 := by positivity
  have hstep2Exact :
      4 * Cb * w ^ 2 * B * si⁻¹ ≤ 160 * Cb * K * w ^ 2 := by
    calc
      4 * Cb * w ^ 2 * B * si⁻¹ = 4 * Cb * w ^ 2 * (B * si⁻¹) := by ring
      _ ≤ 4 * Cb * w ^ 2 * (40 * K) :=
        mul_le_mul_of_nonneg_left hBinv hcoeff
      _ = 160 * Cb * K * w ^ 2 := by ring
  have hstep2 :
      4 * Cb * w ^ 2 * B * si⁻¹ ≤ 640 * Cb * K * w ^ 2 := by
    refine hstep2Exact.trans ?_
    have hnonneg : 0 ≤ Cb * K * w ^ 2 := by positivity
    nlinarith
  have hinner :
      c * (4 * A + Cb * 8 * w ^ 2 * B) * si⁻¹ ≤
        160 * c * (1 + 8 * Cb * K * w ^ 2) := by
    have hsum :
        2 * A * si⁻¹ + 4 * Cb * w ^ 2 * B * si⁻¹ ≤
          80 + 640 * Cb * K * w ^ 2 := by
      linarith [hstep1, hstep2]
    calc
      c * (4 * A + Cb * 8 * w ^ 2 * B) * si⁻¹ =
          2 * c * (2 * A * si⁻¹ + 4 * Cb * w ^ 2 * B * si⁻¹) := by
        ring
      _ ≤ 2 * c * (80 + 640 * Cb * K * w ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 160 * c * (1 + 8 * Cb * K * w ^ 2) := by ring
  refine hbase.trans ?_
  calc
    c * (W * (4 * A + Cb * 8 * w ^ 2 * B)) * (si⁻¹ * np) =
        W * (c * (4 * A + Cb * 8 * w ^ 2 * B) * si⁻¹) * np := by
      ring
    _ ≤ W * (160 * c * (1 + 8 * Cb * K * w ^ 2)) * np :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hinner hW) hnp
    _ = 160 * c * W * (1 + 8 * Cb * K * w ^ 2) * np := by ring

/-- The normalized potential response with the global depth frame retained in
the increment term. -/
theorem probe_responseJ_simplexDomain_normalized_flux_le_framed_ae
    (hd : 2 ≤ d) (M : ABKModel d) {m₀ : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m₀ E)
    (Q : TriadicCube d) (hm : Q.scale ≤ m₀) (k : ℤ) {i : ℤ}
    (hji : Q.scale ≤ i) (hi : i ≤ m₀) :
    ∀ᵐ omega ∂(Algsuperdiff.Section3.Cutoff.cutoffSampleLaw M).toMeasure,
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
                    (3 : ℝ) ^
                      (-(M.gamma * ((i - Q.scale : ℤ) : ℝ))) *
                    (incrementUnitCube₂ Q Q.scale L omega).w1Infinity ^ 2) *
                vecNormSq p := by
  let : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) hd)⟩
  filter_upwards [LambdaSq_quarter_le_of_notMem_bad_ae hd M hS Q hm,
    LambdaSq_quarter_le_ten_mul_sigmaBar_of_notMem_badLoc_ae M Q,
    lambdaSq_quarter_inv_le_ten_mul_inv_sigmaBar_of_notMem_badLoc_ae M Q]
    with omega hLamL hLam hlam hosc hloc L hL T hT p
  set sj : ℝ := ((Algsuperdiff.Section3.Annealed.sigmaBar M Q.scale : ℝ))
  set si : ℝ := ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ))
  have hsj : 0 < sj := (Algsuperdiff.Section3.Annealed.sigmaBar M Q.scale).2
  have hsi : 0 < si := (Algsuperdiff.Section3.Annealed.sigmaBar M i).2
  set W : ℝ := Ch02.multiscaleDescendantWeight Q k (1 / 4)
  have hW : 0 ≤ W := multiscaleDescendantWeight_nonneg Q k (1 / 4)
  set S : ℝ := simplexCrudeConst d (1 / 4)
  have hSnn : 0 ≤ S := simplexCrudeConst_nonneg d (by norm_num)
  set A : ℝ := Ch02.LambdaSq Q (1 / 4) (.finite 2)
    (coefficientCutoffTriadicCoeffFamily M Q.scale omega)
  set B : ℝ := (Ch02.lambdaSq Q (1 / 4) (.finite 2)
    (coefficientCutoffTriadicCoeffFamily M Q.scale omega))⁻¹
  set Cb : ℝ := bigLambdaSensitivityConst d
  have hCb : 0 ≤ Cb := (bigLambdaSensitivityConst_pos hd).le
  set w : ℝ := (incrementUnitCube₂ Q Q.scale L omega).w1Infinity
  set K : ℝ := (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
    (3 : ℝ) ^ (-(2 * M.gamma * (Q.scale : ℝ))) *
    (3 : ℝ) ^ (-(M.gamma * ((i - Q.scale : ℤ) : ℝ)))
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (inv_nonneg.mpr
            (Algsuperdiff.Section3.Disorder.cstar_characterization M).1.le)
          M.shellPrefix.gamma_pos.le)
        (Real.rpow_nonneg (by norm_num) _))
      (Real.rpow_nonneg (by norm_num) _)
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
  have hprod₀ := sigmaBar_inv_mul_sigmaBar_inv_le_framed_wave_coefficient
    M hS hji hi
  have hprod : si⁻¹ * sj⁻¹ ≤ 4 * K := by
    dsimp only [si, sj, K]
    convert hprod₀ using 1
    all_goals ring
  have hcore := normalized_flux_framed_core
    (J := Ch02.responseJ (simplexDomain T)
      (simplexCoeffOn (coefficientCutoffTriadicCoeffFamily M L omega) T)
      ((Real.sqrt si)⁻¹ • p) 0)
    hSnn hW hsj hsi hCb hK hnp (hLam hloc) (hlam hloc)
    (sigmaBar_le_four_mul_sigmaBar M hS hji hi) hprod hbase
  dsimp only [S, W, Cb, K, w] at hcore
  convert hcore using 1
  all_goals ring

/-- The preceding framed response estimate after replacing the increment
supremum by its simplex mean and oscillation threshold.  Only the random
simplex-mean term retains the frame; the deterministic threshold term uses
that the frame is at most one. -/
theorem probe_responseJ_simplexDomain_normalized_flux_le_framed_simplexMean_ae
    (hd : 2 ≤ d) (M : ABKModel d) {m₀ : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m₀ E)
    (Q : TriadicCube d) (hm : Q.scale ≤ m₀) (k : ℤ) {i : ℤ}
    (hji : Q.scale ≤ i) (hi : i ≤ m₀) :
    ∀ᵐ omega ∂(Algsuperdiff.Section3.Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∉ badOsc M Q → omega ∉ badLoc M Q → ∀ L : ℤ, Q.scale ≤ L →
        ∀ T : KuhnCell d, T.supportCube ∈ descendantsAtScale Q k → ∀ p : Vec d,
          Ch02.responseJ (simplexDomain T)
              (simplexCoeffOn (coefficientCutoffTriadicCoeffFamily M L omega) T)
              ((Real.sqrt ((Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)))⁻¹ • p)
              0 ≤
            160 * simplexCrudeConst d (1 / 4) *
                Ch02.multiscaleDescendantWeight Q k (1 / 4) *
                (1 + probeSimplexMeanSensitivityConst d * deltaOsc d ^ 2 +
                  probeSimplexMeanSensitivityConst d *
                    (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
                    (3 : ℝ) ^ (-(2 * M.gamma * (Q.scale : ℝ))) *
                    (3 : ℝ) ^
                      (-(M.gamma * ((i - Q.scale : ℤ) : ℝ))) *
                    matrixOperatorNorm
                      (simplexIncrementValue Q.scale L omega.1 T) ^ 2) *
                vecNormSq p := by
  filter_upwards
    [probe_responseJ_simplexDomain_normalized_flux_le_framed_ae
      hd M hS Q hm k hji hi]
    with omega hbase hosc hloc L hL T hT p
  have hk : k ≤ Q.scale := scale_le_of_mem_descendantsAtScale hT
  have hTQ : T.openCarrier ⊆ openCubeSet Q :=
    T.openCarrier_subset_openCubeSet.trans
      (openCubeSet_subset_of_mem_descendantsAtScale hk hT)
  have hw :=
    probe_w1Infinity_incrementUnitCube₂_sq_le_simplexMean_sq_add_oscThreshold_sq
      M Q hL hosc T hTQ
  have hraw := hbase hosc hloc L hL T hT p
  let Cb : ℝ := bigLambdaSensitivityConst d
  let Cw : ℝ := probeSimplexW1Const d
  let K₀ : ℝ := (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
    (3 : ℝ) ^ (-(2 * M.gamma * (Q.scale : ℝ)))
  let F : ℝ :=
    (3 : ℝ) ^ (-(M.gamma * ((i - Q.scale : ℤ) : ℝ)))
  let K : ℝ := K₀ * F
  let H : ℝ := matrixOperatorNorm (simplexIncrementValue Q.scale L omega.1 T)
  let O : ℝ := oscThreshold M Q.scale
  let A : ℝ := probeSimplexMeanSensitivityConst d
  have hCb : 0 ≤ Cb := (bigLambdaSensitivityConst_pos hd).le
  have hK₀ : 0 ≤ K₀ := by
    dsimp only [K₀]
    exact mul_nonneg
      (mul_nonneg
        (inv_nonneg.mpr
          (Algsuperdiff.Section3.Disorder.cstar_characterization M).1.le)
        M.shellPrefix.gamma_pos.le)
      (Real.rpow_nonneg (by norm_num) _)
  have hF₀ : 0 ≤ F := by
    dsimp only [F]
    positivity
  have hF₁ : F ≤ 1 := by
    dsimp only [F]
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    have hgap : (0 : ℤ) ≤ i - Q.scale := sub_nonneg.mpr hji
    have hgapReal : (0 : ℝ) ≤ ((i - Q.scale : ℤ) : ℝ) := by exact_mod_cast hgap
    exact neg_nonpos.mpr (mul_nonneg M.shellPrefix.gamma_pos.le hgapReal)
  have hK : 0 ≤ K := mul_nonneg hK₀ hF₀
  have hcoef : 0 ≤ 8 * Cb * K := by positivity
  have hscaled₀ : K₀ * O ^ 2 = deltaOsc d ^ 2 := by
    simpa only [K₀, O] using
      probe_inv_cstar_mul_gamma_mul_rpow_mul_oscThreshold_sq M Q.scale
  have hKO : K * O ^ 2 ≤ deltaOsc d ^ 2 := by
    calc
      K * O ^ 2 = F * (K₀ * O ^ 2) := by
        dsimp only [K]
        ring
      _ = F * deltaOsc d ^ 2 := by rw [hscaled₀]
      _ ≤ 1 * deltaOsc d ^ 2 :=
        mul_le_mul_of_nonneg_right hF₁ (sq_nonneg _)
      _ = deltaOsc d ^ 2 := one_mul _
  have hA : A = 16 * Cb * Cw ^ 2 := rfl
  have hAnn : 0 ≤ A := probeSimplexMeanSensitivityConst_nonneg hd
  have hscaledKO : A * (K * O ^ 2) ≤ A * deltaOsc d ^ 2 :=
    mul_le_mul_of_nonneg_left hKO hAnn
  have hmul := mul_le_mul_of_nonneg_left hw hcoef
  have hmul' :
      8 * Cb * K * (incrementUnitCube₂ Q Q.scale L omega).w1Infinity ^ 2 ≤
        8 * Cb * K * (2 * Cw ^ 2 * (H ^ 2 + O ^ 2)) := by
    simpa only [Cw, H, O] using hmul
  have hinner :
      1 + 8 * Cb * K * (incrementUnitCube₂ Q Q.scale L omega).w1Infinity ^ 2 ≤
        1 + A * deltaOsc d ^ 2 + A * K * H ^ 2 := by
    calc
      1 + 8 * Cb * K * (incrementUnitCube₂ Q Q.scale L omega).w1Infinity ^ 2
          ≤ 1 + 8 * Cb * K * (2 * Cw ^ 2 * (H ^ 2 + O ^ 2)) :=
        add_le_add le_rfl hmul'
      _ = 1 + A * (K * O ^ 2) + A * K * H ^ 2 := by
        rw [hA]
        ring
      _ ≤ 1 + A * deltaOsc d ^ 2 + A * K * H ^ 2 := by
        linarith
  have houter : 0 ≤ 160 * simplexCrudeConst d (1 / 4) *
      Ch02.multiscaleDescendantWeight Q k (1 / 4) := by
    have hSimp : 0 ≤ simplexCrudeConst d (1 / 4) :=
      simplexCrudeConst_nonneg d (by norm_num)
    have hW : 0 ≤ Ch02.multiscaleDescendantWeight Q k (1 / 4) :=
      multiscaleDescendantWeight_nonneg Q k (1 / 4)
    positivity
  have hp : 0 ≤ vecNormSq p := vecNormSq_nonneg p
  refine hraw.trans ?_
  have hstep := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hinner houter) hp
  dsimp only [Cb, K, K₀, F, H, A] at hstep
  convert hstep using 1 <;> ring

/-- The full simplex quadratic form obtained by combining the framed
potential leg with the unchanged normalized slope leg. -/
theorem probe_blockVecDot_coarseBlockMatrix_simplexDomain_le_framedMean_ae
    (hd : 2 ≤ d) (M : ABKModel d) {m₀ : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m₀ E)
    (Q : TriadicCube d) (hm : Q.scale ≤ m₀) (k : ℤ) {i : ℤ}
    (hji : Q.scale ≤ i) (hi : i ≤ m₀) :
    ∀ᵐ omega ∂(Algsuperdiff.Section3.Cutoff.cutoffSampleLaw M).toMeasure,
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
                  (1 + probeSimplexMeanSensitivityConst d * deltaOsc d ^ 2 +
                    probeSimplexMeanSensitivityConst d *
                      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
                      (3 : ℝ) ^ (-(2 * M.gamma * (Q.scale : ℝ))) *
                      (3 : ℝ) ^
                        (-(M.gamma * ((i - Q.scale : ℤ) : ℝ))) *
                      matrixOperatorNorm
                        (simplexIncrementValue Q.scale L omega.1 T) ^ 2) *
                  vecNormSq p +
                320 * simplexCrudeConst d (1 / 4) *
                  Ch02.multiscaleDescendantWeight Q k (1 / 4) *
                  (3 : ℝ) ^ (M.gamma * ((i : ℝ) - (Q.scale : ℝ))) *
                  vecNormSq q := by
  filter_upwards
    [probe_responseJ_simplexDomain_normalized_flux_le_framed_simplexMean_ae
      hd M hS Q hm k hji hi,
     responseJ_simplexDomain_normalized_slope_le_of_notMem_bad_ae
      hd M hS Q hm k hji hi]
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

/-- Cellwise majorant whose random potential term retains the observation-to-
cube scale frame. -/
def probeFramedMeanCellMajorant (M : ABKModel d) (Q : TriadicCube d)
    (k i L : ℤ) (omega : CutoffSample d) (T : KuhnCell d)
    (p q : Vec d) : ℝ :=
  640 * simplexCrudeConst d (1 / 4) *
      Ch02.multiscaleDescendantWeight Q k (1 / 4) *
      (1 + probeSimplexMeanSensitivityConst d * deltaOsc d ^ 2 +
        probeSimplexMeanSensitivityConst d *
          (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
          (3 : ℝ) ^ (-(2 * M.gamma * (Q.scale : ℝ))) *
          (3 : ℝ) ^ (-(M.gamma * ((i - Q.scale : ℤ) : ℝ))) *
          matrixOperatorNorm (simplexIncrementValue Q.scale L omega.1 T) ^ 2) *
      vecNormSq p +
    320 * simplexCrudeConst d (1 / 4) *
      Ch02.multiscaleDescendantWeight Q k (1 / 4) *
      (3 : ℝ) ^ (M.gamma * ((i : ℝ) - (Q.scale : ℝ))) * vecNormSq q

theorem probeFramedMeanCellMajorant_nonneg
    (hd : 2 ≤ d) (M : ABKModel d) (Q : TriadicCube d)
    (k i L : ℤ) (omega : CutoffSample d) (T : KuhnCell d)
    (p q : Vec d) :
    0 ≤ probeFramedMeanCellMajorant M Q k i L omega T p q := by
  have hSimp : 0 ≤ simplexCrudeConst d (1 / 4) :=
    simplexCrudeConst_nonneg d (by norm_num)
  have hW : 0 ≤ Ch02.multiscaleDescendantWeight Q k (1 / 4) :=
    multiscaleDescendantWeight_nonneg Q k (1 / 4)
  have hA : 0 ≤ probeSimplexMeanSensitivityConst d :=
    probeSimplexMeanSensitivityConst_nonneg hd
  have hc : 0 ≤ (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ :=
    inv_nonneg.mpr
      (Algsuperdiff.Section3.Disorder.cstar_characterization M).1.le
  have hg : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hframe : 0 ≤
      (3 : ℝ) ^ (-(M.gamma * ((i - Q.scale : ℤ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hp : 0 ≤ vecNormSq p := vecNormSq_nonneg p
  have hq : 0 ≤ vecNormSq q := vecNormSq_nonneg q
  rw [probeFramedMeanCellMajorant]
  positivity

theorem probe_blockVecDot_coarseBlockMatrix_simplexDomain_le_framedMeanMajorant_ae
    (hd : 2 ≤ d) (M : ABKModel d) {m₀ : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m₀ E)
    (Q : TriadicCube d) (hm : Q.scale ≤ m₀) (k : ℤ) {i : ℤ}
    (hji : Q.scale ≤ i) (hi : i ≤ m₀) :
    ∀ᵐ omega ∂(Algsuperdiff.Section3.Cutoff.cutoffSampleLaw M).toMeasure,
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
              probeFramedMeanCellMajorant M Q k i L omega T p q := by
  simpa only [probeFramedMeanCellMajorant] using
    probe_blockVecDot_coarseBlockMatrix_simplexDomain_le_framedMean_ae
      hd M hS Q hm k hji hi

end

end Algsuperdiff.Section3.Provider.Multiscale
