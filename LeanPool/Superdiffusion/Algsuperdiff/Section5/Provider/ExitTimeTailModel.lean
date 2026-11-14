/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.ExitTimeTailStream
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.PercolationScaleV2
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SmallGammaRpow

/-!
# ExitTimeTailModel

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The early-exit tail of the stream process from the model alone

The early-exit estimate of the chained layer carries the crossing count of the percolation
estimate, and asks each cell of the chain for the analytic data of its exit-time problem.
Both premises are discharged here, in the two steps the displacement form uses.

The first step supplies the crossing count.  A single measurable scale `Y` serves almost
every sample and every smaller cube scale; transporting the successor percolation estimate
to the injection constant of the exit-time joint rescales the accuracy parameter by
`K = max 1 C_ev`, which multiplies the lower endpoint of the accuracy window by `K` and
divides the tail rate of the crossing scale by `K²`.

The second step supplies the analytic data of the cells, which exist for every model, every
sample, every centre and every cube scale; shrinks the disorder threshold until the accuracy
window

```text
  C_floor γ^{1/2} |log γ|^{7/2} ≤ ep ≤ 1/4 ,     ep ≤ c_small
```

contains a point, that comparison being carried in the conclusion; and transports the almost
sure statement from the coefficient cutoff sample to the full sample, which is the form the
quenched moment estimates consume.

## Main results

* `measure_exitTime_le_exp_neg_displacementMinScale_streamProcess_v2` — the early-exit tail
  of the stream process with the crossing premise supplied.
* `measure_exitTime_le_exp_neg_displacementMinScale_streamProcess_v2_of_model` — the same,
  almost surely for the full-sample law, with a nonempty accuracy window and no premise on
  the cells.

## References

* ABK26, the localized exit-time problem of Section 5.2, and the early-exit estimate of
  Section 5.3.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Field
open Algsuperdiff.Section5.Support
open Algsuperdiff.Section5.Trace
open DivergenceFormProcess.Form
open HCPolySupport MeasureTheory
open MarkovProcess
open scoped ENNReal NNReal

noncomputable section

/-! ## 1. The crossing count supplied -/

/-- **The early-exit tail of the stream process with the crossing premise supplied.**  A
single measurable scale serves almost every sample and every smaller cube scale.  The
rescaling by `K = max 1 C_ev` weakens the anchor's accuracy floor by the factor `K` and its
exponential rate by the factor `K²`. -/
theorem measure_exitTime_le_exp_neg_displacementMinScale_streamProcess_v2
    (d : ℕ) [NeZero d] (hdim : 2 ≤ d) (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ gamma0 Cev Cfloor Cchain ctail csmall Creg : ℝ,
      0 < gamma0 ∧ 0 < Cev ∧ 0 < Cfloor ∧ 0 < Cchain ∧ 0 < ctail ∧
      0 < csmall ∧ 0 < Creg ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ ep : ℝ, ep ∈ Set.Icc (Cfloor * Real.sqrt M.gamma *
          Real.rpow |Real.log M.gamma| (7 / 2)) (1 / 4) → ep ≤ csmall →
      ∀ m : ℤ, ∃ Y : Cutoff.CutoffSample d → ℕ,
        Measurable Y ∧
        (∀ N : ℕ, 1 ≤ N →
          (Cutoff.cutoffSampleLaw M).toMeasure {omega | N ≤ Y omega} ≤
            ENNReal.ofReal (Real.exp (-(ctail * ep ^ (2 : ℕ) * M.gamma⁻¹ *
              |Real.log M.gamma| ^ (-6 : ℤ) * (3 : ℝ) ^ N)))) ∧
        ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ n : ℤ,
          n ≤ m - (Y omega : ℤ) →
          ∀ omegaFull : Field.FullSample d M.gamma, omegaFull.1 = omega →
          ∀ i : Fin d,
          ∀ (Good : Section5.Percolation.Site d → Prop) [DecidablePred Good],
            (∀ z, Good z ↔ omega ∈ qEvent M Creg Cev n
              (rescaledLatticePoint n z) ep) →
            (∀ j : Fin (goodSites ((m - n).toNat + 1) Good).card,
              HasCubeStreamExitTimeData M n omegaFull i
                (rescaledLatticePoint n (goodSiteEnum ((m - n).toNat + 1) Good j))) →
          ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
          ∀ t : NNReal, 0 < (t : ℝ) →
            (3 : ℝ) ^ n ≤
              auxiliaryScaleBound M.nu (Disorder.cstar M) M.gamma delta (t : ℝ) m →
            auxiliaryScaleBound M.nu (Disorder.cstar M) M.gamma delta (t : ℝ) m <
              (3 : ℝ) ^ (n + 1) →
            lengthTimeScale M.nu (Disorder.cstar M) M.gamma ((3 : ℝ) ^ n) ≤
              2 * exitTimeScale M n →
            128 * (3 : ℝ) ^ d * delta *
                earlyExitProfileCost (Disorder.cstar M) M.gamma ≤
              Cchain * earlyExitKappa (Real.toNNReal Cchain) (Real.toNNReal Cchain⁻¹) →
            earlyExitBaseScale d ≤ 3 ^ (m - n).toNat →
          ∀ x ∈ Metric.closedBall (0 : Vec d) ((1 / 2 : ℝ) * (3 : ℝ) ^ (m - 1)),
            letI := (streamExhaustionTailInput M omegaFull).toOnePointRegular.metricSpace
            letI :=
              (streamExhaustionTailInput M omegaFull).toOnePointRegular.completeSpace
            streamProcess M omegaFull (x : OnePoint (Vec d))
                {eta | ContinuousPath.exitTime
                  (((↑) : Vec d → OnePoint (Vec d)) '' openCubeSet (originCube d m)) eta ≤
                    (t : ℝ≥0∞)} ≤
              ENNReal.ofReal (Real.exp
                (-earlyExitDecayConstant d M.gamma delta
                    (earlyExitKappa (Real.toNNReal Cchain) (Real.toNNReal Cchain⁻¹)) *
                  displacementMinScale M.nu (Disorder.cstar M) M.gamma (t : ℝ) m)) := by
  obtain ⟨gammaP, cp, Cp, Creg, hgammaP, hcp, hCp, hCreg, hcross⟩ :=
    exists_measurable_scale_ae_crossing_v2 d cstar hcstar
  obtain ⟨gammaE, Cev, Cchain, csmall, hgammaE, hCev, hCchain, hcsmall, htail⟩ :=
    measure_exitTime_le_exp_neg_displacementMinScale_streamProcess
      d hdim cstar hcstar Creg hCreg
  let K : ℝ := max 1 Cev
  let gamma0 : ℝ := min gammaP gammaE
  let Cfloor : ℝ := Cp * K
  let ctail : ℝ := cp / K ^ (2 : ℕ)
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left 1 Cev)
  have hgamma0 : 0 < gamma0 := lt_min hgammaP hgammaE
  have hCfloor : 0 < Cfloor := mul_pos hCp hK
  have hctail : 0 < ctail := div_pos hcp (pow_pos hK _)
  refine ⟨gamma0, Cev, Cfloor, Cchain, ctail, csmall, Creg, hgamma0, hCev,
    hCfloor, hCchain, hctail, hcsmall, hCreg, ?_⟩
  intro M hcstarM hgamma ep hep hepsmall m
  have hgammaP' : M.gamma ≤ gammaP := hgamma.trans (min_le_left _ _)
  have hgammaE' : M.gamma ≤ gammaE := hgamma.trans (min_le_right _ _)
  have hepP : ep ∈ Set.Icc ((Cp * max 1 Cev) * Real.sqrt M.gamma *
      Real.rpow |Real.log M.gamma| (7 / 2)) (1 / 4) := by
    simpa only [Cfloor, K] using hep
  obtain ⟨Y, hYmeas, hYtail, hYcross⟩ :=
    hcross Cev hCev M hcstarM hgammaP' ep hepP m
  refine ⟨Y, hYmeas, ?_, ?_⟩
  · intro N hN
    simpa only [ctail, K] using hYtail N hN
  · filter_upwards [hYcross] with omega homega
    intro n hn omegaFull hfull i Good instGood hGood hdata delta hdelta hdelta1 t ht hnLower
      hnUpper hscale hdeltaSmall hlarge x hx
    have hnm : n ≤ m := by omega
    have hepPos : 0 < ep := by
      have hlower : 0 < Cfloor * Real.sqrt M.gamma *
          Real.rpow |Real.log M.gamma| (7 / 2) :=
        mul_pos (mul_pos hCfloor (Real.sqrt_pos.2 M.shellPrefix.gamma_pos))
          (Real.rpow_pos_of_pos (abs_log_gamma_pos M) _)
      exact hlower.trans_le hep.1
    have hGoodFull : ∀ z, Good z ↔ omegaFull.1 ∈ qEvent M Creg Cev n
        (rescaledLatticePoint n z) ep := by
      simpa only [hfull] using hGood
    have hcrossing := homega n hn
    have hcrossingFull : ∀ (N : ℕ) (y : ℕ → Fin d → ℤ),
        Provider.Percolation.IsLatticePath y N →
        y 0 ∈ Provider.Percolation.cubeAt (m - n).toNat 0 →
        y N ∉ Provider.Percolation.cubeAt ((m - n).toNat + 1) 0 →
        (3 / 4 : ℝ) * (3 : ℝ) ^ (m - n).toNat ≤
          ((qSiteCount M Creg Cev n ep
            (Section5.Percolation.pathSites N y) omegaFull.1 : ℕ) : ℝ) := by
      simpa only [hfull] using hcrossing
    have hprovider0 := htail M hcstarM hgammaE'
    have hprovider1 := hprovider0 ep ⟨hepPos, hep.2⟩ hepsmall
    have hprovider2 := hprovider1 n m hnm
    have hprovider3 := hprovider2 omegaFull i
    have hprovider4 := hprovider3 Good
    have hprovider5 := hprovider4 hGoodFull
    have hprovider6 := hprovider5 hcrossingFull
    have hprovider7 := hprovider6 hdata
    have hprovider8 := hprovider7 delta hdelta hdelta1
    have hprovider9 := hprovider8 t ht hnLower hnUpper hscale hdeltaSmall hlarge
    let streamMetricSpace :=
      (streamExhaustionTailInput M omegaFull).toOnePointRegular.metricSpace
    let streamCompleteSpace :=
      (streamExhaustionTailInput M omegaFull).toOnePointRegular.completeSpace
    change streamProcess M omegaFull (x : OnePoint (Vec d))
        {eta | ContinuousPath.exitTime
          (((↑) : Vec d → OnePoint (Vec d)) '' openCubeSet (originCube d m)) eta ≤
            (t : ℝ≥0∞)} ≤
      ENNReal.ofReal (Real.exp
        (-earlyExitDecayConstant d M.gamma delta
            (earlyExitKappa (Real.toNNReal Cchain) (Real.toNNReal Cchain⁻¹)) *
          displacementMinScale M.nu (Disorder.cstar M) M.gamma (t : ℝ) m))
    exact hprovider9 x hx

/-! ## 2. The cells and the accuracy window supplied -/

/-- **The early-exit tail of the stream process, with no premise beyond the model.**  The
crossing count of the percolation estimate and the analytic data of the cells are both
supplied, and the disorder threshold is small enough that the accuracy window

```text
  C_floor γ^{1/2}|log γ|^{7/2} ≤ ep ≤ 1/4 ,     ep ≤ c_small
```

is nonempty; that comparison is the first conjunct of the conclusion.  The estimate itself
holds almost surely for the full-sample law.

The accuracy rescaling that produced the successor form costs a factor: with
`K = max 1 C_ev`, the floor `C_floor` is the floor of the percolation estimate at injection
constant `1` multiplied by `K`, and the tail rate `c_tail` is that estimate's rate divided
by `K²`.

The index `i` no longer occurs in the conclusion, the premise that used it having been
discharged; the statement is the one the successor form has at every index. -/
theorem measure_exitTime_le_exp_neg_displacementMinScale_streamProcess_v2_of_model
    (d : ℕ) [NeZero d] (hdim : 2 ≤ d) (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ gamma0 Cev Cfloor Cchain ctail csmall Creg : ℝ,
      0 < gamma0 ∧ 0 < Cev ∧ 0 < Cfloor ∧ 0 < Cchain ∧ 0 < ctail ∧
      0 < csmall ∧ 0 < Creg ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      Cfloor * Real.sqrt M.gamma * Real.rpow |Real.log M.gamma| (7 / 2) ≤
          min (1 / 4) csmall ∧
      ∀ ep : ℝ, ep ∈ Set.Icc (Cfloor * Real.sqrt M.gamma *
          Real.rpow |Real.log M.gamma| (7 / 2)) (1 / 4) → ep ≤ csmall →
      ∀ m : ℤ, ∃ Y : Cutoff.CutoffSample d → ℕ,
        Measurable Y ∧
        (∀ N : ℕ, 1 ≤ N →
          (fullSampleLaw M).toMeasure {omegaFull | N ≤ Y omegaFull.1} ≤
            ENNReal.ofReal (Real.exp (-(ctail * ep ^ (2 : ℕ) * M.gamma⁻¹ *
              |Real.log M.gamma| ^ (-6 : ℤ) * (3 : ℝ) ^ N)))) ∧
        ∀ᵐ omegaFull ∂(fullSampleLaw M).toMeasure, ∀ n : ℤ,
          n ≤ m - (Y omegaFull.1 : ℤ) →
          ∀ _i : Fin d,
          ∀ (Good : Section5.Percolation.Site d → Prop) [DecidablePred Good],
            (∀ z, Good z ↔ omegaFull.1 ∈ qEvent M Creg Cev n
              (rescaledLatticePoint n z) ep) →
          ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
          ∀ t : NNReal, 0 < (t : ℝ) →
            (3 : ℝ) ^ n ≤
              auxiliaryScaleBound M.nu (Disorder.cstar M) M.gamma delta (t : ℝ) m →
            auxiliaryScaleBound M.nu (Disorder.cstar M) M.gamma delta (t : ℝ) m <
              (3 : ℝ) ^ (n + 1) →
            lengthTimeScale M.nu (Disorder.cstar M) M.gamma ((3 : ℝ) ^ n) ≤
              2 * exitTimeScale M n →
            128 * (3 : ℝ) ^ d * delta *
                earlyExitProfileCost (Disorder.cstar M) M.gamma ≤
              Cchain * earlyExitKappa (Real.toNNReal Cchain) (Real.toNNReal Cchain⁻¹) →
            earlyExitBaseScale d ≤ 3 ^ (m - n).toNat →
          ∀ x ∈ Metric.closedBall (0 : Vec d) ((1 / 2 : ℝ) * (3 : ℝ) ^ (m - 1)),
            letI := (streamExhaustionTailInput M omegaFull).toOnePointRegular.metricSpace
            letI :=
              (streamExhaustionTailInput M omegaFull).toOnePointRegular.completeSpace
            streamProcess M omegaFull (x : OnePoint (Vec d))
                {eta | ContinuousPath.exitTime
                  (((↑) : Vec d → OnePoint (Vec d)) '' openCubeSet (originCube d m)) eta ≤
                    (t : ℝ≥0∞)} ≤
              ENNReal.ofReal (Real.exp
                (-earlyExitDecayConstant d M.gamma delta
                    (earlyExitKappa (Real.toNNReal Cchain) (Real.toNNReal Cchain⁻¹)) *
                  displacementMinScale M.nu (Disorder.cstar M) M.gamma (t : ℝ) m)) := by
  obtain ⟨gammaV, Cev, Cfloor, Cchain, ctail, csmall, Creg,
    hgammaV, hCev, hCfloor, hCchain, hctail, hcsmall, hCreg, hmain⟩ :=
    measure_exitTime_le_exp_neg_displacementMinScale_streamProcess_v2 d hdim cstar hcstar
  obtain ⟨gammaS, hgammaS, hsmall⟩ :=
    exists_sqrt_mul_abs_log_rpow_le (K := Cfloor) (q := 7 / 2)
      (eps := min (1 / 4) csmall) hCfloor.le (by norm_num)
      (lt_min (by norm_num) hcsmall)
  refine ⟨min gammaV gammaS, Cev, Cfloor, Cchain, ctail, csmall, Creg,
    lt_min hgammaV hgammaS, hCev, hCfloor, hCchain, hctail, hcsmall, hCreg, ?_⟩
  intro M hcs hgam
  have hgamV : M.gamma ≤ gammaV := hgam.trans (min_le_left _ _)
  have hgamS : M.gamma ≤ gammaS := hgam.trans (min_le_right _ _)
  have hi : (0 : ℕ) < d := lt_of_lt_of_le (by norm_num) hdim
  refine ⟨?_, ?_⟩
  · have h := hsmall M.gamma M.shellPrefix.gamma_pos hgamS
    rw [← mul_assoc] at h
    exact h
  intro ep hep hepsmall m
  obtain ⟨Y, hYmeas, hYtail, hYcross⟩ := hmain M hcs hgamV ep hep hepsmall m
  refine ⟨Y, hYmeas, ?_, ?_⟩
  · intro N hN
    have hS : MeasurableSet {omega : Cutoff.CutoffSample d | N ≤ Y omega} :=
      measurableSet_le measurable_const hYmeas
    have hEq : (fullSampleLaw M).toMeasure {omegaFull | N ≤ Y omegaFull.1} =
        (Cutoff.cutoffSampleLaw M).toMeasure {omega | N ≤ Y omega} := by
      rw [← map_fullSampleLaw_val M, Measure.map_apply measurable_subtype_coe hS]
      rfl
    rw [hEq]
    exact hYtail N hN
  · have hcut := hYcross
    rw [← map_fullSampleLaw_val M] at hcut
    have htransport := ae_of_ae_map (μ := (fullSampleLaw M).toMeasure)
      measurable_subtype_coe.aemeasurable hcut
    filter_upwards [htransport] with omegaFull homega
    intro n hn _i Good instGood hGood delta hdelta hdelta1 t ht hnLower hnUpper hscale
      hdeltaSmall hlarge x hx
    exact homega n hn omegaFull rfl ⟨0, hi⟩ Good hGood
      (fun j => hasCubeStreamExitTimeData M n omegaFull ⟨0, hi⟩ _)
      delta hdelta hdelta1 t ht hnLower hnUpper hscale hdeltaSmall hlarge x hx

end

end Algsuperdiff.Section5.Provider
