/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.ExitTimeCutoffLimitTailData

/-!
# ExitTimeTailStream

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The early-exit tail of the stream process

The chaining layer produces two estimates at once.  The event it controls is the early exit
from the cube `□_m`, and the displacement of the path at the fixed time `t` is bounded by
it, because a path whose position has left the cube has left the cube.  The displacement
form is the one carried by the reading of the chain at the process of the stream field; the
early-exit form, which is the stronger of the two, is carried here.

Nothing beyond the chained estimate changes.  The Chernoff conversion and the deterministic
optimization of the exponent are stated for the early-exit event itself, so replacing the
final inclusion by the identity gives the early-exit tail with the same constants, the same
accuracy window and the same regime as the displacement tail.

## Main results

* `measure_exitTime_le_exp_neg_displacementMinScale_of_oneStepLaplace_on` — the printed
  early-exit tail on a carrier, with the contraction and the discount rate of the collected
  one-step Laplace estimate.
* `measure_exitTime_le_exp_neg_displacementMinScale_streamProcess` — the early-exit tail for
  the process of one sample of the stream field.

## References

* ABK26, the one-step Laplace estimate, the chaining and the early-exit estimate of
  Section 5.3.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open Algsuperdiff.Section5.Field Algsuperdiff.Section5.Support Algsuperdiff.Section5.Trace
open DivergenceFormProcess.Form
open DivergenceFormProcess.StoppedDirichlet
open HCPolySupport MarkovProcess MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

/-! ## 1. The printed early-exit tail on a carrier -/

section Carrier

variable {d : ℕ} {alpha : Type*} [PseudoMetricSpace alpha]

/-- **Composer-fit printed early-exit tail on a carrier.**  The chained estimate carries
exactly the contraction and the discount rate returned by the collected one-step Laplace
estimate, so no exponential-domination input remains for its caller. -/
theorem measure_exitTime_le_exp_neg_displacementMinScale_of_oneStepLaplace_on
    (M : ABKModel d) (Q : Measure (ContinuousPath alpha)) (U : Set alpha)
    {C delta : ℝ} {m n : ℤ} (t : NNReal)
    (hC : 0 < C) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (ht : 0 < (t : ℝ)) (hnm : n ≤ m)
    (hnLower : (3 : ℝ) ^ n ≤ auxiliaryScaleBound M.nu (Disorder.cstar M)
      M.gamma delta (t : ℝ) m)
    (hnUpper : auxiliaryScaleBound M.nu (Disorder.cstar M) M.gamma delta (t : ℝ) m <
      (3 : ℝ) ^ (n + 1))
    (hscale : lengthTimeScale M.nu (Disorder.cstar M) M.gamma ((3 : ℝ) ^ n) ≤
      2 * exitTimeScale M n)
    (hdeltaSmall : 128 * (3 : ℝ) ^ d * delta *
        earlyExitProfileCost (Disorder.cstar M) M.gamma ≤
      C * earlyExitKappa (Real.toNNReal C) (Real.toNNReal C⁻¹))
    (hlarge : earlyExitBaseScale d ≤ 3 ^ (m - n).toNat)
    (hchain : Q {eta | ContinuousPath.exitTime U eta ≤ (t : ℝ≥0∞)} ≤
      ENNReal.ofReal (Real.exp ((C * exitTimeScale M n)⁻¹ * (t : ℝ))) *
        oneStepLaplaceContraction (Real.toNNReal C) (Real.toNNReal C⁻¹) ^
          earlyExitChainLength d (m - n).toNat) :
    Q {eta | ContinuousPath.exitTime U eta ≤ (t : ℝ≥0∞)} ≤
      ENNReal.ofReal (Real.exp
        (-earlyExitDecayConstant d M.gamma delta
            (earlyExitKappa (Real.toNNReal C) (Real.toNNReal C⁻¹)) *
          displacementMinScale M.nu (Disorder.cstar M) M.gamma (t : ℝ) m)) := by
  have hCinv : 0 < C⁻¹ := inv_pos.mpr hC
  exact measure_exitTime_le_exp_neg_displacementMinScale_on M Q U t
    (oneStepLaplaceContraction (Real.toNNReal C) (Real.toNNReal C⁻¹)) hC hdelta hdelta1 ht
    (earlyExitKappa_pos (Real.toNNReal_pos.mpr hC) (Real.toNNReal_pos.mpr hCinv)) hnm
    hnLower hnUpper hscale hdeltaSmall hlarge hchain
    (oneStepLaplaceContraction_le_exp_neg_earlyExitKappa _ _)

end Carrier

/-! ## 2. The early-exit tail of the stream process -/

/-- **The printed early-exit tail for the stream process.**  The chained estimate of the
canonical chain, the auxiliary-scale straddle and the deterministic exponent optimization
give the paper's exponential minimum for the probability that the process of the stream
field leaves `□_m` before time `t`.

Beside the model data, the accuracy and the scales, the statement carries the percolation
crossing count, the exit-time analytic data of the full field at every good cell, and the
auxiliary-scale straddle.  The counting premise of the canonical chain is not carried: it
follows from the base-scale threshold the straddle already assumes. -/
theorem measure_exitTime_le_exp_neg_displacementMinScale_streamProcess
    (d : ℕ) [NeZero d] (hdim : 2 ≤ d) (cstar : ℝ) (hcstar : 0 < cstar)
    (Creg : ℝ) (hCreg : 0 < Creg) :
    ∃ gamma0 Cev C c : ℝ, 0 < gamma0 ∧ 0 < Cev ∧ 0 < C ∧ 0 < c ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ ep : ℝ, ep ∈ Set.Ioc (0 : ℝ) (1 / 4) → ep ≤ c →
      ∀ n : ℤ,
      ∀ m : ℤ, n ≤ m →
      ∀ (omega : Field.FullSample d M.gamma) (i : Fin d)
        (Good : Section5.Percolation.Site d → Prop) [DecidablePred Good],
        (∀ z, Good z ↔ omega.1 ∈ qEvent M Creg Cev n (rescaledLatticePoint n z) ep) →
        (∀ (N : ℕ) (y : ℕ → Fin d → ℤ),
          Provider.Percolation.IsLatticePath y N →
          y 0 ∈ Provider.Percolation.cubeAt (m - n).toNat 0 →
          y N ∉ Provider.Percolation.cubeAt ((m - n).toNat + 1) 0 →
          (3 / 4 : ℝ) * (3 : ℝ) ^ (m - n).toNat ≤
            ((qSiteCount M Creg Cev n ep
              (Section5.Percolation.pathSites N y) omega.1 : ℕ) : ℝ)) →
        (∀ j : Fin (goodSites ((m - n).toNat + 1) Good).card,
          HasCubeStreamExitTimeData M n omega i
            (rescaledLatticePoint n (goodSiteEnum ((m - n).toNat + 1) Good j))) →
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      ∀ t : NNReal, 0 < (t : ℝ) →
        (3 : ℝ) ^ n ≤ auxiliaryScaleBound M.nu (Disorder.cstar M) M.gamma delta (t : ℝ) m →
        auxiliaryScaleBound M.nu (Disorder.cstar M) M.gamma delta (t : ℝ) m <
          (3 : ℝ) ^ (n + 1) →
        lengthTimeScale M.nu (Disorder.cstar M) M.gamma ((3 : ℝ) ^ n) ≤
          2 * exitTimeScale M n →
        128 * (3 : ℝ) ^ d * delta *
            earlyExitProfileCost (Disorder.cstar M) M.gamma ≤
          C * earlyExitKappa (Real.toNNReal C) (Real.toNNReal C⁻¹) →
        earlyExitBaseScale d ≤ 3 ^ (m - n).toNat →
      ∀ x ∈ Metric.closedBall (0 : Vec d) ((1 / 2 : ℝ) * (3 : ℝ) ^ (m - 1)),
        letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
        letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
        streamProcess M omega (x : OnePoint (Vec d))
            {eta | ContinuousPath.exitTime
              (((↑) : Vec d → OnePoint (Vec d)) '' openCubeSet (originCube d m)) eta ≤
                (t : ℝ≥0∞)} ≤
          ENNReal.ofReal (Real.exp
            (-earlyExitDecayConstant d M.gamma delta
                (earlyExitKappa (Real.toNNReal C) (Real.toNNReal C⁻¹)) *
              displacementMinScale M.nu (Disorder.cstar M) M.gamma (t : ℝ) m)) := by
  obtain ⟨gamma0, Cev, C, c, hgamma0, hCev, hC, hc, hmain⟩ :=
    measure_exitTime_le_canonicalChain_of_percolation_crossing_streamProcess d hdim cstar
      hcstar Creg hCreg
  refine ⟨gamma0, Cev, C, c, hgamma0, hCev, hC, hc, ?_⟩
  intro M hcs hgam ep hep hepc n m hm omega i Good _inst hGood hcrossing hdata
    delta hdelta hdelta1 t ht hnLower hnUpper hscale hdeltaSmall hlarge x hx
  let := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
  let := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
  exact measure_exitTime_le_exp_neg_displacementMinScale_of_oneStepLaplace_on M
    (streamProcess M omega (x : OnePoint (Vec d)))
    (((↑) : Vec d → OnePoint (Vec d)) '' openCubeSet (originCube d m)) t hC hdelta hdelta1
    ht hm hnLower hnUpper hscale hdeltaSmall hlarge
    (hmain M hcs hgam ep hep hepc n m hm omega i Good hGood hcrossing
      (earlyExitTraceCount_pos_of_earlyExitBaseScale_le d (m - n).toNat hlarge) hdata x hx t)

end

end Algsuperdiff.Section5.Provider
