/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.StreamProcess
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.OnePointChainPrinted
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.OnePointChainStreamJoint
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ParameterizedProcessSemigroup

/-!
# OnePointChainStreamFull

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The displacement tail for the process of the stream field, from the full field's cell problems

The chaining layer of `OnePointChainTrace` and the printed optimization of `OnePointChainPrinted`
are read here at the process the model produces, with the per-cell exit-time joint taken for the
full stream field.  Every input the chain asks about the process is supplied by the model: the
resolvent is the split-skew analytic resolvent, its regularity datum is the shift-dependent
exhaustion-tail input, conservativity of the live kernel semigroup and the bounded-measurable
identification are the model's own theorems, and the operator identification holds by definition.

Two hypotheses of the earlier reading disappear here.  The small-contrast datum of the stream
field is gone, because the exit-time identity used is the one proved directly from the localized
split-skew barrier.  The compatibility of the stream coefficient with a truncated field is gone,
because the cell problems are now posed for the stream coefficient itself.  In particular one
sample of the full field, rather than a sample of the full field together with an unrelated
truncation sample, determines both the process and the cells.

## Main results

* `earlyExitTraceCount_pos_of_earlyExitBaseScale_le` — the counting premise of the canonical
  chain length follows from the base-scale threshold of the printed optimization.
* `measure_exitTime_le_canonicalChain_of_percolation_crossing_streamProcess` — the chained
  early-exit estimate for the stream process at the canonical chain length.

## References

* ABK26, the one-step Laplace estimate, the chaining and the displacement tail of Section 5.3.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open Algsuperdiff.Section5.Field Algsuperdiff.Section5.Support Algsuperdiff.Section5.Trace
open DivergenceFormProcess.Form
open DivergenceFormProcess.LiveRestriction
open DivergenceFormProcess.StoppedDirichlet
open HCPolySupport MarkovProcess MarkovProcess.Semigroup
open MarkovProcess.SubMarkovKernelSemigroup MeasureTheory Set
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-! ## 1. The counting premise of the canonical chain -/

/-- **The base-scale threshold already forces a usable trace count.**  At `3^k` above
`64 (d + 1 + 3^d)` the number of trace sites left after discarding the `2 d` sites of the two
endpoints is positive, which is the premise the canonical chain length needs. -/
theorem earlyExitTraceCount_pos_of_earlyExitBaseScale_le (d k : ℕ)
    (h : earlyExitBaseScale d ≤ 3 ^ k) : 0 < earlyExitTraceCount d k := by
  have hbase : 64 * (d + 1) ≤ earlyExitBaseScale d := by
    unfold earlyExitBaseScale
    exact Nat.mul_le_mul (le_refl 64) (Nat.le_add_right (d + 1) (3 ^ d))
  have h1 : 64 * (d + 1) ≤ 3 ^ k := le_trans hbase h
  have h2 : 4 * (48 * (d + 1)) ≤ 3 * 3 ^ k := by omega
  have h3 : 48 * (d + 1) ≤ 3 * 3 ^ k / 4 := by
    have hdiv : 4 * (48 * (d + 1)) / 4 ≤ 3 * 3 ^ k / 4 := Nat.div_le_div_right h2
    rwa [Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)] at hdiv
  have h4 : 2 * d < 3 * 3 ^ k / 4 := lt_of_lt_of_le (by omega) h3
  unfold earlyExitTraceCount
  exact Nat.sub_pos_of_lt h4

/-! ## 2. The chained early-exit estimate -/

/-- **The chained early-exit estimate for the stream process.**  At one sample of the full field
and one nonnegative cube scale `n ≤ m`, the crossing count of the annulus at index `m - n`, the
counting premise of the canonical chain length and the exit-time analytic data of the full field
at every good cell give the tail bound for the process of the stream field, at the discount rate
`(C T(3^n))⁻¹` and the one-step contraction factor.

No hypothesis about a resolvent, a small-contrast datum, or a truncated coefficient field
appears. -/
theorem measure_exitTime_le_canonicalChain_of_percolation_crossing_streamProcess
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
        0 < earlyExitTraceCount d (m - n).toNat →
        (∀ j : Fin (goodSites ((m - n).toNat + 1) Good).card,
          HasCubeStreamExitTimeData M n omega i
            (rescaledLatticePoint n (goodSiteEnum ((m - n).toNat + 1) Good j))) →
      ∀ x ∈ Metric.closedBall (0 : Vec d) ((1 / 2 : ℝ) * (3 : ℝ) ^ (m - 1)),
      ∀ t : NNReal,
        letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
        letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
        streamProcess M omega (x : OnePoint (Vec d))
            {eta | ContinuousPath.exitTime
              (((↑) : Vec d → OnePoint (Vec d)) '' openCubeSet (originCube d m)) eta ≤
                (t : ℝ≥0∞)} ≤
          ENNReal.ofReal (Real.exp ((C * exitTimeScale M n)⁻¹ * (t : ℝ))) *
            oneStepLaplaceContraction (Real.toNNReal C) (Real.toNNReal C⁻¹) ^
              earlyExitChainLength d (m - n).toNat := by
  obtain ⟨g1, CevA, C, c, hg1, hCevA, hC, hc, hlap⟩ :=
    one_step_laplace_hone_of_good_sites_stream_image d hdim cstar hcstar Creg hCreg
  obtain ⟨g2, CevB, hg2, hCevB, hjointOf⟩ :=
    isCubeExitTimeSolutionDataStream_onePoint_of_mem_qEvent d hdim cstar hcstar Creg hCreg
  refine ⟨min g1 g2, max CevA CevB, C, c, lt_min hg1 hg2,
    lt_of_lt_of_le hCevA (le_max_left _ _), hC, hc, ?_⟩
  intro M hcs hgam ep hep hepc n m hm omega i Good _inst hGood hcrossing htraceCount hdata
    x hx t
  have hepnn : (0 : ℝ) ≤ ep := hep.1.le
  have hgam1 : M.gamma ≤ g1 := le_trans hgam (min_le_left _ _)
  have hgam2 : M.gamma ≤ g2 := le_trans hgam (min_le_right _ _)
  have hqA : ∀ z, Good z → omega.1 ∈ qEvent M Creg CevA n (rescaledLatticePoint n z) ep :=
    fun z hz =>
      qEvent_antitone_const M Creg hCevA (le_max_left _ _) n _ hepnn ((hGood z).1 hz)
  have hqB : ∀ z, Good z → omega.1 ∈ qEvent M Creg CevB n (rescaledLatticePoint n z) ep :=
    fun z hz =>
      qEvent_antitone_const M Creg hCevB (le_max_right _ _) n _ hepnn ((hGood z).1 hz)
  let := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
  let := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
  have hjoint : ∀ j : Fin (goodSites ((m - n).toNat + 1) Good).card,
      IsCubeExitTimeSolutionDataStream M n omega (OnePoint (Vec d))
        (streamWholeSpaceResolvent M omega).onePointKernelSemigroup
        (streamWholeSpaceResolvent M omega).isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt (rescaledLatticePoint n
          (goodSiteEnum ((m - n).toNat + 1) Good j)) n)
        ((↑) : Vec d → OnePoint (Vec d)) i
        (rescaledLatticePoint n (goodSiteEnum ((m - n).toNat + 1) Good j)) := fun j =>
    hjointOf M hcs hgam2 ep hep n _ i omega (hqB _ (good_goodSiteEnum Good j)) (hdata j)
      (streamWholeSpaceResolvent M omega) (streamExhaustionTailInput M omega).toOnePointRegular
      (isConservative_streamKernelSemigroup M omega)
      (kernelResolventIdentifiesAnalyticMinimal_stream M omega) (fun _ _ => rfl)
  obtain ⟨hlam, -, hone⟩ :=
    hlap M hcs hgam1 ep hep hepc n omega i _ (goodSiteEnum ((m - n).toNat + 1) Good)
      (fun j => hqA _ (good_goodSiteEnum Good j)) (OnePoint (Vec d)) (liveEmbedding (Vec d))
      (streamWholeSpaceResolvent M omega).onePointKernelSemigroup
      (streamWholeSpaceResolvent M omega).isConservative_onePointKernelSemigroup
      (streamWholeSpaceResolvent M omega).isFellerKernelSemigroup_onePointKernelSemigroup
      (streamExhaustionTailInput M omega).toOnePointRegular.kolmogorovRegular hjoint
  have hstay : ∀ᵐ eta ∂(IsConservative.continuousProcess
      (streamWholeSpaceResolvent M omega).onePointKernelSemigroup
      (streamWholeSpaceResolvent M omega).isConservative_onePointKernelSemigroup
      (x : OnePoint (Vec d))),
      ContinuousPath.exitTime (Set.range ((↑) : Vec d → OnePoint (Vec d))) eta = ⊤ :=
    onePointProcess_ae_stays_live (streamExhaustionTailInput M omega).toOnePointRegular
      (isConservative_streamKernelSemigroup M omega) x
  refine measure_exitTime_le_le_rho_pow_of_percolation_crossing_image (by omega) M Creg
    (max CevA CevB) hm ep omega.1 hcrossing Good hGood (liveEmbedding (Vec d))
    OnePoint.isOpenEmbedding_coe
    (streamWholeSpaceResolvent M omega).onePointKernelSemigroup
    (streamWholeSpaceResolvent M omega).isConservative_onePointKernelSemigroup
    (streamWholeSpaceResolvent M omega).isFellerKernelSemigroup_onePointKernelSemigroup
    (streamExhaustionTailInput M omega).toOnePointRegular.kolmogorovRegular _ hlam _
    (oneStepLaplaceContraction_ne_top _ _) hone (earlyExitChainLength d (m - n).toNat) ?_ x hx
    hstay t
  simpa only [earlyExitTraceCount] using
    earlyExitChainLength_mul_lt d (m - n).toNat htraceCount

end

end Algsuperdiff.Section5.Provider
