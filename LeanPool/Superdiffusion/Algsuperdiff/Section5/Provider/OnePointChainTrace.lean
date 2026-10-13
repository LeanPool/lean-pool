/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.OnePointChainPath
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Trace.GoodCubeCrossing
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Trace.HitExitBridge

/-!
# OnePointChainTrace

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The early-exit bound for a process read inside a larger carrier

The chaining input of the early-exit bound is a cube trace: almost every path leaving the maximal
cube in finite time visits, strictly before that exit, at least `D` distinct good scale-`n` cells.
The trace is produced by a deterministic argument about continuous paths of the state space.

Here the process lives on a larger carrier, the state space being read inside it by an open
embedding, and the paths are paths of the carrier.  Two facts bridge the gap.  A path that never
leaves the read state space is the reading of a path of the state space itself, so the
deterministic trace argument applies to it verbatim; and the exit time from a read set, along a
read path, is the exit time from the set itself.  The chaining estimate is then applied on the
carrier, at the read cube families of `OnePointChainPath`.

The hypothesis that the paths stay in the read state space is explicit.  For the compactified
process of a conservative live semigroup it is the almost-sure liveness of the paths.

## Main results

* `exists_goodCubeTrace_of_eval_zero` — the deterministic pre-exit trace at a fixed starting
  point.
* `ae_exists_goodCubeTrace_image` — its almost-sure form for a process of the carrier.
* `measure_exitTime_le_le_rho_pow_of_good_cube_trace_image` — the hit-then-exit estimate for the
  read families.
* `measure_exitTime_le_le_rho_pow_of_percolation_crossing_image` — the early-exit bound at one
  sample and one scale, on the carrier.

## References

* ABK26, the chaining of Section 5.3.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support Algsuperdiff.Section5.Trace
open DivergenceFormProcess.LiveRestriction
open HCPolySupport MarkovProcess MarkovProcess.SubMarkovKernelSemigroup MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

variable {d r : ℕ}

/-! ## 1. The deterministic pre-exit trace -/

/-- **The pre-exit good cube trace at a fixed starting point.**  A continuous path starting in the
closed cube `□_{n+k}` and leaving `□_{n+k+1}` in finite time has a scale-`n` cube trace, all of
whose vertices are visited strictly before the exit, with at least `L - 2 d` good vertices, each
enumerated by `goodSiteEnum (k + 1)`. -/
theorem exists_goodCubeTrace_of_eval_zero (hd : 0 < d) (n : ℤ) (k L : ℕ)
    (Good : Section5.Percolation.Site d → Prop) [DecidablePred Good]
    (hcross : ∀ Xi : List (Section5.Percolation.Site d),
      Section5.Percolation.IsPathFrom k Xi → L ≤ (Xi.toFinset.filter Good).card)
    (x : Vec d) (hx : x ∈ Metric.closedBall (0 : Vec d)
      ((1 / 2 : ℝ) * (3 : ℝ) ^ (n + (k : ℤ))))
    (w : ContinuousPath (Vec d)) (hzero : w 0 = x)
    (hfin : ContinuousPath.exitTime
      (openCubeSet (originCube d (n + ((k + 1 : ℕ) : ℤ)))) w < ⊤) :
    ∃ Gamma : List (Section5.Percolation.Site d),
      L - 2 * d ≤ (Gamma.toFinset.filter Good).card ∧
      (∀ z ∈ Gamma.toFinset, Good z →
        ∃ j : Fin (goodSites (k + 1) Good).card,
          goodSiteEnum (k + 1) Good j = z) ∧
      ∀ z ∈ Gamma.toFinset, ∃ t : NNReal,
        ((t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime
          (openCubeSet (originCube d (n + ((k + 1 : ℕ) : ℤ)))) w ∧
        w t ∈ cubeSet (partitionCube n z) := by
  have hs : (0 : ℝ) < (3 : ℝ) ^ (n + (k : ℤ)) := zpow_pos (by norm_num) _
  have hpow : (3 : ℝ) ^ (n + ((k + 1 : ℕ) : ℤ)) = 3 * (3 : ℝ) ^ (n + (k : ℤ)) := by
    rw [show n + ((k + 1 : ℕ) : ℤ) = (n + (k : ℤ)) + 1 by push_cast; ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0) _ 1, zpow_one]
    ring
  have hstart : w 0 ∈ Metric.closedBall (0 : Vec d)
      ((1 / 2 : ℝ) * (3 : ℝ) ^ (n + (k : ℤ))) := by
    rw [hzero]; exact hx
  have hcoord : ∀ i, |w 0 i| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ (n + (k : ℤ)) := by
    intro i
    have hball := (dist_pi_le_iff (by positivity)).mp
      (Metric.mem_closedBall.mp hstart) i
    rwa [Real.dist_eq, Pi.zero_apply, sub_zero] at hball
  have hmem : w 0 ∈ openCubeSet (originCube d (n + ((k + 1 : ℕ) : ℤ))) := by
    refine mem_openCubeSet_originCube_iff.mpr fun i => ?_
    have hi := abs_le.mp (hcoord i)
    rw [hpow]
    constructor <;> linarith only [hi.1, hi.2, hs]
  have hpos : 0 < ContinuousPath.exitTime
      (openCubeSet (originCube d (n + ((k + 1 : ℕ) : ℤ)))) w :=
    (ContinuousPath.exitTime_pos_iff _ (isOpen_openCubeSet _) w).mpr hmem
  obtain ⟨Gamma, hGammaCount, hGammaVisit⟩ :=
    exists_preExit_goodCubeTrace hd n k L w hstart hpos hfin.ne Good hcross
  refine ⟨Gamma, hGammaCount, ?_, hGammaVisit⟩
  intro z hz hgood
  obtain ⟨s, hs', hmemCube⟩ := hGammaVisit z hz
  exact exists_goodSiteEnum_eq Good
    (inCube_of_mem_cubeSet_partitionCube n k hmemCube
      (ContinuousPath.mem_of_lt_exitTime _ w s hs')) hgood

/-! ## 2. The trace along a path of the carrier -/

section Carrier

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

omit [LocallyCompactSpace alpha] in
/-- **The trace hypothesis on the carrier.**  Almost every path of the read process that leaves
the read maximal cube in finite time has a read cube trace with the same count.  The two inputs
are that the paths stay in the read state space and that they start where the process is
started. -/
theorem ae_exists_goodCubeTrace_image (hd : 0 < d) (n : ℤ) (k L : ℕ)
    (emb : C(Vec d, alpha)) (hemb : Topology.IsEmbedding emb)
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (hK : P.KolmogorovRegular hP)
    (Good : Section5.Percolation.Site d → Prop) [DecidablePred Good]
    (hcross : ∀ Xi : List (Section5.Percolation.Site d),
      Section5.Percolation.IsPathFrom k Xi → L ≤ (Xi.toFinset.filter Good).card)
    (x : Vec d) (hx : x ∈ Metric.closedBall (0 : Vec d)
      ((1 / 2 : ℝ) * (3 : ℝ) ^ (n + (k : ℤ))))
    (hstay : ∀ᵐ omega ∂(hP.continuousProcess P (emb x)),
      ContinuousPath.exitTime (Set.range emb) omega = ⊤) :
    ∀ᵐ omega ∂(hP.continuousProcess P (emb x)),
      ContinuousPath.exitTime
          (emb '' openCubeSet (originCube d (n + ((k + 1 : ℕ) : ℤ)))) omega < ⊤ →
        ∃ Gamma : List (Section5.Percolation.Site d),
          L - 2 * d ≤ (Gamma.toFinset.filter Good).card ∧
          (∀ z ∈ Gamma.toFinset, Good z →
            ∃ j : Fin (goodSites (k + 1) Good).card,
              goodSiteEnum (k + 1) Good j = z) ∧
          ∀ z ∈ Gamma.toFinset, ∃ t : NNReal,
            ((t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime
              (emb '' openCubeSet (originCube d (n + ((k + 1 : ℕ) : ℤ)))) omega ∧
            omega t ∈ emb '' cubeSet (partitionCube n z) := by
  filter_upwards [hstay, hP.ae_eval_zero_eq hK (emb x)] with omega hlive hzero
  obtain ⟨w, rfl⟩ := exists_pathPostcomp_eq_of_exitTime_range_eq_top emb hemb omega hlive
  have hexit : ContinuousPath.exitTime
      (emb '' openCubeSet (originCube d (n + ((k + 1 : ℕ) : ℤ))))
        (pathPostcomp emb w) =
      ContinuousPath.exitTime
        (openCubeSet (originCube d (n + ((k + 1 : ℕ) : ℤ)))) w :=
    exitTime_image_pathPostcomp emb hemb.injective _ w
  have hw0 : w 0 = x := hemb.injective (by simpa only [pathPostcomp_apply] using hzero)
  rw [hexit]
  intro hfin
  obtain ⟨Gamma, hcount, henum, hvisit⟩ :=
    exists_goodCubeTrace_of_eval_zero hd n k L Good hcross x hx w hw0 hfin
  refine ⟨Gamma, hcount, henum, fun z hz => ?_⟩
  obtain ⟨s, hs, hmem⟩ := hvisit z hz
  exact ⟨s, hs, ⟨w s, hmem, rfl⟩⟩

omit [CompleteSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [Nonempty alpha] [LocallyCompactSpace alpha] in
/-- **The read family of visited cells.**  Distinct good sites of a read cube trace give the
finite set of distinct family indices the chaining estimate consumes. -/
theorem exists_image_enumeratedClosedCubeFamily_visitFinset {D : ℕ} (emb : C(Vec d, alpha))
    (n : ℤ) (sites : Fin r ↪ Section5.Percolation.Site d) (U : Set alpha)
    (omega : ContinuousPath alpha) (Gamma : List (Section5.Percolation.Site d))
    (Good : Section5.Percolation.Site d → Prop) [DecidablePred Good]
    (hcount : D ≤ (Gamma.toFinset.filter Good).card)
    (henumerated : ∀ z ∈ Gamma.toFinset, Good z → ∃ j : Fin r, sites j = z)
    (hvisited : ∀ z ∈ Gamma.toFinset, ∃ t : NNReal,
      ((t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega ∧
      omega t ∈ emb '' cubeSet (partitionCube n z)) :
    ∃ s : Finset ℕ, D ≤ s.card ∧ ∀ i ∈ s,
      ∃ t : NNReal,
        ((t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega ∧
        omega t ∈ emb '' enumeratedClosedCubeFamily n sites i := by
  let q : Finset (Fin r) := Finset.univ.filter fun j =>
    sites j ∈ Gamma.toFinset.filter Good
  let s : Finset ℕ := q.image Fin.val
  have himage : q.image sites = Gamma.toFinset.filter Good := by
    ext z
    constructor
    · intro hz
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hj).2
    · intro hz
      obtain ⟨j, hj⟩ := henumerated z (Finset.mem_filter.mp hz).1
        (Finset.mem_filter.mp hz).2
      apply Finset.mem_image.mpr
      refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hj⟩
      simpa only [hj] using hz
  refine ⟨s, ?_, ?_⟩
  · calc
      D ≤ (Gamma.toFinset.filter Good).card := hcount
      _ = (q.image sites).card := by rw [himage]
      _ = q.card := Finset.card_image_of_injective q sites.injective
      _ = s.card := (Finset.card_image_of_injective q Fin.val_injective).symm
  · intro i hi
    obtain ⟨j, hjq, hji⟩ := Finset.mem_image.mp hi
    have hjTrace : sites j ∈ Gamma.toFinset :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hjq).2).1
    obtain ⟨t, ht, htCube⟩ := hvisited (sites j) hjTrace
    refine ⟨t, ht, ?_⟩
    rw [← hji, enumeratedClosedCubeFamily, dite_eq_left j.isLt]
    exact Set.image_mono (cubeSet_partitionCube_subset_closedPartitionCube n (sites j)) htCube

/-! ## 3. The hit-then-exit estimate on the carrier -/

/-- **Trace-to-tail consumer bridge on a carrier.**  The read padded cells satisfy the counting
hypothesis of the hit-then-exit estimate and their read threefold enlargements the overlap
hypothesis with `K = 3^d`, so the estimate gives `Q_x(τ ≤ t) ≤ exp(lam t) rho^N` whenever
`N 3^d < D`. -/
theorem measure_exitTime_le_le_rho_pow_of_good_cube_trace_image
    (emb : C(Vec d, alpha)) (hemb : Topology.IsOpenEmbedding emb)
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP) (n : ℤ)
    (sites : Fin r ↪ Section5.Percolation.Site d)
    (U : Set (Vec d)) (hU : IsOpen U)
    (lam : ℝ) (hlam : 0 < lam) (rho : ℝ≥0∞) (hrho : rho ≠ ⊤)
    (hone : ∀ i, ∀ z ∈ emb '' enumeratedClosedCubeFamily n sites i,
      ∫⁻ eta, Algsuperdiff.Process.ContinuousPath.discountedStoppingWeight lam
          (ContinuousPath.exitTime
            (emb '' enumeratedOpenEnlargementFamily n sites i)) eta
        ∂(hP.continuousProcess P z) ≤ rho)
    (Good : Section5.Percolation.Site d → Prop) [DecidablePred Good]
    (D N : ℕ) (x : alpha)
    (htrace : ∀ᵐ omega ∂(hP.continuousProcess P x),
      ContinuousPath.exitTime (emb '' U) omega < ⊤ →
        ∃ Gamma : List (Section5.Percolation.Site d),
          D ≤ (Gamma.toFinset.filter Good).card ∧
          (∀ z ∈ Gamma.toFinset, Good z → ∃ j : Fin r, sites j = z) ∧
          ∀ z ∈ Gamma.toFinset, ∃ t : NNReal,
            ((t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime (emb '' U) omega ∧
            omega t ∈ emb '' cubeSet (partitionCube n z))
    (hcount : N * 3 ^ d < D) (t : NNReal) :
    hP.continuousProcess P x
        {omega | ContinuousPath.exitTime (emb '' U) omega ≤ (t : ℝ≥0∞)} ≤
      ENNReal.ofReal (Real.exp (lam * (t : ℝ))) * rho ^ N := by
  apply Algsuperdiff.Process.SubMarkovKernelSemigroup.IsConservative.measure_exitTime_le_le_rho_pow_hitExit
    P hP hFeller hK
    (fun i => emb '' enumeratedClosedCubeFamily n sites i)
    (fun i => emb '' enumeratedOpenEnlargementFamily n sites i)
    (measurableSet_image_enumeratedClosedCubeFamily emb n sites)
    (isClosed_iUnion_image_enumeratedClosedCubeFamily emb n sites)
    (isOpen_image_enumeratedOpenEnlargementFamily emb hemb n sites)
    (emb '' U) (hemb.isOpenMap _ hU) lam hlam rho hrho hone
    (3 ^ d) D N x (image_enumeratedCubeFamily_overlap emb hemb.injective n sites) _ hcount t
  filter_upwards [htrace] with omega homega
  intro hexit
  obtain ⟨Gamma, hD, henumerated, hvisited⟩ := homega hexit
  exact exists_image_enumeratedClosedCubeFamily_visitFinset emb n sites (emb '' U) omega Gamma
    Good hD henumerated hvisited

/-! ## 4. The early-exit bound at one sample and one scale -/

/-- **The early-exit bound from one crossing count, on the carrier.**  This is the estimate of
`measure_exitTime_le_le_rho_pow_of_percolation_crossing` for a process of a carrier in which the
state space is read by an open embedding, with the almost-sure confinement of the paths to the
read state space as the one extra input. -/
theorem measure_exitTime_le_le_rho_pow_of_percolation_crossing_image (hd : 0 < d)
    (M : ABKModel d) (Creg Cinj : ℝ) {m n : ℤ} (hnm : n ≤ m) (ep : ℝ)
    (omega : Cutoff.CutoffSample d)
    (hcrossing : ∀ (N : ℕ) (y : ℕ → Fin d → ℤ),
      Provider.Percolation.IsLatticePath y N →
      y 0 ∈ Provider.Percolation.cubeAt (m - n).toNat 0 →
      y N ∉ Provider.Percolation.cubeAt ((m - n).toNat + 1) 0 →
      (3 / 4 : ℝ) * (3 : ℝ) ^ (m - n).toNat ≤
        ((qSiteCount M Creg Cinj n ep
          (Section5.Percolation.pathSites N y) omega : ℕ) : ℝ))
    (Good : Section5.Percolation.Site d → Prop) [DecidablePred Good]
    (hGood : ∀ z, Good z ↔
      omega ∈ qEvent M Creg Cinj n (rescaledLatticePoint n z) ep)
    (emb : C(Vec d, alpha)) (hemb : Topology.IsOpenEmbedding emb)
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (lam : ℝ) (hlam : 0 < lam) (rho : ℝ≥0∞) (hrho : rho ≠ ⊤)
    (hone : ∀ i, ∀ z ∈ emb '' enumeratedClosedCubeFamily (n - 1)
        (goodSiteEnum ((m - n).toNat + 1) Good) i,
      ∫⁻ eta, Algsuperdiff.Process.ContinuousPath.discountedStoppingWeight lam
          (ContinuousPath.exitTime
            (emb '' enumeratedOpenEnlargementFamily (n - 1)
              (goodSiteEnum ((m - n).toNat + 1) Good) i)) eta
        ∂(hP.continuousProcess P z) ≤ rho)
    (Nchain : ℕ) (hcount : Nchain * 3 ^ d < 3 * 3 ^ (m - n).toNat / 4 - 2 * d)
    (x : Vec d)
    (hx : x ∈ Metric.closedBall (0 : Vec d) ((1 / 2 : ℝ) * (3 : ℝ) ^ (m - 1)))
    (hstay : ∀ᵐ eta ∂(hP.continuousProcess P (emb x)),
      ContinuousPath.exitTime (Set.range emb) eta = ⊤)
    (t : NNReal) :
    hP.continuousProcess P (emb x)
        {eta | ContinuousPath.exitTime
          (emb '' openCubeSet (originCube d m)) eta ≤ (t : ℝ≥0∞)} ≤
      ENNReal.ofReal (Real.exp (lam * (t : ℝ))) * rho ^ Nchain := by
  have houter : (n - 1) + (((m - n).toNat + 1 : ℕ) : ℤ) = m := by
    push_cast
    omega
  have hinner : (n - 1) + (((m - n).toNat : ℕ) : ℤ) = m - 1 := by
    omega
  have hcross : ∀ Xi : List (Section5.Percolation.Site d),
      Section5.Percolation.IsPathFrom (m - n).toNat Xi →
        3 * 3 ^ (m - n).toNat / 4 ≤ (Xi.toFinset.filter Good).card :=
    fun Xi hXi => natThreshold_le_card_filter_of_isPathFrom M Creg Cinj m n ep omega
      Good hGood hcrossing Xi hXi
  have hxball : x ∈ Metric.closedBall (0 : Vec d)
      ((1 / 2 : ℝ) * (3 : ℝ) ^ ((n - 1) + (((m - n).toNat : ℕ) : ℤ))) := by
    rw [hinner]; exact hx
  have htrace := ae_exists_goodCubeTrace_image hd (n - 1) (m - n).toNat
    (3 * 3 ^ (m - n).toNat / 4) emb hemb.isEmbedding P hP hK Good hcross x hxball hstay
  rw [houter] at htrace
  exact measure_exitTime_le_le_rho_pow_of_good_cube_trace_image emb hemb P hP hFeller hK (n - 1)
    (goodSiteEnum ((m - n).toNat + 1) Good) (openCubeSet (originCube d m))
    (isOpen_openCubeSet _) lam hlam rho hrho hone Good
    (3 * 3 ^ (m - n).toNat / 4 - 2 * d) Nchain (emb x) htrace hcount t

end Carrier

end

end Algsuperdiff.Section5.Provider
