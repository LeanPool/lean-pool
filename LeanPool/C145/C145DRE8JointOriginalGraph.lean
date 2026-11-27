/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145DRE8JointTransferInverse
public import LeanPool.C145.C145DRE8OriginalGraphInverse

/-! The original fixed-horizon graph/port inverse under the DRE8 literal joint quadratic-Krylov
signature sufficient condition, with unrestricted-size admissible competitors.
Caller actual response and local C2 regularity are retained exactly as in the
accepted small-graph endpoint. The graph result identifies L, generator and
signed b; it does not identify unobservable self-loop weights. -/

@[expose] public section

noncomputable section
namespace C145DRE8
open scoped BigOperators Topology ContDiff
open MeasureTheory Set C145.DelayKernel
open C145.ActualResponse C145.ObservedKernelRecovery
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup
  AddCommGroup.toAddCommMonoid
  NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace
  UniformSpace.toTopologicalSpace

private theorem rates_pos_of_ground {n : ℕ} (μ : ℝ) (hμ : 0 < μ)
    (rates : Fin (n + 1) → ℝ) (hGround : rates 0 = μ)
    (hAbove : ∀ i : Fin n, μ < rates i.succ) : ∀ i, 0 < rates i := by
  intro i
  rcases Fin.eq_zero_or_eq_succ i with hi | ⟨j, hj⟩
  · rw [hi, hGround]
    exact hμ
  · rw [hj]
    exact lt_trans hμ (hAbove j)

theorem actual_time_kernel_theoremC_vertex_identification {m n : ℕ}
    (μ c0 c1 : ℝ) (hμ : 0 < μ)
    (Q0 : Fin (m + 1) → Fin (m + 1) → ℝ)
    (Q1 : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates0 b0 : Fin (m + 1) → ℝ)
    (rates1 b1 : Fin (n + 1) → ℝ)
    (hQ0 : C145PhysicalFrame.ColumnOrthonormal Q0)
    (hQ1 : C145PhysicalFrame.ColumnOrthonormal Q1)
    (hGround0 : ∀ v, Q0 v 0 = c0)
    (hGround1 : ∀ v, Q1 v 0 = c1)
    (hRates0 : Function.Injective rates0)
    (hRates1 : Function.Injective rates1)
    (hRateGround0 : rates0 0 = μ)
    (hRateGround1 : rates1 0 = μ)
    (hAbove0 : ∀ i : Fin m, μ < rates0 i.succ)
    (hAbove1 : ∀ j : Fin n, μ < rates1 j.succ)
    (ha0 : ∀ i, 0 < C145.Pulse.modalOverlap Q0 b0 i)
    (ha1 : ∀ j, 0 < C145.Pulse.modalOverlap Q1 b1 j)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hEig : ∀ i, A.mulVec (fun v => Q0 v i) =
      (-rates0 i) • (fun v => Q0 v i))
    (ell u : ℝ) (hw : ell < u) (hband : u < 2 * ell)
    (hlo : ∀ i : Fin m, ell ≤ rates0 i.succ) (hhi : ∀ i : Fin m, rates0 i.succ ≤ u)
    (delta : ℝ) (hd : 0 < delta)
    (hsep : ∀ j k, j ≠ k →
      delta ^ 2 ≤ signatureSq (physicalKrylov A b0 ell (u-ell)) j k)
    (hq : ((m + 1 : ℕ) + 2 : ℝ) *
      jointBetaSq (fun i : Fin m => C145.Pulse.modalOverlap Q0 b0 i.succ)
        (fun i => (rates0 i.succ-ell) / (u-ell)) (ell / (u-ell)) < delta ^ 2)
    (hK1 : ∀ r : ℝ, 0 ≤ r →
      firstKernel Q0 rates0 b0 r = firstKernel Q1 rates1 b1 r)
    (hK2 : ∀ r₁ r₂ : ℝ, 0 ≤ r₁ → 0 ≤ r₂ →
      delayKernel Q0 rates0 b0 r₁ r₂ =
        delayKernel Q1 rates1 b1 r₁ r₂) :
    ∃ e : Fin (m + 1) ≃ Fin (n + 1),
      m = n ∧ e 0 = 0 ∧
      (∀ i, rates1 (e i) = rates0 i) ∧
      (∀ i, C145.Pulse.modalOverlap Q1 b1 (e i) =
        C145.Pulse.modalOverlap Q0 b0 i) ∧
      c0 = c1 ∧ (∑ v, b0 v) = (∑ w, b1 w) ∧
      ∃ π : Fin (m + 1) ≃ Fin (n + 1),
        (∀ (w : Fin (n + 1)) (v : Fin (m + 1)),
          (∑ i : Fin (m + 1), Q1 w (e i) * Q0 v i) =
            if w = π v then 1 else 0) ∧
        (∀ (v i : Fin (m + 1)), Q1 (π v) (e i) = Q0 v i) ∧
        (∀ (v u : Fin (m + 1)),
          C145CoordinatePermutation.spectralGenerator rates1 Q1 (π v) (π u) =
            C145CoordinatePermutation.spectralGenerator rates0 Q0 v u) ∧
        (∀ v : Fin (m + 1), b1 (π v) = b0 v) ∧
        (∀ (v u : Fin (m + 1)),
          C145CoordinatePermutation.decayLaplacian μ rates1 Q1 (π v) (π u) =
            C145CoordinatePermutation.decayLaplacian μ rates0 Q0 v u) := by
  have hPos0 := rates_pos_of_ground μ hμ rates0 hRateGround0 hAbove0
  have hPos1 := rates_pos_of_ground μ hμ rates1 hRateGround1 hAbove1
  have hH1 : ∀ s : ℝ, 0 < s →
      C145.H1.firstTransfer rates0 (C145.Pulse.modalOverlap Q0 b0) s =
        C145.H1.firstTransfer rates1 (C145.Pulse.modalOverlap Q1 b1) s := by
    intro s hs
    rw [← (firstKernel_transform Q0 rates0 b0 hPos0 s hs).2,
      ← (firstKernel_transform Q1 rates1 b1 hPos1 s hs).2]
    unfold laplace
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    change Real.exp (-s * r) * firstKernel Q0 rates0 b0 r =
      Real.exp (-s * r) * firstKernel Q1 rates1 b1 r
    rw [hK1 r hr.le]
  have hH2 : ∀ s t : ℝ, 0 < s → 0 < t →
      C145.H2.H rates0 (C145PhysicalFrame.T Q0 (C145.Pulse.modalOverlap Q0 b0)) s t =
        C145.H2.H rates1 (C145PhysicalFrame.T Q1 (C145.Pulse.modalOverlap Q1 b1)) s t := by
    intro s t hs ht
    rw [← (delayKernel_transform Q0 rates0 b0 hPos0 s t hs ht).2,
      ← (delayKernel_transform Q1 rates1 b1 hPos1 s t hs ht).2]
    unfold doubleLaplace
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r₁ hr₁
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r₂ hr₂
    change Real.exp (-s * r₁) * Real.exp (-t * r₂) * delayKernel Q0 rates0 b0 r₁ r₂ =
      Real.exp (-s * r₁) * Real.exp (-t * r₂) * delayKernel Q1 rates1 b1 r₁ r₂
    rw [hK2 r₁ r₂ hr₁.le hr₂.le]
  exact actual_H1_H2_theoremC_vertex_identification
    μ c0 c1 hμ Q0 Q1 rates0 b0 rates1 b1 hQ0 hQ1 hGround0 hGround1
    hRates0 hRates1 hRateGround0 hRateGround1 hAbove0 hAbove1 ha0 ha1
    A hEig ell u hw hband hlo hhi delta hd hsep hq
    hH1 hH2

theorem ordinary_C2_jets_determine_theoremC_spectral_model {m n : ℕ} {T : ℝ}
    (hT : 0 < T)
    (μ c0 c1 : ℝ) (hμ : 0 < μ)
    (Q0 : Fin (m + 1) → Fin (m + 1) → ℝ)
    (Q1 : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates0 b0 : Fin (m + 1) → ℝ)
    (rates1 b1 : Fin (n + 1) → ℝ)
    (hQ0 : C145PhysicalFrame.ColumnOrthonormal Q0)
    (hQ1 : C145PhysicalFrame.ColumnOrthonormal Q1)
    (hGround0 : ∀ v, Q0 v 0 = c0)
    (hGround1 : ∀ v, Q1 v 0 = c1)
    (hRates0 : Function.Injective rates0)
    (hRates1 : Function.Injective rates1)
    (hRateGround0 : rates0 0 = μ)
    (hRateGround1 : rates1 0 = μ)
    (hAbove0 : ∀ i : Fin m, μ < rates0 i.succ)
    (hAbove1 : ∀ j : Fin n, μ < rates1 j.succ)
    (ha0 : ∀ i, 0 < C145.Pulse.modalOverlap Q0 b0 i)
    (ha1 : ∀ j, 0 < C145.Pulse.modalOverlap Q1 b1 j)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hEig : ∀ i, A.mulVec (fun v => Q0 v i) =
      (-rates0 i) • (fun v => Q0 v i))
    (ell u : ℝ) (hw : ell < u) (hband : u < 2 * ell)
    (hlo : ∀ i : Fin m, ell ≤ rates0 i.succ) (hhi : ∀ i : Fin m, rates0 i.succ ≤ u)
    (delta : ℝ) (hd : 0 < delta)
    (hsep : ∀ j k, j ≠ k →
      delta ^ 2 ≤ signatureSq (physicalKrylov A b0 ell (u-ell)) j k)
    (hq : ((m + 1 : ℕ) + 2 : ℝ) *
      jointBetaSq (fun i : Fin m => C145.Pulse.modalOverlap Q0 b0 i.succ)
        (fun i => (rates0 i.succ-ell) / (u-ell)) (ell / (u-ell)) < delta ^ 2)
    (R0 : Input T → Path m T) (R1 : Input T → Path n T)
    (hR0 : IsActualResponse hT Q0 rates0 b0 R0)
    (hR1 : IsActualResponse hT Q1 rates1 b1 R1)
    (hcR0 : ContDiffAt ℝ 2 R0 0) (hcR1 : ContDiffAt ℝ 2 R1 0)
    (hFirst : ∀ (g : ℝ → ℝ) (hg : SmoothTemporalTest T g),
      rawFirst b0 R0 (restrictInput T g hg.1.continuous) (endTime T hT) =
      rawFirst b1 R1 (restrictInput T g hg.1.continuous) (endTime T hT))
    (hMixed : ∀ (g h : ℝ → ℝ) (hg : SmoothTemporalTest T g) (hh : SmoothTemporalTest T h),
      rawMixed b0 R0 (restrictInput T g hg.1.continuous) (restrictInput T h hh.1.continuous)
          (endTime T hT) =
      rawMixed b1 R1 (restrictInput T g hg.1.continuous) (restrictInput T h hh.1.continuous)
          (endTime T hT)) :
    ∃ e : Fin (m + 1) ≃ Fin (n + 1),
      m = n ∧ e 0 = 0 ∧
      (∀ i, rates1 (e i) = rates0 i) ∧
      (∀ i, C145.Pulse.modalOverlap Q1 b1 (e i) =
        C145.Pulse.modalOverlap Q0 b0 i) ∧
      c0 = c1 ∧ (∑ v, b0 v) = (∑ w, b1 w) ∧
      ∃ π : Fin (m + 1) ≃ Fin (n + 1),
        (∀ (w : Fin (n + 1)) (v : Fin (m + 1)),
          (∑ i : Fin (m + 1), Q1 w (e i) * Q0 v i) =
            if w = π v then 1 else 0) ∧
        (∀ (v i : Fin (m + 1)), Q1 (π v) (e i) = Q0 v i) ∧
        (∀ (v u : Fin (m + 1)),
          C145CoordinatePermutation.spectralGenerator rates1 Q1 (π v) (π u) =
            C145CoordinatePermutation.spectralGenerator rates0 Q0 v u) ∧
        (∀ v : Fin (m + 1), b1 (π v) = b0 v) ∧
        (∀ (v u : Fin (m + 1)),
          C145CoordinatePermutation.decayLaplacian μ rates1 Q1 (π v) (π u) =
            C145CoordinatePermutation.decayLaplacian μ rates0 Q0 v u) := by
  have hObserved := ordinary_C2_jets_recover_observed_time_kernels hT
    Q0 rates0 b0 Q1 rates1 b1 hQ0 hQ1 R0 R1 hR0 hR1 hcR0 hcR1 hFirst hMixed
  have hAll := C145.TimeKernelContinuation.observed_time_kernels_determine_all_nonnegative_delays
    hT Q0 rates0 b0 Q1 rates1 b1 hObserved.1 hObserved.2
  exact actual_time_kernel_theoremC_vertex_identification
    μ c0 c1 hμ Q0 Q1 rates0 b0 rates1 b1 hQ0 hQ1 hGround0 hGround1
    hRates0 hRates1 hRateGround0 hRateGround1 hAbove0 hAbove1 ha0 ha1
    A hEig ell u hw hband hlo hhi delta hd hsep hq hAll.1 hAll.2

open Matrix C145.WeightedGraph C145.CyclicSpectral C145.GraphSpectralRealization

/-- One fixed actual source realization, derived from the original connected
cyclic graph. Its choice only selects an ordering of the genuine nonground
spectrum; no desired transport, tensor equality or reconstruction is supplied. -/
def sourceOrientedRealization {m : ℕ}
    (μ : ℝ) (hμ : 0 < μ)
    (W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hs : W.IsSymm) (hn : ∀ v u, 0 ≤ W v u)
    (hc : (supportGraph W hs).Connected)
    (b : State m) (hcyc : KrylovCyclic (generator μ W) b) :
    OrientedRealization μ W b :=
  Classical.choice (connected_cyclic_graph_has_oriented_spectral_realization
    μ hμ W hs hn hc b hcyc)

/-- Literal beta_0²+beta_1²+beta_2² from the actual source's nonground
rates and positive modal overlaps. The kappa_p inside jointBetaSq are true
weighted orthogonal projection residuals, for p=3,4,5. This is source spectral
data, not a hypothesis quantified over arbitrary realizations. -/
def originalSourceJointBetaSq {m : ℕ}
    (μ : ℝ) (hμ : 0 < μ)
    (W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hs : W.IsSymm) (hn : ∀ v u, 0 ≤ W v u)
    (hc : (supportGraph W hs).Connected)
    (b : State m) (hcyc : KrylovCyclic (generator μ W) b)
    (ell u : ℝ) : ℝ :=
  let S := sourceOrientedRealization μ hμ W hs hn hc b hcyc
  jointBetaSq (fun i : Fin m => C145.Pulse.modalOverlap S.Q b i.succ)
    (fun i => (S.rates i.succ-ell) / (u-ell)) (ell / (u-ell))

/-- DRE8 Theorem C for the actual original graph and signed port from fixed
positive-horizon ordinary response jets. Source q_H is expressed by its literal exact square; the
  joint separation
uses h0=b_perp, h1=S b_perp, h2=S² b_perp and permits repeated b entries. Modal
calibration, common signed ground, physical transport, residual H2 equality,
size equality and the simultaneous vertex bijection are all derived. -/
theorem ordinary_C2_jets_determine_theoremC_graph {m n : ℕ} {T : ℝ}
    (hT : 0 < T) (μ : ℝ) (hμ : 0 < μ)
    (W0 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (W1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hs0 : W0.IsSymm) (hs1 : W1.IsSymm)
    (hn0 : ∀ v u, 0 ≤ W0 v u) (hn1 : ∀ v u, 0 ≤ W1 v u)
    (hc0 : (supportGraph W0 hs0).Connected) (hc1 : (supportGraph W1 hs1).Connected)
    (b0 : State m) (b1 : State n)
    (hcyc0 : KrylovCyclic (generator μ W0) b0)
    (hcyc1 : KrylovCyclic (generator μ W1) b1)
    (ell u : ℝ) (hw : ell < u) (hband : u < 2 * ell)
    (hSpectrum : NonGroundDecayBand μ W0 ell u)
    (delta : ℝ) (hd : 0 < delta)
    (hsep : ∀ j k, j ≠ k → delta ^ 2 ≤
      signatureSq (physicalKrylov (generator μ W0) b0 ell (u - ell)) j k)
    (hq : ((m + 1 : ℕ) + 2 : ℝ) *
      originalSourceJointBetaSq μ hμ W0 hs0 hn0 hc0 b0 hcyc0 ell u < delta ^ 2)
    (R0 : Input T → Path m T) (R1 : Input T → Path n T)
    (hR0 : IsGraphResponse hT μ W0 b0 R0) (hR1 : IsGraphResponse hT μ W1 b1 R1)
    (hC0 : ContDiffAt ℝ 2 R0 0) (hC1 : ContDiffAt ℝ 2 R1 0)
    (hFirst : ∀ (g : ℝ → ℝ) (hg : SmoothTemporalTest T g),
      rawFirst b0 R0 (restrictInput T g hg.1.continuous) (endTime T hT) =
      rawFirst b1 R1 (restrictInput T g hg.1.continuous) (endTime T hT))
    (hMixed : ∀ (g h : ℝ → ℝ) (hg : SmoothTemporalTest T g) (hh : SmoothTemporalTest T h),
      rawMixed b0 R0 (restrictInput T g hg.1.continuous) (restrictInput T h hh.1.continuous)
          (endTime T hT) =
      rawMixed b1 R1 (restrictInput T g hg.1.continuous) (restrictInput T h hh.1.continuous)
          (endTime T hT)) :
    ∃ (S0 : OrientedRealization μ W0 b0) (S1 : OrientedRealization μ W1 b1)
        (e : Fin (m + 1) ≃ Fin (n + 1)),
      m = n ∧ e 0 = 0 ∧ (∀ i, S1.rates (e i) = S0.rates i) ∧
      (∀ i, C145.Pulse.modalOverlap S1.Q b1 (e i) =
        C145.Pulse.modalOverlap S0.Q b0 i) ∧
      S0.c = S1.c ∧ (∑ v, b0 v) = (∑ v, b1 v) ∧
      ∃ π : Fin (m + 1) ≃ Fin (n + 1),
        (∀ v i, S1.Q (π v) (e i) = S0.Q v i) ∧
        (∀ v u, generator μ W1 (π v) (π u) = generator μ W0 v u) ∧
        (∀ v, b1 (π v) = b0 v) ∧
        (∀ v u, laplacian W1 (π v) (π u) = laplacian W0 v u) := by
  let S0 := sourceOrientedRealization μ hμ W0 hs0 hn0 hc0 b0 hcyc0
  have hq0 : ((m + 1 : ℕ) + 2 : ℝ) *
      jointBetaSq (fun i : Fin m => C145.Pulse.modalOverlap S0.Q b0 i.succ)
        (fun i => (S0.rates i.succ-ell) / (u-ell)) (ell / (u-ell)) < delta ^ 2 := hq
  obtain ⟨S1⟩ := connected_cyclic_graph_has_oriented_spectral_realization
    μ hμ W1 hs1 hn1 hc1 b1 hcyc1
  have hBounds := orientedRealization_decayBand S0 ell u hSpectrum
  obtain ⟨e, hmn, he0, hr, ha, hc, hb, π, _, hQ, hA, hport, hL⟩ :=
    ordinary_C2_jets_determine_theoremC_spectral_model
      hT μ S0.c S1.c hμ S0.Q S1.Q S0.rates b0 S1.rates b1
      S0.orthonormal S1.orthonormal S0.ground S1.ground S0.simple S1.simple
      S0.ground_rate S1.ground_rate S0.higher S1.higher
      S0.positive_overlap S1.positive_overlap
      (generator μ W0) S0.eigenvectors
      ell u hw hband (fun i => (hBounds i).1) (fun i => (hBounds i).2)
      delta hd hsep hq0 R0 R1
      (S0.actualResponse hT R0 hR0) (S1.actualResponse hT R1 hR1)
      hC0 hC1 hFirst hMixed
  refine ⟨S0, S1, e, hmn, he0, hr, ha, hc, hb, π, hQ, ?_, hport, ?_⟩
  · simpa only [S0.original_generator, S1.original_generator] using hA
  · simpa only [S0.original_laplacian, S1.original_laplacian] using hL

end C145DRE8

end
