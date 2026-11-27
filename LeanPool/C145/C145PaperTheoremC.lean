/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145PaperResidualInvariance
public import LeanPool.C145.C145PaperRealizationInvariance
public import LeanPool.C145.C145PaperActualResponse
public import LeanPool.C145.C145DRE8JointOriginalGraph

/-! Theorem C's criterion is independent of the chosen oriented eigenbasis.
The application accepts the displayed square-root criterion computed in ANY
actual source realization, including the manuscript's increasing-rate basis.
No all-realizations criterion, response-existence premise or reconstruction
certificate is required. -/

@[expose] public section

noncomputable section
namespace C145.PaperTheoremC
open Matrix C145.WeightedGraph C145.CyclicSpectral
  C145.GraphSpectralRealization C145.ActualResponse
  C145.PaperActualResponse C145DRE8
open scoped BigOperators Topology ContDiff

theorem realization_kappa_eq {m : ℕ} {μ : ℝ}
    {W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} {b : State m}
    (S0 S1 : OrientedRealization μ W b) (ell u : ℝ) (k : ℕ) :
    kappa (fun i : Fin m => C145.Pulse.modalOverlap S0.Q b i.succ)
      (fun i => (S0.rates i.succ-ell) / (u-ell)) k =
    kappa (fun i : Fin m => C145.Pulse.modalOverlap S1.Q b i.succ)
      (fun i => (S1.rates i.succ-ell) / (u-ell)) k := by
  obtain ⟨e, p, he0, hp, hr, hQ, ha, hrN, hQN, haN, hc⟩ :=
    C145.PaperRealizationInvariance.realizations_full_and_nonground_equivalent S0 S1
  apply kappa_eq_of_reindex p
  · intro i; exact (haN i).symm
  · intro i; rw [hrN]

theorem realization_jointBetaSq_eq {m : ℕ} {μ : ℝ}
    {W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} {b : State m}
    (S0 S1 : OrientedRealization μ W b) (ell u : ℝ) :
    jointBetaSq (fun i : Fin m => C145.Pulse.modalOverlap S0.Q b i.succ)
      (fun i => (S0.rates i.succ-ell) / (u-ell)) (ell / (u-ell)) =
    jointBetaSq (fun i : Fin m => C145.Pulse.modalOverlap S1.Q b i.succ)
      (fun i => (S1.rates i.succ-ell) / (u-ell)) (ell / (u-ell)) := by
  obtain ⟨e, p, he0, hp, hr, hQ, ha, hrN, hQN, haN, hc⟩ :=
    C145.PaperRealizationInvariance.realizations_full_and_nonground_equivalent S0 S1
  apply jointBetaSq_eq_of_reindex p
  · intro i; exact (haN i).symm
  · intro i; rw [hrN]

theorem realization_jointBetaNorm_eq {m : ℕ} {μ : ℝ}
    {W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} {b : State m}
    (S0 S1 : OrientedRealization μ W b) (ell u : ℝ) :
    jointBetaNorm (fun i : Fin m => C145.Pulse.modalOverlap S0.Q b i.succ)
      (fun i => (S0.rates i.succ-ell) / (u-ell)) (ell / (u-ell)) =
    jointBetaNorm (fun i : Fin m => C145.Pulse.modalOverlap S1.Q b i.succ)
      (fun i => (S1.rates i.succ-ell) / (u-ell)) (ell / (u-ell)) := by
  unfold jointBetaNorm
  rw [realization_jointBetaSq_eq S0 S1 ell u]

/-- The original graph criterion's chosen realization may be replaced by any
genuine oriented realization; the value itself, not just its sign, is equal. -/
theorem originalSourceJointBetaSq_eq_realization {m : ℕ}
    (μ : ℝ) (hμ : 0 < μ)
    (W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hs : W.IsSymm) (hn : ∀ v u, 0 ≤ W v u)
    (hc : (supportGraph W hs).Connected) (b : State m)
    (hcyc : KrylovCyclic (generator μ W) b)
    (S : OrientedRealization μ W b) (ell u : ℝ) :
    originalSourceJointBetaSq μ hμ W hs hn hc b hcyc ell u =
      jointBetaSq (fun i : Fin m => C145.Pulse.modalOverlap S.Q b i.succ)
        (fun i => (S.rates i.succ-ell) / (u-ell)) (ell / (u-ell)) := by
  exact realization_jointBetaSq_eq
    (sourceOrientedRealization μ hμ W hs hn hc b hcyc) S ell u

/-- The displayed paper criterion and the existing graph theorem's squared
criterion agree for every genuine oriented source basis. -/
theorem displayed_criterion_iff_original {m : ℕ}
    (μ : ℝ) (hμ : 0 < μ)
    (W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hs : W.IsSymm) (hn : ∀ v u, 0 ≤ W v u)
    (hc : (supportGraph W hs).Connected) (b : State m)
    (hcyc : KrylovCyclic (generator μ W) b)
    (S : OrientedRealization μ W b) (ell u delta : ℝ) (hd : 0 < delta) :
    (Real.sqrt ((m + 1 : ℕ) + 2) *
      jointBetaNorm (fun i : Fin m => C145.Pulse.modalOverlap S.Q b i.succ)
        (fun i => (S.rates i.succ-ell) / (u-ell)) (ell / (u-ell)) / delta < 1) ↔
      ((m + 1 : ℕ) + 2 : ℝ) *
        originalSourceJointBetaSq μ hμ W hs hn hc b hcyc ell u < delta ^ 2 := by
  rw [originalSourceJointBetaSq_eq_realization μ hμ W hs hn hc b hcyc S ell u]
  exact joint_qH_lt_one_iff_sq (m + 1) _ _ _ delta hd

/-- Theorem C on original graphs, their proved actual response jets, and the
paper's literal q_H computed in any oriented source eigenbasis. -/
theorem selected_response_theoremC_graph {m n : ℕ} {T : ℝ}
    (hT : 0 < T) (μ : ℝ) (hμ : 0 < μ)
    (W0 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (W1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hs0 : W0.IsSymm) (hs1 : W1.IsSymm)
    (hn0 : ∀ v u, 0 ≤ W0 v u) (hn1 : ∀ v u, 0 ≤ W1 v u)
    (hc0 : (supportGraph W0 hs0).Connected) (hc1 : (supportGraph W1 hs1).Connected)
    (b0 : State m) (b1 : State n)
    (hcyc0 : KrylovCyclic (generator μ W0) b0)
    (hcyc1 : KrylovCyclic (generator μ W1) b1)
    (S : OrientedRealization μ W0 b0)
    (ell u : ℝ) (hw : ell < u) (hband : u < 2 * ell)
    (hSpectrum : NonGroundDecayBand μ W0 ell u)
    (delta : ℝ) (hd : 0 < delta)
    (hsep : ∀ j k, j ≠ k → delta ^ 2 ≤
      signatureSq (physicalKrylov (generator μ W0) b0 ell (u - ell)) j k)
    (hq : Real.sqrt ((m + 1 : ℕ) + 2) *
      jointBetaNorm (fun i : Fin m => C145.Pulse.modalOverlap S.Q b0 i.succ)
        (fun i => (S.rates i.succ-ell) / (u-ell)) (ell / (u-ell)) / delta < 1)
    (hData : TerminalJetsAgree hT
      b0 (selectedResponse hT μ hμ W0 hs0 hn0 hc0 b0 hcyc0)
      b1 (selectedResponse hT μ hμ W1 hs1 hn1 hc1 b1 hcyc1)) :
    m = n ∧ ∃ π : Fin (m + 1) ≃ Fin (n + 1),
      (∀ v u, generator μ W1 (π v) (π u) = generator μ W0 v u) ∧
      (∀ v, b1 (π v) = b0 v) ∧
      (∀ v u, laplacian W1 (π v) (π u) = laplacian W0 v u) := by
  have hqSq := (displayed_criterion_iff_original μ hμ W0 hs0 hn0 hc0 b0 hcyc0
    S ell u delta hd).mp hq
  have hspec0 := selectedResponse_spec hT μ hμ W0 hs0 hn0 hc0 b0 hcyc0
  have hspec1 := selectedResponse_spec hT μ hμ W1 hs1 hn1 hc1 b1 hcyc1
  obtain ⟨S0, S1, e, hmn, he0, hr, ha, hc, hb, π, hQ, hA, hport, hL⟩ :=
    ordinary_C2_jets_determine_theoremC_graph hT μ hμ W0 W1 hs0 hs1 hn0 hn1 hc0 hc1
      b0 b1 hcyc0 hcyc1 ell u hw hband hSpectrum delta hd hsep hqSq
      (selectedResponse hT μ hμ W0 hs0 hn0 hc0 b0 hcyc0)
      (selectedResponse hT μ hμ W1 hs1 hn1 hc1 b1 hcyc1)
      hspec0.1 hspec1.1 hspec0.2 hspec1.2 hData.1 hData.2
  exact ⟨hmn, π, hA, hport, hL⟩

end C145.PaperTheoremC

end
