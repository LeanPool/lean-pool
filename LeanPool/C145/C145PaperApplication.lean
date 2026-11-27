/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145PaperPositiveWitness
public import LeanPool.C145.C145PaperActualResponse

/-! A proof-checked application of the paper-facing inverse theorem to a
nontrivial normalized source. The source's graph, spectrum, contraction
criterion and local response are proved; only an admissible competitor and
equality of its actual terminal data remain conditional. -/

@[expose] public section

noncomputable section
namespace C145.PaperApplication
open Matrix C145.WeightedGraph C145.CyclicSpectral C145.GraphSpectralRealization
  C145.ActualResponse C145.PaperActualResponse C145.PaperPositiveWitness
open scoped Topology ContDiff

theorem path_three_has_actual_C2_response {T : ℝ} (hT : 0 < T) :
    ∃ R : Input T → C145.ActualResponse.Path 2 T,
      IsGraphResponse hT 10 weights port R ∧ ContDiffAt ℝ 2 R 0 :=
  exists_graph_C2_response hT 10 (by norm_num) weights weights_symmetric
    weights_nonnegative support_connected port port_cyclic

theorem path_three_identified_against_arbitrary_competitor {n : ℕ} {T : ℝ}
    (hT : 0 < T)
    (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hs : W.IsSymm) (hn : ∀ v u, 0 ≤ W v u)
    (hc : (supportGraph W hs).Connected) (b : State n)
    (hcyc : KrylovCyclic (generator 10 W) b)
    (hData : TerminalJetsAgree hT
      port (selectedResponse hT 10 (by norm_num) weights weights_symmetric
        weights_nonnegative support_connected port port_cyclic)
      b (selectedResponse hT 10 (by norm_num) W hs hn hc b hcyc)) :
    2 = n ∧ ∃ π : Fin 3 ≃ Fin (n + 1),
      (∀ v u, generator 10 W (π v) (π u) = generator 10 weights v u) ∧
      (∀ v, b (π v) = port v) ∧
      (∀ v u, laplacian W (π v) (π u) = laplacian weights v u) := by
  exact selected_response_theoremA_graph hT 10 (by norm_num) weights W
    weights_symmetric hs weights_nonnegative hn support_connected hc port b
    port_cyclic hcyc 11 13 (by norm_num) (by norm_num) nonground_decay_band
    delta delta_pos port_separation source_q_lt_one hData

end C145.PaperApplication

end
