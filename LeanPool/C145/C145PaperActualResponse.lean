/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145DRE8OriginalGraphInverse

/-!
The local C2 response is a consequence of the original graph hypotheses, rather
than an additional existence premise of the inverse problem.  Selection below
uses only this proved existence.  Its ordinary measured jets agree with those
of every other actual C2 response of the same graph.

The final application presents Theorem A directly through these terminal jets,
without carrying auxiliary modal realizations in its conclusion.
-/

@[expose] public section

noncomputable section
namespace C145.PaperActualResponse

open Matrix C145.WeightedGraph C145.CyclicSpectral
  C145.GraphSpectralRealization C145.ActualResponse C145.ObservedKernelRecovery
open scoped BigOperators Topology ContDiff

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup
  AddCommGroup.toAddCommMonoid
  NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace
  UniformSpace.toTopologicalSpace

/-- The same path-valued response solves the spectral ODE exactly when it solves
the original vertex-coordinate graph ODE.  In particular the input neighborhood,
initial state, and coordinatewise quadratic reaction are all unchanged. -/
theorem actualResponse_iff_graphResponse {n : ℕ} {T : ℝ} (hT : 0 < T)
    {μ : ℝ} {W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {b : State n}
    (S : OrientedRealization μ W b) (R : Input T → Path n T) :
    IsActualResponse hT S.Q S.rates b R ↔ IsGraphResponse hT μ W b R := by
  unfold IsActualResponse IsGraphResponse vectorField graphVectorField
  rw [S.original_generator]

/-- Proved local C2 existence for the original graph ODE, from an actual
orthonormal spectral realization of its original generator. -/
theorem exists_graph_C2_response_of_realization {n : ℕ} {T : ℝ} (hT : 0 < T)
    {μ : ℝ} {W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {b : State n}
    (S : OrientedRealization μ W b) :
    ∃ R : Input T → Path n T,
      IsGraphResponse hT μ W b R ∧ ContDiffAt ℝ 2 R 0 := by
  obtain ⟨R, hR, hC⟩ := exists_actual_C2_response hT S.Q S.rates b S.orthonormal
  exact ⟨R, (actualResponse_iff_graphResponse hT S R).mp hR, hC⟩

section OriginalGraph

variable {n : ℕ} {T : ℝ} (hT : 0 < T) (μ : ℝ) (hμ : 0 < μ)
  (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
  (hs : W.IsSymm) (hn : ∀ v u, 0 ≤ W v u)
  (hc : (supportGraph W hs).Connected) (b : State n)
  (hcyc : KrylovCyclic (generator μ W) b)

include hμ hs hn hc hcyc in
/-- Every connected symmetric nonnegative graph with positive uniform decay and
a cyclic real port has an actual response germ on every fixed positive horizon,
with C2 dependence on the continuous temporal input. -/
theorem exists_graph_C2_response :
    ∃ R : Input T → Path n T,
      IsGraphResponse hT μ W b R ∧ ContDiffAt ℝ 2 R 0 := by
  obtain ⟨S⟩ := connected_cyclic_graph_has_oriented_spectral_realization
    μ hμ W hs hn hc b hcyc
  exact exists_graph_C2_response_of_realization hT S

/-- A named mathematical response selected from proved original-graph existence.
Only its local input germ is used; no global large-forcing solution is claimed. -/
def selectedResponse : Input T → Path n T :=
  Classical.choose (exists_graph_C2_response hT μ hμ W hs hn hc b hcyc)

/-- The selected response satisfies the actual original graph equation and the
regularity required by the ordinary-jet inverse theorems. -/
theorem selectedResponse_spec :
    IsGraphResponse hT μ W b (selectedResponse hT μ hμ W hs hn hc b hcyc) ∧
      ContDiffAt ℝ 2 (selectedResponse hT μ hμ W hs hn hc b hcyc) 0 :=
  Classical.choose_spec (exists_graph_C2_response hT μ hμ W hs hn hc b hcyc)

/-- The selected response's ordinary derivatives are the accepted exact first
and half-second variations.  The realization is arbitrary, so selection does
not impose a preferred modal frame on the physical experiment. -/
theorem selectedResponse_variations (S : OrientedRealization μ W b)
    (g h : Input T) (t : Time T) :
    rawFirst b (selectedResponse hT μ hμ W hs hn hc b hcyc) g t =
        observe b (firstState hT S.Q S.rates b g t) ∧
      rawMixed b (selectedResponse hT μ hμ W hs hn hc b hcyc) g h t =
        observe b (secondState hT S.Q S.rates b g h t) ∧
      rawQuadratic b (selectedResponse hT μ hμ W hs hn hc b hcyc) g t =
        observe b (secondState hT S.Q S.rates b g g t) := by
  have hspec := selectedResponse_spec hT μ hμ W hs hn hc b hcyc
  exact actual_response_variations hT S.Q S.rates b S.orthonormal
    (selectedResponse hT μ hμ W hs hn hc b hcyc)
    (S.actualResponse hT _ hspec.1) hspec.2 g h t

/-- The named response supplies the same measured jets as any actual C2
response of this graph.  Hence arbitrary behavior of a chosen representative
away from zero input cannot affect the data used in the application below. -/
theorem measured_jets_eq_selectedResponse (R : Input T → Path n T)
    (hR : IsGraphResponse hT μ W b R) (hC : ContDiffAt ℝ 2 R 0)
    (g h : Input T) (t : Time T) :
    rawFirst b R g t = rawFirst b (selectedResponse hT μ hμ W hs hn hc b hcyc) g t ∧
      rawMixed b R g h t =
        rawMixed b (selectedResponse hT μ hμ W hs hn hc b hcyc) g h t ∧
      rawQuadratic b R g t =
        rawQuadratic b (selectedResponse hT μ hμ W hs hn hc b hcyc) g t := by
  obtain ⟨S⟩ := connected_cyclic_graph_has_oriented_spectral_realization
    μ hμ W hs hn hc b hcyc
  have hmeas := actual_response_variations hT S.Q S.rates b S.orthonormal
    R (S.actualResponse hT R hR) hC g h t
  have hsel := selectedResponse_variations hT μ hμ W hs hn hc b hcyc S g h t
  exact ⟨hmeas.1.trans hsel.1.symm, hmeas.2.1.trans hsel.2.1.symm,
    hmeas.2.2.trans hsel.2.2.symm⟩

end OriginalGraph

/-- Equality of the exact first and half-mixed-second terminal derivatives in
all smooth temporal directions on the one fixed horizon.  This is a predicate
on actual observed derivatives, not a target graph-identification certificate. -/
def TerminalJetsAgree {m n : ℕ} {T : ℝ} (hT : 0 < T)
    (b0 : State m) (R0 : Input T → Path m T)
    (b1 : State n) (R1 : Input T → Path n T) : Prop :=
  (∀ (g : ℝ → ℝ) (hg : SmoothTemporalTest T g),
    rawFirst b0 R0 (restrictInput T g hg.1.continuous) (endTime T hT) =
      rawFirst b1 R1 (restrictInput T g hg.1.continuous) (endTime T hT)) ∧
  (∀ (g h : ℝ → ℝ) (hg : SmoothTemporalTest T g) (hh : SmoothTemporalTest T h),
    rawMixed b0 R0 (restrictInput T g hg.1.continuous) (restrictInput T h hh.1.continuous)
        (endTime T hT) =
      rawMixed b1 R1 (restrictInput T g hg.1.continuous) (restrictInput T h hh.1.continuous)
        (endTime T hT))

/-- Theorem A as an application to the two original graphs' named measured
responses.  Existence and C2 regularity are derived above, so callers provide
only graph hypotheses, the source criterion, and equality of measured data.
The same vertex bijection identifies the original generator, signed port, and
Laplacian; the competitor's size and topology are initially unrestricted. -/
theorem selected_response_theoremA_graph {m n : ℕ} {T : ℝ}
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
    (hSpectrum : C145DRE8.NonGroundDecayBand μ W0 ell u)
    (delta : ℝ) (hd : 0 < delta)
    (hsep : ∀ j k, j ≠ k → delta ^ 2 ≤ (b0 j - b0 k) ^ 2)
    (hq : C145DRE8.sourceQChebyshevSq b0 ell u delta < 1)
    (hData : TerminalJetsAgree hT
      b0 (selectedResponse hT μ hμ W0 hs0 hn0 hc0 b0 hcyc0)
      b1 (selectedResponse hT μ hμ W1 hs1 hn1 hc1 b1 hcyc1)) :
    m = n ∧ ∃ π : Fin (m + 1) ≃ Fin (n + 1),
      (∀ v u, generator μ W1 (π v) (π u) = generator μ W0 v u) ∧
      (∀ v, b1 (π v) = b0 v) ∧
      (∀ v u, laplacian W1 (π v) (π u) = laplacian W0 v u) := by
  have hspec0 := selectedResponse_spec hT μ hμ W0 hs0 hn0 hc0 b0 hcyc0
  have hspec1 := selectedResponse_spec hT μ hμ W1 hs1 hn1 hc1 b1 hcyc1
  obtain ⟨S0, S1, e, hmn, he0, hr, ha, hc, hb, π, hQ, hA, hport, hL⟩ :=
    C145DRE8.ordinary_C2_jets_determine_theoremA_graph hT μ hμ W0 W1
      hs0 hs1 hn0 hn1 hc0 hc1 b0 b1 hcyc0 hcyc1
      ell u hw hband hSpectrum delta hd hsep hq
      (selectedResponse hT μ hμ W0 hs0 hn0 hc0 b0 hcyc0)
      (selectedResponse hT μ hμ W1 hs1 hn1 hc1 b1 hcyc1)
      hspec0.1 hspec1.1 hspec0.2 hspec1.2 hData.1 hData.2
  exact ⟨hmn, π, hA, hport, hL⟩


end C145.PaperActualResponse
end

end
