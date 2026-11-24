/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section8Truncation
import LeanPool.GraphMinor.GM16.MetricPoints

/-!
# Lifting a rearrangement in Graph Minors XVI

Deleting vertices lowers the tangle order. In Claim (4) of the proof of (8.3),
the rearranged tangle is truncated once more so that the lost order is exactly
`4λ' + 2`. Lifting the span and comparing the two cutoffs gives the required
rearrangement in the original graph.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe u v w
variable {S : Type w} [TopologicalSpace S] [T2Space S]

/-- Graph Minors XVI, proof of (8.3), Claim (3), pages 65–66.
Once the order bound and absence of long paths have been checked, failure to
be level supplies a rearrangement with a long path near its centre. -/
theorem theorem_8_3_claim_3 {α : Type u} {β : Type v}
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {θ_star θ lam ψ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    (hSpan : IsSigmaSpan G H η θ_star θ T_star T) (hMet : HasTangleMetric H θ T d)
    (horder : 4 * lam + 2 * ψ + 2 ≤ θ)
    (hnotstep : ¬ IsMuSteppedSpan G H η d (2 * ψ))
    (hnotlevel : ¬ IsLevelSpan G H η θ_star θ lam (2 * ψ) T_star T d) :
    ∃ (H' : Drawing S) (η' : SpanEmbedding H' G)
      (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d' : Set S → Set S → ℕ) (z : Set S) (P : Graph α β) (s t : S),
      IsRearrangedWithin G H H' η η' θ_star θ lam T_star T T' d d' z ∧
      IsMuStepped G H' η' d' (2 * ψ) P s t ∧
      pointAtomDist H d s z ≤ lam ∧ pointAtomDist H d t z ≤ lam := by
  classical
  by_contra hn
  apply hnotlevel
  refine ⟨hSpan, hMet, horder, hnotstep, ?_⟩
  intro H' η' T' d' z hRearr P s t hStep hnear
  exact hn ⟨H', η', T', d', z, P, s, t, hRearr, hStep, hnear⟩

/-- Graph Minors XVI, proof of (8.3), Claim (4), page 66, lifting and
rearrangement part. The inequalities are those satisfied by the paper's
choice `λ + |Z|/4 ≤ λ' < λ + |Z|/4 + 1`. -/
theorem theorem_8_3_claim_4 {α : Type u} {β : Type v}
    {G : Graph α β} {H H' : Drawing S} {η : SpanEmbedding H G}
    {θ_star θ lam lam' : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d'' : Set S → Set S → ℕ} {z : Set S}
    (hSpan : IsSigmaSpan G H η θ_star θ T_star T)
    (hMet : HasTangleMetric H θ T d) {Z : Set α}
    (hZsub : Z ⊆ V(G)) (hZdisj : Disjoint V(η.imageGraph) Z)
    (η' : SpanEmbedding H' (GM09.deleteVertices G Z))
    (h : IsRearrangedWithin (GM09.deleteVertices G Z) H H'
      (restrictDeleteVertices η Z hZdisj) η' (θ_star - Z.ncard) (θ - Z.ncard) lam
      (deleteGraphVerticesTangle G hSpan.isControlling.isTangle_star.finite_V
        hSpan.isControlling.isTangle_star.finite_E Z T_star θ_star)
      (GM10.truncation T (θ - Z.ncard)) T''
      (fun a b => min (d a b) (θ - Z.ncard)) d'' z)
    (hlam : lam ≤ lam') (hgap : lam' < θ - Z.ncard)
    (hbudget : Z.ncard + (4 * lam + 2) ≤ 4 * lam' + 2)
    (hpos : 4 * lam' + 2 < θ) :
    IsRearrangedWithin G H H' η (liftSpanEmbedding η' (G.induce_le sdiff_subset))
      θ_star θ lam' T_star T (GM10.truncation T'' (θ - (4 * lam' + 2)))
      d (fun a b => min (d'' a b) (θ - (4 * lam' + 2))) z := by
  have hnewpos : 1 ≤ θ - (4 * lam' + 2) := by omega
  have hle : θ - (4 * lam' + 2) ≤ (θ - Z.ncard) - (4 * lam + 2) := by omega
  have hZlt : Z.ncard < θ_star := by
    have hθ := hSpan.isControlling.theta_le
    omega
  have hnewSpan := IsSigmaSpan.truncation h.isSpan' hnewpos hle
  have hnewMet := HasTangleMetric.truncation h.isCompression.hasMetric' hnewpos hle
  refine ⟨h.z_mem, hSpan, ?_, ?_, ?_, ?_, ?_⟩
  · exact theorem_7_4_proof G θ_star (θ - (4 * lam' + 2)) T_star
      hSpan.isControlling.isTangle_star Z H' η'
      (GM10.truncation T'' (θ - (4 * lam' + 2))) hZsub hZlt hnewSpan
  · intro a ha hfar
    exact h.atom_mem a ha (lt_min (hlam.trans_lt hfar) (hlam.trans_lt hgap))
  · intro v hv hfar
    exact h.vMap_eq v hv (lt_min (hlam.trans_lt hfar) (hlam.trans_lt hgap))
  · intro e he hfar
    exact h.eMap_eq e he (lt_min (hlam.trans_lt hfar) (hlam.trans_lt hgap))
  · refine ⟨hpos, hMet, hnewMet, ?_⟩
    intro x y
    have hbound := h.isCompression.dist_le x y
    rw [pointDist_min] at hbound ⊢
    have hfull := pointDist_le_order hMet x y
    omega

end GraphMinor.GM16
