/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Cited
public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM15.Defs
public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM12.Section4CliqueLabels
import LeanPool.GraphMinor.GM12.Section4VertexConnections
import LeanPool.GraphMinor.GM12.Section4TerminalIndexing
import LeanPool.GraphMinor.GM12.Section4SpanControl
import LeanPool.GraphMinor.GM12.Section4ExternalPathBranches
import LeanPool.GraphMinor.GM12.Section4SpanBranchBound
import LeanPool.GraphMinor.GM12.Section4Minor
import LeanPool.GraphMinor.GM12.Section2NonemptyEdges
import LeanPool.GraphMinor.Minor.Basic
import Mathlib.Data.Fintype.EquivFin

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# Graph Minors XII (4.4): the branch construction

For at least three clique vertices, carry out XII (4.4), pages
251--252. Index both ends of each external path and partition them
by the oriented clique ends. Apply (3.2), embed its connected
subdrawings into the ambient graph, and absorb each external path
except its terminal edge. The retained edges join the enlarged
branches. Each branch contains two distant prescribed vertices,
so (4.1) excludes an ambient small separation containing it.
The same argument covers three and four vertices as well as the
paper's stated reduction to at least five vertices.
-/

public section

namespace GraphMinor.GM12

open Set Graph Surface Hypergraph GM10 GM14 GM15

universe u

/-- XII (4.4), pages 251--252, for at least three clique vertices,
in the span formulation used by XVI. The statement hypotheses are
only the cited VII (7.5), (5.1), and (5.5). -/
theorem theorem_4_4_span_large
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (p : ℕ) (hp : 3 ≤ p) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ {α β : Type*} (G : Graph α β) (θstar θ : ℕ)
        (Tstar : Set (Hypergraph α β × Hypergraph α β))
        (Γ : Drawing S) (η : SpanEmbedding Γ G)
        (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d : Set S → Set S → ℕ)
        (s r : Fin (p * (p - 1) / 2) → S) (P : Fin (p * (p - 1) / 2) → Graph α β)
        (hCtrl : IsControllingTangle G Γ η θstar θ Tstar T),
      HasTangleMetric Γ θ T d → N ≤ θ →
      (∀ i, s i ∈ Γ.V ∧ r i ∈ Γ.V ∧ s i ≠ r i) →
      Function.Injective s → Function.Injective r → Disjoint (range s) (range r) →
      (∀ x ∈ range s ∪ range r, ∀ y ∈ range s ∪ range r, x ≠ y → N ≤ d {x} {y}) →
      (∀ i, IsHPathWithEnds G η.imageGraph (P i) (η.vMap (s i)) (η.vMap (r i))) →
      Pairwise (fun i j => Disjoint (P i).vertexSet (P j).vertexSet) →
      ControlsMinor (Hypergraph.ofGraph G hCtrl.isTangle_star.finite_V
        hCtrl.isTangle_star.finite_E) θstar Tstar (GM16.completeGraph p) := by
  classical
  let μ := p * (p - 1) / 2
  obtain ⟨K, κ, hKV, hKE, ⟨φ⟩, hloop, hassign, hslots⟩ := exists_oriented_clique_labels hp
  let σ : Fin (2 * μ) ≃ Fin μ × Bool := Fintype.equivOfCardEq (by simp [Nat.mul_comm])
  obtain ⟨N, hN, hpN, hconnect⟩ := exists_threshold_for_vertex_connections hS p (2 * μ)
  refine ⟨N, hN, ?_⟩
  intro α β G θstar θ Tstar Γ η T d s r P hCtrl hm hθ hends hs hr hsr hfar hP hPP
  let ends : Fin μ × Bool → S := fun q => if q.2 then s q.1 else r q.1
  let z : Fin (2 * μ) → S := fun q => ends (σ q)
  let owner : Fin (2 * μ) → Fin p := fun q => κ (σ q)
  have hinjEnds : Function.Injective ends := path_ends_injective s r hs hr hsr
  have hinjz : Function.Injective z := hinjEnds.comp σ.injective
  have hEndsMem : ∀ q, ends q ∈ range s ∪ range r := by
    intro ⟨i, c⟩
    cases c
    · exact Or.inr (mem_range_self i)
    · exact Or.inl (mem_range_self i)
  have hEndsΓ : ∀ q, ends q ∈ Γ.V := by
    intro ⟨i, c⟩
    cases c
    · exact (hends i).2.1
    · exact (hends i).1
  have hzΓ : ∀ q, z q ∈ Γ.V := fun q => hEndsΓ (σ q)
  have hfarz : ∀ i j, i ≠ j → N ≤ d {z i} {z j} :=
    fun i j hij => hfar (z i) (hEndsMem (σ i)) (z j) (hEndsMem (σ j))
      (fun h => hij (hinjz h))
  obtain ⟨D, hD, hDconn, hDdisj, hDclass⟩ :=
    hconnect Γ θ T d z owner hm hθ hzΓ hinjz hfarz
  have hpoint : ∀ q, ends q ∈ (D (κ q)).V := by
    intro q
    have hmem : ends q ∈ edgeEndClass z owner (κ q) :=
      ⟨σ.symm q, by simp only [mem_ofPred_eq, owner, σ.apply_symm_apply],
        by simp only [z, σ.apply_symm_apply]⟩
    exact ((hDclass (κ q)).symm.subset hmem).1
  have hDne : ∀ v, (D v).V.Nonempty := by
    intro v
    obtain ⟨i, j, _, c, e, hic, _⟩ := hslots v (hKV ▸ mem_univ v)
    exact ⟨ends (i, c), hic ▸ hpoint (i, c)⟩
  have hTG := hCtrl.isTangle_star
  obtain ⟨A, hA, hAA, hAV⟩ := exists_embedded_connecting_branches hTG.finite_V hTG.finite_E
    η D hD hDne hDconn hDdisj
  have hAF : ∀ v, (A v).vertexSet ⊆ η.imageGraph.vertexSet := by
    intro v x hx
    obtain ⟨y, hy, rfl⟩ := (hAV v).subset hx
    exact η.bijOn_v.mapsTo ((hD v).1 hy)
  have hsA : ∀ i, η.vMap (s i) ∈ (A (κ (i, true))).vertexSet := by
    intro i
    rw [hAV]
    exact mem_image_of_mem η.vMap (hpoint (i, true))
  have hrA : ∀ i, η.vMap (r i) ∈ (A (κ (i, false))).vertexSet := by
    intro i
    rw [hAV]
    exact mem_image_of_mem η.vMap (hpoint (i, false))
  obtain ⟨C, b, hC, hCC, hAC, hbinj, hjoin⟩ := exists_branches_from_external_paths
    hTG.finite_V hTG.finite_E A hA hAA hAF P
    (fun i => η.vMap (s i)) (fun i => η.vMap (r i))
    (fun i => κ (i, true)) (fun i => κ (i, false)) hP hPP hsA hrA
  have hcontrol : ∀ A' B', (A', B') ∈ Tstar → separationOrder A' B' < p →
      ∀ v : Fin p, ¬ (C v).vertexSet ⊆ A'.vertexSet := by
    intro A' B' hAB horder v
    obtain ⟨i, j, hij, c, e, hic, hje⟩ := hslots v (hKV ▸ mem_univ v)
    have hiD : ends (i, c) ∈ (D v).V := hic ▸ hpoint (i, c)
    have hjD : ends (j, e) ∈ (D v).V := hje ▸ hpoint (j, e)
    have hneq : ends (i, c) ≠ ends (j, e) :=
      fun h => hij (congrArg Prod.fst (hinjEnds h))
    have hdist := hfar _ (hEndsMem (i, c)) _ (hEndsMem (j, e)) hneq
    have htwo : 2 * p ≤ d {ends (i, c)} {ends (j, e)} := by omega
    apply not_subset_small_side_of_embedded_distant_drawing hS η hm hCtrl
      (by omega) (hDconn v) (hD v) hiD hjD htwo
      (fun x hx => (hAC v).vertexSet_subset ((hAV v).symm.subset hx)) hAB horder
  have hcK : ControlsMinor (Hypergraph.ofGraph G hTG.finite_V hTG.finite_E) θstar Tstar K := by
    refine ⟨C, b, fun v _ => hC v, fun v _ w _ hvw => hCC v w hvw, ?_, ?_,
      fun e _ f _ hef heq => hef (hbinj heq), ?_, ?_⟩
    · intro e u v hl huv
      obtain ⟨heG, x, hx, y, hy, hxy⟩ := hjoin e
      rcases hassign e u v hl with ⟨hu, hv⟩ | ⟨hv, hu⟩
      · rw [hu] at hx
        rw [hv] at hy
        exact ⟨heG, ⟨x, hx, hxy.inc_left⟩, y, hy, hxy.inc_right⟩
      · rw [hv] at hx
        rw [hu] at hy
        exact ⟨heG, ⟨y, hy, hxy.inc_right⟩, x, hx, hxy.inc_left⟩
    · intro e v hl
      exact False.elim (hloop e v hl)
    · rw [hKV]
      have hcard : (univ : Set (Fin p)).ncard = p := by simp
      rw [hcard]
      exact (show p ≤ θ by omega).trans hCtrl.theta_le
    · intro A' B' hAB hord v _
      rw [hKV] at hord
      have hcard : (univ : Set (Fin p)).ncard = p := by simp
      rw [hcard] at hord
      exact hcontrol A' B' hAB hord v
  have hEΓ : Γ.E.Nonempty := edges_nonempty_of_tangle_order_two hm.1.2.1 (by omega)
  obtain ⟨e, _⟩ := hEΓ
  let : Nonempty β := ⟨η.eMap e⟩
  exact controlsMinor_of_iso φ.symm hcK

end GraphMinor.GM12
