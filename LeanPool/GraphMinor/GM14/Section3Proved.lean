/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Section3
import LeanPool.GraphMinor.GM12.Section710

/-!
# Graph Minors XIV, (3.2)

Apply the proved XII (7.10) to the subdrawing obtained by clearing the zone.
The preliminary clearing lemmas stay in Section3, since XII uses them too.
-/

public section

namespace GraphMinor.GM14

open Set Topology Graph GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T1Space S]

/-- Graph Minors XIV, (3.2) (page 28):
"If $\theta \ge 4\lambda + 3$ then there is a unique tangle of order $\theta - 4\lambda - 2$
obtained by clearing $\Lambda$."
Follows from Graph Minors XII, (7.10) (`GM12Theorem710Statement`). -/
theorem theorem_3_2_of_710
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {H : Drawing S} {θ lam : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {z Λ : Set S}
    (hθ : 4 * lam + 3 ≤ θ)
    (hMetric : HasTangleMetric H θ T d)
    (hZone : IsLambdaZoneAround H d lam z Λ) :
    ∃ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d' : Set S → Set S → ℕ),
      IsClearedTangle H T d θ lam Λ T' d' ∧
      ∀ (T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d'' : Set S → Set S → ℕ),
        IsClearedTangle H T d θ lam Λ T'' d'' → T'' = T' := by
  have : T2Space S := hS.2.1
  have hSub : (clearedSubdrawing H Λ).IsSubdrawing H := clearedSubdrawing_isSubdrawing H Λ
  have h2cell' : (PaintingOrDrawing.drawing (clearedSubdrawing H Λ)).IsTwoCell :=
    clearedSubdrawing_isTwoCell hMetric.1.1 hZone
  have hEdist : ∀ e ∈ H.E \ (clearedSubdrawing H Λ).E, d z e ≤ lam := by
    rintro e ⟨heH, henot⟩
    rcases edge_subset_or_subset_compl_of_zone hZone heH with heΛ | hec
    · exact hZone.dist_le e (Or.inl (Or.inr heH)) (heΛ.trans subset_closure)
    · exfalso
      apply henot
      change e ∈ (H.span _ _).E
      rw [H.span_E]
      exact ⟨⟨heH, hec⟩, heH⟩
  have hEdge2 : z ∈ H.E \ (clearedSubdrawing H Λ).E → 2 ≤ lam :=
    fun hz => hZone.two_le_of_edge hz.1
  obtain ⟨T', d', ⟨hM', hMem', hDist'⟩, hUniq⟩ :=
    GraphMinor.GM12.gm14_theorem_7_10.{u} S hS hConn H (clearedSubdrawing H Λ) θ lam T d z
      hθ hMetric hZone.z_mem hSub h2cell' hEdist hEdge2
  refine ⟨T', d', ⟨hM', hMem', hDist'⟩, fun T'' d'' hC'' => ?_⟩
  exact hUniq T'' d'' hC''.hasMetric fun a ha b hb a' ha' b' hb' haa' hbb' =>
    (hC''.dist_bounds a ha b hb a' ha' b' hb' haa' hbb').1

end GraphMinor.GM14
