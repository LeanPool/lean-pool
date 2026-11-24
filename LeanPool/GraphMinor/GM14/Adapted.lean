/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
public import LeanPool.GraphMinor.GM14.Cited
public import LeanPool.GraphMinor.GM14.Section6a
public import LeanPool.GraphMinor.GM14.Section7a
public import LeanPool.GraphMinor.GM16.Battlefields

/-!
# Graph Minors XIV: Adapted and Open Local Steps

This file states as closed `Prop`s:
1. Result `(8.1)` (`Theorem81Statement`, page 40) of N. Robertson and P. D. Seymour,
   *Graph Minors. XIV. Extending an embedding*, J. Combin. Theory Ser. B **65** (1995) 23–50, which
   the paper introduces with:
   "The proof of [3, theorem (11.11)] may easily be adapted to yield the following."
2. The remaining local topological/drawing gluing step in Section 10, kept as an explicit
   closed `...Statement : Prop` definition outside `Cited.lean`.
-/

@[expose] public section

namespace GraphMinor.GM14

open Set Function Topology Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09
  GraphMinor.GM10 GraphMinor.GM11 Hypergraph

universe u v w

/-! ## Result (8.1) (adapted from Graph Minors IX, (11.11)) -/

/-- Statement of Graph Minors XIV, (8.1) (page 40), whose proof adapts the proof of Graph Minors IX,
(11.11):
"A society $(G, \Omega)$ has no cross if and only if there is a 3-segregation $\mathscr{S}$
of $G$ with $\bar{\Omega} \subseteq V(\mathscr{S})$ and an arrangement $\alpha$ of
$\mathscr{S}$ in a closed disc $\Delta$ with $\Omega = \alpha^{-1}(bd(\Delta))$." -/
def Theorem81Statement : Prop :=
  ∀ {D : Type w} [TopologicalSpace D] [T2Space D] {α : Type u} {β : Type v}
    (S : Society α β),
    IsSurface D → Nonempty (D ≃ₜ ClosedUnitDisc) →
    ((∀ P_set : Set (Graph α β), S.IsCrookedTransaction P_set → P_set.ncard ≠ 2) ↔
      ∃ (S_seg : Set (Society α β)) (α_disc : Society α β → Set D) (α_pt : α → D),
        IsThreeSegregation S.G S_seg ∧
        S.Ω.bar ⊆ segregationVertices S_seg ∧
        IsSurfaceArrangement S_seg α_disc α_pt ∧
        IsPullbackPerm S_seg α_pt (bd D) S.Ω)

/-! ## Section 10 Local Translation Step -/

/-- Local translation between representativity `≥ 209` on a non-spherical closed surface `S` for a
subdivision `H` of a simple 3-connected graph inside a 4-connected graph `G` and the tangle-metric /
zone / 3-segregation conditions of `(4.1)` in the proof of Graph Minors XIV, (1.1)
(pages 24–25, 30–31). -/
def Theorem11TranslationStatement : Prop :=
  ∀ {S : Type u} [TopologicalSpace S] [T2Space S] {α : Type v} {β : Type w}
    (_hS : IsClosedSurface S) (_hConn : ConnectedSpace S) (_hnot_sphere : ¬ IsSphere S)
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G),
    V(G).Finite → E(G).Finite →
    (5 ≤ V(G).ncard ∧
      ∀ G₁ G₂ : Graph α β, IsGraphSeparation G G₁ G₂ →
        (V(G₁) ∩ V(G₂)).ncard < 4 → V(G₁) = V(G) ∨ V(G₂) = V(G)) →
    IsSubdivisionOfSimpleThreeConnected η.imageGraph →
    H.IsRepresentative 209 →
    ∃ (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d : Set S → Set S → ℕ),
      H.IsTwoCell ∧ IsRigid H ∧
      IsRespectfulDrawingTangle H 209 T ∧ HasTangleMetric H 209 T d ∧
      (∀ (P : Graph α β) (u v : S),
        u ∈ H.V → v ∈ H.V →
        IsHPathWithEnds G η.imageGraph P (η.vMap u) (η.vMap v) →
        ¬ (d {u} {v} < 12) →
        ∃ (P_G : Graph α β) (u_H v_H : S),
          u_H ∈ H.V ∧ v_H ∈ H.V ∧
          IsHPathWithEnds G η.imageGraph P_G (η.vMap u_H) (η.vMap v_H) ∧
          ¬ ∃ φ : C(Circle, S),
            (range φ ∩ H.U).encard ≤ 3 ∧ u_H ∈ curveIns φ ∧ v_H ∈ curveIns φ) ∧
      (∀ (Λ : Set S)
        (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d' : Set S → Set S → ℕ)
        (η_cl : SpanEmbedding (clearedSubdrawing H Λ) G),
        IsLambdaZone H d 39 Λ →
        IsRigid (clearedSubdrawing H Λ) →
        IsClearedTangle H T d 209 39 Λ T' d' →
        (∀ v ∈ (clearedSubdrawing H Λ).V, η_cl.vMap v = η.vMap v) →
        IsDrawingEye G (clearedSubdrawing H Λ) η_cl (209 - 158) T' Λ →
        ∃ (C : Drawing S) (Λ₀ : Set S) (x : S) (a b c d_v : S) (P₁ P₂ : Graph α β),
          C.IsCircuit ∧ C.IsSubdrawing H ∧ IsOpenDisc Λ₀ ∧ subBd Λ₀ = C.U ∧ x ∈ Λ₀ ∧
          a ∈ C.V ∧ b ∈ C.V ∧ c ∈ C.V ∧ d_v ∈ C.V ∧
          OccurInCircuitOrder C a b c d_v ∧
          IsSubdivisionOfSimpleThreeConnected (clearedSubdrawing H Λ₀).toGraph ∧
          (∀ y ∈ Λ₀, ∃ φ : C(Circle, S),
            (range φ ∩ H.U).encard ≤ 39 ∧ x ∈ curveIns φ ∧ y ∈ curveIns φ) ∧
          (∀ Δ : Set S, IsClosedDisc Δ → ({a, b, c, d_v} : Set S) ⊆ Δ →
            4 ≤ ((subBd Δ \ Λ₀) ∩ H.U).encard) ∧
          Disjoint V(P₁) V(P₂) ∧
          IsGraphPathWithEnds G P₁ (η.vMap a) (η.vMap c) ∧
          IsGraphPathWithEnds G P₂ (η.vMap b) (η.vMap d_v)) ∧
      ((∃ (S_seg : Set (Society α β)) (α_disc : Society α β → Set S) (α_pt : α → S),
          IsThreeSegregation G S_seg ∧ IsTangleLocal G H η T S_seg ∧
          IsSurfaceArrangement S_seg α_disc α_pt ∧ IsCompatibleWith G H η S_seg α_disc α_pt) →
        ∃ (Γ_G : GraphDrawing G S), H.IsSubdrawing Γ_G.drawing)

end GraphMinor.GM14
