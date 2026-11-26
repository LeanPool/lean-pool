/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section8Rearrangement
import LeanPool.GraphMinor.GM16.DrawingAtoms
import LeanPool.GraphMinor.GM16.DrawingConnected
import LeanPool.GraphMinor.GM16.SpanPaths
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM16.MetricPoints
import LeanPool.GraphMinor.GM11.NiceStatements

/-!
# Paths meeting the old span

For XVI (8.3), Claim (5), choose a shortest path in the new drawing to the old
span. Its last edge cannot be far from the rearrangement centre, since that
edge would then be an unchanged old edge. A surviving end supplies the common
vertex needed to start this shortest-path argument.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe u v w
variable {S : Type w} [TopologicalSpace S] [T2Space S]

/-- Graph Minors XVI, proof of (8.3), Claim (5), page 66.
Given a common vertex, every new vertex has a path in the new span to the old
span, meeting it just at an end at distance at most `λ + 2` from the centre. -/
theorem theorem_8_3_claim_5 (hS : IsClosedSurface S)
    {α : Type u} {β : Type v} {G : Graph α β} {H H' : Drawing S}
    {η : SpanEmbedding H G} {η' : SpanEmbedding H' G} {θ_star θ lam : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {z : Set S}
    (h : IsRearrangedWithin G H H' η η' θ_star θ lam T_star T T' d d' z)
    (hsymm : ∀ a ∈ H.A, ∀ b ∈ H.A, d a b = d b a)
    (htri : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A,
      d a c ≤ d a b + d b c)
    (hprox : ∀ x ∈ H.V, ∀ a ∈ H.A, x ∈ closure a → d {x} a ≤ 2)
    (hcommon : (V(η.imageGraph) ∩ V(η'.imageGraph)).Nonempty)
    {w : α} (hw : w ∈ V(η'.imageGraph)) (hwnot : w ∉ V(η.imageGraph)) :
    ∃ (Q : Graph α β) (x : S), x ∈ H.V ∧
      Q ≤ η'.imageGraph ∧ IsGraphPathWithEnds G Q w (η.vMap x) ∧
      V(Q) ∩ V(η.imageGraph) = {η.vMap x} ∧ d z {x} ≤ lam + 2 := by
  obtain ⟨a, ha, haw⟩ := η'.bijOn_v.surjOn hw
  obtain ⟨q, hq, hq'⟩ := hcommon
  obtain ⟨b, hb, hbq⟩ := η'.bijOn_v.surjOn hq'
  obtain ⟨W⟩ := drawing_walk_of_twoCell hS h.isSpan'.isRespectful.1 ha hb
  have W' : GraphWalk η'.imageGraph w q := by
    simpa only [haw, hbq] using mapSpanWalk η' W
  obtain ⟨w', hw', y, hy, Q, _, _, hQ, _, hinter⟩ :=
    exists_isFromToPathWithEnds_of_walk W' (show w ∈ ({w} : Set α) from mem_singleton w) hq
  rw [mem_singleton_iff] at hw'
  subst w'
  obtain ⟨x, hx, hxy⟩ := η.bijOn_v.surjOn hy
  have hQle : Q ≤ η'.imageGraph := hQ.1
  refine ⟨Q, x, hx, hQle, ?_, ?_, ?_⟩
  · rw [hxy]
    exact hQ.mono η'.imageGraph_le
  · rwa [hxy]
  · by_contra hfar
    have hfar' : lam + 3 ≤ d z {x} := by omega
    have hxkeep := h.vMap_eq x hx (by omega)
    obtain ⟨_, WQ, hsimple, hVQ, _⟩ := IsGraphPathWithEnds.symm hQ
    cases WQ with
    | nil hv => exact hwnot hy
    | @cons y u w e hlink R =>
      have huy : u ≠ y := by
        intro heq
        have hnot := (List.nodup_cons.mp hsimple).1
        exact hnot (heq ▸ R.start_mem_support)
      have hlinkNew := (hQle.isLink_iff hlink.edge_mem).mp hlink
      obtain ⟨f, hf, hfe⟩ := η'.bijOn_e.surjOn hlinkNew.edge_mem
      have hinc : η'.imageGraph.Inc (η'.eMap f) (η'.vMap x) := by
        rw [hfe, hxkeep.2, hxy]
        exact ⟨u, hlinkNew⟩
      have hxf := (η'.inc_iff f hf x hxkeep.1).mp hinc
      obtain ⟨hfH, hmap⟩ := rearranged_incident_edge_eq hS h hsymm htri hprox hx hf hxf hfar'
      have heOld : e ∈ E(η.imageGraph) := by
        rw [← hfe, hmap]
        exact η.bijOn_e.mapsTo hfH
      have hlinkG := (η'.imageGraph_le.isLink_iff hlinkNew.edge_mem).mp hlinkNew
      have hlinkOld := (η.imageGraph_le.isLink_iff heOld).mpr hlinkG
      have huOld : u ∈ V(η.imageGraph) := η.imageGraph.left_mem_of_isLink hlinkOld.symm
      have huBoth : u ∈ V(Q) ∩ V(η.imageGraph) := ⟨hlink.right_mem, huOld⟩
      rw [hinter, mem_singleton_iff] at huBoth
      exact huy huBoth

/-- Graph Minors XVI, proof of (8.3), Claim (7), page 67.
A selected horn path has no internal vertex in the rearranged span. Otherwise
Claim (5) and its remaining segment give a forbidden long old-span path. -/
theorem theorem_8_3_claim_7 (hS : IsClosedSurface S)
    {α : Type u} {β : Type v} {G : Graph α β} {H H' : Drawing S}
    {η : SpanEmbedding H G} {η' : SpanEmbedding H' G} {θ_star θ lam ψ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {z : Set S}
    (h : IsRearrangedWithin G H H' η η' θ_star θ lam T_star T T' d d' z)
    (hsymm : ∀ a ∈ H.A, ∀ b ∈ H.A, d a b = d b a)
    (htri : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A,
      d a c ≤ d a b + d b c)
    (hprox : ∀ x ∈ H.V, ∀ a ∈ H.A, x ∈ closure a → d {x} a ≤ 2)
    (hself : ∀ a ∈ H.A, d a a = 0) (hψ : 1 ≤ ψ)
    {Z : Set α} (hnewZ : Disjoint V(η'.imageGraph) Z)
    (hshort : ∀ (L : Graph α β) (s t : S), s ∈ H.V → t ∈ H.V →
      IsHPathWithEnds G η.imageGraph L (η.vMap s) (η.vMap t) →
      Disjoint V(L) Z → d {s} {t} < 2 * ψ)
    {P : Graph α β} {v : α} {u : S} (hu : u ∈ H.V) (hvZ : v ∈ Z)
    (hP : IsGraphPathWithEnds G P v (η.vMap u))
    (hPH : V(P) ∩ V(η.imageGraph) = {η.vMap u})
    (hPZ : V(P) ∩ Z = {v}) (hfar : lam + 2 + 2 * ψ ≤ d z {u}) :
    V(P) ∩ V(η'.imageGraph) ⊆ {η.vMap u} := by
  intro w ⟨hwP, hwnew⟩
  by_contra hne
  have hwne : w ≠ η.vMap u := fun heq => hne (mem_singleton_iff.mpr heq)
  have hwnot : w ∉ V(η.imageGraph) := by
    intro hwold
    exact hwne (mem_singleton_iff.mp (hPH ▸ ⟨hwP, hwold⟩))
  have hwv : w ≠ v := by
    intro heq
    exact hnewZ.notMem_of_mem_left hwnew (heq ▸ hvZ)
  have hukeep := h.vMap_eq u hu (by omega)
  have huold := η.bijOn_v.mapsTo hu
  have hunew : η.vMap u ∈ V(η'.imageGraph) := by
    rw [← hukeep.2]
    exact η'.bijOn_v.mapsTo hukeep.1
  obtain ⟨Q, x, hx, hQnew, hQ, hQH, hxclose⟩ := theorem_8_3_claim_5 hS h hsymm htri hprox
    ⟨η.vMap u, huold, hunew⟩ hwnew hwnot
  obtain ⟨R₁, R₂, hR₁P, hR₂P, hR₁, hR₂, _, hRinter, _⟩ := hP.exists_split_at hwP
  have hvnot : v ∉ V(R₂) := by
    intro hvR₂
    have hvBoth : v ∈ V(R₁) ∩ V(R₂) := ⟨hR₁.left_mem, hvR₂⟩
    rw [hRinter, mem_singleton_iff] at hvBoth
    exact hwv hvBoth.symm
  have hR₂Z : Disjoint V(R₂) Z := disjoint_left.mpr fun y hyR hyZ => by
    have hy : y = v := mem_singleton_iff.mp (hPZ ▸ ⟨hR₂P.vertexSet_mono hyR, hyZ⟩)
    exact hvnot (hy ▸ hyR)
  have hR₂H : V(R₂) ∩ V(η.imageGraph) ⊆ {η.vMap u} := by
    rintro y ⟨hyR, hyH⟩
    exact hPH ▸ ⟨hR₂P.vertexSet_mono hyR, hyH⟩
  have hxA := singleton_mem_A_of_mem_V hx
  have huA := singleton_mem_A_of_mem_V hu
  have hbound := htri z h.z_mem {x} hxA {u} huA
  have hlong : 2 * ψ ≤ d {x} {u} := by omega
  have hxu : x ≠ u := by
    intro heq
    subst x
    rw [hself {u} huA] at hlong
    omega
  have hmapne : η.vMap x ≠ η.vMap u := fun heq => hxu (η.bijOn_v.injOn hx hu heq)
  obtain ⟨L, hLsub, hL⟩ := exists_hPath_of_two_paths η.imageGraph_le hQ.symm
    (hR₂.mono hP.le) (η.bijOn_v.mapsTo hx) huold hmapne
    (by rw [hQH]) hR₂H
  have hQZ : Disjoint V(Q) Z := hnewZ.mono_left hQnew.vertexSet_mono
  have hLZ : Disjoint V(L) Z := by
    apply disjoint_left.mpr
    intro y hyL hyZ
    have hy := hLsub.vertexSet_mono hyL
    change y ∈ V(Q) ∪ V(R₂) at hy
    exact hy.elim (fun hyQ => hQZ.notMem_of_mem_left hyQ hyZ)
      (fun hyR => hR₂Z.notMem_of_mem_left hyR hyZ)
  exact (Nat.not_lt_of_ge hlong) (hshort L x u hx hu hL hLZ)

/-- The first new-span vertex met by an old hair is far from its retained
end. This is the first case of XVI (8.3), Claim (12), page 68. -/
theorem rearranged_hair_hit_dist (hS : IsClosedSurface S)
    {α : Type u} {β : Type v} {G : Graph α β} {H H' : Drawing S}
    {η : SpanEmbedding H G} {η' : SpanEmbedding H' G} {θ_star θ lam ψ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {z : Set S}
    (h : IsRearrangedWithin G H H' η η' θ_star θ lam T_star T T' d d' z)
    (hsymm : ∀ a ∈ H.A, ∀ b ∈ H.A, d a b = d b a)
    (htri : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A,
      d a c ≤ d a b + d b c)
    {P : Graph α β} {y x v : S} (hy : y ∈ H.V) (hx : x ∈ H.V)
    (hy' : y ∈ H'.V) (hv' : v ∈ H'.V)
    (hP : IsHPathWithEnds G η.imageGraph P (η.vMap y) (η.vMap x))
    (hvP : η'.vMap v ∈ V(P)) (hvy : η'.vMap v ≠ η.vMap y)
    (hfar : ψ + 5 * lam + 2 ≤ d z {y})
    (hθ : ψ + (4 * lam + 2) ≤ θ) (hdist : θ ≤ d {y} {x}) :
    ψ ≤ d' {y} {v} := by
  obtain ⟨a, ha, hva⟩ := exists_atom H v
  by_cases haway : lam < d z a
  · obtain ⟨_, hv, hmap⟩ := old_vertex_of_far_atom hS h ha hva hv' haway
    have hvBoth : η'.vMap v ∈ V(P) ∩ V(η.imageGraph) := by
      refine ⟨hvP, ?_⟩
      rw [hmap]
      exact η.bijOn_v.mapsTo hv
    rw [hP.2.2.2.2.2.1] at hvBoth
    have hveq : η'.vMap v = η.vMap x := by
      rcases hvBoth with hsame | hsame
      · exact (hvy hsame).elim
      · exact mem_singleton_iff.mp hsame
    have hvx : v = x := η.bijOn_v.injOn hv hx (hmap.symm.trans hveq)
    subst v
    have hb := compression_vertex_dist_le h.isCompression hy hx hy' hv'
    omega
  · have hnear : d z a ≤ lam := Nat.le_of_not_gt haway
    have hyA := singleton_mem_A_of_mem_V hy
    have hb := htri z h.z_mem a ha {y} hyA
    rw [hsymm a ha {y} hyA] at hb
    have hc := h.isCompression.dist_le y v
    rw [pointDist_of_mem_atoms d hyA ha (mem_singleton y) hva,
      pointDist_of_mem_vertices d' hy' hv'] at hc
    omega

/-- In the second case of XVI (8.3), Claim (12), the first new-span vertex
reached through the old drawing is far from the retained hair.
We retain hairs at distance `ψ + 5λ + 4`, two more than the paper's cutoff,
to keep a distance buffer for the last old edge. -/
theorem rearranged_exit_path_dist (hS : IsClosedSurface S)
    {α : Type u} {β : Type v} {G : Graph α β} {H H' : Drawing S}
    {η : SpanEmbedding H G} {η' : SpanEmbedding H' G} {θ_star θ lam ψ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {z : Set S}
    (h : IsRearrangedWithin G H H' η η' θ_star θ lam T_star T T' d d' z)
    (hsymm : ∀ a ∈ H.A, ∀ b ∈ H.A, d a b = d b a)
    (htri : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A,
      d a c ≤ d a b + d b c)
    (hprox : ∀ x ∈ H.V, ∀ a ∈ H.A, x ∈ closure a → d {x} a ≤ 2)
    {R : Graph α β} {y x v : S} (hy : y ∈ H.V) (hy' : y ∈ H'.V) (hv' : v ∈ H'.V)
    (hR : IsGraphPathWithEnds G R (η.vMap x) (η'.vMap v)) (hRold : R ≤ η.imageGraph)
    (hRnew : V(R) ∩ V(η'.imageGraph) = {η'.vMap v})
    (hxnot : η.vMap x ∉ V(η'.imageGraph)) (hfar : ψ + 5 * lam + 4 ≤ d z {y}) :
    ψ ≤ d' {y} {v} := by
  by_contra hn
  have hsmall : d' {y} {v} < ψ := Nat.lt_of_not_ge hn
  obtain ⟨a, ha, hva⟩ := exists_atom H v
  have hyA := singleton_mem_A_of_mem_V hy
  have hb := htri z h.z_mem a ha {y} hyA
  rw [hsymm a ha {y} hyA] at hb
  have hc := h.isCompression.dist_le y v
  rw [pointDist_of_mem_atoms d hyA ha (mem_singleton y) hva,
    pointDist_of_mem_vertices d' hy' hv'] at hc
  have hfar_a : lam + 2 < d z a := by omega
  obtain ⟨heq, hv, hmap⟩ := old_vertex_of_far_atom hS h ha hva hv' (by omega)
  have hvA := singleton_mem_A_of_mem_V hv
  have hfar_v : lam + 2 < d z {v} := by simpa only [heq] using hfar_a
  have hends : η.vMap x ≠ η'.vMap v := by
    intro he
    exact hxnot (he ▸ η'.bijOn_v.mapsTo hv')
  obtain ⟨e, u, hlinkR, hune⟩ := path_edge_at_end hR hends
  have hlinkOld := (hRold.isLink_iff hlinkR.edge_mem).mp hlinkR
  obtain ⟨f, hf, hfe⟩ := η.bijOn_e.surjOn hlinkOld.edge_mem
  have hinc : η.imageGraph.Inc (η.eMap f) (η.vMap v) := by
    rw [hfe, ← hmap]
    exact ⟨u, hlinkOld.symm⟩
  have hvf := (η.inc_iff f hf v hv).mp hinc
  have hfA : f ∈ H.A := Or.inl (Or.inr hf)
  have hp := hprox v hv f hfA hvf
  have ht := htri z h.z_mem f hfA {v} hvA
  rw [hsymm f hfA {v} hvA] at ht
  have hfar_f : lam < d z f := by omega
  obtain ⟨hf', hmapf⟩ := h.eMap_eq f hf hfar_f
  have heNew : e ∈ E(η'.imageGraph) := by
    rw [← hfe, ← hmapf]
    exact η'.bijOn_e.mapsTo hf'
  have hlinkG := (hR.1.isLink_iff hlinkR.edge_mem).mp hlinkR
  have hlinkNew := (η'.imageGraph_le.isLink_iff heNew).mpr hlinkG
  have huBoth : u ∈ V(R) ∩ V(η'.imageGraph) := ⟨hlinkR.left_mem, hlinkNew.left_mem⟩
  rw [hRnew, mem_singleton_iff] at huBoth
  exact hune huBoth

end GraphMinor.GM16
