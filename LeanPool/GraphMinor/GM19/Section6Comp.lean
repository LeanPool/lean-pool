/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section6Graph

/-!
# Composing enlargements

An enlargement of `G` in `G'` and an enlargement of `G'` in `G''` give an enlargement of `G` in
`G''` (`IsEnlargement.comp`). This is the step "and hence an enlargement of `H` in `G'`" in the
proof of Graph Minors XIX, (6.5) (page 341). We first restate connectivity of a set of vertices
without walks (`preconnected_iff_connIn`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11

variable {S : Type} [TopologicalSpace S]

theorem preconnected_iff_connIn (D : Drawing S) (X : Set S) : (D.adj.induce X).Preconnected ↔
  ConnIn D X := by
  constructor
  · intro h Y hY ⟨a, ha⟩ hc
    refine Subset.antisymm hY fun b hb => ?_
    obtain ⟨w⟩ := h ⟨a, hY ha⟩ ⟨b, hb⟩
    have key : ∀ {p q : X}, (D.adj.induce X).Walk p q → p.1 ∈ Y → q.1 ∈ Y := fun w => by
      induction w with
      | nil => exact id
      | cons hadj _ ih => exact fun hp => ih (hc _ hp _ (Subtype.coe_prop _) hadj)
    exact key w ha
  · intro h a b
    let Y : Set S := {y | ∃ hy : y ∈ X, (D.adj.induce X).Reachable a ⟨y, hy⟩}
    have hY : Y = X := h Y (fun y hy => hy.1) ⟨a.1, a.2, .refl _⟩ (fun p ⟨hpX, hr⟩ q hq hadj =>
      ⟨hq, hr.trans (SimpleGraph.Adj.reachable (G := D.adj.induce X) (u := ⟨p, hpX⟩) (v
        := ⟨q, hq⟩) hadj)⟩)
    have hb : b.1 ∈ Y := by
      rw [hY]
      exact b.2
    obtain ⟨_, hr⟩ := hb
    exact hr

theorem adj_mono {D D' : Drawing S} (h : D.IsSubdrawing D') {a b : S}
  (hab : D.adj.Adj a b) : D'.adj.Adj a b := by
  obtain ⟨h1, ha, hb, e, he, h2, h3⟩ := hab
  exact ⟨h1, h.1 ha, h.1 hb, e, h.2 he, h2, h3⟩

variable [T2Space S]

/-- **Composing enlargements.** See the module docstring. -/
theorem IsEnlargement.comp {G G' G'' : Drawing S} (hl' : LoopFree G')
  (hl'' : LoopFree G'') {σv τv : S → Drawing S} {σe τe : Set S → Set S}
    (hσ : IsEnlargement G G' σv σe) (hτ : IsEnlargement G' G'' τv τe) :
    ∃ (ρv : S → Drawing S), IsEnlargement G G'' ρv (τe ∘ σe) ∧ ∀ v ∈ G.V, ∀ x ∈ (σv v).V,
      (τv x).IsSubdrawing (ρv v) := by
  classical
  let RV : S → Set S := fun v => ⋃ x ∈ (σv v).V, (τv x).V
  let RE : S → Set (Set S) := fun v => (⋃ x ∈ (σv v).V, (τv x).E) ∪ τe '' (σv v).E
  have hsubV : ∀ v ∈ G.V, ∀ x ∈ (σv v).V, x ∈ G'.V := fun v hv x hx =>
    (hσ.vertex_subdrawing v hv).1 hx
  have hsubE : ∀ v ∈ G.V, ∀ f ∈ (σv v).E, f ∈ G'.E := fun v hv f hf =>
    (hσ.vertex_subdrawing v hv).2 hf
  have hend : ∀ v ∈ G.V, ∀ f ∈ (σv v).E, ∀ x ∈ tilde f, x ∈ (σv v).V := fun v hv f hf x hx => by
    have h1 : x ∈ closure f ∩ G'.V := by
      rw [← tilde_eq_inter_V G' (hsubE v hv f hf)]
      exact hx
    have h2 := (hσ.vertex_subdrawing v hv).closure_inter_V hf
    rw [← h2] at h1
    exact h1.2
  have hends : ∀ f ∈ G'.E, ∀ x ∈ tilde f, ∃ y ∈ tilde (τe f), y ∈ (τv x).V := fun f hf x hx => by
    have hxV : x ∈ G'.V := by
      rw [tilde_eq_inter_V G' hf] at hx
      exact hx.2
    obtain ⟨y, hy1, hy2⟩ := (hτ.ends_iff f hf x hxV).mpr hx
    exact ⟨y, hy2, hy1⟩
  have hREG : ∀ v ∈ G.V, RE v ⊆ G''.E := fun v hv e he => by
    rcases he with he | ⟨f, hf, rfl⟩
    · obtain ⟨x, hx, he⟩ := mem_iUnion₂.mp he
      exact (hτ.vertex_subdrawing x (hsubV v hv x hx)).2 he
    · exact hτ.edge_mem f (hsubE v hv f hf)
  have hRVG : ∀ v ∈ G.V, RV v ⊆ G''.V := fun v hv y hy => by
    obtain ⟨x, hx, hy⟩ := mem_iUnion₂.mp hy
    exact (hτ.vertex_subdrawing x (hsubV v hv x hx)).1 hy
  have hspanV : ∀ v ∈ G.V, G''.spanV (RV v) (RE v) = RV v := fun v hv => by
    refine Subset.antisymm (union_subset inter_subset_left (iUnion₂_subset fun e he y hy
      => ?_)) fun y hy => .inl ⟨hy, hRVG v hv hy⟩
    rcases he.1 with he' | ⟨f, hf, rfl⟩
    · obtain ⟨x, hx, he'⟩ := mem_iUnion₂.mp he'
      have h1 : y ∈ closure e ∩ (τv x).V := by
        rw [(hτ.vertex_subdrawing x (hsubV v hv x hx)).closure_inter_V he']
        exact hy
      exact mem_iUnion₂.mpr ⟨x, hx, h1.2⟩
    · obtain ⟨p, q, hpq, ht, -⟩ := hl' f (hsubE v hv f hf)
      have hp : p ∈ tilde f := ht ▸ .inl rfl
      have hq : q ∈ tilde f := ht ▸ .inr rfl
      obtain ⟨p', hp1, hp2⟩ := hends f (hsubE v hv f hf) p hp
      obtain ⟨q', hq1, hq2⟩ := hends f (hsubE v hv f hf) q hq
      have hne : p' ≠ q' := fun h' => disjoint_left.mp (hτ.vertex_disjoint p (hsubV v hv p
        (hend v hv f hf p hp)) q (hsubV v hv q (hend v hv f hf q hq)) hpq) hp2 (h' ▸ hq2)
      obtain ⟨a, b, -, ht', -⟩ := hl'' (τe f) (hτ.edge_mem f (hsubE v hv f hf))
      have hyt : y ∈ tilde (τe f) := by
        rw [tilde_eq_inter_V G'' (hτ.edge_mem f (hsubE v hv f hf))]
        exact hy
      have hcases : y = p' ∨ y = q' := by
        rw [ht'] at hp1 hq1 hyt
        rcases hp1 with rfl | rfl <;> rcases hq1 with rfl | rfl <;> rcases hyt with rfl | rfl
          <;> simp_all
      rcases hcases with rfl | rfl
      · exact mem_iUnion₂.mpr ⟨p, hend v hv f hf p hp, hp2⟩
      · exact mem_iUnion₂.mpr ⟨q, hend v hv f hf q hq, hq2⟩
  have hspanE : ∀ v ∈ G.V, (G''.span (RV v) (RE v)).E = RE v := fun v hv => by
    rw [Drawing.span_E, inter_eq_left.mpr (hREG v hv)]
  have hsub : ∀ v ∈ G.V, ∀ x ∈ (σv v).V, (τv x).IsSubdrawing (G''.span (RV v) (RE v))
    := fun v hv x hx => by
    refine ⟨fun y hy => ?_, fun e he => ?_⟩
    · change y ∈ G''.spanV _ _
      rw [hspanV v hv]
      exact mem_iUnion₂.mpr ⟨x, hx, hy⟩
    · rw [hspanE v hv]
      exact .inl (mem_iUnion₂.mpr ⟨x, hx, he⟩)
  refine ⟨fun v => G''.span (RV v) (RE v),
    ⟨fun e he => hτ.edge_mem _ (hσ.edge_mem e he), ?_, fun v hv => ?_, fun v hv => ?_,
      fun v hv => ?_, fun v₁ hv₁ v₂ hv₂ hne => ?_, fun e he v hv => ?_⟩, hsub⟩
  · exact hτ.edge_injOn.comp hσ.edge_injOn fun e he => hσ.edge_mem e he
  · refine ⟨fun y hy => G''.spanV_subset _ _ hy, fun e he => ?_⟩
    have h1 := he
    rw [hspanE v hv] at h1
    exact hREG v hv h1
  · obtain ⟨x, hx⟩ := hσ.vertex_nonempty v hv
    obtain ⟨y, hy⟩ := hτ.vertex_nonempty x (hsubV v hv x hx)
    exact ⟨y, (hsub v hv x hx).1 hy⟩
  · rw [preconnected_iff_connIn]
    change ConnIn _ (G''.spanV _ _)
    rw [hspanV v hv]
    intro Y hY ⟨y₀, hy₀⟩ hcl
    have hcl' : ∀ x ∈ (σv v).V, (Y ∩ (τv x).V).Nonempty → (τv x).V ⊆ Y := fun x hx hne' => by
      have h1 := (preconnected_iff_connIn _ _).mp (hτ.vertex_connected x (hsubV v hv x hx)) (Y ∩
        (τv x).V) inter_subset_right hne' (fun a ha b hb hab =>
        ⟨hcl a ha.1 b (mem_iUnion₂.mpr ⟨x, hx, hb⟩) (adj_mono (hsub v hv x hx) hab), hb⟩)
      exact fun y hy => (h1.symm ▸ hy : y ∈ Y ∩ (τv x).V).1
    have hZ := (preconnected_iff_connIn _ _).mp (hσ.vertex_connected v hv) {x | x ∈ (σv v).V ∧ (Y ∩
      (τv x).V).Nonempty} (fun x hx => hx.1) (by
      obtain ⟨x, hx, hy⟩ := mem_iUnion₂.mp (hY hy₀)
      exact ⟨x, hx, y₀, hy₀, hy⟩) (by
      rintro a ⟨ha, hne'⟩ b hb ⟨hab, -, -, f, hf, haf, hbf⟩
      refine ⟨hb, ?_⟩
      have hfG := hsubE v hv f hf
      obtain ⟨p, hp1, hp2⟩ := hends f hfG a haf
      obtain ⟨q, hq1, hq2⟩ := hends f hfG b hbf
      have hpY : p ∈ Y := hcl' a ha hne' hp2
      have hpq : p ≠ q := fun h' => disjoint_left.mp (hτ.vertex_disjoint a (hsubV v hv a ha) b
        (hsubV v hv b hb) hab) hp2 (h' ▸ hq2)
      have hq' : q ∈ RV v := mem_iUnion₂.mpr ⟨b, hb, hq2⟩
      have hadj : (Drawing.adj (G''.span (RV v) (RE v))).Adj p q := ⟨hpq, by
        change p ∈ G''.spanV _ _
        rw [hspanV v hv]
        exact hY hpY, by
        change q ∈ G''.spanV _ _
        rw [hspanV v hv]
        exact hq', τe f, by
        rw [hspanE v hv]
        exact .inr ⟨f, hf, rfl⟩, hp1, hq1⟩
      exact ⟨q, hcl p hpY q hq' hadj, hq2⟩)
    refine Subset.antisymm hY fun y hy => ?_
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp hy
    have h2 : x ∈ {x | x ∈ (σv v).V ∧ (Y ∩ (τv x).V).Nonempty} := hZ.symm ▸ hx
    exact hcl' x hx h2.2 hyx
  · change Disjoint (G''.spanV _ _) (G''.spanV _ _)
    rw [hspanV v₁ hv₁, hspanV v₂ hv₂]
    refine disjoint_left.mpr fun y hy hy' => ?_
    obtain ⟨x, hx, h1⟩ := mem_iUnion₂.mp hy
    obtain ⟨x', hx', h2⟩ := mem_iUnion₂.mp hy'
    have hne' : x ≠ x' := fun h' => disjoint_left.mp (hσ.vertex_disjoint v₁ hv₁ v₂ hv₂ hne) hx
      (h' ▸ hx')
    exact disjoint_left.mp (hτ.vertex_disjoint x (hsubV v₁ hv₁ x hx) x'
      (hsubV v₂ hv₂ x' hx') hne') h1 h2
  · change ((G''.spanV _ _) ∩ _).Nonempty ↔ _
    rw [hspanV v hv]
    have hfG := hσ.edge_mem e he
    constructor
    · rintro ⟨y, hy, hyt⟩
      obtain ⟨x, hx, h1⟩ := mem_iUnion₂.mp hy
      have h2 := (hτ.ends_iff _ hfG x (hsubV v hv x hx)).mp ⟨y, h1, hyt⟩
      exact (hσ.ends_iff e he v hv).mp ⟨x, hx, h2⟩
    · intro h1
      obtain ⟨x, hx, h2⟩ := (hσ.ends_iff e he v hv).mpr h1
      obtain ⟨y, hy, hyt⟩ := (hτ.ends_iff _ hfG x (hsubV v hv x hx)).mpr h2
      exact ⟨y, mem_iUnion₂.mpr ⟨x, hx, hy⟩, hyt⟩

end GraphMinor.GM19
