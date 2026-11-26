/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffCollapse
public import LeanPool.GraphMinor.GM07.PushForest

/-!
# From the graph after the collapse back to the graph

Graph Minors VII, (5.9), page 236: "if it is $G'$-feasible then $H$ is $G$-feasible". The map `ρ`
carries the edges of `G₁` to the edges of `G'`. It collapses a tree `Tr x` of `G`, built from a path
`N_i(C)` and a path `Q_i(C)`, to the vertex `x` of the cuff. A forest in `G'` lifts to a forest in
`G`, by taking the edges that map to it and all the trees. Since `ρ` is homotopic to the identity,
the lift has the same homotopy class.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function Metric GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-- The facts on the collapse map that we use to lift a forest. -/
structure IsCollapse (G G₁ G' : Drawing S) (ρ : S → S) (Ψ : unitInterval × S → S) (X A : Set S)
  (Tr : S → Drawing S) : Prop where
  contΨ : Continuous Ψ
  zero : ∀ x, Ψ (0, x) = x
  one : ∀ x, Ψ (1, x) = ρ x
  fix : ∀ x ∈ X, ∀ τ, Ψ (τ, x) = x
  inj : ∀ x ∈ A, ∀ y, ρ y = ρ x → y = x
  sub : G₁.IsSubdrawing G
  off : G₁.U \ G₁.V ⊆ A
  imU : G'.U = ρ '' G₁.U
  imV : G'.V = ρ '' G₁.V
  imE : G'.E = image ρ '' G₁.E
  X_eq : X = G.V ∩ bd S
  vert : ∀ v ∈ G₁.V, v ∈ A ∨ (ρ v ∈ X ∧ v ∈ (Tr (ρ v)).V)
  tree : ∀ x ∈ X, (Tr x).IsSubdrawing G ∧ IsGraphForest (Tr x).toGraph ∧ x ∈ (Tr x).V ∧ (∀ a ∈
    (Tr x).U, ρ a = x) ∧ ∀ a ∈ (Tr x).V, ∀ b ∈ (Tr x).V, Nonempty (GraphWalk (Tr x).toGraph a b)

variable {G G₁ G' H : Drawing S} {ρ : S → S} {Ψ : unitInterval × S → S} {X A : Set S} {Tr : S
  → Drawing S}

/-- A curve is homotopic to its image by `ρ`, if its ends are in `X`. -/
theorem IsCollapse.curvesHomotopic (h : IsCollapse G G₁ G' ρ Ψ X A Tr) {φ φ' : Curve S}
  (h0 : φ 0 ∈ X) (h1 : φ 1 ∈ X) (he : ∀ u, φ' u = ρ (φ u)) : CurvesHomotopic φ φ' := by
  have hc := h.contΨ
  refine ⟨⟨fun q => Ψ (q.2, φ q.1), by fun_prop⟩, fun _ => mem_univ _, fun x => h.zero _,
    fun x => ?_, fun y => h.fix _ h0 _, fun y => ?_, fun y => h.fix _ h1 _, fun y => ?_⟩
  · change Ψ (1, φ x) = φ' x
    rw [h.one, he]
  · change Ψ (y, φ 0) = φ' 0
    rw [h.fix _ h0, he, ← h.one, h.fix _ h0]
  · change Ψ (y, φ 1) = φ' 1
    rw [h.fix _ h1, he, ← h.one, h.fix _ h1]

variable [T2Space S]

private theorem forest_lift_maps_into_forest
    {S : Type u}
    [TopologicalSpace S]
    [T1Space S]
    {G : Drawing S}
    {G₁ : Drawing S}
    {ρ : S → S}
    {X : Set S}
    {Tr : S → Drawing S}
    (H₂ : Drawing S)
    (hXV : ∀ x ∈ X, x ∈ H₂.V) :
    let E₁ : Set (Set S) := {e | e ∈ G₁.E ∧ ρ '' e ∈ H₂.E}
    ∀ (VF : Set S),
    let EF : Set (Set S) := E₁ ∪ ⋃ x ∈ X, (Tr x).E
    (∀ x ∈ X, ∀ a ∈ (Tr x).U, ρ a = x) →
    (∀ e ∈ G₁.E, ∀ z ∈ closure e, ρ z ∈ closure (ρ '' e)) →
    let F : Drawing S := G.span VF EF
    (∀ a ∈ F.V, ρ a ∈ H₂.V) →
    ∀ (a : S),
    (a ∈ F.U) →
    ρ a ∈ H₂.U := by
  intro E₁ VF EF hρT hclE F hFρ a ha
  rcases ha with ha | ha
  · exact H₂.V_subset_U (hFρ a ha)
  · obtain ⟨e, he, ha⟩ := mem_iUnion₂.mp ha
    rcases he.1 with he₁ | he₁
    · exact H₂.closure_subset_U he₁.2 (hclE e he₁.1 a ha)
    · obtain ⟨x, hx, he₂⟩ := mem_iUnion₂.mp he₁
      rw [hρT x hx a ((Tr x).closure_subset_U he₂ ha)]
      exact H₂.V_subset_U (hXV x hx)

private theorem project_lifted_forest_walk
    {S : Type u}
    [TopologicalSpace S]
    {ρ : S → S}
    {X : Set S}
    {Tr : S → Drawing S}
    (H₂ : Drawing S)
    (E₁ : Set (Set S))
    (F : Drawing S)
    (hFρ : ∀ a ∈ F.V, ρ a ∈ H₂.V)
    (hlink : ∀ {e : Set S} {a b : S}, e ∈ E₁ → F.toGraph.IsLink e a b → H₂.toGraph.IsLink (ρ '' e)
      (ρ a) (ρ b))
    (htreeLink : ∀ {e : Set S} {a b : S}, e ∉ E₁ → F.toGraph.IsLink e a b → ρ a = ρ b ∧ ∃ x ∈ X, e
      ∈ (Tr x).E ∧ a ∈ (Tr x).V ∧ b ∈ (Tr x).V)
    (himage : ∀ {e e' : Set S}, e ∈ E₁ → e' ∈ E₁ → ρ '' e = ρ '' e' → e = e') :
    ∀ {u v : S} (R : GraphWalk F.toGraph u v), R.edges.Nodup → ∃ R' : GraphWalk H₂.toGraph (ρ u)
      (ρ v),
      R'.edges.Nodup ∧ (∀ e' ∈
      R'.edges, ∃ e ∈ R.edges, e ∈ E₁ ∧ e' = ρ '' e) ∧ ∀ e ∈ R.edges, e ∈ E₁ → ρ '' e ∈ R'.edges
        := by
  intro u v R
  induction R with
  | @nil v hv =>
    intro _
    exact ⟨.nil (hFρ v hv), by simp [GraphWalk.edges], by simp [GraphWalk.edges],
      by simp [GraphWalk.edges]⟩
  | @cons u w v e hl rest ih =>
    intro hn
    have hn' : e ∉ rest.edges ∧ rest.edges.Nodup := by
      simpa [GraphWalk.edges] using hn
    obtain ⟨R', h1, h2, h3⟩ := ih hn'.2
    by_cases he : e ∈ E₁
    · refine ⟨.cons (hlink he hl) R', ?_, ?_, ?_⟩
      · refine List.nodup_cons.mpr ⟨fun h4 => ?_, h1⟩
        obtain ⟨e₀, he₀, he₁, h5⟩ := h2 _ h4
        exact hn'.1 (himage he he₁ h5 ▸ he₀)
      · intro e' he'
        rcases List.mem_cons.mp he' with rfl | he'
        · exact ⟨e, List.mem_cons_self, he, rfl⟩
        · obtain ⟨e₀, he₀, he₁, h5⟩ := h2 _ he'
          exact ⟨e₀, List.mem_cons_of_mem _ he₀, he₁, h5⟩
      · intro e₀ he₀ he₁
        rcases List.mem_cons.mp he₀ with rfl | he₀
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (h3 e₀ he₀ he₁)
    · have h4 := (htreeLink he hl).1
      rw [h4]
      refine ⟨R', h1, fun e' he' => ?_, fun e₀ he₀ he₁ => ?_⟩
      · obtain ⟨e₀, he₀, he₁, h5⟩ := h2 _ he'
        exact ⟨e₀, List.mem_cons_of_mem _ he₀, he₁, h5⟩
      · rcases List.mem_cons.mp he₀ with rfl | he₀
        · exact absurd he₁ he
        · exact h3 e₀ he₀ he₁

private theorem walk_without_uncontracted_edges_stays_in_tree
    {S : Type u}
    [TopologicalSpace S]
    {ρ : S → S}
    {X : Set S}
    {Tr : S → Drawing S}
    (E₁ : Set (Set S))
    (hρT : ∀ x ∈ X, ∀ a ∈ (Tr x).U, ρ a = x)
    (F : Drawing S)
    (htreeLink : ∀ {e : Set S} {a b : S}, e ∉ E₁ → F.toGraph.IsLink e a b → ρ a = ρ b ∧ ∃ x ∈ X, e
      ∈ (Tr x).E ∧ a ∈ (Tr x).V ∧ b ∈ (Tr x).V) :
    ∀ {u v : S} (R : GraphWalk F.toGraph u v), (∀ e ∈ R.edges, e ∉ E₁) → ∀ x ∈ X, u ∈ (Tr x).V →
      (∀ z ∈ R.support, z ∈ (Tr x).V) ∧ ∀ e ∈ R.edges, e ∈ (Tr x).E := by
  intro u v R
  induction R with
  | @nil v hv =>
    intro _ x _ hu
    exact ⟨by simpa [GraphWalk.support] using hu, by simp [GraphWalk.edges]⟩
  | @cons u w v e hl rest ih =>
    intro hE x hx hu
    have he : e ∉ E₁ := hE e List.mem_cons_self
    obtain ⟨-, x', hx', h1, h2, h3⟩ := htreeLink he hl
    have hxx : x' = x := by
      rw [← hρT x' hx' u ((Tr x').V_subset_U h2), hρT x hx u ((Tr x).V_subset_U hu)]
    subst hxx
    obtain ⟨h4, h5⟩ := ih (fun f hf => hE f (List.mem_cons_of_mem _ hf)) x' hx h3
    refine ⟨fun z hz => ?_, fun f hf => ?_⟩
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact hu
      · exact h4 z hz
    · rcases List.mem_cons.mp hf with rfl | hf
      · exact h1
      · exact h5 f hf

private theorem lift_is_graph_forest
    {S : Type u}
    [TopologicalSpace S]
    {G : Drawing S}
    {G₁ : Drawing S}
    {G' : Drawing S}
    {ρ : S → S}
    {Ψ : ↑unitInterval × S → S}
    {X : Set S}
    {A : Set S}
    {Tr : S → Drawing S}
    (h : IsCollapse G G₁ G' ρ Ψ X A Tr)
    (H₂ : Drawing S)
    (hH₂f : IsGraphForest H₂.toGraph)
    (E₁ : Set (Set S))
    (F : Drawing S)
    (hTF : ∀ x ∈ X, (Tr x).IsSubdrawing F)
    (htreeLink : ∀ {e : Set S} {a b : S}, e ∉ E₁ → F.toGraph.IsLink e a b → ρ a = ρ b ∧ ∃ x ∈ X, e
      ∈ (Tr x).E ∧ a ∈ (Tr x).V ∧ b ∈ (Tr x).V)
    (hproj : ∀ {u v : S} (R : GraphWalk F.toGraph u v), R.edges.Nodup → ∃ R' : GraphWalk H₂.toGraph
      (ρ u) (ρ v),
      R'.edges.Nodup ∧ (∀
      e' ∈ R'.edges, ∃ e ∈ R.edges, e ∈ E₁ ∧ e' = ρ '' e) ∧ ∀ e ∈ R.edges, e ∈ E₁ → ρ '' e ∈
      R'.edges)
    (hstay : ∀ {u v : S} (R : GraphWalk F.toGraph u v), (∀ e ∈ R.edges, e ∉ E₁) → ∀ x ∈ X, u ∈ (Tr
      x).V → (∀ z ∈ R.support, z ∈ (Tr x).V) ∧ ∀ e ∈ R.edges, e ∈ (Tr x).E) :
    IsGraphForest F.toGraph := by
  intro u W hW
  obtain ⟨R', h1, h2, h3⟩ := hproj W hW.2
  have h4 := trail_length_of_eq hH₂f rfl R' h1
  have hR : R'.edges = [] := List.length_eq_zero_iff.mp h4
  have hnone : ∀ e ∈ W.edges, e ∉ E₁ := fun e he he₁ => by
    have := h3 e he he₁
    rw [hR] at this
    simp at this
  by_contra hne
  cases W with
  | nil hv => exact hne rfl
  | @cons u w _ e hl rest =>
    obtain ⟨-, x, hx, -, h5, -⟩ := htreeLink (hnone e List.mem_cons_self) hl
    obtain ⟨h6, h7⟩ := hstay _ hnone x hx h5
    obtain ⟨W', h8, h9⟩ := (hTF x hx).exists_walk_down (GraphWalk.cons hl rest) h6 h7
    have h10 : W'.IsSimpleClosed := by
      unfold GraphWalk.IsSimpleClosed
      rw [h8, h9]
      exact hW
    have h11 := (h.tree x hx).2.1 _ W' h10
    apply hne
    unfold GraphWalk.length at h11 ⊢
    rw [h9] at h11
    exact h11

private theorem lift_walk_between_fibres
    {S : Type u}
    [TopologicalSpace S]
    {G : Drawing S}
    {G₁ : Drawing S}
    {G' : Drawing S}
    {ρ : S → S}
    {Ψ : ↑unitInterval × S → S}
    {X : Set S}
    {A : Set S}
    {Tr : S → Drawing S}
    (h : IsCollapse G G₁ G' ρ Ψ X A Tr)
    (H₂ : Drawing S)
    (hH₂G : H₂.IsSubdrawing G') :
    let E₁ : Set (Set S) := {e | e ∈ G₁.E ∧ ρ '' e ∈ H₂.E}
    let VF : Set S := (⋃ x ∈ X, (Tr x).V) ∪ {v | v ∈ G₁.V ∧ ρ v ∈ H₂.V}
    let EF : Set (Set S) := E₁ ∪ ⋃ x ∈ X, (Tr x).E
    (∀ e ∈ E₁, ∀ w ∈ closure e, w ∈ G.V → w ∈ G₁.V ∧ ρ w ∈ H₂.V) →
    ∀ (F : Drawing S),
    (F.V = VF) →
    (F.E = EF) →
    (F.IsSubdrawing G) →
    (∀ e ∈ G₁.E, closure (ρ '' e) ∩ G'.V = ρ '' (closure e ∩ G₁.V)) →
    (∀ a ∈ F.V, ∀ b ∈ F.V, ρ a = ρ b → Nonempty (GraphWalk F.toGraph a b)) →
    ∀ {u v : S}, GraphWalk H₂.toGraph u v → ∀ a ∈ F.V, ρ a = u → ∀ b ∈ F.V, ρ b = v → Nonempty
      (GraphWalk F.toGraph a b) := by
  intro E₁ VF EF hVF F hFV hFE hFG hcap hfib u v R
  induction R with
  | @nil v hv =>
    intro a ha h1 b hb h2
    exact hfib a ha b hb (h1.trans h2.symm)
  | @cons u w v e' hl rest ih =>
    intro a ha h1 b hb h2
    have he' : e' ∈ H₂.E := hl.1
    have he'G : e' ∈ G'.E := hH₂G.2 he'
    rw [h.imE] at he'G
    obtain ⟨e, he, rfl⟩ := he'G
    have heE₁ : e ∈ E₁ := ⟨he, he'⟩
    obtain ⟨p, q, hpq⟩ : ∃ p q, closure e ∩ G₁.V = {p, q} := by
      rcases G₁.edge_cond e he with ⟨p, q, -, h3, -⟩ | ⟨p, h3, -⟩
      · exact ⟨p, q, h3⟩
      · exact ⟨p, p, by rw [h3, pair_eq_singleton]⟩
    have hl' := hl.2.2.2
    have hco : closure (ρ '' e) ∩ H₂.V = closure (ρ '' e) ∩ G'.V := by
      refine subset_antisymm (fun z hz => ⟨hz.1, hH₂G.1 hz.2⟩) fun z hz => ⟨hz.1,
        mem_V_of_subdrawing hH₂G (H₂.closure_subset_U he' hz.1) hz.2⟩
    rw [hco, hcap e he, hpq, image_pair] at hl'
    have hmem : ∀ z ∈ ({p, q} : Set S), z ∈ closure e ∩ G₁.V := fun z hz => hpq ▸ hz
    have hFm : ∀ z ∈ ({p, q} : Set S), z ∈ F.V := fun z hz => hFV ▸ .inr (hVF e heE₁ z
      (hmem z hz).1 (h.sub.1 (hmem z hz).2))
    have hlinkF : ∀ {y z}, y ∈ ({p, q} : Set S) → z ∈ ({p, q} : Set S) → ({y, z} : Set S) = {p, q}
      → F.toGraph.IsLink e y z := fun {y z} hy hz he₂ => by
      refine ⟨hFE ▸ .inl heE₁, hFm y hy, hFm z hz, ?_⟩
      rw [he₂, ← hpq]
      refine subset_antisymm (fun w hw => ⟨hw.1, mem_V_of_subdrawing h.sub
        (G₁.closure_subset_U he hw.1) (hFG.1 hw.2)⟩) fun w hw => ⟨hw.1, hFm w (hpq ▸ hw)⟩
    -- The two ends of the step.
    have hend : ∃ y z, y ∈ ({p, q} : Set S) ∧ z ∈ ({p, q} : Set S) ∧ ({y, z} : Set S) = {p, q}
      ∧ ρ y = u ∧ ρ z = w := by
      rcases Set.pair_eq_pair_iff.mp hl' with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact ⟨p, q, .inl rfl, .inr rfl, rfl, h3, h4⟩
      · exact ⟨q, p, .inr rfl, .inl rfl, pair_comm q p, h4, h3⟩
    obtain ⟨y, z, hy, hz, hyz, h3, h4⟩ := hend
    obtain ⟨R₁⟩ := hfib a ha y (hFm y hy) (h1.trans h3.symm)
    obtain ⟨R₂⟩ := ih z (hFm z hz) h4 b hb h2
    exact ⟨R₁.append (.cons (hlinkF hy hz hyz) R₂)⟩

private theorem boundary_fixed_image_membership
    {S : Type u}
    [TopologicalSpace S]
    (β : S ≃ₜ S)
    (hβ : ∀ x ∈ bd S, β x = x)
    {B : Set S}
    {x : S}
    (hx : x ∈ bd S) :
    x ∈ ⇑β '' B ↔ x ∈ B := by
  constructor
  · rintro ⟨y, hy, he⟩
    have : β y = β x := he.trans (hβ x hx).symm
    rwa [← β.injective this]
  · intro h
    exact ⟨x, h, hβ x hx⟩

private theorem lifted_forest_span_vertices
    {S : Type u}
    [TopologicalSpace S]
    {G : Drawing S}
    {G₁ : Drawing S}
    {G' : Drawing S}
    {ρ : S → S}
    {Ψ : ↑unitInterval × S → S}
    {X : Set S}
    {A : Set S}
    {Tr : S → Drawing S}
    (h : IsCollapse G G₁ G' ρ Ψ X A Tr)
    (H₂ : Drawing S) :
    let E₁ : Set (Set S) := {e | e ∈ G₁.E ∧ ρ '' e ∈ H₂.E}
    let VF : Set S := (⋃ x ∈ X, (Tr x).V) ∪ {v | v ∈ G₁.V ∧ ρ v ∈ H₂.V}
    let EF : Set (Set S) := E₁ ∪ ⋃ x ∈ X, (Tr x).E
    (∀ x ∈ X, (Tr x).IsSubdrawing G) →
    (∀ e ∈ E₁, ∀ w ∈ closure e, w ∈ G.V → w ∈ G₁.V ∧ ρ w ∈ H₂.V) →
    G.spanV VF EF = VF := by
  intro E₁ VF EF hTsub hVF
  refine subset_antisymm ?_ ?_
  · rintro w (hw | hw)
    · exact hw.1
    · obtain ⟨e, he, hw⟩ := mem_iUnion₂.mp hw
      rcases he.1 with he₁ | he₁
      · exact .inr (hVF e he₁ w hw.1 hw.2)
      · obtain ⟨x, hx, he₂⟩ := mem_iUnion₂.mp he₁
        exact .inl (mem_iUnion₂.mpr ⟨x, hx, mem_V_of_subdrawing (hTsub x hx)
          ((Tr x).closure_subset_U he₂ hw.1) hw.2⟩)
  · intro w hw
    refine .inl ⟨hw, ?_⟩
    rcases hw with hw | hw
    · obtain ⟨x, hx, hw⟩ := mem_iUnion₂.mp hw
      exact (hTsub x hx).1 hw
    · exact h.sub.1 hw.1

/-- **The lift of a forest.** -/
theorem IsCollapse.isGFeasible [CompactSpace S] [T1Space S] (hS : IsSurface S) [ConnectedSpace S]
  (h : IsCollapse G G₁ G' ρ Ψ X A Tr) (hG : G.IsProper) (hH : IsSurfaceForest H) (hV : H.V ∩ bd S
    = X) (hfe : IsGFeasible G' H) : IsGFeasible G H := by
  classical
  obtain ⟨H₂, ⟨hH₂p, hH₂f⟩, ⟨β, hβ, hhom⟩, hH₂G⟩ := hfe
  obtain ⟨hp₁, hp₂, hf₁, hf₂, hV₂, hpaths⟩ := hhom
  have hbdβ : ∀ {B : Set S} {x : S}, x ∈ bd S → (x ∈ β '' B ↔ x ∈ B) := fun {B x} hx => by
    exact boundary_fixed_image_membership (S := S) β hβ (B := B) (x := x) hx
  have hV₃ : (mapDrawingHomeo β H).V ∩ bd S = H.V ∩ bd S := by
    ext x
    exact and_congr_left fun hx => hbdβ hx
  have hXH₂ : H₂.V ∩ bd S = X := by
    rw [← hV₂, hV₃, hV]
  have hXV : ∀ x ∈ X, x ∈ H₂.V := fun x hx => (hXH₂.symm ▸ hx : x ∈ H₂.V ∩ bd S).1
  have hρX : ∀ x ∈ X, ρ x = x := fun x hx => by
    rw [← h.one, h.fix x hx]
  let E₁ : Set (Set S) := {e | e ∈ G₁.E ∧ image ρ e ∈ H₂.E}
  let VF : Set S := (⋃ x ∈ X, (Tr x).V) ∪ {v | v ∈ G₁.V ∧ ρ v ∈ H₂.V}
  let EF : Set (Set S) := E₁ ∪ ⋃ x ∈ X, (Tr x).E
  have hTsub : ∀ x ∈ X, (Tr x).IsSubdrawing G := fun x hx => (h.tree x hx).1
  have hρT : ∀ x ∈ X, ∀ a ∈ (Tr x).U, ρ a = x := fun x hx => (h.tree x hx).2.2.2.1
  have hclE : ∀ e ∈ G₁.E, ∀ z ∈ closure e, ρ z ∈ closure (ρ '' e) := fun e _ z hz
    => image_closure_subset_closure_image (by
    have := h.contΨ
    have hρc : Continuous ρ := by
      have : ρ = fun x => Ψ (1, x) := funext fun x => (h.one x).symm
      rw [this]
      fun_prop
    exact hρc) (mem_image_of_mem ρ hz)
  have hρc : Continuous ρ := by
    have := h.contΨ
    have : ρ = fun x => Ψ (1, x) := funext fun x => (h.one x).symm
    rw [this]
    fun_prop
  have hcl : ∀ e : Set S, closure (ρ '' e) = ρ '' closure e := fun e =>
    (image_closure_subset_closure_image hρc).antisymm' (closure_minimal (image_mono subset_closure)
      (hρc.isClosedMap _ isClosed_closure))
  -- A vertex of `G` on an edge of `E₁` lies in `VF`.
  have hVF : ∀ e ∈ E₁, ∀ w ∈ closure e, w ∈ G.V → w ∈ G₁.V ∧ ρ w ∈ H₂.V := fun e he w hw hwV => by
    have h1 : w ∈ G₁.V := mem_V_of_subdrawing h.sub (G₁.closure_subset_U he.1 hw) hwV
    refine ⟨h1, mem_V_of_subdrawing hH₂G (H₂.closure_subset_U he.2 (hclE e he.1 w hw))
      (h.imV ▸ mem_image_of_mem ρ h1)⟩
  have hEG : EF ⊆ G.E := by
    rintro e (he | he)
    · exact h.sub.2 he.1
    · obtain ⟨x, hx, he⟩ := mem_iUnion₂.mp he
      exact (hTsub x hx).2 he
  have hFV' : G.spanV VF EF = VF := by
    exact lifted_forest_span_vertices (S := S) (G := G) (G₁ := G₁) (G' := G') (ρ := ρ) (Ψ := Ψ) (X
      := X) (A := A) (Tr := Tr) h H₂    hTsub hVF
  set F : Drawing S := G.span VF EF with hF
  have hFV : F.V = VF := hFV'
  have hFE : F.E = EF := by
    rw [hF, G.span_E]
    exact inter_eq_left.mpr hEG
  have hFG : F.IsSubdrawing G := ⟨G.spanV_subset _ _, by rw [hFE]; exact hEG⟩
  have hTF : ∀ x ∈ X, (Tr x).IsSubdrawing F := fun x hx => ⟨fun w hw => hFV ▸ .inl
    (mem_iUnion₂.mpr ⟨x, hx, hw⟩), fun e he => hFE ▸ .inr (mem_iUnion₂.mpr ⟨x, hx, he⟩)⟩
  have hFcase : ∀ a ∈ F.V, a ∈ A ∨ (ρ a ∈ X ∧ a ∈ (Tr (ρ a)).V) := fun a ha => by
    rw [hFV] at ha
    rcases ha with ha | ha
    · obtain ⟨x, hx, ha⟩ := mem_iUnion₂.mp ha
      have h1 := hρT x hx a ((Tr x).V_subset_U ha)
      rw [← h1] at hx ha
      exact .inr ⟨hx, ha⟩
    · exact h.vert a ha.1
  have hFρ : ∀ a ∈ F.V, ρ a ∈ H₂.V := fun a ha => by
    rw [hFV] at ha
    rcases ha with ha | ha
    · obtain ⟨x, hx, ha⟩ := mem_iUnion₂.mp ha
      rw [hρT x hx a ((Tr x).V_subset_U ha)]
      exact hXV x hx
    · exact ha.2
  have hFU : ∀ a ∈ F.U, ρ a ∈ H₂.U := fun a ha => by
    exact forest_lift_maps_into_forest (S := S) (G := G) (G₁ := G₁) (ρ := ρ) (X := X) (Tr := Tr)
      H₂ hXV VF hρT hclE hFρ a ha
  have hFVb : F.V ∩ bd S = X := by
    refine subset_antisymm ?_ ?_
    · rintro x ⟨hx, hb⟩
      rw [h.X_eq]
      exact ⟨hFG.1 hx, hb⟩
    · intro x hx
      exact ⟨(hTF x hx).1 (h.tree x hx).2.2.1, (h.X_eq ▸ hx : x ∈ G.V ∩ bd S).2⟩
  have hFp : F.IsProper := fun x hx => mem_V_of_subdrawing hFG hx.2 (hG ⟨hx.1, hFG.U_subset hx.2⟩)
  -- A link over an edge of `E₁`.
  have hcap : ∀ e ∈ G₁.E, closure (ρ '' e) ∩ G'.V = ρ '' (closure e ∩ G₁.V) := fun e he => by
    rw [hcl, h.imV]
    refine subset_antisymm ?_ (image_inter_subset _ _ _)
    rintro _ ⟨⟨z, hz, rfl⟩, ⟨v, hv, hvz⟩⟩
    by_cases hzV : z ∈ G₁.V
    · exact mem_image_of_mem ρ ⟨hz, hzV⟩
    · have h1 := h.inj z (h.off ⟨G₁.closure_subset_U he hz, hzV⟩) v hvz
      exact absurd (h1 ▸ hv) hzV
  have hlink : ∀ {e a b}, e ∈ E₁ → F.toGraph.IsLink e a b → H₂.toGraph.IsLink (ρ '' e) (ρ a) (ρ b)
    := fun {e a b} he hl => by
    have hg : G.toGraph.IsLink e a b := (hFG.isLink_iff (hFE ▸ .inl he)).mp hl
    have hg₁ : G₁.toGraph.IsLink e a b := (h.sub.isLink_iff he.1).mpr hg
    refine (hH₂G.isLink_iff he.2).mpr ⟨h.imE ▸ mem_image_of_mem _ he.1,
      h.imV ▸ mem_image_of_mem ρ hg₁.2.1, h.imV ▸ mem_image_of_mem ρ hg₁.2.2.1, ?_⟩
    rw [hcap e he.1, hg₁.2.2.2, image_pair]
  have htreeLink : ∀ {e a b}, e ∉ E₁ → F.toGraph.IsLink e a b → ρ a = ρ b ∧ ∃ x ∈ X, e ∈ (Tr x).E
    ∧ a ∈ (Tr x).V ∧ b ∈ (Tr x).V := fun {e a b} he hl => by
    have h1 : e ∈ EF := hFE ▸ hl.1
    rcases h1 with h1 | h1
    · exact absurd h1 he
    · obtain ⟨x, hx, h2⟩ := mem_iUnion₂.mp h1
      have h3 := hl.2.2.2
      have ha : a ∈ closure e := (h3.symm ▸ mem_insert a {b} : a ∈ closure e ∩ F.V).1
      have hb : b ∈ closure e := (h3.symm ▸ mem_insert_of_mem a rfl : b ∈ closure e ∩ F.V).1
      have hcl' := (Tr x).closure_subset_U h2
      refine ⟨by rw [hρT x hx a (hcl' ha), hρT x hx b (hcl' hb)], x, hx, h2, mem_V_of_subdrawing
        (hTsub x hx) (hcl' ha) (hFG.1 hl.2.1), mem_V_of_subdrawing (hTsub x hx) (hcl' hb)
          (hFG.1 hl.2.2.1)⟩
  have himage : ∀ {e e' : Set S}, e ∈ G₁.E → e' ∈ G₁.E → image ρ e = image ρ e' → e = e'
    := fun {e e'} he he' hi => by
    have hA' : ∀ {f}, f ∈ G₁.E → f ⊆ A := fun {f} hf => (hf.2.1).trans h.off
    have hsub : ∀ {f f' : Set S}, f ⊆ A → f' ⊆ A → image ρ f = image ρ f' → f ⊆ f'
      := fun {f f'} h1 h2 h3 z hz => by
      have h4 : ρ z ∈ ρ '' f' := h3 ▸ mem_image_of_mem ρ hz
      obtain ⟨z', hz', he'⟩ := h4
      rw [← h.inj z (h1 hz) z' he']
      exact hz'
    exact subset_antisymm (hsub (hA' he) (hA' he') hi) (hsub (hA' he') (hA' he) hi.symm)
  -- The projection of a trail of `F`.
  have hproj : ∀ {u v : S} (R : GraphWalk F.toGraph u v), R.edges.Nodup
    → ∃ R' : GraphWalk H₂.toGraph (ρ u) (ρ v), R'.edges.Nodup ∧ (∀ e' ∈ R'.edges, ∃ e ∈ R.edges, e
      ∈ E₁ ∧ e' = image ρ e) ∧ ∀ e ∈ R.edges, e ∈ E₁ → image ρ e ∈ R'.edges := by
    exact project_lifted_forest_walk (S := S) (ρ := ρ) (X := X) (Tr := Tr) H₂ E₁ F hFρ
      hlink htreeLink (fun he he' => himage he.1 he'.1)
  have hstay : ∀ {u v : S} (R : GraphWalk F.toGraph u v), (∀ e ∈ R.edges, e ∉ E₁) → ∀ x ∈ X, u ∈
    (Tr x).V → (∀ z ∈ R.support, z ∈ (Tr x).V) ∧ ∀ e ∈ R.edges, e ∈ (Tr x).E := by
    exact walk_without_uncontracted_edges_stays_in_tree (S := S) (ρ := ρ) (X := X) (Tr := Tr) E₁
      hρT F htreeLink
  have hFf : IsGraphForest F.toGraph := by
    exact lift_is_graph_forest (S := S) (G := G) (G₁ := G₁) (G' := G') (ρ := ρ) (Ψ := Ψ) (X := X)
      (A := A) (Tr := Tr) h H₂ hH₂f E₁ F hTF htreeLink hproj hstay
  have hfib : ∀ a ∈ F.V, ∀ b ∈ F.V, ρ a = ρ b → Nonempty (GraphWalk F.toGraph a b)
    := fun a ha b hb he => by
    rcases hFcase a ha with h1 | ⟨h1, h2⟩
    · rw [h.inj a h1 b he.symm]
      exact ⟨.nil ha⟩
    · rcases hFcase b hb with h3 | ⟨-, h4⟩
      · rw [h.inj b h3 a he]
        exact ⟨.nil hb⟩
      · rw [← he] at h4
        obtain ⟨R⟩ := (h.tree _ h1).2.2.2.2 a h2 b h4
        obtain ⟨R', -, -⟩ := (hTF _ h1).exists_walk_up R
        exact ⟨R'⟩
  have hup : ∀ {u v : S} (R : GraphWalk H₂.toGraph u v), ∀ a ∈ F.V, ρ a = u → ∀ b ∈ F.V, ρ b = v
    → Nonempty (GraphWalk F.toGraph a b) := by
    exact lift_walk_between_fibres (S := S) (G := G) (G₁ := G₁) (G' := G') (ρ := ρ) (Ψ := Ψ) (X :=
      X) (A := A) (Tr := Tr) h H₂ hH₂G hVF F hFV hFE hFG hcap hfib
  refine ⟨F, ⟨hFp, hFf⟩, ⟨β, hβ, (hH.map_homeo β).1, hFp, (hH.map_homeo β).2, hFf,
    hV₃.trans (hV.trans hFVb.symm), ?_⟩, hFG⟩
  intro s hs₁ t ht₁ hne
  have hsX : s ∈ X := by
    rw [← hV, ← hV₃]
    exact hs₁
  have htX : t ∈ X := by
    rw [← hV, ← hV₃]
    exact ht₁
  have hmemH : ∀ x ∈ X, x ∈ H₂.V ∩ bd S := fun x hx => hXH₂.symm ▸ hx
  have hsF : s ∈ F.V := (hFVb.symm ▸ hsX : s ∈ F.V ∩ bd S).1
  have htF : t ∈ F.V := (hFVb.symm ▸ htX : t ∈ F.V ∩ bd S).1
  have hp := hpaths s hs₁ t ht₁ hne
  have hdown : ∀ P₂ : GraphWalk F.toGraph s t, P₂.IsSimple → ∃ R : GraphWalk H₂.toGraph s t,
    R.IsSimple := fun P₂ hP₂ => by
    obtain ⟨R', -, -, -⟩ := hproj P₂ hP₂.edges_nodup
    rw [hρX s hsX, hρX t htX] at R'
    obtain ⟨R, hR, -, -⟩ := GM09.exists_isSimple_subwalk R'
    exact ⟨R, hR⟩
  refine ⟨⟨fun ⟨P₁, hP₁⟩ => ?_, fun ⟨P₂, hP₂⟩ => hp.1.mpr (hdown P₂ hP₂)⟩, ?_⟩
  · obtain ⟨R, -⟩ := hp.1.mp ⟨P₁, hP₁⟩
    obtain ⟨W⟩ := hup R s hsF (hρX s hsX) t htF (hρX t htX)
    obtain ⟨P, hP, -, -⟩ := GM09.exists_isSimple_subwalk W
    exact ⟨P, hP⟩
  · intro P₁ P₂ φ₁ φ₂ hP₁ hP₂ ht₁' ht₂
    obtain ⟨R, hR⟩ := hdown P₂ hP₂
    obtain ⟨φ'', hφ''⟩ := exists_curveTracesWalk R
    have ha := hp.2 P₁ R φ₁ φ'' hP₁ hR ht₁' hφ''
    let κ : Curve S := ⟨fun u => ρ (φ₂ u), hρc.comp φ₂.continuous⟩
    have hκ : ∀ u, κ u = ρ (φ₂ u) := fun _ => rfl
    have h0 := ht₂.endpoints.1
    have h1 := ht₂.endpoints.2
    have hκr : range κ ⊆ H₂.U := by
      rintro _ ⟨u, rfl⟩
      exact hFU _ (CurveTracesWalk.range_subset P₂ φ₂ ht₂ (mem_range_self u))
    have hc : CurvesHomotopic φ'' κ := by
      refine IsFlat.curvesHomotopic (isFlat_U_of_forest hS hH₂f) (CurveTracesWalk.range_subset R
        φ'' hφ'') hκr ?_ ?_
      · rw [hφ''.endpoints.1, hκ, h0, hρX s hsX]
      · rw [hφ''.endpoints.2, hκ, h1, hρX t htX]
    have hd : CurvesHomotopic φ₂ κ := h.curvesHomotopic (h0 ▸ hsX) (h1 ▸ htX) hκ
    exact CurvesHomotopic.trans ha (CurvesHomotopic.trans hc (CurvesHomotopicIn.symm hd))

end GraphMinor.GM07
