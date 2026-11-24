/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section4b
public import LeanPool.GraphMinor.GM04.Patchwork.VerifyAxioms
public import LeanPool.GraphMinor.GM04.Patchwork.Menger

/-!
# Graph Minors XX, Section 4, (4.7) and (4.8)

The proofs of (4.7) and (4.9) have the same core. A patchwork `Q` arises from a patchwork `S` by
adding one vertex `v`, and changing a set `A` of edges of `dom(μ)` to have `v` as an end
(`VertexStep`). Each edge of `A` carries in its label a code of its new march and patch, in terms of
its march in `S` followed by `v`. If `S` is simulated in `S'` then `Q` is simulated in `Q'`
(`simulated_of_vertexStep`): we send `v` to `v'` and keep the rest.

The paper orders the labels of the new edges by simulation of one-edge patchworks. We use finite
codes and equality instead, which is enough and gives the well-quasi-order directly.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph GraphMinor.GM04

universe u v

variable {α : Type u} {β : Type v}

theorem sup_emptySubgraph_empty (δ : (⊤ : SimpleGraph α).Subgraph) :
    δ ⊔ emptySubgraph ∅ = δ := by
  apply le_antisymm (sup_le le_rfl _) le_sup_left
  exact ⟨by simp, fun _ _ h ↦ h.elim⟩

/-- Adding isolated vertices `X` to a realization `H` of `P` gives a realization of `Q`, if `Q` has
the extra vertices and the groupings of `P` with `X` added are groupings of `Q`. -/
theorem realization_sup_emptySubgraph {Ω Ω' : Type*} {P : Patchwork Ω α β} {Q : Patchwork Ω' α β}
    {H : (⊤ : SimpleGraph α).Subgraph} (X : Set α) (hH : P.IsRealization H)
    (hV : Q.G.vertexSet = P.G.vertexSet ∪ X) (hE : Q.G.edgeSet = P.G.edgeSet)
    (hΔ : ∀ e ∈ P.G.edgeSet, ∀ δ ∈ P.Δ e, δ ⊔ emptySubgraph (X ∩ Q.G.ends e) ∈ Q.Δ e) :
    Q.IsRealization (H ⊔ emptySubgraph X) := by
  have hv := hH.verts_eq
  obtain ⟨δ, hδ, rfl⟩ := hH
  refine ⟨fun e ↦ δ e ⊔ emptySubgraph (X ∩ Q.G.ends e), fun e he ↦ hΔ e (hE ▸ he) _ (hδ e
    (hE ▸ he)),
    ?_⟩
  have hv' := realizationOf_verts (G := Q.G.toHypergraph)
    (δ := fun e ↦ δ e ⊔ emptySubgraph (X ∩ Q.G.ends e)) fun e he ↦
    ((Q.Δ e).verts_eq _ (hΔ e (hE ▸ he) _ (hδ e (hE ▸ he)))).trans (Q.Δ_verts e he)
  apply SimpleGraph.Subgraph.ext
  · rw [hv']
    simp only [SimpleGraph.Subgraph.verts_sup, emptySubgraph_verts, hv, hV]
  · funext a b
    apply propext
    rw [realizationOf_adj]
    simp only [SimpleGraph.Subgraph.sup_adj, not_emptySubgraph_adj, or_false, realizationOf_adj, hE]

/-- `Q` arises from `S` by adding the vertex `v` and changing the edges in `A`. -/
structure VertexStep {Ω Ω' : Type*} (Q : Patchwork Ω α β) (S : Patchwork Ω' α β) (v : α) (A : Set β)
    (k : ℕ) : Prop where
  v_notMem : v ∉ S.G.vertexSet
  vertexSet_eq : Q.G.vertexSet = S.G.vertexSet ∪ {v}
  edgeSet_eq : Q.G.edgeSet = S.G.edgeSet
  dom_eq : Q.dom = S.dom
  A_subset : A ⊆ S.dom
  ends_ne : ∀ e ∈ S.G.edgeSet, e ∉ A → Q.G.ends e = S.G.ends e
  μ_ne : ∀ e ∈ S.dom, e ∉ A → Q.μ e = S.μ e
  Δ_ne : ∀ e ∈ S.G.edgeSet, e ∉ A → Q.Δ e = S.Δ e
  μ_subset : ∀ e ∈ A, ∀ x ∈ Q.μ e, x ∈ S.μ e ++ [v]
  length_le : ∀ e ∈ A, (S.μ e ++ [v]).length ≤ k

/-- The expansion `η` with the new vertex `v` sent to `{v'}`. -/
noncomputable def addVertex (ηv : α → Set α) (v v' : α) : α → Set α := by
  classical exact fun x ↦ if x = v then {v'} else ηv x

theorem addVertex_self (ηv : α → Set α) (v v' : α) : addVertex ηv v v' v = {v'} := by
  simp [addVertex]

theorem addVertex_of_ne {ηv : α → Set α} {v v' x : α} (h : x ≠ v) :
    addVertex ηv v v' x = ηv x := by
  simp [addVertex, h]

/-- The core of (4.7) and (4.9): a realizable expansion of `S` in `S'` gives a simulation of `Q` in
`Q'`, when edges of `A` go to edges of `A'` with the same codes. -/
theorem simulated_of_vertexStep {Ω Ω₁ : Type*} [Preorder Ω] [Preorder Ω₁] {Q Q' : Patchwork Ω α β}
    {S S' : Patchwork Ω₁ α β} {v v' : α} {A A' : Set β} {k : ℕ} (hS : VertexStep Q S v A k)
    (hS' : VertexStep Q' S' v' A' k) {ηv : α → Set α} {ηe : β → β}
    (hη : IsRealizableExpansion S S' ηv ηe) (hA : ∀ e ∈ S.G.edgeSet, e ∈ A ↔ ηe e ∈ A')
    (hcode : ∀ e ∈ A, edgeCode k (S.μ e ++ [v]) Q e = edgeCode k (S'.μ (ηe e) ++ [v']) Q' (ηe e))
    (hφ : ∀ e ∈ S.G.edgeSet, Q.φ e ≤ Q'.φ (ηe e))
    (hlen : Q.G.roots.length = Q'.G.roots.length)
    (hroots : ∀ (i : ℕ) (hi : i < Q.G.roots.length) (hi' : i < Q'.G.roots.length),
      Q'.G.roots[i] ∈ addVertex ηv v v' Q.G.roots[i])
    (hΔ' : ∀ e ∈ S'.G.edgeSet \ ηe '' S.G.edgeSet, ∀ δ ∈ S'.Δ e,
      δ ⊔ emptySubgraph ({v'} ∩ Q'.G.ends e) ∈ Q'.Δ e) :
    Simulated Q Q' := by
  obtain ⟨hex, H, hH, hcomp⟩ := hη
  have hne : ∀ {x}, x ∈ S.G.vertexSet → x ≠ v := fun hx h ↦ hS.v_notMem (h ▸ hx)
  have hne' : ∀ {x}, x ∈ S'.G.vertexSet → x ≠ v' := fun hx h ↦ hS'.v_notMem (h ▸ hx)
  have hη₂ : ∀ {x}, x ∈ S.G.vertexSet → addVertex ηv v v' x = ηv x := fun hx ↦
    addVertex_of_ne (hne hx)
  have hV : ∀ {x}, x ∈ Q.G.vertexSet → x ∈ S.G.vertexSet ∨ x = v := fun {x} hx ↦ by
    rw [hS.vertexSet_eq] at hx
    exact hx
  have hincA : ∀ {e x}, e ∉ A → Q.G.Inc e x → S.G.Inc e x := by
    intro e x heA hx
    have heS : e ∈ S.G.edgeSet := hS.edgeSet_eq ▸ Q.G.edge_mem_of_inc hx
    have : x ∈ Q.G.ends e := hx
    rw [hS.ends_ne e heS heA] at this
    exact this
  have hμmem : ∀ {R : Patchwork Ω₁ α β} {e x}, e ∈ R.dom → x ∈ R.μ e → x ∈ R.G.vertexSet := by
    intro R e x he hx
    have h₁ : x ∈ {x | x ∈ R.μ e} := hx
    rw [R.μ_set e he] at h₁
    exact R.G.vertex_mem_of_inc h₁
  have hdomA : ∀ {e}, e ∈ A → e ∈ S.G.edgeSet := fun he ↦ S.dom_subset (hS.A_subset he)
  have hμlen : ∀ e ∈ A, (Q.μ e).length = (Q'.μ (ηe e)).length := by
    intro e he
    have he' := (hA e (hdomA he)).mp he
    have h₁ := hcode e he
    simp only [edgeCode, Prod.mk.injEq] at h₁
    have hd : e ∈ Q.dom := hS.dom_eq ▸ hS.A_subset he
    have hd' : ηe e ∈ Q'.dom := hS'.dom_eq ▸ hS'.A_subset he'
    exact length_eq_of_code (hS.length_le e he) (hS'.length_le _ he') (Q.μ_nodup e hd)
      (Q'.μ_nodup _ hd') (hS.μ_subset e he) (hS'.μ_subset _ he') h₁.2.2.1
  have hposition : ∀ e ∈ A, ∀ (i : Fin k) (x y : α), (S.μ e ++ [v])[i.1]? = some x →
      (S'.μ (ηe e) ++ [v'])[i.1]? = some y → y ∈ addVertex ηv v v' x := by
    intro e he i x y hx hy
    have hSd := hS.A_subset he
    have hL := hex.μ_length e hSd
    by_cases hi : i.1 < (S.μ e).length
    · have hi' : i.1 < (S'.μ (ηe e)).length := hL ▸ hi
      rw [List.getElem?_append_left hi] at hx
      rw [List.getElem?_append_left hi'] at hy
      obtain ⟨hl, h₂⟩ := List.getElem?_eq_some_iff.mp hx
      obtain ⟨hl', h₂'⟩ := List.getElem?_eq_some_iff.mp hy
      have hm := hex.μ_mem e hSd i.1 hl hl'
      rw [h₂, h₂'] at hm
      rw [hη₂ (hμmem hSd (h₂ ▸ List.getElem_mem hl))]
      exact hm
    · have hi' : ¬ i.1 < (S'.μ (ηe e)).length := hL ▸ hi
      rw [List.getElem?_append_right (by omega)] at hx
      rw [List.getElem?_append_right (by omega)] at hy
      have h₁ : i.1 - (S.μ e).length = 0 := by
        have := (List.getElem?_eq_some_iff.mp hx).1
        simp only [List.length_singleton] at this
        omega
      have h₂ : i.1 - (S'.μ (ηe e)).length = 0 := by rw [← hL]; exact h₁
      rw [h₁] at hx
      rw [h₂] at hy
      have e₁ : v = x := by simpa using hx
      have e₂ : v' = y := by simpa using hy
      rw [← e₁, ← e₂, addVertex_self]
      rfl
  refine ⟨addVertex ηv v v', ηe, ?_, H ⊔ emptySubgraph {v'}, ?_, ?_⟩
  · refine
    { vertex_nonempty := fun x hx ↦ ?_
      vertex_subset := fun x hx y hy ↦ ?_
      edge_mem := fun e he ↦ ?_
      vertex_disjoint := fun x₁ h₁ x₂ h₂ hx ↦ ?_
      edge_injOn := hS.edgeSet_eq ▸ hex.edge_injOn
      mem_dom_iff := fun e he ↦ ?_
      ends_nonempty := fun e he hd x hx ↦ ?_
      μ_length := fun e he ↦ ?_
      μ_mem := fun e he i hi hi' ↦ ?_
      roots_length := hlen
      roots_mem := hroots
      maps_Δ := fun e he ↦ ?_
      φ_le := fun e he ↦ hφ e (hS.edgeSet_eq ▸ he) }
    · rcases hV hx with hx | rfl
      · rw [hη₂ hx]
        exact hex.vertex_nonempty x hx
      · rw [addVertex_self]
        exact singleton_nonempty _
    · rw [hS'.vertexSet_eq]
      rcases hV hx with hx | rfl
      · rw [hη₂ hx] at hy
        exact Or.inl (hex.vertex_subset x hx hy)
      · rw [addVertex_self] at hy
        exact Or.inr hy
    · rw [hS'.edgeSet_eq]
      exact hex.edge_mem e (hS.edgeSet_eq ▸ he)
    · rcases hV h₁ with h₁ | rfl <;> rcases hV h₂ with h₂ | rfl
      · rw [hη₂ h₁, hη₂ h₂]
        exact hex.vertex_disjoint x₁ h₁ x₂ h₂ hx
      · rw [hη₂ h₁, addVertex_self, Set.disjoint_singleton_right]
        exact fun hmem ↦ hS'.v_notMem (hex.vertex_subset x₁ h₁ hmem)
      · rw [hη₂ h₂, addVertex_self, Set.disjoint_singleton_left]
        exact fun hmem ↦ hS'.v_notMem (hex.vertex_subset x₂ h₂ hmem)
      · exact absurd rfl hx
    · rw [hS.dom_eq, hS'.dom_eq]
      exact hex.mem_dom_iff e (hS.edgeSet_eq ▸ he)
    · have heS : e ∈ S.G.edgeSet := hS.edgeSet_eq ▸ he
      have hdS : e ∉ S.dom := hS.dom_eq ▸ hd
      have heA : e ∉ A := fun h ↦ hdS (hS.A_subset h)
      have hxS := hincA heA hx
      obtain ⟨y, hy, hinc⟩ := hex.ends_nonempty e heS hdS x hxS
      rw [hη₂ (S.G.vertex_mem_of_inc hxS)]
      have heA' : ηe e ∉ A' := fun h ↦ heA ((hA e heS).mpr h)
      refine ⟨y, hy, ?_⟩
      have : y ∈ Q'.G.ends (ηe e) := by
        rw [hS'.ends_ne _ (hex.edge_mem e heS) heA']
        exact hinc
      exact this
    · by_cases heA : e ∈ A
      · exact hμlen e heA
      · have hdS : e ∈ S.dom := hS.dom_eq ▸ he
        have heA' : ηe e ∉ A' := fun h ↦ heA ((hA e (S.dom_subset hdS)).mpr h)
        rw [hS.μ_ne e hdS heA, hS'.μ_ne _ ((hex.mem_dom_iff e (S.dom_subset hdS)).mp hdS) heA']
        exact hex.μ_length e hdS
    · by_cases heA : e ∈ A
      · have h₁ := hcode e heA
        simp only [edgeCode, Prod.mk.injEq] at h₁
        have heA' := (hA e (hdomA heA)).mp heA
        have hx := hS.μ_subset e heA _ (List.getElem_mem hi)
        obtain ⟨j, hj⟩ := exists_index (hS.length_le e heA) hx
        have hdQ : e ∈ Q.dom := hS.dom_eq ▸ hS.A_subset heA
        obtain ⟨y, hy, hyj⟩ := marchCode_forward h₁.2.2.1
          ((length_le_of_subset (Q.μ_nodup e hdQ) (hS.μ_subset e heA)).trans (hS.length_le e heA))
          (List.getElem?_eq_getElem hi) hj
        rw [List.getElem?_eq_getElem hi'] at hy
        rw [Option.some.inj hy]
        exact hposition e heA j _ y hj hyj
      · have hdS : e ∈ S.dom := hS.dom_eq ▸ he
        have heA' : ηe e ∉ A' := fun h ↦ heA ((hA e (S.dom_subset hdS)).mpr h)
        have hd' := (hex.mem_dom_iff e (S.dom_subset hdS)).mp hdS
        have e₁ := hS.μ_ne e hdS heA
        have e₂ := hS'.μ_ne _ hd' heA'
        simp only [e₁, e₂] at hi hi' ⊢
        rw [hη₂ (hμmem hdS (List.getElem_mem hi))]
        exact hex.μ_mem e hdS i hi hi'
    · by_cases heA : e ∈ A
      · have h₁ := hcode e heA
        simp only [edgeCode, Prod.mk.injEq] at h₁
        have heA' := (hA e (hdomA heA)).mp heA
        have hdQ : e ∈ Q.dom := hS.dom_eq ▸ hS.A_subset heA
        have hdQ' : ηe e ∈ Q'.dom := hS'.dom_eq ▸ hS'.A_subset heA'
        refine mapsTo_of_code (hS.length_le e heA) (hS'.length_le _ heA') (Q.μ_nodup e hdQ)
          (Q'.μ_nodup _ hdQ') (hS.μ_subset e heA) (hS'.μ_subset _ heA') ?_ ?_ h₁.2.2.1 h₁.2.2.2
        · rw [Q.Δ_verts e (Q.dom_subset hdQ), Q.μ_set e hdQ]
        · rw [Q'.Δ_verts _ (Q'.dom_subset hdQ'), Q'.μ_set _ hdQ']
      · have hdS : e ∈ S.dom := hS.dom_eq ▸ he
        have heS := S.dom_subset hdS
        have heA' : ηe e ∉ A' := fun h ↦ heA ((hA e heS).mpr h)
        have hd' := (hex.mem_dom_iff e heS).mp hdS
        rw [hS.μ_ne e hdS heA, hS'.μ_ne _ hd' heA', hS.Δ_ne e heS heA,
          hS'.Δ_ne _ (S'.dom_subset hd') heA']
        exact hex.maps_Δ e hdS
  · have himg : ηe '' Q.G.edgeSet = ηe '' S.G.edgeSet := by rw [hS.edgeSet_eq]
    rw [himg]
    refine realization_sup_emptySubgraph {v'} hH ?_ ?_ ?_
    · exact hS'.vertexSet_eq
    · change Q'.G.edgeSet \ _ = S'.G.edgeSet \ _
      rw [hS'.edgeSet_eq]
    · intro e he δ hδ
      have hends : (Q'.deleteEdges (ηe '' S.G.edgeSet)).G.ends e = Q'.G.ends e := by
        ext x
        exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, he.2⟩⟩
      change _ ∈ Q'.Δ e
      rw [hends]
      exact hΔ' e he δ hδ
  · intro x hx
    have hHv : H.verts = S'.G.vertexSet := hH.verts_eq
    rcases hV hx with hx | rfl
    · obtain ⟨D, hD, hDv⟩ := hcomp x hx
      exact ⟨D, hD.sup_emptySubgraph _, by rw [hDv, hη₂ hx]⟩
    · refine ⟨_, ⟨⟨v', Or.inr rfl⟩, rfl⟩, ?_⟩
      rw [addVertex_self]
      exact component_sup_emptySubgraph_verts_of_notMem H (Set.mem_singleton v')
        (hHv ▸ hS'.v_notMem)

/-- The order on labels in the proofs of (4.7) and (4.9): the old labels, and a new copy for the
edges in `A`, which also carries a code. -/
abbrev StepLabel (Ω : Type*) (k : ℕ) := DisjointUnionQuasiOrder Ω (Discrete (EdgeCode k) × Ω)

theorem wqo_stepLabel {Ω : Type*} [Preorder Ω] (hΩ : WellQuasiOrderedLE Ω) (k : ℕ) :
    WellQuasiOrderedLE (StepLabel Ω k) := by
  have := wqo_discrete (EdgeCode k)
  exact wqo_disjointUnion hΩ inferInstance

open Classical in
/-- The label of an edge of `Q`, as a label of the matching edge of `S`. -/
noncomputable def stepLabel {Ω Ω' : Type*} (Q : Patchwork Ω α β) (S : Patchwork Ω' α β) (v : α)
    (A : Set β) (k : ℕ) (e : β) : StepLabel Ω k :=
  if e ∈ A then Sum.inr (edgeCode k (S.μ e ++ [v]) Q e, Q.φ e) else Sum.inl (Q.φ e)

/-- An inequality of step labels says that the edges are both in `A` and `A'` or neither, that the
old
labels do not go down, and that the codes agree. -/
theorem stepLabel_le {Ω Ω' Ω'' : Type*} [Preorder Ω] {Q Q' : Patchwork Ω α β} {S : Patchwork Ω' α β}
    {S' : Patchwork Ω'' α β} {v v' : α} {A A' : Set β} {k : ℕ} {e e' : β}
    (h : stepLabel Q S v A k e ≤ stepLabel Q' S' v' A' k e') :
    (e ∈ A ↔ e' ∈ A') ∧ Q.φ e ≤ Q'.φ e' ∧
      (e ∈ A → edgeCode k (S.μ e ++ [v]) Q e = edgeCode k (S'.μ e' ++ [v']) Q' e') := by
  classical
  by_cases he : e ∈ A <;> by_cases he' : e' ∈ A' <;>
    simp only [stepLabel, he, he', ↓reduceIte] at h
  · have hle : DisjointUnionLE _ _ := h
    cases hle with
    | inr h => exact ⟨iff_of_true he he', h.2, fun _ ↦ h.1⟩
  · exact nomatch (show DisjointUnionLE _ _ from h)
  · exact nomatch (show DisjointUnionLE _ _ from h)
  · have hle : DisjointUnionLE _ _ := h
    cases hle with
    | inl h => exact ⟨iff_of_false he he', h, fun h' ↦ absurd h' he⟩

/-- Graph Minors XX, (4.7) (page 332): "Let $\mathcal{F}_1$ be a well-behaved set of patchworks and
let $\mathcal{F}_2$ be a set of
patchworks each of which is a 1-vertex extension of a member of $\mathcal{F}_1$. Then
$\mathcal{F}_2$ is well-behaved." -/
theorem theorem_4_7_proof {𝓕₁ 𝓕₂ : Set (UnlabeledPatchwork α β)} (h : WellBehaved 𝓕₁)
    (h₂ : ∀ P₂ ∈ 𝓕₂, ∃ P₁ ∈ 𝓕₁, ∃ f v, IsOneVertexExtension P₁ P₂ f v) : WellBehaved 𝓕₂ := by
  classical
  obtain ⟨N, hN⟩ := theorem_4_1_proof h
  refine wellBehaved_of_encoding h fun Ω₂ _ hΩ₂ ↦
    ⟨StepLabel Ω₂ (N + 1), inferInstance, wqo_stepLabel hΩ₂ _, fun Q S ↦ ∃ f v,
      VertexStep Q S v {f} (N + 1) ∧ Q.G.roots = S.G.roots ∧
        ∀ e, S.φ e = stepLabel Q S v {f} (N + 1) e, ?_, ?_⟩
  · rintro Q ⟨P₂, hP₂, hQ⟩
    obtain ⟨P₁, hP₁, f, v, hx⟩ := h₂ P₂ hP₂
    have hb : SameBase P₂ Q := hQ.sameBase
    have hends : ∀ e, Q.G.ends e = P₂.G.ends e := fun e ↦ by simp only [Hypergraph.ends, hb.inc_eq]
    refine ⟨P₁.relabel (stepLabel Q P₁ v {f} (N + 1)), ⟨P₁, hP₁, isCompletionOf_relabel _ _⟩, f, v,
      ?_, ?_, fun _ ↦ rfl⟩
    · refine
      { v_notMem := hx.v_notMem
        vertexSet_eq := hb.vertexSet_eq.trans hx.vertexSet_eq
        edgeSet_eq := hb.edgeSet_eq.trans hx.edgeSet_eq
        dom_eq := hb.dom_eq.trans hx.dom_eq
        A_subset := singleton_subset_iff.mpr hx.f_mem
        ends_ne := fun e he hef ↦ (hends e).trans (hx.ends_ne e he hef)
        μ_ne := fun e he hef ↦ (hb.μ_eq (hx.dom_eq ▸ he)).trans (hx.μ_ne e he hef)
        Δ_ne := fun e he hef ↦ (hb.Δ_eq (hx.edgeSet_eq ▸ he)).trans (hx.Δ_ne e he hef)
        μ_subset := ?_
        length_le := ?_ }
      · rintro e rfl x hxm
        have hfd : e ∈ Q.dom := by rw [hb.dom_eq, hx.dom_eq]; exact hx.f_mem
        have h₁ : x ∈ {x | x ∈ Q.μ e} := hxm
        rw [Q.μ_set e hfd, hends, hx.ends_f, ← P₁.μ_set e hx.f_mem] at h₁
        rcases h₁ with h₁ | rfl
        · exact List.mem_append_left _ h₁
        · simp
      · rintro e rfl
        have := hN P₁ hP₁ e hx.f_mem
        simp only [List.length_append, List.length_singleton]
        exact Nat.succ_le_succ this
    · rw [hQ.G_eq, hx.roots_eq]
      rfl
  · rintro Q - Q' - S S' ⟨f, v, hS, hr, hφ⟩ ⟨f', v', hS', hr', hφ'⟩ ⟨ηv, ηe, hη⟩
    have hl : ∀ e ∈ S.G.edgeSet, _ := fun e he ↦ by
      have := hη.1.φ_le e he
      rw [hφ, hφ'] at this
      exact stepLabel_le this
    have hf : f ∈ S.G.edgeSet := S.dom_subset (hS.A_subset rfl)
    have hηf : ηe f = f' := (hl f hf).1.mp rfl
    refine simulated_of_vertexStep hS hS' hη (fun e he ↦ (hl e he).1) ?_ (fun e he ↦ (hl e he).2.1)
      ?_ ?_ ?_
    · rintro e rfl
      exact (hl e hf).2.2 rfl
    · rw [hr, hr']
      exact hη.1.roots_length
    · intro i hi hi'
      simp only [hr, hr'] at hi hi' ⊢
      rw [addVertex_of_ne fun h ↦ hS.v_notMem (by
        rw [← h]
        exact S.G.roots_subset _ (List.getElem_mem hi))]
      exact hη.1.roots_mem i hi hi'
    · rintro e ⟨he, hne⟩ δ hδ
      have hef : e ∉ ({f'} : Set β) := fun h ↦ hne ⟨f, hf, hηf.trans h.symm⟩
      rw [hS'.ends_ne e he hef, hS'.Δ_ne e he hef]
      have : ({v'} : Set α) ∩ S'.G.ends e = ∅ := by
        rw [Set.singleton_inter_eq_empty]
        exact fun h ↦ hS'.v_notMem (S'.G.vertex_mem_of_inc h)
      rw [this, sup_emptySubgraph_empty]
      exact hδ

/-- The members of `𝓕` extended `n` times by one vertex. -/
def extensions (𝓕 : Set (UnlabeledPatchwork α β)) : ℕ → Set (UnlabeledPatchwork α β)
  | 0 => 𝓕
  | n + 1 => {P₂ | ∃ P₁ ∈ extensions 𝓕 n, ∃ f v, IsOneVertexExtension P₁ P₂ f v}

/-- Graph Minors XX, (4.8) (page 333): "Let $\mathcal{F}_1$ be a well-behaved set of patchworks, let
$k \ge 0$, and let
$\mathcal{F}_2$ be the set of all patchworks $P_2$ such that there exist $P_1 \in
\mathcal{F}_1$ and a sequence* $$ P_1 = P^0, P^1, \dots, P^{k'} = P_2 $$ *where $k' \le k$
and for $1 \le i \le k'$, $P^i$ is a 1-vertex extension of $P^{i-1}$. Then $\mathcal{F}_2$
is well-behaved." -/
theorem theorem_4_8_proof {𝓕₁ : Set (UnlabeledPatchwork α β)} (h : WellBehaved 𝓕₁) (k : ℕ) :
    WellBehaved {P₂ | ∃ s : ℕ → UnlabeledPatchwork α β, ∃ k' ≤ k, s 0 ∈ 𝓕₁ ∧ s k' = P₂ ∧
      ∀ i < k', ∃ f v, IsOneVertexExtension (s i) (s (i + 1)) f v} := by
  have hn : ∀ n, WellBehaved (extensions 𝓕₁ n) := by
    intro n
    induction n with
    | zero => exact h
    | succ n ih => exact theorem_4_7_proof ih fun _ hP ↦ hP
  refine (WellBehaved.iUnion_lt (𝓕 := extensions 𝓕₁) (k + 1) fun i _ ↦ hn i).mono ?_
  rintro P₂ ⟨s, k', hk', h0, rfl, hs⟩
  have hmem : ∀ i ≤ k', s i ∈ extensions 𝓕₁ i := by
    intro i
    induction i with
    | zero => exact fun _ ↦ h0
    | succ i ih => exact fun hi ↦ ⟨s i, ih (by omega), hs i (by omega)⟩
  simp only [mem_iUnion, exists_prop]
  exact ⟨k', by omega, hmem k' le_rfl⟩

end GraphMinor.GM20
