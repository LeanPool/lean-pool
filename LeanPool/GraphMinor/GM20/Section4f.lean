/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section4e

/-!
# Graph Minors XX, Section 4, (4.11)

(4.11) says that passing to a complemented part `G₂` of `G₁` with the same roots keeps a set of
active
patchworks well-behaved. Edges outside `G₂` get a new incomparable label `*`, so an expansion keeps
`G₂` apart from the rest. The main point of the proof is `sameComponent_of_sides`: a component of a
realization of the whole meets the rest of the graph in vertices that are roots, and it has at most
one root, so its part inside `G₂` stays connected.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph GraphMinor.GM04

universe u v

variable {α : Type u} {β : Type v}

/-- The key step of (4.11). Let `H₁` be a graph whose edges lie either on the side `W`, where they
are
edges of `H₂`, or on the side `V₃`. If a set `C`, closed under adjacency in `H₁`, has at most one
vertex in both sides, then two vertices of `W` joined by a walk in `C` are in one component of `H₂`.
-/
theorem sameComponent_of_sides {H₁ H₂ : (⊤ : SimpleGraph α).Subgraph} {W V₃ C : Set α}
    (hWH : W ⊆ H₂.verts)
    (hadj : ∀ x y, H₁.Adj x y → (x ∈ W ∧ y ∈ W ∧ H₂.Adj x y) ∨ (x ∈ V₃ ∧ y ∈ V₃))
    (hC : ∀ x y, x ∈ C → H₁.Adj x y → y ∈ C)
    (hone : ∀ x ∈ C, ∀ y ∈ C, x ∈ W → y ∈ W → x ∈ V₃ → y ∈ V₃ → x = y)
    {a b : α} (ha : a ∈ W) (haC : a ∈ C) (hb : b ∈ W) (hab : sameComponent H₁ a b) :
    sameComponent H₂ a b := by
  obtain ⟨hp, hq, hr⟩ := sameComponent_iff.mp hab
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  have hrefl : sameComponent H₂ a a :=
    sameComponent_iff.mpr ⟨hWH ha, hWH ha, SimpleGraph.Reachable.refl _⟩
  suffices ∀ y : H₁.verts, Relation.ReflTransGen H₁.coe.Adj ⟨a, hp⟩ y → y.1 ∈ C ∧
      ((y.1 ∈ W ∧ sameComponent H₂ a y.1) ∨
        (y.1 ∈ V₃ ∧ ∃ z ∈ C, z ∈ W ∧ z ∈ V₃ ∧ sameComponent H₂ a z)) by
    obtain ⟨hbC, h | ⟨hb₃, z, hz, hzW, hz₃, hc⟩⟩ := this ⟨b, hq⟩ hr
    · exact h.2
    · exact hone b hbC z hz hb hzW hb₃ hz₃ ▸ hc
  intro y hy
  induction hy with
  | refl => exact ⟨haC, Or.inl ⟨ha, hrefl⟩⟩
  | @tail x y _ hxy ih =>
    obtain ⟨hxC, ih⟩ := ih
    have hxy' : H₁.Adj x.1 y.1 := hxy
    have hyC := hC _ _ hxC hxy'
    refine ⟨hyC, ?_⟩
    rcases hadj _ _ hxy' with ⟨hxW, hyW, hadj₂⟩ | ⟨hx₃, hy₃⟩
    · refine Or.inl ⟨hyW, ?_⟩
      rcases ih with ⟨-, hc⟩ | ⟨hx₃, z, hz, hzW, hz₃, hc⟩
      · exact hc.trans (sameComponent_of_adj hadj₂)
      · have : x.1 = z := hone _ hxC z hz hxW hzW hx₃ hz₃
        exact (this ▸ hc).trans (sameComponent_of_adj hadj₂)
    · rcases ih with ⟨hxW, hc⟩ | ⟨-, hz⟩
      · exact Or.inr ⟨hy₃, x.1, hxC, hxW, hx₃, hc⟩
      · exact Or.inr ⟨hy₃, hz⟩

/-- The label order of the proof of (4.11): `Ω` with a new element `*`, comparable only to itself.
-/
abbrev StarLabel (Ω : Type*) := DisjointUnionQuasiOrder Ω (Discrete Unit)

theorem wqo_starLabel {Ω : Type*} [Preorder Ω] (hΩ : WellQuasiOrderedLE Ω) :
    WellQuasiOrderedLE (StarLabel Ω) :=
  wqo_disjointUnion hΩ (wqo_discrete Unit)

theorem IsCompletionOf.mem_dom_iff {Ω Ω₁ : Type*} {P₁ : Patchwork Ω₁ α β} {Q : Patchwork Ω α β}
    (h : IsCompletionOf P₁ Q) {e : β} : e ∈ Q.dom ↔ e ∈ P₁.dom := by rw [h.dom_eq]

/-- `Q` is the complemented part of `S` of the proof of (4.11). -/
structure StarStep {Ω Ω₁ : Type*} (Q : Patchwork Ω α β) (S : Patchwork Ω₁ α β) : Prop where
  compl : IsComplemented S.G Q.G
  roots_eq : Q.G.roots = S.G.roots
  restr : IsCompletionOf (S.restrict Q.G) Q
  active : IsActive S

open Classical in
/-- The label of an edge of `S`: its label in `Q`, or `*` for an edge outside `Q`. -/
noncomputable def starLabel {Ω : Type*} (Q : Patchwork Ω α β) (e : β) : StarLabel Ω :=
  if e ∈ Q.G.edgeSet then Sum.inl (Q.φ e) else Sum.inr ()

theorem starLabel_le {Ω : Type*} [Preorder Ω] {Q Q' : Patchwork Ω α β} {e e' : β}
    (h : starLabel Q e ≤ starLabel Q' e') :
    (e ∈ Q.G.edgeSet ↔ e' ∈ Q'.G.edgeSet) ∧ (e ∈ Q.G.edgeSet → Q.φ e ≤ Q'.φ e') := by
  classical
  by_cases he : e ∈ Q.G.edgeSet <;> by_cases he' : e' ∈ Q'.G.edgeSet <;>
    simp only [starLabel, he, he', ↓reduceIte] at h
  · have hle : DisjointUnionLE _ _ := h
    cases hle with
    | inl h => exact ⟨iff_of_true he he', fun _ ↦ h⟩
  · exact nomatch (show DisjointUnionLE _ _ from h)
  · exact nomatch (show DisjointUnionLE _ _ from h)
  · exact ⟨iff_of_false he he', fun h' ↦ absurd h' he⟩

/-- The core of (4.11): a realizable expansion `η` of `S` in `S'` which keeps edges of `Q` and edges
outside `Q` apart gives a simulation of `Q` in `Q'`. -/
theorem simulated_of_starStep {Ω Ω₁ : Type*} [Preorder Ω] [Preorder Ω₁] {Q Q' : Patchwork Ω α β}
    {S S' : Patchwork Ω₁ α β} (hS : StarStep Q S) (hS' : StarStep Q' S') {ηv : α → Set α}
    {ηe : β → β} (hη : IsRealizableExpansion S S' ηv ηe)
    (hE : ∀ e ∈ S.G.edgeSet, e ∈ Q.G.edgeSet ↔ ηe e ∈ Q'.G.edgeSet)
    (hφ : ∀ e ∈ Q.G.edgeSet, Q.φ e ≤ Q'.φ (ηe e)) : Simulated Q Q' := by
  classical
  obtain ⟨hex, H, hH, hcomp⟩ := hη
  have hle := hS.compl.le
  have hle' := hS'.compl.le
  have hdom : Q.dom = S.dom ∩ Q.G.edgeSet := hS.restr.dom_eq.trans (Patchwork.restrict_dom hle)
  have hdom' : Q'.dom = S'.dom ∩ Q'.G.edgeSet := hS'.restr.dom_eq.trans
    (Patchwork.restrict_dom hle')
  have hμ : ∀ e ∈ Q.dom, Q.μ e = S.μ e := fun e he ↦ hS.restr.μ_eq (hS.restr.dom_eq ▸ he)
  have hμ' : ∀ e ∈ Q'.dom, Q'.μ e = S'.μ e := fun e he ↦ hS'.restr.μ_eq (hS'.restr.dom_eq ▸ he)
  have hΔ : ∀ e ∈ Q.G.edgeSet, Q.Δ e = S.Δ e := fun e he ↦
    (hS.restr.Δ_eq he).trans (Patchwork.restrict_Δ hle he)
  have hΔ' : ∀ e ∈ Q'.G.edgeSet, Q'.Δ e = S'.Δ e := fun e he ↦
    (hS'.restr.Δ_eq he).trans (Patchwork.restrict_Δ hle' he)
  have hsub : Q.G.edgeSet ⊆ S.G.edgeSet := hle.edgeSet_subset
  have hsub' : Q'.G.edgeSet ⊆ S'.G.edgeSet := hle'.edgeSet_subset
  have hinc : ∀ {e x}, e ∈ Q.G.edgeSet → (Q.G.Inc e x ↔ S.G.Inc e x) := fun he ↦
    inc_iff_of_le hle he
  have hinc' : ∀ {e x}, e ∈ Q'.G.edgeSet → (Q'.G.Inc e x ↔ S'.G.Inc e x) := fun he ↦
    inc_iff_of_le hle' he
  have hrl : Q.G.roots = S.G.roots := hS.roots_eq
  have hrl' : Q'.G.roots = S'.G.roots := hS'.roots_eq
  -- The new vertices of a term of a march of an edge of `Q` lie in `V(Q')`.
  have hμV : ∀ e ∈ Q.dom, ∀ y ∈ S'.μ (ηe e), y ∈ Q'.G.vertexSet := by
    intro e he y hy
    have heE : e ∈ Q.G.edgeSet := Q.dom_subset he
    have hd : ηe e ∈ S'.dom := (hex.mem_dom_iff e (hsub heE)).mp (hdom ▸ he).1
    have h₁ : y ∈ {x | x ∈ S'.μ (ηe e)} := hy
    rw [S'.μ_set _ hd] at h₁
    exact Q'.G.vertex_mem_of_inc ((hinc' ((hE e (hsub heE)).mp heE)).mpr h₁)
  have hrootV : ∀ (i : ℕ) (hi' : i < S'.G.roots.length), S'.G.roots[i] ∈ Q'.G.vertexSet := by
    intro i hi'
    have hm : ∀ r : List α, r = S'.G.roots → S'.G.roots[i] ∈ r := fun r hr ↦ by
      rw [hr]
      exact List.getElem_mem hi'
    exact Q'.G.roots_subset _ (hm _ hrl')
  -- This is (2) of the paper.
  have hne : ∀ v ∈ Q.G.vertexSet, (ηv v ∩ Q'.G.vertexSet).Nonempty := by
    intro v hv
    have hvS : v ∈ S.G.vertexSet := hle.vertexSet_subset hv
    by_cases hr : v ∈ Q.G.roots
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
      have hi₁ : i < S.G.roots.length := hrl ▸ hi
      have hi₂ : i < S'.G.roots.length := hex.roots_length ▸ hi₁
      have h₁ := hex.roots_mem i hi₁ hi₂
      simp only [hrl] at h₁ ⊢
      exact ⟨_, h₁, hrootV i hi₂⟩
    · obtain ⟨e, he, hinc₁⟩ := hS.active v hvS
      have heQ : e ∈ Q.G.edgeSet := by
        by_contra hn
        exact hr (hS.compl.inc_diff_mem hv ⟨S.dom_subset he, hn⟩ hinc₁)
      have hdQ : e ∈ Q.dom := hdom ▸ ⟨he, heQ⟩
      have hm : v ∈ S.μ e := by
        have : v ∈ S.G.ends e := hinc₁
        rw [← S.μ_set e he] at this
        exact this
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
      have hi₂ : i < (S'.μ (ηe e)).length := hex.μ_length e he ▸ hi
      exact ⟨_, hex.μ_mem e he i hi hi₂, hμV e hdQ _ (List.getElem_mem hi₂)⟩
  have hdomiff : ∀ e ∈ Q.G.edgeSet, e ∈ Q.dom ↔ e ∈ S.dom := fun e he ↦ by
    rw [hdom]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, he⟩⟩
  have hdomiff' : ∀ e ∈ Q'.G.edgeSet, e ∈ Q'.dom ↔ e ∈ S'.dom := fun e he ↦ by
    rw [hdom']
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, he⟩⟩
  have hexp : IsExpansion Q Q' (fun v ↦ ηv v ∩ Q'.G.vertexSet) ηe := by
    refine
    { vertex_nonempty := hne
      vertex_subset := fun v _ ↦ inter_subset_right
      edge_mem := fun e he ↦ (hE e (hsub he)).mp he
      vertex_disjoint := fun v₁ h₁ v₂ h₂ hne' ↦
        (hex.vertex_disjoint v₁ (hle.vertexSet_subset h₁) v₂ (hle.vertexSet_subset h₂) hne').mono
          inter_subset_left inter_subset_left
      edge_injOn := hex.edge_injOn.mono hsub
      mem_dom_iff := fun e he ↦ ?_
      ends_nonempty := fun e he hd x hx ↦ ?_
      μ_length := fun e he ↦ ?_
      μ_mem := fun e he i hi hi' ↦ ?_
      roots_length := ?_
      roots_mem := fun i hi hi' ↦ ?_
      maps_Δ := fun e he ↦ ?_
      φ_le := hφ }
    · rw [hdomiff e he, hdomiff' _ ((hE e (hsub he)).mp he)]
      exact hex.mem_dom_iff e (hsub he)
    · have hη' := (hE e (hsub he)).mp he
      obtain ⟨y, hy, hyinc⟩ := hex.ends_nonempty e (hsub he) (fun h ↦ hd ((hdomiff e he).mpr h)) x
        ((hinc he).mp hx)
      have h₁ := (hinc' hη').mpr hyinc
      exact ⟨y, ⟨hy, Q'.G.vertex_mem_of_inc h₁⟩, h₁⟩
    · have heE := Q.dom_subset he
      have hdS := (hdomiff e heE).mp he
      have hd' : ηe e ∈ Q'.dom :=
        (hdomiff' _ ((hE e (hsub heE)).mp heE)).mpr ((hex.mem_dom_iff e (hsub heE)).mp hdS)
      rw [hμ e he, hμ' _ hd']
      exact hex.μ_length e hdS
    · have heE := Q.dom_subset he
      have hdS := (hdomiff e heE).mp he
      have hd' : ηe e ∈ Q'.dom :=
        (hdomiff' _ ((hE e (hsub heE)).mp heE)).mpr ((hex.mem_dom_iff e (hsub heE)).mp hdS)
      simp only [hμ e he, hμ' _ hd'] at hi hi' ⊢
      exact ⟨hex.μ_mem e hdS i hi hi', hμV e he _ (List.getElem_mem hi')⟩
    · rw [hrl, hrl']
      exact hex.roots_length
    · simp only [hrl, hrl'] at hi hi' ⊢
      exact ⟨hex.roots_mem i hi hi', hrootV i hi'⟩
    · have heE := Q.dom_subset he
      have hdS := (hdomiff e heE).mp he
      have hηE := (hE e (hsub heE)).mp heE
      have hd' : ηe e ∈ Q'.dom :=
        (hdomiff' _ hηE).mpr ((hex.mem_dom_iff e (hsub heE)).mp hdS)
      rw [hμ e he, hμ' _ hd', hΔ e heE, hΔ' _ hηE]
      exact hex.maps_Δ e hdS
  obtain ⟨δ, hδ, hHeq⟩ := id hH
  let H₂ := realizationOf (Q'.deleteEdges (ηe '' Q.G.edgeSet)).G.toHypergraph δ
  have hmemS : ∀ e' ∈ Q'.G.edgeSet, e' ∉ ηe '' Q.G.edgeSet → e' ∉ ηe '' S.G.edgeSet := by
    rintro e' he' hn ⟨e, he, rfl⟩
    exact hn ⟨e, (hE e he).mpr he', rfl⟩
  have hH₂ : (Q'.deleteEdges (ηe '' Q.G.edgeSet)).IsRealization H₂ := by
    refine ⟨δ, fun e' he' ↦ ?_, rfl⟩
    change δ e' ∈ Q'.Δ e'
    rw [hΔ' e' he'.1]
    exact hδ e' ⟨hsub' he'.1, hmemS e' he'.1 he'.2⟩
  have hvH₂ : H₂.verts = Q'.G.vertexSet := hH₂.verts_eq
  have hδverts : ∀ e' ∈ S'.G.edgeSet \ ηe '' S.G.edgeSet, (δ e').verts = S'.G.ends e'
    := fun e' he' ↦
    ((S'.Δ e').verts_eq _ (hδ e' he')).trans (S'.Δ_verts e' he'.1)
  have hH₂le : ∀ a b, H₂.Adj a b → H.Adj a b := by
    intro a b hab
    obtain ⟨e', he', hadj⟩ := realizationOf_adj.mp hab
    rw [hHeq]
    exact realizationOf_adj.mpr ⟨e', ⟨hsub' he'.1, hmemS e' he'.1 he'.2⟩, hadj⟩
  refine ⟨fun v ↦ ηv v ∩ Q'.G.vertexSet, ηe, hexp, H₂, hH₂, fun v hv ↦ ?_⟩
  have hvS := hle.vertexSet_subset hv
  obtain ⟨D₀, hD₀, hDv⟩ := hcomp v hvS
  have hclosed : ∀ x y, x ∈ ηv v → H.Adj x y → y ∈ ηv v := by
    intro x y hx hxy
    obtain ⟨D₁, hD₁, hx₁, hy₁⟩ := sameComponent_iff_connectedIn.mp (sameComponent_of_adj hxy)
    have heq := hD₁.eq_of_mem hD₀ hx₁ (hDv ▸ hx)
    rw [← hDv, ← heq]
    exact hy₁
  rw [exists_isComponent_verts_eq_iff (hne v hv) (by rw [hvH₂]; exact inter_subset_right)]
  refine ⟨fun a ha b hab ↦ ⟨hclosed a b ha.1 (hH₂le a b hab), ?_⟩, fun a ha b hb ↦ ?_⟩
  · have := H₂.edge_vert hab.symm
    rwa [hvH₂] at this
  · refine sameComponent_of_sides (H₁ := H) (W := Q'.G.vertexSet) (C := ηv v)
      (V₃ := {x | ∃ e ∈ S'.G.edgeSet \ Q'.G.edgeSet, S'.G.Inc e x}) hvH₂.ge ?_ hclosed ?_ ha.2 ha.1
      hb.2 (sameComponent_iff_connectedIn.mpr ⟨D₀, hD₀, hDv ▸ ha.1, hDv ▸ hb.1⟩)
    · intro x y hxy
      rw [hHeq] at hxy
      obtain ⟨e', he', hadj⟩ := realizationOf_adj.mp hxy
      have hx : x ∈ S'.G.ends e' := hδverts e' he' ▸ (δ e').edge_vert hadj
      have hy : y ∈ S'.G.ends e' := hδverts e' he' ▸ (δ e').edge_vert hadj.symm
      by_cases heQ : e' ∈ Q'.G.edgeSet
      · refine Or.inl ⟨Q'.G.vertex_mem_of_inc ((hinc' heQ).mpr hx),
          Q'.G.vertex_mem_of_inc ((hinc' heQ).mpr hy), realizationOf_adj.mpr ⟨e', ⟨heQ, ?_⟩, hadj⟩⟩
        rintro ⟨e, he, rfl⟩
        exact he'.2 ⟨e, hsub he, rfl⟩
      · exact Or.inr ⟨⟨e', ⟨he'.1, heQ⟩, hx⟩, ⟨e', ⟨he'.1, heQ⟩, hy⟩⟩
    · -- Both vertices are roots of `Q'` in `η(v)`, and an expansion gives `η(v)` one root.
      have hroot : ∀ x ∈ ηv v, x ∈ Q'.G.vertexSet →
          (∃ e ∈ S'.G.edgeSet \ Q'.G.edgeSet, S'.G.Inc e x) →
          ∃ (i : ℕ) (hi : i < S'.G.roots.length) (hi₀ : i < S.G.roots.length),
            S'.G.roots[i] = x ∧ S.G.roots[i] = v := by
        rintro x hx hxV ⟨e, he, hinc₁⟩
        have hm : x ∈ Q'.G.roots := hS'.compl.inc_diff_mem hxV he hinc₁
        rw [hrl'] at hm
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
        have hi₀ : i < S.G.roots.length := hex.roots_length ▸ hi
        refine ⟨i, hi, hi₀, rfl, ?_⟩
        by_contra hnv
        have hrV : S.G.roots[i] ∈ S.G.vertexSet := S.G.roots_subset _ (List.getElem_mem hi₀)
        exact Set.disjoint_left.mp (hex.vertex_disjoint _ hrV v hvS hnv)
          (hex.roots_mem i hi₀ hi) hx
      intro x hx y hy hxW hyW hx₃ hy₃
      obtain ⟨i, hi, hi₀, rfl, h₁⟩ := hroot x hx hxW hx₃
      obtain ⟨j, hj, hj₀, rfl, h₂⟩ := hroot y hy hyW hy₃
      have hij : i = j := (S.G.roots_nodup.getElem_inj_iff).mp (h₁.trans h₂.symm)
      subst hij
      rfl

/-- Graph Minors XX, (4.11) (page 334): "Let $\mathcal{F}_1$ be a well-behaved set of active
patchworks, and let $\mathcal{F}_2$ be
the set of all patchworks $P_2 = (G_2, \mu_2, \Delta_2)$ such that there exists $P_1 = (G_1,
\mu_1, \Delta_1) \in \mathcal{F}_1$ with $G_2 \subseteq G_1$, $\pi(G_2) = \pi(G_1)$, $G_2$
complemented in $G_1$ and $P_2 = P_1|G_2$. Then $\mathcal{F}_2$ is well-behaved." -/
theorem theorem_4_11_proof {𝓕₁ : Set (UnlabeledPatchwork α β)} (h : WellBehaved 𝓕₁)
    (ha : ∀ P ∈ 𝓕₁, IsActive P) :
    WellBehaved {P₂ | ∃ P₁ ∈ 𝓕₁, IsComplemented P₁.G P₂.G ∧ P₂.G.roots = P₁.G.roots ∧
      IsCompletionOf (P₁.restrict P₂.G) P₂} := by
  refine wellBehaved_of_encoding h fun Ω₂ _ hΩ₂ ↦ ⟨StarLabel Ω₂, inferInstance, wqo_starLabel hΩ₂,
    fun Q S ↦ StarStep Q S ∧ ∀ e, S.φ e = starLabel Q e, ?_, ?_⟩
  · rintro Q ⟨P₂, ⟨P₁, hP₁, hc, hr, hres⟩, hQ⟩
    have hG : Q.G = P₂.G := hQ.G_eq
    have hrel : IsCompletionOf (P₁.restrict P₂.G)
        ((P₁.relabel (starLabel Q)).restrict P₂.G) :=
      ⟨rfl, rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
    refine ⟨P₁.relabel (starLabel Q), ⟨P₁, hP₁, isCompletionOf_relabel _ _⟩,
      ⟨?_, ?_, ?_, ha P₁ hP₁⟩, fun _ ↦ rfl⟩
    · rw [hG]
      exact hc
    · rw [hG]
      exact hr
    · rw [hG]
      exact hrel.symm.trans (hres.trans hQ)
  · rintro Q - Q' - S S' ⟨hS, hφ⟩ ⟨hS', hφ'⟩ ⟨ηv, ηe, hη⟩
    have hl : ∀ e ∈ S.G.edgeSet, _ := fun e he ↦ by
      have := hη.1.φ_le e he
      rw [hφ, hφ'] at this
      exact starLabel_le this
    exact simulated_of_starStep hS hS' hη (fun e he ↦ (hl e he).1)
      fun e he ↦ (hl e (hS.compl.le.edgeSet_subset he)).2 he

end GraphMinor.GM20
