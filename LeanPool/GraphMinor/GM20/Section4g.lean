/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section4f

/-!
# Graph Minors XX, Section 4, (4.12)

(4.12) replaces a piece `A` of a member of `𝓕₁` by a single edge `f`. We follow the paper's proof,
which uses (4.5), (4.11) and (4.6) in turn.

The paper's proof has one gap (see the correction to the proof of (4.12) in `corrections/GM20.md`).
It uses the roots `μ₂(f)` for the
patchwork without `f`, while `P₂ \ f` has the roots `π(G₁)`. And (4.6) needs the ends of `f` to be
roots. So we use the roots `π(G₁)` followed by the terms of `μ₂(f)` that are not yet roots, and at
the end we return to the roots of `P₂` by a further use of (4.5).

The file also has facts about `M(G, ℒ)` used for (4.13) and in Section 5.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph GraphMinor.GM04

universe u v

variable {α : Type u} {β : Type v}

theorem deleteEdges_deleteEdges {Ω : Type*} (P : Patchwork Ω α β) (F F' : Set β) :
    IsCompletionOf ((P.deleteEdges F).deleteEdges F') (P.deleteEdges (F ∪ F')) where
  G_eq := by
    refine RootedHypergraph.ext_of rfl ?_ ?_ rfl
    · change P.G.edgeSet \ (F ∪ F') = (P.G.edgeSet \ F) \ F'
      rw [Set.sdiff_sdiff]
    · funext e x
      apply propext
      change (P.G.Inc e x ∧ e ∉ F ∪ F') ↔ ((P.G.Inc e x ∧ e ∉ F) ∧ e ∉ F')
      simp [not_or, and_assoc]
  dom_eq := by
    change P.dom \ (F ∪ F') = (P.dom \ F) \ F'
    rw [Set.sdiff_sdiff]
  μ_eq _ _ := rfl
  Δ_eq _ _ := rfl

theorem ncard_march {m : List α} (hm : m.Nodup) : ({x | x ∈ m} : Set α).ncard = m.length := by
  classical
  have : ({x | x ∈ m} : Set α) = ↑m.toFinset := by
    ext x
    simp
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hm]

section Core

variable {G : RootedHypergraph α β} {ℒ : Set (RootedHypergraph α β)}

theorem mem_core_vertexSet {v : α} : v ∈ (rootedLocationCore G ℒ).vertexSet ↔ v ∈ G.vertexSet ∧
    ∀ A ∈ ℒ, v ∈ (complementHypergraph G A).vertexSet := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, fun A hA ↦ h₂ _ ⟨A, hA, rfl⟩⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁, ?_⟩
    rintro _ ⟨A, hA, rfl⟩
    exact h₂ A hA

theorem mem_core_edgeSet {e : β} : e ∈ (rootedLocationCore G ℒ).edgeSet ↔ e ∈ G.edgeSet ∧
    ∀ A ∈ ℒ, e ∉ A.edgeSet := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, fun A hA ↦ (h₂ _ ⟨A, hA, rfl⟩).2⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁, ?_⟩
    rintro _ ⟨A, hA, rfl⟩
    exact ⟨h₁, h₂ A hA⟩

/-- A vertex in `V(M(G, ℒ))` and in `V(A)` is a root of `A`. -/
theorem root_of_mem_core {A : RootedHypergraph α β} (hA : A ∈ ℒ) {v : α}
    (hv : v ∈ (rootedLocationCore G ℒ).vertexSet) (hvA : v ∈ A.vertexSet) : v ∈ A.rootSet := by
  rcases (mem_core_vertexSet.mp hv).2 A hA with h | h
  · exact absurd hvA h.2
  · exact h.2

/-- `M(G, ℒ)` is a subhypergraph of `G⁻`. -/
theorem core_le (hℒ : IsRootedLocation G ℒ) : rootedLocationCore G ℒ ≤ G.toHypergraph := by
  refine ⟨fun v h ↦ h.1, fun e h ↦ h.1, fun e he ↦ ?_⟩
  ext v
  constructor
  · intro hinc
    have hG : G.Inc e v := hinc
    refine ⟨hinc, ?_, ?_⟩
    · rintro _ ⟨A, hA, rfl⟩
      by_cases hvA : v ∈ A.vertexSet
      · have heA := (mem_core_edgeSet.mp he).2 A hA
        exact Or.inr ⟨G.vertex_mem_of_inc hG, (hℒ.isComplemented hA).inc_diff_mem hvA
          ⟨(mem_core_edgeSet.mp he).1, heA⟩ hG⟩
      · exact Or.inl ⟨G.vertex_mem_of_inc hG, hvA⟩
    · exact he.2
  · exact fun h ↦ h.1

end Core

/-- `G \ A ⊆ G` for a complemented `A ⊆ G`. -/
theorem complement_le {G A : RootedHypergraph α β} (hA : IsComplemented G A) :
    (complement G A hA).toHypergraph ≤ G.toHypergraph := by
  refine ⟨fun v hv ↦ ?_, fun e he ↦ he.1, fun e he ↦ ?_⟩
  · rcases hv with hv | hv
    · exact hv.1
    · exact hA.le.vertexSet_subset (A.roots_subset v hv)
  · ext v
    exact ⟨fun h ↦ ⟨he, h⟩, fun h ↦ h.2⟩

/-- Graph Minors XX, (4.12) (pages 335–336): "Let $\mathcal{F}_1$ be a well-behaved set of active
patchworks, let $k \ge 0$, and let
$\mathcal{F}_2$ be a set of patchworks such that for each $P_2 = (G_2, \mu_2, \Delta_2) \in
\mathcal{F}_2$ there exists $f \in dom(\mu_2)$ with* ... *$\le k$ ends and $P_1 = (G_1, \mu_1,
\Delta_1) \in \mathcal{F}_1$ so that $G_2 \setminus f = G_1 \setminus A$ and $\pi(A) =
\mu_2(f)$ for some complemented rooted hypergraph $A \subseteq G_1$, and $P_2 \setminus
\{f\} = P_1|(G_2 \setminus \{f\})$. Then $\mathcal{F}_2$ is well-behaved."

The proof is the paper's, with the roots changed as in the module docstring. -/
theorem theorem_4_12_proof {𝓕₁ 𝓕₂ : Set (UnlabeledPatchwork α β)} (h : WellBehaved 𝓕₁)
    (ha : ∀ P ∈ 𝓕₁, IsActive P) (k : ℕ)
    (h₂ : ∀ P₂ ∈ 𝓕₂, ∃ f ∈ P₂.dom, (P₂.G.ends f).ncard ≤ k ∧ ∃ P₁ ∈ 𝓕₁,
      ∃ (A : RootedHypergraph α β) (hA : IsComplemented P₁.G A),
        P₂.G.deleteEdges {f} = complement P₁.G A hA ∧ A.roots = P₂.μ f ∧
        IsCompletionOf (P₁.restrict (P₂.G.deleteEdges {f})) (P₂.deleteEdges {f})) :
    WellBehaved 𝓕₂ := by
  classical
  obtain ⟨K, hK⟩ := h.exists_roots_le
  -- `𝓕₃`: members of `𝓕₁` with other roots, at most `K + k` of them. Well-behaved by (4.5).
  have h₃ := theorem_4_5_proof h ha (K + k)
  set 𝓕₃ : Set (UnlabeledPatchwork α β) :=
    {P₂ | P₂.G.roots.length ≤ K + k ∧ ∃ P₁ ∈ 𝓕₁, SameBase P₁ P₂} with h𝓕₃
  have ha₃ : ∀ P ∈ 𝓕₃, IsActive P := by
    rintro P ⟨-, P₁, hP₁, hb⟩ v hv
    obtain ⟨e, he, hinc⟩ := ha P₁ hP₁ v (hb.vertexSet_eq ▸ hv)
    refine ⟨e, hb.dom_eq ▸ he, ?_⟩
    rw [hb.inc_eq]
    exact hinc
  -- `𝓕₄`: the complemented parts of members of `𝓕₃`. Well-behaved by (4.11).
  have h₄ := theorem_4_11_proof h₃ ha₃
  set 𝓕₄ : Set (UnlabeledPatchwork α β) := {P₂ | ∃ P₁ ∈ 𝓕₃, IsComplemented P₁.G P₂.G ∧
    P₂.G.roots = P₁.G.roots ∧ IsCompletionOf (P₁.restrict P₂.G) P₂} with h𝓕₄
  -- `𝓕₅`: one edge added to a member of `𝓕₄` by (4.6), with the active members kept.
  let 𝓕₅ : Set (UnlabeledPatchwork α β) :=
    {P | (∃ f ∈ P.G.edgeSet, P.deleteEdges {f} ∈ completions Unit 𝓕₄ ∧
      ∀ v, P.G.Inc f v → v ∈ P.G.roots) ∧ IsActive P}
  have h₅ : WellBehaved 𝓕₅ :=
    (theorem_4_6_proof h₄ (𝓕₂ := {P | ∃ f ∈ P.G.edgeSet, P.deleteEdges {f} ∈ completions Unit 𝓕₄ ∧
      ∀ v, P.G.Inc f v → v ∈ P.G.roots}) fun _ hP ↦ hP).mono fun _ hP ↦ hP.1
  -- `𝓕₂` lies in the set of members of `𝓕₅` with other roots, at most `K` of them, which is
  -- well-behaved by (4.5).
  refine (theorem_4_5_proof h₅ (fun _ hP ↦ hP.2) K).mono ?_
  intro P₂ hP₂
  obtain ⟨f, hf, hk, P₁, hP₁, A, hA, heq, hroots, hres⟩ := h₂ P₂ hP₂
  have hfE : f ∈ P₂.G.edgeSet := P₂.dom_subset hf
  have hG : P₂.G.roots = P₁.G.roots := congrArg (·.roots) heq
  have hV : P₂.G.vertexSet = (P₁.G.vertexSet \ A.vertexSet) ∪ A.rootSet :=
    congrArg (·.vertexSet) heq
  have hE : P₂.G.edgeSet \ {f} = P₁.G.edgeSet \ A.edgeSet := congrArg (·.edgeSet) heq
  have hInc : ∀ e v, (P₂.G.Inc e v ∧ e ∉ ({f} : Set β)) ↔
      (e ∈ P₁.G.edgeSet \ A.edgeSet ∧ P₁.G.Inc e v) := fun e v ↦ by
    have := congrArg (·.Inc) heq
    exact Iff.of_eq (congrFun (congrFun this e) v)
  have hAμ : A.rootSet = {x | x ∈ P₂.μ f} := by
    rw [← hroots]
    rfl
  have hμf : {x | x ∈ P₂.μ f} = P₂.G.ends f := P₂.μ_set f hf
  -- The roots `r`: the roots of `P₂`, followed by the terms of `μ₂(f)` that are not roots.
  let r : List α := P₂.G.roots ++ marchSlash (P₂.μ f) {x | x ∈ P₂.G.roots}
  have hrn : r.Nodup := by
    refine List.Nodup.append P₂.G.roots_nodup (nodup_marchSlash (P₂.μ_nodup f hf) _) ?_
    intro x hx hx'
    exact (mem_marchSlash.mp hx').2 hx
  have hrμ : ∀ x ∈ P₂.μ f, x ∈ r := fun x hx ↦ by
    by_cases hxr : x ∈ P₂.G.roots
    · exact List.mem_append_left _ hxr
    · exact List.mem_append_right _ (mem_marchSlash.mpr ⟨hx, hxr⟩)
  have hrs₂ : ∀ x ∈ r, x ∈ P₂.G.vertexSet := fun x hx ↦ by
    rcases List.mem_append.mp hx with hx | hx
    · exact P₂.G.roots_subset x hx
    · have h₁ : x ∈ {x | x ∈ P₂.μ f} := (mem_marchSlash.mp hx).1
      rw [hμf] at h₁
      exact P₂.G.vertex_mem_of_inc h₁
  have hrs₁ : ∀ x ∈ r, x ∈ P₁.G.vertexSet := fun x hx ↦ by
    rcases List.mem_append.mp hx with hx | hx
    · exact P₁.G.roots_subset x (hG ▸ hx)
    · have h₁ : x ∈ A.rootSet := hAμ ▸ (mem_marchSlash.mp hx).1
      exact hA.le.vertexSet_subset (A.roots_subset x h₁)
  have hlen : P₂.G.roots.length ≤ K := hG ▸ hK P₁ hP₁
  have hrlen : r.length ≤ K + k := by
    have h₁ : (marchSlash (P₂.μ f) {x | x ∈ P₂.G.roots}).length ≤ (P₂.μ f).length :=
      List.length_filter_le _ _
    have h₂ : (P₂.μ f).length ≤ k := by
      rw [← ncard_march (P₂.μ_nodup f hf), hμf]
      exact hk
    simp only [r, List.length_append]
    omega
  let P₅ := P₂.reroot r hrn hrs₂
  let P₃ := P₁.reroot r hrn hrs₁
  have hP₃ : P₃ ∈ 𝓕₃ := ⟨hrlen, P₁, hP₁, rfl, rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  have hle : (P₂.G.deleteEdges {f}).toHypergraph ≤ P₁.G.toHypergraph := by
    rw [heq]
    exact complement_le hA
  -- "`((G₁⁻, μ₂(f)), μ₁, Δ₁) ∈ 𝓕₃`, and so `P₂ \ f ∈ 𝓕₄`", with the roots `r`.
  have hP₄ : P₅.deleteEdges {f} ∈ 𝓕₄ := by
    refine ⟨P₃, hP₃, ⟨hle, fun _ _ hv ↦ hv, ?_⟩, rfl, ?_⟩
    · intro v e hv he hinc
      have heA : e ∈ A.edgeSet := by
        by_contra heA
        have : e ∈ P₂.G.edgeSet \ {f} := hE ▸ ⟨he.1, heA⟩
        exact he.2 this
      have hvA : v ∈ A.vertexSet := A.vertex_mem_of_inc ((inc_iff_of_le hA.le heA).mpr hinc)
      have hv' : v ∈ P₂.G.vertexSet := hv
      rw [hV] at hv'
      rcases hv' with hv' | hv'
      · exact absurd hvA hv'.2
      · rw [hAμ] at hv'
        exact hrμ v hv'
    · exact
      { G_eq := rfl
        dom_eq := hres.dom_eq
        μ_eq := hres.μ_eq
        Δ_eq := hres.Δ_eq }
  have hends : ∀ v, P₅.G.Inc f v → v ∈ P₅.G.roots := fun v hv ↦ by
    have hm : v ∈ {x | x ∈ P₂.μ f} := by
      rw [hμf]
      exact hv
    exact hrμ v hm
  -- `P₂` is active, since `P₁` is.
  have hact : IsActive P₅ := by
    intro v hv
    have hv' : v ∈ P₂.G.vertexSet := hv
    rw [hV] at hv'
    rcases hv' with hv' | hv'
    · obtain ⟨e, he, hinc⟩ := ha P₁ hP₁ v hv'.1
      have heA : e ∉ A.edgeSet := fun heA ↦
        hv'.2 (A.vertex_mem_of_inc ((inc_iff_of_le hA.le heA).mpr hinc))
      have h₂ := (hInc e v).mpr ⟨⟨P₁.dom_subset he, heA⟩, hinc⟩
      have hdom : e ∈ (P₂.deleteEdges {f}).dom := by
        rw [hres.dom_eq, Patchwork.restrict_dom hle]
        exact ⟨he, ⟨P₂.G.edge_mem_of_inc h₂.1, h₂.2⟩⟩
      exact ⟨e, hdom.1, h₂.1⟩
    · rw [hAμ, hμf] at hv'
      exact ⟨f, hf, hv'⟩
  -- "and therefore `P₂ ∈ 𝓕₅`", with the roots `r`; then (4.5) restores the roots of `P₂`.
  refine ⟨hlen, P₅, ⟨⟨f, hfE, ⟨_, hP₄, IsCompletionOf.refl _⟩, hends⟩, hact⟩, ?_⟩
  exact ⟨rfl, rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

end GraphMinor.GM20
