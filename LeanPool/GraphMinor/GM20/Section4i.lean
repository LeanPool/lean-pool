/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section4h
public import LeanPool.GraphMinor.GM20.Retag

/-!
# Graph Minors XX, Section 4, (4.13)

`GraphMinor.GM20.Section4h` proves (4.13) by `w` uses of (4.12) when the new edges are not edges of
`G₁`. Here we remove that condition. We tag the edges of `G₁` and of the pieces with `0`, the new
edges with `1`, and the other edges of `G₂` with `0` (`GraphMinor.GM20.Retag`). After tagging, the
new edges are not edges of `G₁`, and tagging keeps sets well-behaved.

The statement of (4.13) in the paper leaves `π(G₂)` free, since `G₁⁻ ∩ ⋂ (G₁ \ A)⁻` has no roots.
With `π(G₂)` free the result is false, because expansions keep the number of roots
(see the correction to (4.13) in `corrections/GM20.md`). As in (4.12) we take `π(G₂) = π(G₁)`.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph GraphMinor.GM04

universe u v

variable {α : Type u} {β : Type v}

/-! ### Tagging commutes with the operations of (4.13) -/

theorem retag_injective (t : β → ℕ) : Function.Injective fun e ↦ (t e, e) :=
  fun _ _ h ↦ congrArg Prod.snd h

theorem retagHyper_le {t : β → ℕ} {H G : Hypergraph α β} (h : H ≤ G) :
    retagHyper t H ≤ retagHyper t G := by
  refine ⟨h.vertexSet_subset, image_mono h.edgeSet_subset, ?_⟩
  rintro _ ⟨e, he, rfl⟩
  rw [retagHyper_ends, retagHyper_ends]
  exact h.ends_eq e he

theorem _root_.GraphMinor.GM18.IsComplemented.retag {G A : RootedHypergraph α β}
    (h : IsComplemented G A) (t : β → ℕ) :
    IsComplemented (retagRooted t G) (retagRooted t A) := by
  refine ⟨retagHyper_le h.le, fun _ hv hr ↦ h.roots_mem hv hr, fun v p hv hp hinc ↦ ?_⟩
  obtain ⟨hpG, hpA⟩ := hp
  obtain ⟨-, he⟩ := mem_retagHyper_edgeSet.mp hpG
  exact h.inc_diff_mem hv ⟨he, fun heA ↦ hpA (mem_retagHyper_edgeSet.mpr ⟨hinc.1, heA⟩)⟩ hinc.2

theorem complement_retag {G A : RootedHypergraph α β} (h : IsComplemented G A) (t : β → ℕ)
    (h' : IsComplemented (retagRooted t G) (retagRooted t A)) :
    (complement (retagRooted t G) (retagRooted t A) h').toHypergraph =
      retagHyper t (complement G A h).toHypergraph := by
  refine Hypergraph.ext rfl ?_ ?_
  · exact (Set.image_sdiff (retag_injective t) _ _).symm
  · funext p v
    apply propext
    change (p ∈ (retagHyper t G.toHypergraph).edgeSet \ (retagHyper t A.toHypergraph).edgeSet ∧
      p.1 = t p.2 ∧ G.Inc p.2 v) ↔ (p.1 = t p.2 ∧ p.2 ∈ G.edgeSet \ A.edgeSet ∧ G.Inc p.2 v)
    simp only [mem_sdiff, mem_retagHyper_edgeSet]
    constructor
    · rintro ⟨⟨⟨-, he⟩, hA⟩, ht, hinc⟩
      exact ⟨ht, ⟨he, fun heA ↦ hA ⟨ht, heA⟩⟩, hinc⟩
    · rintro ⟨ht, ⟨he, hA⟩, hinc⟩
      exact ⟨⟨⟨ht, he⟩, fun h ↦ hA h.2⟩, ht, hinc⟩

theorem _root_.GraphMinor.GM18.IsRootedLocation.retag {G : RootedHypergraph α β}
    {ℒ : Set (RootedHypergraph α β)}
    (h : IsRootedLocation G ℒ) (t : β → ℕ) :
    IsRootedLocation (retagRooted t G) (retagRooted t '' ℒ) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨A, hA, rfl⟩
    exact (h.isComplemented hA).retag t
  · rintro _ ⟨A₁, h₁, rfl⟩ _ ⟨A₂, h₂, rfl⟩ hne
    rw [complement_retag (h.isComplemented h₂)]
    exact retagHyper_le (h.le_complement h₁ h₂ fun heq ↦ hne (heq ▸ rfl))

theorem core_retag {G : RootedHypergraph α β} {ℒ : Set (RootedHypergraph α β)}
    (h : IsRootedLocation G ℒ) (t : β → ℕ) :
    rootedLocationCore (retagRooted t G) (retagRooted t '' ℒ) =
      retagHyper t (rootedLocationCore G ℒ) := by
  refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq (core_le (h.retag t)) (retagHyper_le (core_le h))
    ?_ ?_
  · ext v
    rw [mem_core_vertexSet]
    change _ ↔ v ∈ (rootedLocationCore G ℒ).vertexSet
    rw [mem_core_vertexSet]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨h₁, fun A hA ↦ h₂ _ ⟨A, hA, rfl⟩⟩
    · rintro ⟨h₁, h₂⟩
      refine ⟨h₁, ?_⟩
      rintro _ ⟨A, hA, rfl⟩
      exact h₂ A hA
  · ext p
    rw [mem_core_edgeSet, mem_retagHyper_edgeSet, mem_core_edgeSet]
    change (p ∈ (retagHyper t G.toHypergraph).edgeSet ∧ _) ↔ _
    rw [mem_retagHyper_edgeSet]
    constructor
    · rintro ⟨⟨ht, he⟩, h₂⟩
      exact ⟨ht, he, fun A hA heA ↦ h₂ _ ⟨A, hA, rfl⟩ (mem_retagHyper_edgeSet.mpr ⟨ht, heA⟩)⟩
    · rintro ⟨ht, he, h₂⟩
      refine ⟨⟨ht, he⟩, ?_⟩
      rintro _ ⟨A, hA, rfl⟩ hpA
      exact h₂ A hA (mem_retagHyper_edgeSet.mp hpA).2

theorem retagHyper_deleteEdges (t : β → ℕ) (G : Hypergraph α β) (F : Set β) :
    (retagHyper t G).deleteEdges ((fun e ↦ (t e, e)) '' F) = retagHyper t (G.deleteEdges F) := by
  refine Hypergraph.ext rfl ?_ ?_
  · exact (Set.image_sdiff (retag_injective t) _ _).symm
  · funext p v
    apply propext
    change ((p.1 = t p.2 ∧ G.Inc p.2 v) ∧ p ∉ (fun e ↦ (t e, e)) '' F) ↔
      (p.1 = t p.2 ∧ G.Inc p.2 v ∧ p.2 ∉ F)
    constructor
    · rintro ⟨⟨ht, hinc⟩, hF⟩
      exact ⟨ht, hinc, fun hF' ↦ hF ⟨p.2, hF', Prod.ext ht.symm rfl⟩⟩
    · rintro ⟨ht, hinc, hF⟩
      refine ⟨⟨ht, hinc⟩, ?_⟩
      rintro ⟨e, he, rfl⟩
      exact hF he

theorem retagHyper_congr {t t' : β → ℕ} {G : Hypergraph α β} (h : ∀ e ∈ G.edgeSet, t e = t' e) :
    retagHyper t G = retagHyper t' G := by
  refine Hypergraph.ext rfl ?_ ?_
  · change (fun e ↦ (t e, e)) '' G.edgeSet = (fun e ↦ (t' e, e)) '' G.edgeSet
    exact Set.image_congr fun e he ↦ by rw [h e he]
  · funext p v
    apply propext
    change (p.1 = t p.2 ∧ G.Inc p.2 v) ↔ (p.1 = t' p.2 ∧ G.Inc p.2 v)
    constructor
    · rintro ⟨ht, hinc⟩
      exact ⟨ht.trans (h _ (G.edge_mem_of_inc hinc)), hinc⟩
    · rintro ⟨ht, hinc⟩
      exact ⟨ht.trans (h _ (G.edge_mem_of_inc hinc)).symm, hinc⟩

theorem retag_deleteEdges {Ω : Type*} (t : β → ℕ) (P : Patchwork Ω α β) (F : Set β) :
    IsCompletionOf (retagPatchwork t (P.deleteEdges F))
      ((retagPatchwork t P).deleteEdges ((fun e ↦ (t e, e)) '' F)) where
  G_eq := by
    have := retagHyper_deleteEdges t P.G.toHypergraph F
    exact RootedHypergraph.ext_of (congrArg (·.vertexSet) this) (congrArg (·.edgeSet) this)
      (congrArg (·.Inc) this) rfl
  dom_eq := (Set.image_sdiff (retag_injective t) _ _).symm
  μ_eq _ _ := rfl
  Δ_eq _ _ := rfl

theorem retag_congr {Ω : Type*} {t t' : β → ℕ} {P : Patchwork Ω α β}
    (h : ∀ e ∈ P.G.edgeSet, t e = t' e) :
    IsCompletionOf (retagPatchwork t P) (retagPatchwork t' P) where
  G_eq := by
    have := retagHyper_congr (G := P.G.toHypergraph) h
    exact RootedHypergraph.ext_of (congrArg (·.vertexSet) this.symm)
      (congrArg (·.edgeSet) this.symm) (congrArg (·.Inc) this.symm) rfl
  dom_eq := Set.image_congr fun e he ↦ by rw [h e (P.dom_subset he)]
  μ_eq _ _ := rfl
  Δ_eq _ _ := rfl

theorem restrict_retag {Ω : Type*} {t : β → ℕ} {P : Patchwork Ω α β} {H : RootedHypergraph α β}
    (h : H.toHypergraph ≤ P.G.toHypergraph) :
    IsCompletionOf ((retagPatchwork t P).restrict (retagRooted t H))
      (retagPatchwork t (P.restrict H)) where
  G_eq := rfl
  dom_eq := by
    change (fun e ↦ (t e, e)) '' (P.restrict H).dom = _
    rw [Patchwork.restrict_dom h, Patchwork.restrict_dom (retagHyper_le h)]
    exact Set.image_inter (retag_injective t)
  μ_eq _ _ := rfl
  Δ_eq p hp := by
    obtain ⟨e, he, rfl⟩ := hp
    change (P.restrict H).Δ e = ((retagPatchwork t P).restrict (retagRooted t H)).Δ (t e, e)
    have hp : (t e, e) ∈ (retagRooted t H).edgeSet := ⟨e, he, rfl⟩
    rw [Patchwork.restrict_Δ h he, Patchwork.restrict_Δ (retagHyper_le h) hp]
    rfl

/-! ### (4.13) -/

/-- Graph Minors XX, (4.13) (page 336), with `π(G₂) = π(G₁)`, see the module docstring: "Let
$\mathcal{F}_1$ be a well-behaved set of active patchworks, let $k, w \ge 0$ and let
$\mathcal{F}_2$ be a set of patchworks such that for each $P_2 = (G_2, \mu_2, \Delta_2) \in
\mathcal{F}_2$ there exists $F \subseteq dom(\mu_2)$ with $|F| \le w$ and $P_1 = (G_1,
\mu_1, \Delta_1) \in \mathcal{F}_1$, and a rooted location $\mathcal{L} = \{A_f : f \in F\}$
in $G_1$, such that* - $G_2^- \setminus F = G_1^- \cap \bigcap((G_1 \setminus A)^- : A \in
\mathcal{L})$, - $P_2 \setminus F = P_1|(G_2 \setminus F)$, and - for each $f \in F$,
$\pi(A_f) = \mu_2(f)$ and $f$ has $\le k$ ends. *Then $\mathcal{F}_2$ is well-behaved."

The paper's proof is "By $w$ applications of 4.12": this is `wellBehaved_replaceSet`, applied after
tagging the new edges. -/
theorem theorem_4_13_proof {𝓕₁ 𝓕₂ : Set (UnlabeledPatchwork α β)} (h : WellBehaved 𝓕₁)
    (ha : ∀ P ∈ 𝓕₁, IsActive P) (k w : ℕ)
    (h₂ : ∀ P₂ ∈ 𝓕₂, ∃ F ⊆ P₂.dom, F.ncard ≤ w ∧ ∃ P₁ ∈ 𝓕₁, ∃ A : β → RootedHypergraph α β,
      IsRootedLocation P₁.G (A '' F) ∧ P₂.G.roots = P₁.G.roots ∧
      P₂.G.toHypergraph.deleteEdges F = rootedLocationCore P₁.G (A '' F) ∧
      IsCompletionOf (P₁.restrict (P₂.G.deleteEdges F)) (P₂.deleteEdges F) ∧
      ∀ f ∈ F, (A f).roots = P₂.μ f ∧ (P₂.G.ends f).ncard ≤ k) :
    WellBehaved 𝓕₂ := by
  classical
  let z : β → ℕ := fun _ ↦ 0
  refine wellBehaved_of_retag (𝓢 := replaceSet (retagPatchwork z '' 𝓕₁) k w)
    (wellBehaved_replaceSet h.retag_zero (by rintro _ ⟨P, hP, rfl⟩; exact (ha P hP).retag z) k w)
    fun P₂ hP₂ ↦ ?_
  obtain ⟨F, hF, hw, P₁, hP₁, A, hℒ, hroots, hcore, hres, hA⟩ := h₂ P₂ hP₂
  -- The new edges get the tag `1`, all other edges the tag `0`.
  let t : β → ℕ := fun e ↦ if e ∈ F then 1 else 0
  let ι : β → ℕ × β := fun e ↦ (t e, e)
  refine ⟨t, retagPatchwork t P₂, ?_, IsCompletionOf.refl _⟩
  have himg : (fun p : ℕ × β ↦ retagRooted z (A p.2)) '' (ι '' F) = retagRooted z '' (A '' F) := by
    rw [image_image, image_image]
  have htz : ∀ e ∈ (P₂.G.toHypergraph.deleteEdges F).edgeSet, z e = t e := fun e he ↦
    (ite_eq_right_iff.mpr fun h ↦ absurd h he.2).symm
  have hdel : (retagPatchwork t P₂).G.toHypergraph.deleteEdges (ι '' F) =
      retagHyper z (P₂.G.toHypergraph.deleteEdges F) := by
    change (retagHyper t P₂.G.toHypergraph).deleteEdges (ι '' F) = _
    rw [retagHyper_deleteEdges, retagHyper_congr htz]
  have hle : (P₂.G.deleteEdges F).toHypergraph ≤ P₁.G.toHypergraph := by
    change P₂.G.toHypergraph.deleteEdges F ≤ P₁.G.toHypergraph
    rw [hcore]
    exact core_le hℒ
  refine mem_replaceSet_iff.mpr ⟨ι '' F, ?_, retagPatchwork z P₁, ⟨P₁, hP₁, rfl⟩,
    fun p ↦ retagRooted z (A p.2), ⟨?_, ?_, himg ▸ hℒ.retag z, hroots, ?_, ?_, ?_⟩⟩
  · rw [Set.ncard_image_of_injective _ (retag_injective t)]
    exact hw
  · rintro _ ⟨f, hf, rfl⟩
    exact ⟨f, hF hf, rfl⟩
  · refine Set.disjoint_left.mpr ?_
    rintro _ ⟨f, hf, rfl⟩ hp
    have h₁ : t f = 0 := (mem_retagHyper_edgeSet.mp hp).1
    have h₂ : t f = 1 := by simp [t, hf]
    omega
  · rw [himg, show (retagPatchwork z P₁).G = retagRooted z P₁.G from rfl, core_retag hℒ, hdel,
      hcore]
  · have hG' : (retagPatchwork t P₂).G.deleteEdges (ι '' F) =
        retagRooted z (P₂.G.deleteEdges F) :=
      RootedHypergraph.ext_of (congrArg (·.vertexSet) hdel) (congrArg (·.edgeSet) hdel)
        (congrArg (·.Inc) hdel) rfl
    rw [hG']
    exact (((restrict_retag hle).trans (hres.retag z)).trans (retag_congr htz)).trans
      (retag_deleteEdges t P₂ F)
  · rintro _ ⟨f, hf, rfl⟩
    refine ⟨(hA f hf).1, ?_⟩
    change ((retagHyper t P₂.G.toHypergraph).ends (t f, f)).ncard ≤ k
    rw [retagHyper_ends]
    exact (hA f hf).2

end GraphMinor.GM20
