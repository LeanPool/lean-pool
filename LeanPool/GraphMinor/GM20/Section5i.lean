/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section5h

/-!
# The heart in (5.5) of Graph Minors XX

The heart of `ℒ' = ℒ₁ ∪ {f(A, B) : (A, B) ∈ ℳ}` comes from the heart `Q` of `ℒ` by replacing, for
each `(A, B) ∈ ℳ`, the edges `e(C)` of the members `C` that lie in `A` by one edge with ends `V(A ∩
B)`.
So (4.13) applies. The proof below gives the rooted location in `Q` that (4.13) asks for.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph GraphMinor.GM04

universe u v

variable {α : Type u} {β : Type v}

variable {ℒ : Set (RootedHypergraph α β)} {ℳ : Set (Hypergraph α β × Hypergraph α β)}

private theorem deleted_heart_core_sets
    {P Q Q' : UnlabeledPatchwork α β} {e e' : RootedHypergraph α β → β}
    (hD : SideData P.G ℒ ℳ) (hQ : IsPatchworkHeart P ℒ e Q)
    (hQ' : IsPatchworkHeart P (sideSet P.G ℒ ℳ) e' Q') {F : Set β}
    {own : RootedHypergraph α β → Hypergraph α β × Hypergraph α β}
    (hown : ∀ C, C ∈ ℒ → C ∉ mainSet P.G ℒ ℳ →
      own C ∈ ℳ ∧ C.toHypergraph ≤ (own C).1 ∧
        (own C).2 ≤ complementHypergraph P.G C) :
    let part (p : Hypergraph α β × Hypergraph α β) : Set (RootedHypergraph α β) :=
      {C ∈ ℒ | C ∉ mainSet P.G ℒ ℳ ∧ own C = p}
    let Ap (p : Hypergraph α β × Hypergraph α β) : RootedHypergraph α β :=
      heartPart Q (e '' part p) (sepRooted p.1 p.2)
    (∀ {p}, p ∈ ℳ → (Ap p).vertexSet ⊆ p.1.vertexSet) →
    (∀ p, (Ap p).edgeSet = e '' part p) →
    (∀ {p}, p ∈ ℳ → ∀ {C}, C ∈ ℒ → C ∉ part p → C.toHypergraph ≤ p.2) →
    (∀ {g}, g ∈ Q'.G.edgeSet \ F ↔ ∃ C ∈ mainSet P.G ℒ ℳ, e C = g) →
    (Q'.G.deleteEdges F).vertexSet = (rootedLocationCore Q.G (Ap '' ℳ)).vertexSet ∧
      (Q'.G.deleteEdges F).edgeSet = (rootedLocationCore Q.G (Ap '' ℳ)).edgeSet := by
  classical
  intro part Ap hApV hApE hother hedge'
  have hfine := hD.fine
  let f : Hypergraph α β × Hypergraph α β → RootedHypergraph α β := fun p ↦ sepRooted p.1 p.2
  have hcoreV : (Q'.G.deleteEdges F).vertexSet =
      (rootedLocationCore Q.G (Ap '' ℳ)).vertexSet := by
    change Q'.G.vertexSet = _
    rw [hQ'.vertexSet_eq]
    ext v
    rw [mem_core_iff, mem_core_iff]
    constructor
    · rintro ⟨hvG, hall⟩
      have hvc : v ∈ (rootedLocationCore P.G ℒ).vertexSet :=
        SideData.core_subset (mem_core_iff.mpr ⟨hvG, hall⟩)
      refine ⟨by rw [hQ.vertexSet_eq]; exact hvc, ?_⟩
      rintro _ ⟨p, hp, rfl⟩ hv
      exact hall (f p) (Or.inr ⟨p, hp, rfl⟩) (hApV hp hv)
    · rintro ⟨hvQ, hall⟩
      rw [hQ.vertexSet_eq] at hvQ
      obtain ⟨hvG, hrt⟩ := mem_core_iff.mp hvQ
      refine ⟨hvG, ?_⟩
      rintro L (hL | ⟨p, hp, rfl⟩) hvL
      · exact hrt L hL.1 hvL
      · obtain ⟨C, hC, hvC⟩ := hfine.1 v hvG
        have hvr := hrt C hC hvC
        by_cases hCp : C ∈ part p
        · refine hall (Ap p) ⟨p, hp, rfl⟩ (Or.inr ⟨e C, ⟨C, hCp, rfl⟩, ?_⟩)
          exact (hQ.inc_iff hfine).mpr ⟨C, hC, rfl, hvr⟩
        · exact mem_sepRooted_rootSet.mpr ⟨hvL,
            (hother hp hC hCp).vertexSet_subset hvC⟩
  have hcoreE : (Q'.G.deleteEdges F).edgeSet =
      (rootedLocationCore Q.G (Ap '' ℳ)).edgeSet := by
    ext g
    rw [mem_core_edgeSet]
    change g ∈ Q'.G.edgeSet \ F ↔ _
    rw [hedge', hQ.edgeSet_eq_image hfine]
    constructor
    · rintro ⟨C, hC, rfl⟩
      refine ⟨⟨C, hC.1, rfl⟩, ?_⟩
      rintro _ ⟨p, hp, rfl⟩ hg
      rw [hApE] at hg
      obtain ⟨C', hC', heq⟩ := hg
      have := hQ.injOn_newEdge hC'.1 hC.1 heq
      subst this
      exact hC'.2.1 hC
    · rintro ⟨⟨C, hC, rfl⟩, hall⟩
      refine ⟨C, ⟨hC, ?_⟩, rfl⟩
      intro hex
      have hm : C ∉ mainSet P.G ℒ ℳ := fun h ↦ h.2 hex
      have hp := (hown C hC hm).1
      refine hall _ ⟨own C, hp, rfl⟩ ?_
      rw [hApE]
      exact ⟨C, ⟨hC, hm, rfl⟩, rfl⟩
  exact ⟨hcoreV, hcoreE⟩

/-- If `(P, ℒ)` has heart `Q` then `(P, ℒ')` has a heart got from `Q` as in (4.13). -/
theorem exists_sideSet_heart [Infinite β] {P Q : UnlabeledPatchwork α β}
    {e : RootedHypergraph α β → β} (hD : SideData P.G ℒ ℳ) (hQ : IsPatchworkHeart P ℒ e Q)
    (hfinM : ℳ.Finite) {k : ℕ} (hk : ∀ p ∈ ℳ, separationOrder p.1 p.2 ≤ k) :
    ∃ Q', HasPatchworkHeart P (sideSet P.G ℒ ℳ) Q' ∧
      Q' ∈ locationReplaced {Q} k ℳ.ncard := by
  classical
  have hfine := hD.fine
  have hfin : ℒ.Finite := hQ.finite hfine
  have hfine' := hD.isFine
  have hloc' := hD.isRootedLocation
  have hne : Nonempty (RootedHypergraph α β) := ⟨P.G⟩
  let f : Hypergraph α β × Hypergraph α β → RootedHypergraph α β := fun p ↦ sepRooted p.1 p.2
  have hfinj : InjOn f ℳ := fun p hp q hq h ↦ hD.inj p hp q hq (congrArg (·.toHypergraph) h)
  have hmainfin : (mainSet P.G ℒ ℳ).Finite := hfin.subset fun _ h ↦ h.1
  obtain ⟨fresh, hfresh, havoid⟩ := exists_injOn_avoid (δ := β) (hfinM.image f)
    (hmainfin.image e)
  let e' : RootedHypergraph α β → β := fun L ↦ if L ∈ mainSet P.G ℒ ℳ then e L else fresh L
  have he₁ : ∀ {C}, C ∈ mainSet P.G ℒ ℳ → e' C = e C := fun hC ↦ ite_eq_left hC
  have he₂ : ∀ {p}, p ∈ ℳ → e' (f p) = fresh (f p) := fun hp ↦ ite_eq_right (hD.sep_notMem_main hp)
  have hinj' : InjOn e' (sideSet P.G ℒ ℳ) := by
    rintro L₁ (h₁ | ⟨p, hp, rfl⟩) L₂ (h₂ | ⟨q, hq, rfl⟩) heq
    · rw [he₁ h₁, he₁ h₂] at heq
      exact hQ.injOn_newEdge h₁.1 h₂.1 heq
    · rw [he₁ h₁, he₂ hq] at heq
      exact absurd (heq ▸ ⟨L₁, h₁, rfl⟩) (havoid (f q))
    · rw [he₂ hp, he₁ h₂] at heq
      exact absurd (heq ▸ ⟨L₂, h₂, rfl⟩) (havoid (f p))
    · rw [he₂ hp, he₂ hq] at heq
      exact hfresh ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩ heq
  have hfinS : (sideSet P.G ℒ ℳ).Finite := hmainfin.union (hfinM.image f)
  obtain ⟨Q', hQ'⟩ := exists_heart hloc' hfine' hfinS hinj'
  refine ⟨Q', ⟨e', hQ'⟩, ?_⟩
  -- Each member of `ℒ` outside `ℒ₁` has one owner.
  have hown : ∀ C, ∃ p : Hypergraph α β × Hypergraph α β, C ∈ ℒ → C ∉ mainSet P.G ℒ ℳ →
      p ∈ ℳ ∧ C.toHypergraph ≤ p.1 ∧ p.2 ≤ complementHypergraph P.G C := by
    intro C
    by_cases h : C ∈ ℒ ∧ C ∉ mainSet P.G ℒ ℳ
    · have : ∃ p ∈ ℳ, C.toHypergraph ≤ p.1 ∧ p.2 ≤ complementHypergraph P.G C := by
        by_contra hn
        exact h.2 ⟨h.1, hn⟩
      obtain ⟨p, hp⟩ := this
      exact ⟨p, fun _ _ ↦ hp⟩
    · exact ⟨(P.G.toHypergraph, P.G.toHypergraph), fun h₁ h₂ ↦ absurd ⟨h₁, h₂⟩ h⟩
  choose own hown using hown
  let part : Hypergraph α β × Hypergraph α β → Set (RootedHypergraph α β) :=
    fun p ↦ {C ∈ ℒ | C ∉ mainSet P.G ℒ ℳ ∧ own C = p}
  let Ap : Hypergraph α β × Hypergraph α β → RootedHypergraph α β :=
    fun p ↦ heartPart Q (e '' part p) (f p)
  have hsubE : ∀ p, e '' part p ⊆ Q.G.edgeSet := by
    rintro p _ ⟨C, hC, rfl⟩
    rw [hQ.edgeSet_eq_image hfine]
    exact ⟨C, hC.1, rfl⟩
  have hApE : ∀ p, (Ap p).edgeSet = e '' part p := fun p ↦ inter_eq_left.mpr (hsubE p)
  have hrootsQ : Q.G.rootSet = ∅ := by
    have h₁ : Q.G.roots = P.G.roots := hQ.roots_eq
    change {v | v ∈ Q.G.roots} = ∅
    rw [h₁]
    exact hD.rootless
  have hApV : ∀ {p}, p ∈ ℳ → (Ap p).vertexSet ⊆ p.1.vertexSet := by
    rintro p hp v (h | ⟨_, ⟨C, hC, rfl⟩, hinc⟩)
    · exact (mem_sepRooted_rootSet.mp h).1
    · obtain ⟨C', hC', h₁, h₂⟩ := (hQ.inc_iff hfine).mp hinc
      have heq := hQ.injOn_newEdge hC' hC.1 h₁
      subst heq
      have hC₂ := hown C' hC.1 hC.2.1
      rw [hC.2.2] at hC₂
      exact hC₂.2.1.vertexSet_subset (C'.roots_subset v h₂)
  have hApQ : ∀ {p}, p ∈ ℳ → (Ap p).vertexSet ⊆ Q.G.vertexSet := by
    rintro p hp v (h | ⟨_, h₁, hinc⟩)
    · rw [hQ.vertexSet_eq]
      exact hD.sep_mem_core hp (mem_sepRooted_rootSet.mp h)
    · exact Q.G.vertex_mem_of_inc hinc
  have hApLe : ∀ {p}, p ∈ ℳ → (Ap p).toHypergraph ≤ Q.G.toHypergraph := by
    intro p hp
    refine ⟨hApQ hp, inter_subset_right, fun g hg ↦ ?_⟩
    ext v
    exact ⟨fun h ↦ ⟨hg.1, h⟩, fun h ↦ h.2⟩
  have hother : ∀ {p}, p ∈ ℳ → ∀ {C}, C ∈ ℒ → C ∉ part p → C.toHypergraph ≤ p.2 := by
    intro p hp C hC hn
    by_cases hm : C ∈ mainSet P.G ℒ ℳ
    · exact (hD.main_side hm hp).1
    · obtain ⟨h₁, h₂, -⟩ := hown C hC hm
      have hne : own C ≠ p := fun h ↦ hn ⟨hC, hm, h⟩
      exact h₂.trans (hD.cross _ h₁ p hp hne)
  have hApC : ∀ {p}, p ∈ ℳ → IsComplemented Q.G (Ap p) := by
    intro p hp
    refine ⟨hApLe hp, fun v _ hr ↦ ?_, fun v g hv hg hinc ↦ ?_⟩
    · rw [hrootsQ] at hr
      exact hr.elim
    · obtain ⟨C, hC, rfl, hvC⟩ := (hQ.inc_iff hfine).mp hinc
      have hnot : C ∉ part p := fun h ↦ hg.2 (by rw [hApE]; exact ⟨C, h, rfl⟩)
      exact mem_sepRooted_rootSet.mpr ⟨hApV hp hv,
        (hother hp hC hnot).vertexSet_subset (C.roots_subset v hvC)⟩
  have hApLoc : IsRootedLocation Q.G (Ap '' ℳ) := by
    have hcomp : ∀ ⦃X⦄, X ∈ Ap '' ℳ → IsComplemented Q.G X := by
      rintro _ ⟨p, hp, rfl⟩
      exact hApC hp
    refine ⟨hcomp, ?_⟩
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hne
    have hpq : p ≠ q := fun h ↦ hne (by rw [h])
    rw [complement_toHypergraph]
    rw [le_iff_of_le (hApLe hp) (complementHypergraph_le (hApC hq))]
    refine ⟨fun v hv ↦ ?_, fun g hg ↦ ⟨(hApLe hp).edgeSet_subset hg, fun hg' ↦ ?_⟩⟩
    · by_cases hvq : v ∈ (Ap q).vertexSet
      · exact Or.inr ⟨hApQ hp hv, mem_sepRooted_rootSet.mpr ⟨hApV hq hvq,
          (hD.cross p hp q hq hpq).vertexSet_subset (hApV hp hv)⟩⟩
      · exact Or.inl ⟨hApQ hp hv, hvq⟩
    · rw [hApE] at hg hg'
      obtain ⟨C, hC, rfl⟩ := hg
      obtain ⟨C', hC', heq⟩ := hg'
      have := hQ.injOn_newEdge hC'.1 hC.1 heq
      subst this
      exact hpq (hC.2.2.symm.trans hC'.2.2)
  let g₀ : Hypergraph α β × Hypergraph α β → β := fun p ↦ fresh (f p)
  have hg₀ : InjOn g₀ ℳ := fun p hp q hq h ↦ hfinj hp hq (hfresh ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩ h)
  let A : β → RootedHypergraph α β := fun g ↦ Ap (Function.invFunOn g₀ ℳ g)
  have hA : ∀ {p}, p ∈ ℳ → A (g₀ p) = Ap p := fun {p} hp ↦ by
    change Ap (Function.invFunOn g₀ ℳ (g₀ p)) = _
    rw [hg₀ (Function.invFunOn_mem ⟨_, hp, rfl⟩) hp (Function.invFunOn_eq ⟨_, hp, rfl⟩)]
  set F : Set β := g₀ '' ℳ with hF
  have hAF : A '' F = Ap '' ℳ := by
    ext X
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p, hp, (hA hp).symm⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨g₀ p, ⟨p, hp, rfl⟩, hA hp⟩
  have hedge' : ∀ {g}, g ∈ Q'.G.edgeSet \ F ↔ ∃ C ∈ mainSet P.G ℒ ℳ, e C = g := by
    intro g
    rw [hQ'.edgeSet_eq_image hfine']
    constructor
    · rintro ⟨⟨L, hL | ⟨p, hp, rfl⟩, rfl⟩, h₂⟩
      · exact ⟨L, hL, (he₁ hL).symm⟩
      · exact absurd ⟨p, hp, (he₂ hp).symm⟩ h₂
    · rintro ⟨C, hC, rfl⟩
      refine ⟨⟨C, Or.inl hC, he₁ hC⟩, ?_⟩
      rintro ⟨p, -, h⟩
      exact havoid (f p) ⟨C, hC, h.symm⟩
  have hdelLe : (Q'.G.deleteEdges F).toHypergraph ≤ Q.G.toHypergraph := by
    refine ⟨?_, ?_, fun g hg ↦ ?_⟩
    · intro v hv
      have hv' : v ∈ Q'.G.vertexSet := hv
      rw [hQ'.vertexSet_eq] at hv'
      rw [hQ.vertexSet_eq]
      exact SideData.core_subset hv'
    · intro g hg
      obtain ⟨C, hC, rfl⟩ := hedge'.mp hg
      rw [hQ.edgeSet_eq_image hfine]
      exact ⟨C, hC.1, rfl⟩
    · obtain ⟨C, hC, rfl⟩ := hedge'.mp hg
      have h₁ : (Q'.G.deleteEdges F).ends (e C) = Q'.G.ends (e C) := by
        ext v
        exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hg.2⟩⟩
      have hC' : C ∈ sideSet P.G ℒ ℳ := Or.inl hC
      rw [h₁, hQ.ends_newEdge hC.1, ← he₁ hC, hQ'.ends_newEdge hC']
  obtain ⟨hcoreV, hcoreE⟩ := deleted_heart_core_sets hD hQ hQ' hown hApV hApE hother hedge'
  refine ⟨F, ?_, ?_, Q, rfl, A, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    rw [hQ'.dom_eq_image hfine']
    exact ⟨f p, Or.inr ⟨p, hp, rfl⟩, he₂ hp⟩
  · exact Set.ncard_image_le hfinM
  · rw [hAF]
    exact hApLoc
  · exact hQ'.roots_eq.trans hQ.roots_eq.symm
  · rw [hAF]
    exact eq_of_le_of_vertexSet_eq_of_edgeSet_eq hdelLe (core_le hApLoc) hcoreV hcoreE
  · refine ⟨rfl, ?_, ?_, ?_⟩
    · rw [Patchwork.restrict_dom hdelLe]
      ext g
      change g ∈ Q'.dom \ F ↔ _
      rw [hQ'.dom_eq_image hfine', hQ.dom_eq_image hfine, ← hQ'.edgeSet_eq_image hfine',
        hedge']
      constructor
      · rintro ⟨C, hC, rfl⟩
        exact ⟨⟨C, hC.1, rfl⟩, hedge'.mpr ⟨C, hC, rfl⟩⟩
      · exact fun h ↦ hedge'.mp h.2
    · intro g hg
      have hg' : g ∈ Q'.G.edgeSet \ F := by
        rw [Patchwork.restrict_dom hdelLe] at hg
        exact hg.2
      obtain ⟨C, hC, rfl⟩ := hedge'.mp hg'
      have hC' : C ∈ sideSet P.G ℒ ℳ := Or.inl hC
      change Q'.μ (e C) = Q.μ (e C)
      rw [hQ.μ_newEdge hC.1, ← he₁ hC, hQ'.μ_newEdge hC']
    · intro g hg
      obtain ⟨C, hC, rfl⟩ := hedge'.mp hg
      have hC' : C ∈ sideSet P.G ℒ ℳ := Or.inl hC
      rw [Patchwork.restrict_Δ hdelLe hg]
      change Q'.Δ (e C) = Q.Δ (e C)
      rw [hQ.Δ_newEdge hC.1, ← he₁ hC, hQ'.Δ_newEdge hC']
  · rintro _ ⟨p, hp, rfl⟩
    have hL : f p ∈ sideSet P.G ℒ ℳ := Or.inr ⟨p, hp, rfl⟩
    have hgp : g₀ p = e' (f p) := (he₂ hp).symm
    constructor
    · rw [hA hp, hgp, hQ'.μ_newEdge hL]
      rfl
    · rw [hgp, hQ'.ends_newEdge hL]
      have : (f p).rootSet = (p.1 ∩ p.2).vertexSet := by
        ext v
        exact mem_sepRooted_rootSet
      rw [this]
      exact hk p hp

end GraphMinor.GM20
