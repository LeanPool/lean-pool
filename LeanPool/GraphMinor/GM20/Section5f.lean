/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section5e

/-!
# Cutting a rooted location along a family of subhypergraphs

The proof of (5.4) of Graph Minors XX cuts each `C ∈ ℒ` into the pieces `f_i(C) = C ∩ A_i`. This
file
treats a general family `(A_i : i ∈ ι)` with the properties that the proof uses, in `SplitFamily`.
The new set `splitSet ℒ A` is a fine rooted location with the same core, and the heart of `ℒ` is a
condensation of the heart of `splitSet ℒ A` (`exists_condensation`).

A set of rooted hypergraphs cannot hold the same piece twice, and two pairs `(C, i)` can give the
same piece. So each piece gets one owner `C`, and in the condensation an edge `e(C)` stands for the
pieces that `C` owns. Such a clash can only happen to a piece without edges, so nothing is lost.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph GraphMinor.GM04

universe u v

variable {α : Type u} {β : Type v} {ι : Type*}

/-- The rooted hypergraph `f(C)` with `f(C)⁻ = C⁻ ∩ A` and `πBar(f(C)) = πBar(C) ∩ V(A)`. -/
noncomputable def piece (C : RootedHypergraph α β) (A : Hypergraph α β) : RootedHypergraph α β where
  toHypergraph := C.toHypergraph ∩ A
  roots := marchSlash C.roots A.vertexSetᶜ
  roots_nodup := nodup_marchSlash C.roots_nodup _
  roots_subset v hv := by
    obtain ⟨h₁, h₂⟩ := mem_marchSlash.mp hv
    exact ⟨C.roots_subset v h₁, not_not.mp h₂⟩

theorem mem_piece_rootSet {C : RootedHypergraph α β} {A : Hypergraph α β} {v : α} :
    v ∈ (piece C A).rootSet ↔ v ∈ C.rootSet ∧ v ∈ A.vertexSet := by
  change v ∈ marchSlash C.roots A.vertexSetᶜ ↔ _
  rw [mem_marchSlash, mem_compl_iff, not_not]
  rfl

/-- The properties of the family `(A_i)` in the proof of (5.4). -/
structure SplitFamily (G : RootedHypergraph α β) (ℒ : Set (RootedHypergraph α β))
    (A : ι → Hypergraph α β) : Prop where
  le : ∀ i, A i ≤ G.toHypergraph
  cover_v : ∀ v ∈ G.vertexSet, ∃ i, v ∈ (A i).vertexSet
  cover_e : ∀ e ∈ G.edgeSet, ∃ i, e ∈ (A i).edgeSet
  disj : ∀ i j, i ≠ j → ∀ e, e ∈ (A i).edgeSet → e ∉ (A j).edgeSet
  sep : ∀ C ∈ ℒ, ∀ i j, i ≠ j → ∀ v ∈ C.vertexSet, v ∈ (A i).vertexSet → v ∈ (A j).vertexSet →
    v ∈ C.rootSet

/-- The set `ℒ'` of the proof of (5.4). -/
def splitSet (ℒ : Set (RootedHypergraph α β)) (A : ι → Hypergraph α β) :
    Set (RootedHypergraph α β) :=
  {L | ∃ C ∈ ℒ, ∃ i, L = piece C (A i)}

variable {G : RootedHypergraph α β} {ℒ : Set (RootedHypergraph α β)} {A : ι → Hypergraph α β}

theorem piece_le {C : RootedHypergraph α β} {B : Hypergraph α β} (hC : C.toHypergraph
  ≤ G.toHypergraph) (hA : B ≤ G.toHypergraph) :
    (piece C B).toHypergraph ≤ C.toHypergraph :=
  inter_le_left hC hA

theorem piece_le_right {C : RootedHypergraph α β} {B : Hypergraph α β}
    (hC : C.toHypergraph ≤ G.toHypergraph) (hA : B ≤ G.toHypergraph) :
    (piece C B).toHypergraph ≤ B :=
  inter_le_right hC hA

theorem isComplemented_piece (hS : SplitFamily G ℒ A) (hloc : IsRootedLocation G ℒ) {C} (hC : C ∈ ℒ)
    (i : ι) : IsComplemented G (piece C (A i)) := by
  have hc := hloc.isComplemented hC
  refine ⟨inter_le hc.le (hS.le i), ?_, ?_⟩
  · intro v hv hr
    exact mem_piece_rootSet.mpr ⟨hc.roots_mem hv.1 hr, hv.2⟩
  · intro v e hv he hinc
    refine mem_piece_rootSet.mpr ⟨?_, hv.2⟩
    by_cases heC : e ∈ C.edgeSet
    · obtain ⟨j, hj⟩ := hS.cover_e e he.1
      have hij : i ≠ j := by
        rintro rfl
        exact he.2 ⟨heC, hj⟩
      have hvj : v ∈ (A j).vertexSet := by
        have h₁ : v ∈ G.ends e := hinc
        rw [(hS.le j).ends_eq e hj] at h₁
        exact (A j).vertex_mem_of_inc h₁
      exact hS.sep C hC i j hij v hv.1 hv.2 hvj
    · exact hc.inc_diff_mem hv.1 ⟨he.1, heC⟩ hinc

/-- Each `X ⊆ G` that shares no edge with `L = f(C)`, and meets it only in roots of `C`, lies in
`G \ L`. -/
theorem le_complementHypergraph_piece {C : RootedHypergraph α β} {B X : Hypergraph α β}
    (hL : IsComplemented G (piece C B)) (hX : X ≤ G.toHypergraph)
    (he : ∀ e ∈ X.edgeSet, e ∉ (piece C B).edgeSet)
    (hv : ∀ v ∈ X.vertexSet, v ∈ (piece C B).vertexSet → v ∈ C.rootSet) :
    X ≤ complementHypergraph G (piece C B) := by
  rw [le_iff_of_le hX (complementHypergraph_le hL)]
  refine ⟨fun v hvX ↦ ?_, fun e heX ↦ ⟨hX.edgeSet_subset heX, he e heX⟩⟩
  by_cases hvL : v ∈ (piece C B).vertexSet
  · exact Or.inr ⟨hX.vertexSet_subset hvX, mem_piece_rootSet.mpr ⟨hv v hvX hvL, hvL.2⟩⟩
  · exact Or.inl ⟨hX.vertexSet_subset hvX, hvL⟩

theorem complementHypergraph_le_piece {C : RootedHypergraph α β} {B : Hypergraph α β}
    (hC : IsComplemented G C) (hL : IsComplemented G (piece C B)) :
    complementHypergraph G C ≤ complementHypergraph G (piece C B) := by
  refine le_complementHypergraph_piece hL (complementHypergraph_le hC) ?_ ?_
  · exact fun e he he' ↦ he.2 he'.1
  · rintro v (h | h) hv
    · exact absurd hv.1 h.2
    · exact h.2

theorem isRootedLocation_splitSet (hS : SplitFamily G ℒ A) (hloc : IsRootedLocation G ℒ) :
    IsRootedLocation G (splitSet ℒ A) := by
  have hcomp : ∀ ⦃L⦄, L ∈ splitSet ℒ A → IsComplemented G L := by
    rintro _ ⟨C, hC, i, rfl⟩
    exact isComplemented_piece hS hloc hC i
  refine ⟨hcomp, ?_⟩
  rintro _ ⟨C, hC, i, rfl⟩ _ ⟨C', hC', j, rfl⟩ hne
  rw [complement_toHypergraph]
  have hc := hloc.isComplemented hC
  have hc' := hloc.isComplemented hC'
  refine le_complementHypergraph_piece (hcomp ⟨C', hC', j, rfl⟩) (inter_le hc.le (hS.le i)) ?_ ?_
  · intro e he he'
    by_cases hCC : C = C'
    · subst hCC
      have hij : i ≠ j := fun h ↦ hne (by rw [h])
      exact hS.disj i j hij e he.2 he'.2
    · exact ((hloc.le_complement hC hC' hCC).edgeSet_subset he.1).2 he'.1
  · intro v hv hv'
    by_cases hCC : C = C'
    · subst hCC
      have hij : i ≠ j := fun h ↦ hne (by rw [h])
      exact hS.sep C hC i j hij v hv.1 hv.2 hv'.2
    · rcases (hloc.le_complement hC hC' hCC).vertexSet_subset hv.1 with h | h
      · exact absurd hv'.1 h.2
      · exact h

theorem isFine_splitSet (hS : SplitFamily G ℒ A) (hfine : IsFine G ℒ) :
    IsFine G (splitSet ℒ A) := by
  refine ⟨fun v hv ↦ ?_, fun e he ↦ ?_⟩
  · obtain ⟨C, hC, hvC⟩ := hfine.1 v hv
    obtain ⟨i, hi⟩ := hS.cover_v v hv
    exact ⟨_, ⟨C, hC, i, rfl⟩, hvC, hi⟩
  · obtain ⟨C, hC, heC⟩ := hfine.2 e he
    obtain ⟨i, hi⟩ := hS.cover_e e he
    exact ⟨_, ⟨C, hC, i, rfl⟩, heC, hi⟩

theorem core_splitSet (hS : SplitFamily G ℒ A) :
    (rootedLocationCore G (splitSet ℒ A)).vertexSet = (rootedLocationCore G ℒ).vertexSet := by
  ext v
  rw [mem_core_iff, mem_core_iff]
  refine and_congr_right fun hv ↦ ⟨fun h C hC hvC ↦ ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hS.cover_v v hv
    exact (mem_piece_rootSet.mp (h _ ⟨C, hC, i, rfl⟩ ⟨hvC, hi⟩)).1
  · rintro h _ ⟨C, hC, i, rfl⟩ hvL
    exact mem_piece_rootSet.mpr ⟨h C hC hvL.1, hvL.2⟩

theorem ncard_piece_rootSet_le (C : RootedHypergraph α β) (B : Hypergraph α β) :
    (piece C B).rootSet.ncard ≤ C.rootSet.ncard :=
  Set.ncard_le_ncard (fun _ h ↦ (mem_piece_rootSet.mp h).1) (List.finite_toSet _)

theorem finite_splitSet [Finite ι] (h : ℒ.Finite) : (splitSet ℒ A).Finite := by
  have hfin : ((fun p : RootedHypergraph α β × ι ↦ piece p.1 (A p.2)) '' (ℒ ×ˢ univ)).Finite :=
    (h.prod finite_univ).image _
  refine hfin.subset ?_
  rintro _ ⟨C, hC, i, rfl⟩
  exact ⟨(C, i), ⟨hC, mem_univ _⟩, rfl⟩

/-- A finite set has an injective map into an infinite type. -/
theorem exists_injOn_of_finite {γ δ : Type*} [Infinite δ] [Nonempty δ] {s : Set γ} (hs : s.Finite) :
    ∃ f : γ → δ, InjOn f s := by
  classical
  have : Finite s := hs
  let g : s ↪ δ := ((Finite.equivFin s).toEmbedding.trans Fin.valEmbedding).trans
    (Infinite.natEmbedding δ)
  refine ⟨fun x ↦ if h : x ∈ s then g ⟨x, h⟩ else Classical.arbitrary δ, ?_⟩
  intro x hx y hy hxy
  simp only [hx, hy, ↓reduceDIte] at hxy
  exact congrArg Subtype.val (g.injective hxy)

/-- The rooted part of `Q'` with edges `E`, and with the march of `C`. -/
noncomputable def heartPart (Q' : UnlabeledPatchwork α β) (E : Set β) (C : RootedHypergraph α β) :
    RootedHypergraph α β where
  vertexSet := C.rootSet ∪ {v | ∃ f ∈ E, Q'.G.Inc f v}
  edgeSet := E ∩ Q'.G.edgeSet
  Inc f v := f ∈ E ∧ Q'.G.Inc f v
  vertex_mem_of_inc _ _ h := Or.inr ⟨_, h.1, h.2⟩
  edge_mem_of_inc _ _ h := ⟨h.1, Q'.G.edge_mem_of_inc h.2⟩
  vertexSet_finite := (List.finite_toSet _).union
    (Q'.G.vertexSet_finite.subset fun _ ⟨_, _, h⟩ ↦ Q'.G.vertex_mem_of_inc h)
  edgeSet_finite := Q'.G.edgeSet_finite.subset inter_subset_right
  roots := C.roots
  roots_nodup := C.roots_nodup
  roots_subset _ h := Or.inl h

variable [Finite ι]

/-- The heart of `(P, ℒ)` is a condensation of a heart of `(P, splitSet ℒ A)`. -/
theorem exists_condensation [Infinite β] {P Q : UnlabeledPatchwork α β}
    {e : RootedHypergraph α β → β} (hS : SplitFamily P.G ℒ A) (hfine : IsFine P.G ℒ)
    (hQ : IsPatchworkHeart P ℒ e Q) :
    ∃ Q', HasPatchworkHeart P (splitSet ℒ A) Q' ∧ IsCondensation Q Q' := by
  classical
  have hloc := hQ.isRootedLocation
  have hne : Nonempty (RootedHypergraph α β) := ⟨P.G⟩
  have hne' : Nonempty β := inferInstance
  have hfin := hQ.finite hfine
  have hfine' := isFine_splitSet hS hfine
  have hloc' := isRootedLocation_splitSet hS hloc
  obtain ⟨e', he'⟩ := exists_injOn_of_finite (δ := β) (finite_splitSet (A := A) hfin)
  obtain ⟨Q', hQ'⟩ := exists_heart hloc' hfine' (finite_splitSet hfin) he'
  refine ⟨Q', ⟨e', hQ'⟩, ?_⟩
  -- Each piece has one owner.
  have hown : ∀ L : RootedHypergraph α β, ∃ C, L ∈ splitSet ℒ A →
      C ∈ ℒ ∧ ∃ i, L = piece C (A i) := by
    intro L
    by_cases hL : L ∈ splitSet ℒ A
    · obtain ⟨C, hC, i, h⟩ := hL
      exact ⟨C, fun _ ↦ ⟨hC, i, h⟩⟩
    · exact ⟨L, fun h ↦ absurd h hL⟩
  choose own hown using hown
  let part : RootedHypergraph α β → Set (RootedHypergraph α β) :=
    fun C ↦ {L ∈ splitSet ℒ A | own L = C}
  have hpart : ∀ {C L}, L ∈ part C → C ∈ ℒ ∧ ∃ i, L = piece C (A i) := by
    rintro C L ⟨h₁, rfl⟩
    exact hown L h₁
  let inv : β → RootedHypergraph α β := Function.invFunOn e ℒ
  have hinv : ∀ {C}, C ∈ ℒ → inv (e C) = C := fun hC ↦
    hQ.injOn_newEdge (Function.invFunOn_mem ⟨_, hC, rfl⟩) hC (Function.invFunOn_eq ⟨_, hC, rfl⟩)
  let R : β → RootedHypergraph α β := fun g ↦ heartPart Q' (e' '' part (inv g)) (inv g)
  have hsubE : ∀ C, e' '' part C ⊆ Q'.G.edgeSet := by
    rintro C _ ⟨L, hL, rfl⟩
    rw [hQ'.edgeSet_eq_image hfine']
    exact ⟨L, hL.1, rfl⟩
  have hRE : ∀ C, (heartPart Q' (e' '' part C) C).edgeSet = e' '' part C := fun C ↦
    inter_eq_left.mpr (hsubE C)
  have hRV : ∀ {C}, C ∈ ℒ → (heartPart Q' (e' '' part C) C).vertexSet = C.rootSet := by
    intro C hC
    refine subset_antisymm ?_ subset_union_left
    rintro v (h | ⟨_, ⟨L, hL, rfl⟩, hinc⟩)
    · exact h
    · obtain ⟨-, i, rfl⟩ := hpart hL
      obtain ⟨L', hL', h₁, h₂⟩ := (hQ'.inc_iff hfine').mp hinc
      have := he' hL' hL.1 h₁
      subst this
      exact (mem_piece_rootSet.mp h₂).1
  have hRle : ∀ {C}, C ∈ ℒ → (heartPart Q' (e' '' part C) C).toHypergraph ≤ Q'.G.toHypergraph := by
    intro C hC
    refine ⟨?_, inter_subset_right, fun f hf ↦ ?_⟩
    · intro v hv
      rw [hRV hC] at hv
      rw [hQ'.vertexSet_eq, core_splitSet hS]
      exact root_mem_core hloc hC hv
    · ext v
      exact ⟨fun h ↦ ⟨hf.1, h⟩, fun h ↦ h.2⟩
  refine ⟨?_, hQ'.roots_eq.trans hQ.roots_eq.symm |>.symm, ?_, ?_, R, ?_, ?_, ?_, ?_⟩
  · rw [hQ.vertexSet_eq, hQ'.vertexSet_eq, core_splitSet hS]
  · rw [hQ.dom_eq_image hfine, hQ.edgeSet_eq_image hfine]
  · rw [hQ'.dom_eq_image hfine', hQ'.edgeSet_eq_image hfine']
  · intro g hg
    rw [hQ.edgeSet_eq_image hfine] at hg
    obtain ⟨C, hC, rfl⟩ := hg
    simp only [R, hinv hC]
    refine ⟨hRle hC, ?_, ?_⟩
    · rw [hRV hC, hQ.ends_newEdge hC]
    · rw [hQ.μ_newEdge hC]
      rfl
  · rw [hQ'.edgeSet_eq_image hfine']
    ext f
    simp only [mem_iUnion, exists_prop]
    constructor
    · rintro ⟨g, -, hf⟩
      obtain ⟨⟨L, hL, rfl⟩, -⟩ := hf
      exact ⟨L, hL.1, rfl⟩
    · rintro ⟨L, hL, rfl⟩
      have hC := (hown L hL).1
      refine ⟨e (own L), ?_, ?_⟩
      · rw [hQ.edgeSet_eq_image hfine]
        exact ⟨_, hC, rfl⟩
      · have hR : R (e (own L)) = heartPart Q' (e' '' part (own L)) (own L) := by
          simp only [R, hinv hC]
        rw [hR, hRE]
        exact ⟨L, ⟨hL, rfl⟩, rfl⟩
  · intro g hg g' hg' hne
    rw [hQ.edgeSet_eq_image hfine] at hg hg'
    obtain ⟨C, hC, rfl⟩ := hg
    obtain ⟨C', hC', rfl⟩ := hg'
    have hCC : C ≠ C' := fun h ↦ hne (by rw [h])
    simp only [R, hinv hC, hinv hC', hRE]
    rw [Set.disjoint_left]
    rintro _ ⟨L, hL, rfl⟩ ⟨L', hL', heq⟩
    have := he' hL'.1 hL.1 heq
    subst this
    exact hCC (hL.2.symm.trans hL'.2)
  · intro g hg K hK
    rw [hQ.edgeSet_eq_image hfine] at hg
    obtain ⟨C, hC, rfl⟩ := hg
    have hK' : IsFeasibleGrouping (P.restrict C) K := by
      rw [hQ.Δ_newEdge hC] at hK
      exact hK
    have hR : R (e C) = heartPart Q' (e' '' part C) C := by
      simp only [R, hinv hC]
    rw [hR]
    have hcC := hloc.isComplemented hC
    refine feasible_of_split (C := C) (R := heartPart Q' (e' '' part C) C) rfl (hRE C) (hRle hC) ?_
      (he'.mono fun L hL ↦ hL.1) hcC.le ?_ ?_ ?_ ?_ (hRV hC) hK'
    · exact fun L hL ↦ hQ'.Δ_newEdge hL.1
    · intro L hL
      obtain ⟨-, i, rfl⟩ := hpart hL
      exact inter_le_left hcC.le (hS.le i)
    · intro L hL v
      obtain ⟨-, i, rfl⟩ := hpart hL
      rw [mem_piece_rootSet]
      exact and_congr_right fun hv ↦ ⟨fun h ↦ ⟨C.roots_subset v hv, h⟩, fun h ↦ h.2⟩
    · intro L hL L' hL' hLL v hv hv'
      obtain ⟨-, i, rfl⟩ := hpart hL
      obtain ⟨-, j, rfl⟩ := hpart hL'
      have hij : i ≠ j := fun h ↦ hLL (by rw [h])
      exact mem_piece_rootSet.mpr ⟨hS.sep C hC i j hij v hv.1 hv.2 hv'.2, hv.2⟩
    · intro f hf
      obtain ⟨i, hi⟩ := hS.cover_e f (hcC.le.edgeSet_subset hf)
      have hL : piece C (A i) ∈ splitSet ℒ A := ⟨C, hC, i, rfl⟩
      refine ⟨piece C (A i), ⟨hL, ?_⟩, hf, hi⟩
      obtain ⟨hown₁, j, hj⟩ := hown _ hL
      by_contra hCC
      have key : ∀ X, X = piece (own (piece C (A i))) (A j) → f ∈ X.edgeSet →
          f ∈ (own (piece C (A i))).edgeSet := by
        rintro _ rfl h
        exact h.1
      have hf' := key _ hj ⟨hf, hi⟩
      exact ((hloc.le_complement hC hown₁ (Ne.symm hCC)).edgeSet_subset hf).2 hf'

end GraphMinor.GM20
