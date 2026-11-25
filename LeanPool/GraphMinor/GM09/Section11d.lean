/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.CliqueDiscs
public import LeanPool.GraphMinor.GM09.Section6c
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM14.DiscSlope
import LeanPool.GraphMinor.GM09.Section3a

/-!
# Graph Minors IX, (11.11)

This file ends the proof of (11.11). Take a consolidation with smallest core. The core `(C, Ω)` is
4-connected and simple, so (6.1) and (11.5) split it into a society `(C₁, Ω₀)` with no large
transaction and a rural neighborhood `(C₂, Ω, Ω₀)`. The rest of the proof needs a closed disc for
each small clique of `C₂` that is not a clique of `C₁`.

The paper says that a triangle of `C₂` "bounds a region of the drawing". This needs care, since the
triangle could go around `Δ₀`. In that case 4-connectivity shows that `ΩBar₀` is a set of at most
three
vertices of the triangle, and all of `C₁` lies in `C₂`. We then replace `Ω₀` by the empty cyclic
permutation and `C₁` by the empty graph, and choose `Δ₀` last.
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11

universe u v

variable {α : Type u} {β : Type v}

/-- A set with at most three vertices that separates `A` from `B`, with `ΩBar` in `B`, in a
4-connected
society has `V(A) ⊆ V(B)`. The two sides may share edges. -/
theorem Society.vertexSet_subset_of_isFourConnected {CS : Society α β} (hc : CS.IsKConnected 4)
    {A B : Graph α β} (hA : A ≤ CS.G) (hB : B ≤ CS.G) (hV : V(A) ∪ V(B) = V(CS.G))
    (hE : E(A) ∪ E(B) = E(CS.G)) (hcard : (V(A) ∩ V(B)).ncard ≤ 3) (hΩ : CS.Ω.bar ⊆ V(B)) :
    V(A) ⊆ V(B) := by
  by_contra hn
  have hne : V(B) ≠ V(CS.G) := fun h => hn (h ▸ hA.vertexSet_mono)
  let A' : Graph α β := A.restrict (E(A) \ E(B))
  have hV' : V(A') = V(A) := rfl
  have hE' : E(A') = E(A) \ E(B) := by
    change E(A.restrict _) = _
    rw [edgeSet_restrict, inter_eq_right]
    exact sdiff_subset
  refine hc 3 (by omega) A' B ⟨⟨⟨restrict_le.trans hA, hB, ?_, ?_, ?_⟩, hΩ⟩, ?_, hne⟩
  · rw [hV', hV]
  · rw [hE', sdiff_union_self, hE]
  · rw [hE']
    exact disjoint_sdiff_left
  · rw [hV']
    exact hcard

/-- The `(6.1) + (11.5)` split of a core `CS = (C, Ω)` into a society `S₁ = (C₁, Ω₀)` and a rural
neighborhood `N₂ = (C₂, Ω, Ω₀)` with properties (i)–(iii) on page 75 of Graph Minors IX, with `q` in
place of `3p + 9`. -/
structure CoreRuralDecomposition (q : ℕ) (CS : Society α (Sym2 α))
    (S₁ : Society α (Sym2 α)) (N₂ : Neighborhood α (Sym2 α)) : Prop where
  /-- (i) `C₁ ⊆ C`. -/
  C₁_le : S₁.G ≤ CS.G
  /-- (i) `C₂ ⊆ C`. -/
  C₂_le : N₂.G ≤ CS.G
  /-- (i) `C₁ ∪ C₂ = C`. -/
  union_eq : subgraphUnion CS.G S₁.G N₂.G = CS.G
  /-- `N₂.Ω = Ω`. -/
  Ω_eq : N₂.Ω = CS.Ω
  /-- `N₂.Ω₀ = Ω₀`. -/
  Ω₀_eq : N₂.Ω₀ = S₁.Ω
  /-- (i) `V(C₁ ∩ C₂) = ΩBar₀`. -/
  inter_eq_bar₀ : V(S₁.G) ∩ V(N₂.G) = S₁.Ω.bar
  /-- `(C₂, Ω, Ω₀)` is a rural neighborhood. -/
  isRural : N₂.IsRural
  /-- (ii) `(C₁, Ω₀)` has no transaction of cardinality `> q`. -/
  no_large_transaction : ∀ Q_set : Set (Graph α (Sym2 α)),
    S₁.IsTransaction Q_set → Q_set.ncard ≤ q
  /-- (iii) For every triangle `T` of `C`, either `T ⊆ C₁` or `T ⊆ C₂`. -/
  triangle_in_left_or_right : ∀ T : Graph α (Sym2 α),
    IsTriangle CS.G T → T ≤ S₁.G ∨ T ≤ N₂.G

namespace CoreRuralDecomposition

variable {q : ℕ} {CS : Society α (Sym2 α)} {S₁ : Society α (Sym2 α)} {N₂ : Neighborhood α (Sym2 α)}

theorem vertexSet_union (D : CoreRuralDecomposition q CS S₁ N₂) :
    V(S₁.G) ∪ V(N₂.G) = V(CS.G) := by
  have h := congrArg Graph.vertexSet D.union_eq
  rwa [vertexSet_subgraphUnion] at h

theorem edgeSet_union (D : CoreRuralDecomposition q CS S₁ N₂) :
    E(S₁.G) ∪ E(N₂.G) = E(CS.G) := by
  have h := congrArg Graph.edgeSet D.union_eq
  rwa [edgeSet_subgraphUnion D.C₁_le D.C₂_le] at h

end CoreRuralDecomposition

/-- The drawing of a triangle is the union of the closures of its three edges. -/
theorem subgraphU_eq_of_triangle {G T : Graph α β} (Γ : GraphDrawing G EuclideanPlane) (hT : T ≤ G)
    {x y z : α} {e₁ e₂ e₃ : β} (hV : V(T) = {x, y, z}) (hE : E(T) = {e₁, e₂, e₃})
    (h₁ : G.IsLink e₁ x y) (h₂ : G.IsLink e₂ y z) :
    graphDrawingSubgraphU Γ T = closure (graphDrawingEdgeSet Γ e₁) ∪
      closure (graphDrawingEdgeSet Γ e₂) ∪ closure (graphDrawingEdgeSet Γ e₃) := by
  have hv₁ := (closure_inter_V_of_isLink Γ h₁).2
  have hv₂ := (closure_inter_V_of_isLink Γ h₂).2
  have hmem : ∀ {w : α} {e : β} {S : Set EuclideanPlane},
      closure (graphDrawingEdgeSet Γ e) ∩ Γ.drawing.V = S → vertexPt Γ w ∈ S → w ∈ V(G) →
      vertexPt Γ w ∈ closure (graphDrawingEdgeSet Γ e) := by
    intro w e S hS hw _
    have h : vertexPt Γ w ∈ closure (graphDrawingEdgeSet Γ e) ∩ Γ.drawing.V := by
      rw [hS]
      exact hw
    exact h.1
  apply Subset.antisymm
  · intro p hp
    rcases mem_subgraphU_cases Γ hT hp with ⟨v, hv, rfl⟩ | ⟨e, he, hpe, -⟩
    · rw [hV] at hv
      rcases hv with rfl | rfl | rfl
      · exact Or.inl (Or.inl (hmem hv₁ (Or.inl rfl) h₁.left_mem))
      · exact Or.inl (Or.inl (hmem hv₁ (Or.inr rfl) h₁.right_mem))
      · exact Or.inl (Or.inr (hmem hv₂ (Or.inr rfl) h₂.right_mem))
    · rw [hE] at he
      rcases he with rfl | rfl | rfl
      · exact Or.inl (Or.inl (subset_closure hpe))
      · exact Or.inl (Or.inr (subset_closure hpe))
      · exact Or.inr (subset_closure hpe)
  · have hin : ∀ e ∈ E(T), closure (graphDrawingEdgeSet Γ e) ⊆ graphDrawingSubgraphU Γ T :=
      fun e he p hp => Or.inr (mem_iUnion₂.mpr ⟨e, he, hp⟩)
    refine union_subset (union_subset (hin _ ?_) (hin _ ?_)) (hin _ ?_) <;> rw [hE] <;> simp

variable {N : Neighborhood α (Sym2 α)}

/-- A triangle of a simple neighborhood is drawn as an `O`-arc. We give the three edges as `s(x,
y)`,
`s(y, z)` and `s(z, x)`. -/
theorem isOArc_triangle (P : Presentation N) (_hs : IsSimpleGraph N.G) {x y z : α}
    (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
    (h₁ : N.G.IsLink s(x, y) x y) (h₂ : N.G.IsLink s(y, z) y z) (h₃ : N.G.IsLink s(z, x) z x) :
    IsOArc (closure (graphDrawingEdgeSet P.Γ s(x, y)) ∪ closure (graphDrawingEdgeSet P.Γ s(y, z)) ∪
      closure (graphDrawingEdgeSet P.Γ s(z, x))) := by
  have hne₁₂ : s(x, y) ≠ s(y, z) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨h, -⟩
    · exact hxy h
    · exact hzx h.symm
  have hne₂₃ : s(y, z) ≠ s(z, x) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨h, -⟩
    · exact hyz h
    · exact hxy h.symm
  have hne₃₁ : s(z, x) ≠ s(x, y) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨h, -⟩
    · exact hzx h
    · exact hyz h.symm
  have hi₁₂ := closure_inter_closure P.Γ h₁.symm h₂ hzx.symm hne₁₂
  have hi₁₃ := closure_inter_closure P.Γ h₁ h₃.symm hyz hne₃₁.symm
  have hi₂₃ := closure_inter_closure P.Γ h₂.symm h₃ hxy.symm hne₂₃
  have hl₁ := isLine_closure_of_isLink P.Γ h₁ hxy
  have hl₂ := isLine_closure_of_isLink P.Γ h₂ hyz
  have hl₃ := isLine_closure_of_isLink P.Γ h₃ hzx
  refine GraphMinor.GM14.isOArc_union (hl₁.union hl₂ hi₁₂) hl₃.symm ?_
  rintro p ⟨hp | hp, hp₃⟩
  · have h : p ∈ closure (graphDrawingEdgeSet P.Γ s(x, y)) ∩
        closure (graphDrawingEdgeSet P.Γ s(z, x)) := ⟨hp, hp₃⟩
    rw [hi₁₃] at h
    exact Or.inl h
  · have h : p ∈ closure (graphDrawingEdgeSet P.Γ s(y, z)) ∩
        closure (graphDrawingEdgeSet P.Γ s(z, x)) := ⟨hp, hp₃⟩
    rw [hi₂₃] at h
    exact Or.inr h

/-- A point of a drawing is a vertex or it lies on an edge. -/
theorem mem_U_cases {G : Graph α β} (Γ : GraphDrawing G EuclideanPlane) {x : EuclideanPlane}
    (hx : x ∈ Γ.drawing.U) :
    (∃ v ∈ V(G), x = vertexPt Γ v) ∨
      (∃ e ∈ E(G), x ∈ graphDrawingEdgeSet Γ e ∧ x ∉ Γ.drawing.V) := by
  by_cases hV : x ∈ Γ.drawing.V
  · exact Or.inl (exists_vertexPt_of_mem_V Γ hV)
  · obtain ⟨f, hf, hxf⟩ := exists_edge_of_mem' hx hV
    let e := Γ.iso.edgeEquiv.symm ⟨f, hf⟩
    refine Or.inr ⟨e.1, e.2, ?_, hV⟩
    rw [graphDrawingEdgeSet_eq Γ e.2]
    simpa [e] using hxf

/-- **The triangles of the rural part bound empty regions.** Let `(C₁, Ω₀)` and `(C₂, Ω, Ω₀)` split
the 4-connected simple society `CS`. Let `K` be a set of three pairwise adjacent vertices of `C₂`.
If `Δ₀` is empty or `ΩBar₀` is not a clique of `C₂`, the triangle bounds a closed disc in `Δ` whose
interior misses the drawing and `Δ₀`. The separation given by the disc has order three, so
4-connectivity leaves nothing on the side away from `ΩBar`. -/
theorem exists_emptyRegion {q : ℕ} {CS S₁ : Society α (Sym2 α)}
    (D : CoreRuralDecomposition q CS S₁ N) (hc : CS.IsKConnected 4) (hs : IsSimpleGraph N.G)
    (P : Presentation N) (hΔ₀ : P.Δ₀ = ∅ ∨ ¬ IsLeThreeClique N.G N.Ω₀.bar) {K : Set α}
    (hK : IsLeThreeClique N.G K) (h3 : K.ncard = 3) : ∃ E, IsEmptyRegion P K E := by
  classical
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Set.ncard_eq_three.mp h3
  have hx : x ∈ ({x, y, z} : Set α) := Or.inl rfl
  have hy : y ∈ ({x, y, z} : Set α) := Or.inr (Or.inl rfl)
  have hz : z ∈ ({x, y, z} : Set α) := Or.inr (Or.inr rfl)
  have hl₁ := hK.2.2 x hx y hy hxy
  have hl₂ := hK.2.2 y hy z hz hyz
  have hl₃ := hK.2.2 z hz x hx hxz.symm
  obtain ⟨T, hT, hVT, hl₁T, hl₂T, hl₃T⟩ :=
    exists_triangle_of_three_clique hxy hyz hxz.symm hl₁ hl₂ hl₃
  have hTle : T ≤ N.G := hT.1.1
  have hO := isOArc_triangle P hs hxy hyz hxz.symm hl₁ hl₂ hl₃
  have hET : E(T) = {s(x, y), s(y, z), s(z, x)} := by
    symm
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (N.finite_E.subset hTle.edgeSet_mono)
    · rintro e (rfl | rfl | rfl)
      exacts [hl₁T.edge_mem, hl₂T.edge_mem, hl₃T.edge_mem]
    · rw [hT.2]
      refine (Set.ncard_eq_three.mpr ⟨s(x, y), s(y, z), s(z, x), ?_, ?_, ?_, rfl⟩).ge
      · intro h
        rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨h, -⟩
        · exact hxy h
        · exact hxz h
      · intro h
        rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨-, h⟩
        · exact hxz h
        · exact hyz h
      · intro h
        rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨h, -⟩
        · exact hyz h
        · exact hxy h.symm
  have hU := subgraphU_eq_of_triangle P.Γ hTle hVT hET hl₁ hl₂
  rw [← hU] at hO
  have hUsub : graphDrawingSubgraphU P.Γ T ⊆ P.Γ.drawing.U := subgraphU_subset_U P.Γ hTle
  obtain ⟨E₀, ⟨hsub, hd, hb, -⟩, -⟩ := disc_oArc P.Δ _ P.isClosedDisc_Δ
    (hUsub.trans fun p hp => (P.U_subset hp).1) hO
  have hsubBd : subBd E₀ = graphDrawingSubgraphU P.Γ T := by
    rw [subBd_eq_discBd_plane hd, hb]
  obtain ⟨H₁, H₂, hsep, hVi, hTH, hin, hout, hU₁, hU₂⟩ := exists_separation_of_disc P.Γ
    P.isClosedDisc_Δ.isCompact.isClosed (fun p hp => (P.U_subset hp).1) hTle hd hsub hsubBd
  have hH₁C := hsep.1.trans D.C₂_le
  have hH₂C := hsep.2.1.trans D.C₂_le
  have hbdi : Disjoint (interior E₀) (discBd E₀) := by
    rw [interior_eq_discInt_plane hd, disjoint_left]
    exact fun p hp h => hp.2 h
  have hbdiff : ∀ {p : EuclideanPlane}, p ∈ E₀ → p ∉ interior E₀ →
      p ∈ graphDrawingSubgraphU P.Γ T := by
    intro p hp hi
    rw [interior_eq_discInt_plane hd] at hi
    rw [← hb]
    by_contra h
    exact hi ⟨hp, h⟩
  have hptK : ∀ {v : α}, v ∈ V(N.G) → vertexPt P.Γ v ∈ graphDrawingSubgraphU P.Γ T →
      v ∈ ({x, y, z} : Set α) := fun hv h => hVT ▸ mem_vertexSet_of_vertexPt_mem P.Γ hTle hv h
  have hH₂int : ∀ {v : α}, v ∈ V(H₂) → vertexPt P.Γ v ∉ interior E₀ := fun hv =>
    (hU₂ (vertexPt_mem_subgraphU P.Γ hv hsep.2.1)).2
  have hH₁E : ∀ {v : α}, v ∈ V(H₁) → vertexPt P.Γ v ∈ E₀ := fun hv =>
    hU₁ (vertexPt_mem_subgraphU P.Γ hv hsep.1)
  have hKH₂ : ({x, y, z} : Set α) ⊆ V(H₂) := by
    rw [← hVT, ← hVi]
    exact inter_subset_right
  have hN : ∀ {v : α}, v ∈ V(H₁) ∪ V(H₂) → v ∈ V(N.G) := fun hv => hsep.2.2.1 ▸ hv
  have hbar : CS.Ω.bar ⊆ V(H₂) := by
    intro v hv
    have hv' : v ∈ N.Ω.bar := D.Ω_eq ▸ hv
    have hvN := N.bar_subset hv'
    have hvb : vertexPt P.Γ v ∈ subBd P.Δ :=
      (IsCleanPresentation.vertexSet_subset_iff hvN).mp ((P.mem_bd_Δ_iff v hvN).mpr hv')
    by_cases hvE : vertexPt P.Γ v ∈ E₀
    · refine hKH₂ (hptK hvN (hbdiff hvE fun hi => ?_))
      exact disjoint_left.mp (disjoint_interior_subBd P.Δ) (interior_mono hsub hi) hvb
    · refine hout v hvN ?_
      rw [vertexSet_eq_vertexPt P.Γ hvN, singleton_subset_iff]
      exact ⟨(P.U_subset (IsTidyPresentation.mem_U hvN)).1, hvE⟩
  have hbar₀ : ∀ {v : α}, v ∈ V(S₁.G) → v ∈ V(N.G) → v ∈ N.Ω₀.bar := fun h₁ h₂ => by
    rw [D.Ω₀_eq, ← D.inter_eq_bar₀]
    exact ⟨h₁, h₂⟩
  have hpt₀ : ∀ {v : α}, v ∈ N.Ω₀.bar → vertexPt P.Γ v ∈ P.Δ₀ := fun hv =>
    subBd_subset_of_isClosed (isClosed_Δ₀ P) ((IsCleanPresentation.vertexSet_subset_iff
      (N.bar₀_subset hv)).mp ((P.mem_bd_Δ₀_iff _ (N.bar₀_subset hv)).mpr hv))
  have hcard : ∀ {W : Set α}, W ⊆ {x, y, z} → W.ncard ≤ 3 := fun hW =>
    (Set.ncard_le_ncard hW (N.finite_V.subset hK.1)).trans h3.le
  -- `Δ₀` lies on one side of the triangle.
  have hside : Disjoint (interior E₀) P.Δ₀ := by
    have hdis : P.Δ₀ = ∅ ∨ (IsClosedDisc P.Δ₀) := by
      rcases P.agrees_Δ₀ with ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
    rcases hdis with h₀ | h₀
    · rw [h₀]
      exact disjoint_empty _
    have hdj : Disjoint (interior P.Δ₀) (discBd E₀) := by
      rw [hb, disjoint_left]
      exact fun p hp hp' => (P.U_subset (hUsub hp')).2 hp
    have hpre : IsPreconnected (interior P.Δ₀) := by
      rw [interior_eq_discInt_plane h₀]
      exact h₀.isPreconnected_discInt
    rcases subset_interior_or_compl hd hpre hdj with hin₀ | hout₀
    · exfalso
      have hsub₀ : P.Δ₀ ⊆ E₀ := by
        rw [← closure_interior_of_isClosedDisc h₀]
        exact closure_minimal (hin₀.trans interior_subset) hd.isCompact.isClosed
      let A : Graph α (Sym2 α) := subgraphUnion CS.G S₁.G H₁
      have hAle : A ≤ CS.G := subgraphUnion_le D.C₁_le hH₁C
      have hkey : ∀ {v : α}, v ∈ V(S₁.G) → v ∈ V(H₂) → v ∈ ({x, y, z} : Set α) := by
        intro v h₁ h₂
        have hvN := hN (Or.inr h₂)
        exact hptK hvN (hbdiff (hsub₀ (hpt₀ (hbar₀ h₁ hvN))) (hH₂int h₂))
      have hinter : V(A) ∩ V(H₂) ⊆ {x, y, z} := by
        rintro v ⟨h₁ | h₁, h₂⟩
        · exact hkey h₁ h₂
        · rw [← hVT, ← hVi]
          exact ⟨h₁, h₂⟩
      have hsubV := CS.vertexSet_subset_of_isFourConnected hc hAle hH₂C
        (by
          rw [vertexSet_subgraphUnion, union_assoc, hsep.2.2.1, D.vertexSet_union])
        (by
          rw [edgeSet_subgraphUnion D.C₁_le hH₁C, union_assoc, hsep.2.2.2.1, D.edgeSet_union])
        (hcard hinter) hbar
      have hsubK : N.Ω₀.bar ⊆ {x, y, z} := by
        intro v hv
        have hv₁ : v ∈ V(S₁.G) := S₁.bar_subset (D.Ω₀_eq ▸ hv)
        exact hkey hv₁ (hsubV (Or.inl hv₁))
      refine hΔ₀.elim (fun h => ?_) fun hn => hn ⟨hsubK.trans hK.1, hcard hsubK, ?_⟩
      · have hne := h₀.nonempty_discInt.mono (discInt_subset _)
        rw [h] at hne
        exact hne.ne_empty rfl
      · exact fun u hu w hw huw => hK.2.2 u (hsubK hu) w (hsubK hw) huw
    · rw [disjoint_left]
      intro p hp hp₀
      have hcl : p ∈ closure (interior P.Δ₀) := by
        rw [closure_interior_of_isClosedDisc h₀]
        exact hp₀
      obtain ⟨w, hwo, hw⟩ := mem_closure_iff.mp hcl _ isOpen_interior hp
      exact hout₀ hw (interior_subset hwo)
  -- So the side of the disc is empty.
  have hkey : ∀ {v : α}, v ∈ V(H₁) → v ∈ V(S₁.G) → v ∈ ({x, y, z} : Set α) := by
    intro v h₁ h₂
    have hvN := hN (Or.inl h₁)
    exact hptK hvN (hbdiff (hH₁E h₁) (disjoint_right.mp hside (hpt₀ (hbar₀ h₂ hvN))))
  let B : Graph α (Sym2 α) := subgraphUnion CS.G S₁.G H₂
  have hBle : B ≤ CS.G := subgraphUnion_le D.C₁_le hH₂C
  have hinter : V(H₁) ∩ V(B) ⊆ {x, y, z} := by
    rintro v ⟨h₁, h₂ | h₂⟩
    · exact hkey h₁ h₂
    · rw [← hVT, ← hVi]
      exact ⟨h₁, h₂⟩
  have hsubV := CS.vertexSet_subset_of_isFourConnected hc hH₁C hBle
    (by
      rw [vertexSet_subgraphUnion, union_left_comm, hsep.2.2.1, D.vertexSet_union])
    (by
      rw [edgeSet_subgraphUnion D.C₁_le hH₂C, union_left_comm, hsep.2.2.2.1, D.edgeSet_union])
    (hcard hinter) (hbar.trans subset_union_right)
  have hH₁K : V(H₁) ⊆ {x, y, z} := fun v hv => hinter ⟨hv, hsubV hv⟩
  have hintU : Disjoint (interior E₀) P.Γ.drawing.U := by
    rw [disjoint_left]
    intro p hp hpU
    have hnot : p ∉ graphDrawingSubgraphU P.Γ T := by
      rw [← hb]
      exact disjoint_left.mp hbdi hp
    rcases mem_U_cases P.Γ hpU with ⟨v, hv, rfl⟩ | ⟨e, he, hpe, hpV⟩
    · have hv₁ : v ∈ V(H₁) := by
        refine hin v hv ?_
        rw [vertexSet_eq_vertexPt P.Γ hv, singleton_subset_iff, subBd_eq_discBd_plane hd]
        rw [interior_eq_discInt_plane hd] at hp
        exact hp
      exact hnot (vertexPt_mem_subgraphU P.Γ (hVT ▸ hH₁K hv₁) hTle)
    · have hEu : e ∈ E(H₁) ∪ E(H₂) := hsep.2.2.2.1 ▸ he
      rcases hEu with he₁ | he₂
      · obtain ⟨u, w, hl⟩ := H₁.exists_isLink_of_mem_edgeSet he₁
        have hlN := hl.mono hsep.1
        have huw : u ≠ w := hs.ne_of_isLink hlN
        have hlK := hK.2.2 u (hH₁K hl.left_mem) w (hH₁K hl.right_mem) huw
        have hee : e = s(u, w) := hs.2 e hlN.edge_mem _ hlK.edge_mem u w hlN hlK
        have heT : e ∈ E(T) := by
          rw [hET, hee]
          have hu := hH₁K hl.left_mem
          have hw := hH₁K hl.right_mem
          rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
            first
            | exact (huw rfl).elim
            | simp [Sym2.eq_swap]
        exact hnot (Or.inr (mem_iUnion₂.mpr ⟨e, heT, subset_closure hpe⟩))
      · exact (hU₂ (Or.inr (mem_iUnion₂.mpr ⟨e, he₂, subset_closure hpe⟩))).2 hp
  refine ⟨E₀, hd, hsub, hb ▸ hUsub, fun v hv => ⟨fun h => hptK hv (hb ▸ h), fun h => ?_⟩, hintU,
    hside⟩
  rw [hb]
  exact vertexPt_mem_subgraphU P.Γ (hVT ▸ h) hTle

/-- The cyclic permutation of the empty set. -/
def emptyCyclicPerm : CyclicPerm α where
  bar := ∅
  toFun := id
  finite_bar := finite_empty
  bijOn := bijOn_empty id
  single_orbit := fun _ hx => hx.elim

instance : Nonempty (CyclicPerm α) := ⟨emptyCyclicPerm⟩

/-- The core of a consolidation is a simple graph. -/
theorem isSimpleGraph_consolidationCore (S : Society α β) (D_set : Set (Graph α β × Graph α β)) :
    IsSimpleGraph (consolidationCore S D_set) :=
  ⟨fun _ _ _ h => h.1 rfl, fun _ _ _ _ _ _ h₁ h₂ => h₁.2.1.trans h₂.2.1.symm⟩

/-- A society with empty `ΩBar` has no nonempty transaction. -/
theorem Society.eq_empty_of_isTransaction {S : Society α β} (hbar : S.Ω.bar = ∅)
    {Q : Set (Graph α β)} (hQ : S.IsTransaction Q) : Q = ∅ := by
  obtain ⟨A, B, -, hF, hP⟩ := hQ
  rw [eq_empty_iff_forall_notMem]
  intro R hR
  obtain ⟨a, ha, -⟩ := hP R hR
  have := hF.1 ha
  rw [hbar] at this
  exact this

/-- If the rural part of a split is all of `C`, we may drop `C₁` and `Ω₀`: the core is a rural
neighborhood `N'` with empty `Ω₀` and `Δ₀`, and the society left over is the empty graph. -/
theorem exists_core_decomposition_of_eq {CS : Society α (Sym2 α)} (hs : IsSimpleGraph CS.G)
    {N₂ : Neighborhood α (Sym2 α)} (hr : N₂.IsRural) (hEq : N₂.G = CS.G) (hΩ : N₂.Ω = CS.Ω)
    (q : ℕ) :
    ∃ (S₁ : Society α (Sym2 α)) (N' : Neighborhood α (Sym2 α)) (P : Presentation N'),
      CoreRuralDecomposition q CS S₁ N' ∧ IsTidyPresentation P ∧ P.Δ₀ = ∅ ∧
        S₁.Ω.bar = ∅ := by
  obtain ⟨P, h₁, -, -⟩ := hr.exists_clean
  have hC₂ : N₂.G ≤ CS.G := hEq.le
  have hsN := hs.mono hC₂
  let N' : Neighborhood α (Sym2 α) :=
    { N₂ with
      Ω₀ := emptyCyclicPerm
      bar₀_subset := empty_subset _ }
  let S' : Society α (Sym2 α) :=
    { G := ⊥
      Ω := emptyCyclicPerm
      finite_V := finite_empty
      finite_E := finite_empty
      bar_subset := empty_subset _ }
  have hb : subBd (∅ : Set EuclideanPlane) = ∅ := by simp [subBd]
  have hbd₀ : ∀ v ∈ V(N'.G), graphDrawingVertexSet P.Γ v ⊆ subBd ∅ ↔ v ∈ N'.Ω₀.bar := by
    intro v hv
    constructor
    · intro h
      have hm : vertexPt P.Γ v ∈ graphDrawingVertexSet P.Γ v :=
        (mem_vertexSet_iff P.Γ hv).mpr rfl
      have := h hm
      rw [hb] at this
      exact this.elim
    · intro h
      exact (h : v ∈ (∅ : Set α)).elim
  let P' : Presentation N' :=
    ⟨P.Γ, P.Δ, ∅, P.isClosedDisc_Δ, empty_subset _,
      fun x hx => ⟨(P.U_subset hx).1, by simp⟩, P.mem_bd_Δ_iff, hbd₀, P.agrees_Δ,
      Or.inl ⟨rfl, rfl⟩⟩
  have hle : (⊥ : Graph α (Sym2 α)) ≤ CS.G := bot_le
  refine ⟨S', N', P', ⟨hle, hC₂, ?_, hΩ, rfl, ?_, ?_, ?_, ?_⟩, ?_, rfl, rfl⟩
  · refine (Compatible.of_le_le (subgraphUnion_le hle hC₂) le_rfl).ext ?_ ?_
    · rw [vertexSet_subgraphUnion]
      rw [vertexSet_bot, empty_union, hEq]
    · rw [edgeSet_subgraphUnion hle hC₂]
      rw [edgeSet_bot, empty_union, hEq]
  · change V(⊥) ∩ V(N₂.G) = ∅
    rw [vertexSet_bot, empty_inter]
  · exact ⟨P'.Γ, P'.Δ, P'.Δ₀, P'.isClosedDisc_Δ, P'.Δ₀_subset_Δ, P'.U_subset, P'.mem_bd_Δ_iff,
      P'.mem_bd_Δ₀_iff, P'.agrees_Δ, P'.agrees_Δ₀⟩
  · intro Q hQ
    rw [Society.eq_empty_of_isTransaction (S := S') rfl hQ]
    simp
  · intro T hT
    right
    change T ≤ N₂.G
    rw [hEq]
    exact hT.1.1
  · refine IsTidyPresentation.of_clean (P := P') hsN h₁ ?_ ?_
    · change (∅ : Set EuclideanPlane) ∩ _ ⊆ _
      rw [empty_inter]
      exact empty_subset _
    · change _ ∩ subBd ∅ ⊆ _
      rw [hb, inter_empty]
      exact empty_subset _

/-- The split of a 4-connected simple society of bounded sophistication, with a tidy presentation of
the rural part. Either `Δ₀` is empty, or `ΩBar₀` is not a clique of the rural part, so that no
triangle
goes around `Δ₀`. In the first case, `ΩBar₀` had at most three vertices, forming a clique of `C₂`.
Then
all of `C₁` lies in `C₂` by 4-connectivity, and we drop `C₁` and `Ω₀`. -/
theorem exists_core_decomposition {CS : Society α (Sym2 α)} (hc : CS.IsKConnected 4)
    (hs : IsSimpleGraph CS.G) {p : ℕ} (hsoph : CS.HasSophisticationLE p) :
    ∃ (S₁ : Society α (Sym2 α)) (N₂ : Neighborhood α (Sym2 α)) (P : Presentation N₂),
      CoreRuralDecomposition (p + 2) CS S₁ N₂ ∧ IsTidyPresentation P ∧
        (P.Δ₀ = ∅ ∨ ¬ IsLeThreeClique N₂.G N₂.Ω₀.bar) := by
  obtain ⟨S₁, N₂, hr, hΩ, hΩ₀, hC₁, hC₂, hun, hint, hno, htri⟩ := theorem_11_5_proof CS hs hsoph
  have D : CoreRuralDecomposition (p + 2) CS S₁ N₂ := ⟨hC₁, hC₂, hun, hΩ, hΩ₀, hint, hr, hno, htri⟩
  have hsN := hs.mono hC₂
  by_cases hcl : IsLeThreeClique N₂.G N₂.Ω₀.bar
  · have hVsub : V(S₁.G) ⊆ V(N₂.G) := CS.vertexSet_subset_of_isFourConnected hc hC₁ hC₂
      D.vertexSet_union D.edgeSet_union (by rw [D.inter_eq_bar₀, ← hΩ₀]; exact hcl.2.1)
      (hΩ ▸ N₂.bar_subset)
    have hbar : ∀ v ∈ V(S₁.G), v ∈ N₂.Ω₀.bar := by
      intro v hv
      rw [hΩ₀, ← D.inter_eq_bar₀]
      exact ⟨hv, hVsub hv⟩
    have hEsub : E(S₁.G) ⊆ E(N₂.G) := by
      intro e he
      obtain ⟨u, w, hl⟩ := S₁.G.exists_isLink_of_mem_edgeSet he
      have hlC := hl.mono hC₁
      have huw := hs.ne_of_isLink hlC
      have hlN := hcl.2.2 u (hbar u hl.left_mem) w (hbar w hl.right_mem) huw
      have hlN' := hlN.mono hC₂
      have hee : e = s(u, w) := hs.2 e hlC.edge_mem _ hlN'.edge_mem u w hlC hlN'
      rw [hee]
      exact hlN.edge_mem
    have hEq : N₂.G = CS.G := by
      refine (Compatible.of_le_le hC₂ le_rfl).ext ?_ ?_
      · rw [← D.vertexSet_union, union_eq_right.mpr hVsub]
      · rw [← D.edgeSet_union, union_eq_right.mpr hEsub]
    obtain ⟨S', N', P', D', hT', h₀, -⟩ := exists_core_decomposition_of_eq hs hr hEq hΩ (p + 2)
    exact ⟨S', N', P', D', hT', Or.inl h₀⟩
  · obtain ⟨P, h₁, h₂, h₃⟩ := hr.exists_clean
    exact ⟨S₁, N₂, P, D, IsTidyPresentation.of_clean hsN h₁ h₂ h₃, Or.inr hcl⟩

/-- Clockwise agreement of a drawing gives clockwise agreement of its vertex map. -/
theorem agreesWith_of_drawing {G : Graph α β} {Γ : GraphDrawing G EuclideanPlane} {Ω : CyclicPerm α}
    {C : Set EuclideanPlane} {φ : Circle ≃ₜ C} (hbar : Ω.bar ⊆ V(G))
    (h : DrawingAgreesWithOArcHomeo Γ Ω C φ) : AgreesWithOArcHomeo (vertexPt Γ) Ω C φ := by
  refine ⟨fun v hv => h.1 v hv ((mem_vertexSet_iff Γ (hbar hv)).mpr rfl), fun v₁ v₂ v₃ hc => ?_⟩
  obtain ⟨t₁, t₂, t₃, h₁, h₂, h₃, m₁, m₂, m₃⟩ := h.2 v₁ v₂ v₃ hc
  have hm : ∀ v ∈ [v₁, v₂, v₃], v ∈ V(G) := fun v hv => hbar (hc.2.1 v hv)
  exact ⟨t₁, t₂, t₃, h₁, h₂, h₃, (mem_vertexSet_iff Γ (hm v₁ (by simp))).mp m₁,
    (mem_vertexSet_iff Γ (hm v₂ (by simp))).mp m₂, (mem_vertexSet_iff Γ (hm v₃ (by simp))).mp m₃⟩

/-- The discs, points and cyclic permutations for the family `F` that the last part of the proof of
(11.11) of Graph Minors IX uses (page 76). -/
def RuralCliqueDiscSelection (N₂ : Neighborhood α (Sym2 α)) (F : Set (Set α)) : Prop :=
  ∃ (Δ Δ₀ : Set EuclideanPlane) (α_pt : α → EuclideanPlane)
    (β_disc : Set α → Set EuclideanPlane) (Ω_clique : Set α → CyclicPerm α),
    IsClosedDisc Δ ∧
    (IsClosedDisc Δ₀ ∧ Δ₀ ⊆ Δ) ∧
    (∃ φ : Circle ≃ₜ subBd Δ,
      IsClockwiseDiscHomeo Δ φ ∧ AgreesWithOArcHomeo α_pt N₂.Ω (subBd Δ) φ) ∧
    (∃ φ₀ : Circle ≃ₜ subBd Δ₀,
      IsClockwiseDiscHomeo Δ₀ φ₀ ∧ AgreesWithOArcHomeo α_pt N₂.Ω₀ (subBd Δ₀) φ₀) ∧
    (Δ₀ ∩ subBd Δ ⊆ α_pt '' (N₂.Ω₀.bar ∩ N₂.Ω.bar)) ∧
    InjOn α_pt V(N₂.G) ∧
    (∀ K ∈ F, IsClosedDisc (β_disc K) ∧ β_disc K ⊆ Δ) ∧
    (∀ K ∈ F, (Ω_clique K).bar = K) ∧
    (∀ K ∈ F, ∃ φ_K : Circle ≃ₜ subBd (β_disc K),
      IsClockwiseDiscHomeo (β_disc K) φ_K ∧
      AgreesWithOArcHomeo α_pt (Ω_clique K) (subBd (β_disc K)) φ_K) ∧
    (∀ K ∈ F, Δ₀ ∩ β_disc K ⊆ α_pt '' (N₂.Ω₀.bar ∩ K)) ∧
    (∀ K ∈ F, β_disc K ∩ subBd Δ ⊆ α_pt '' (K ∩ N₂.Ω.bar)) ∧
    (∀ K ∈ F, ∀ K' ∈ F, K ≠ K' → β_disc K ∩ β_disc K' ⊆ α_pt '' (K ∩ K'))

/-- The boundary of a closed disc as an `O`-arc, in the form the arrangements use. -/
theorem nonempty_homeomorph_subBd {D : Set EuclideanPlane} (hD : IsClosedDisc D) :
    Nonempty (Circle ≃ₜ subBd D) := by
  rw [subBd_eq_discBd_plane hD]
  exact hD.isOArc_discBd

/-- The selection of discs. If `Δ₀` is empty, we choose a new `Δ₀` last, away from the other discs.
-/
theorem exists_selection {P : Presentation N} (T : IsTidyPresentation P) {F : Set (Set α)}
    (C : IsCliqueFamily P F) : RuralCliqueDiscSelection N F := by
  classical
  obtain ⟨β, hβ, hp⟩ := exists_clique_discs T C
  have hKV : ∀ K ∈ F, K ⊆ V(N.G) := fun K hK => (C.clique K hK).1
  have hfin : ∀ K ∈ F, K.Finite := fun K hK => N.finite_V.subset (hKV K hK)
  have hΩex : ∀ K ∈ F, ∃ Ω : CyclicPerm α, Ω.bar = K ∧ ∃ φ : Circle ≃ₜ subBd (β K),
      IsClockwiseDiscHomeo (β K) φ ∧
      AgreesWithOArcHomeo (vertexPt P.Γ) Ω (subBd (β K)) φ := by
    intro K hK
    have B := hβ K hK
    obtain ⟨φ, hφ_cw⟩ := exists_isClockwiseDiscHomeo B.disc
    obtain ⟨Ω, hbar, hag, -⟩ := exists_cyclicPerm_of_oArc P.Γ φ (hKV K hK) (hfin K hK)
      (fun v hv => by
        rw [subBd_eq_discBd_plane B.disc]
        exact B.bd v hv)
    exact ⟨Ω, hbar, φ, hφ_cw, agreesWith_of_drawing (hbar ▸ hKV K hK) hag⟩
  choose! Ω hΩ hag using hΩex
  obtain ⟨φ, hφ_cw, hφ⟩ := P.agrees_Δ
  have hΔ₀ex : ∃ Δ₀ : Set EuclideanPlane, (IsClosedDisc Δ₀ ∧ Δ₀ ⊆ P.Δ) ∧
      (∃ φ₀ : Circle ≃ₜ subBd Δ₀,
        IsClockwiseDiscHomeo Δ₀ φ₀ ∧ AgreesWithOArcHomeo (vertexPt P.Γ) N.Ω₀ (subBd Δ₀) φ₀) ∧
      Δ₀ ∩ subBd P.Δ ⊆ vertexPt P.Γ '' (N.Ω₀.bar ∩ N.Ω.bar) ∧
      ∀ K ∈ F, Δ₀ ∩ β K ⊆ vertexPt P.Γ '' (N.Ω₀.bar ∩ K) := by
    rcases P.agrees_Δ₀ with ⟨-, hemp⟩ | ⟨hd, φ₀, hφ₀_cw, hag₀⟩
    · let Z : Set EuclideanPlane := ⋃ K ∈ F, β K
      have hZ : IsClosed Z := C.finite.isClosed_biUnion fun K hK =>
        (hβ K hK).disc.isCompact.isClosed
      have hZf : (Z ∩ discBd P.Δ).Finite := by
        refine ((C.finite.biUnion hfin).image (vertexPt P.Γ)).subset ?_
        rintro x ⟨hx, hxb⟩
        obtain ⟨K, hK, hxK⟩ := mem_iUnion₂.mp hx
        rw [← subBd_eq_discBd_plane P.isClosedDisc_Δ] at hxb
        obtain ⟨v, hv, rfl⟩ := (hβ K hK).inter_bd ⟨hxK, hxb⟩
        exact mem_image_of_mem _ (mem_iUnion₂.mpr ⟨K, hK, hv.1⟩)
      obtain ⟨a, ha, haZ⟩ := exists_interior_point_off P.isClosedDisc_Δ hZ hZf
      obtain ⟨B, hBs, hBW, hBd, -, -⟩ := exists_small_disc_at P.isClosedDisc_Δ (interior_subset ha)
        (isOpen_interior.inter hZ.isOpen_compl) ⟨ha, haZ⟩
      obtain ⟨φ₀, hφ₀_cw⟩ := exists_isClockwiseDiscHomeo hBd
      refine ⟨B, ⟨hBd, hBs⟩, ⟨φ₀, hφ₀_cw, fun v hv => ?_, fun v₁ v₂ v₃ hc => ?_⟩, ?_,
        fun K hK => ?_⟩
      · rw [hemp] at hv
        exact hv.elim
      · have := hc.2.1 v₁ (by simp)
        rw [hemp] at this
        exact this.elim
      · rintro x ⟨hx, hxb⟩
        exact (disjoint_left.mp (disjoint_interior_subBd P.Δ) (hBW hx).1 hxb).elim
      · rintro x ⟨hx, hxK⟩
        exact ((hBW hx).2 (mem_iUnion₂.mpr ⟨K, hK, hxK⟩)).elim
    · refine ⟨P.Δ₀, ⟨hd, P.Δ₀_subset_Δ⟩, ⟨φ₀, hφ₀_cw, agreesWith_of_drawing N.bar₀_subset hag₀⟩,
        ?_, fun K hK x hx => (hβ K hK).inter₀ ⟨hx.2, hx.1⟩⟩
      rintro x ⟨hx₀, hxb⟩
      obtain ⟨v, hv, rfl⟩ := T.bd_U x (T.Δ₀_bd ⟨hx₀, hxb⟩) hxb
      exact T.pt_Δ₀ N.bar_subset (mem_image_of_mem _ hv) hx₀
  obtain ⟨Δ₀, h₀, h₁, h₂, h₃⟩ := hΔ₀ex
  exact ⟨P.Δ, Δ₀, vertexPt P.Γ, β, Ω, P.isClosedDisc_Δ, h₀,
    ⟨φ, hφ_cw, agreesWith_of_drawing N.bar_subset hφ⟩, h₁, h₂, vertexPt_injOn P.Γ,
    fun K hK => ⟨(hβ K hK).disc, (hβ K hK).sub⟩, hΩ, hag, h₃, fun K hK => (hβ K hK).inter_bd, hp⟩

/-- The last part of the proof of (11.11) of Graph Minors IX. A consolidation with least core and
a split of its core give a feasible segregation. -/
theorem exists_feasible_of_core_decomposition (S : Society α β)
    {D_set : Set (Graph α β × Graph α β)} (hD : IsConsolidation S D_set)
    (hmin_card : ∀ D_set' : Set (Graph α β × Graph α β), IsConsolidation S D_set' →
      V(consolidationCore S D_set').ncard = V(consolidationCore S D_set).ncard →
      D_set.ncard ≤ D_set'.ncard)
    (hCS_conn : (consolidationCoreSociety S D_set hD).IsKConnected 4)
    (hsimple : IsSimpleGraph (consolidationCoreSociety S D_set hD).G) {q : ℕ}
    {S₁ : Society α (Sym2 α)} {N₂ : Neighborhood α (Sym2 α)} {P : Presentation N₂}
    (hdecomp : CoreRuralDecomposition q (consolidationCoreSociety S D_set hD) S₁ N₂)
    (hT : IsTidyPresentation P) (hΔ₀c : P.Δ₀ = ∅ ∨ ¬ IsLeThreeClique N₂.G N₂.Ω₀.bar) :
    ∃ (k : ℕ) (S₀ : Society α β) (S_fam : Fin k → Society α β),
      IsFeasibleSegregation S S₀ S_fam ∧ S₀.Ω = S₁.Ω ∧
      (∀ i : Fin k, (S_fam i).Ω.bar.ncard ≤ 3) ∧
      (∀ P_set : Set (Graph α β), S₀.IsTransaction P_set → P_set.ncard ≤ q) := by
  classical
  let CS := consolidationCoreSociety S D_set hD
  have hK_all : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D_set →
      IsLeThreeClique S₁.G (V(A) ∩ V(B)) ∨ IsLeThreeClique N₂.G (V(A) ∩ V(B)) := by
    intro A B hAB
    have hfin_AB : (V(A) ∩ V(B)).Finite :=
      S.finite_V.subset (inter_subset_left.trans (hD.left_le hAB).vertexSet_mono)
    have hclique_C : IsLeThreeClique CS.G (V(A) ∩ V(B)) :=
      ⟨hD.inter_subset_consolidationCore hAB, hD.order_le_three hAB,
        fun u hu v hv huv => hD.consolidationCore_isLink_of_mem_inter hAB hu hv huv⟩
    exact isLeThreeClique_left_or_right hdecomp.C₁_le hdecomp.C₂_le hdecomp.union_eq
      hdecomp.triangle_in_left_or_right hfin_AB hclique_C
  let D₁ : Set (Graph α β × Graph α β) := {q ∈ D_set | IsLeThreeClique S₁.G (V(q.1) ∩ V(q.2))}
  let D₂ : Set (Graph α β × Graph α β) := D_set \ D₁
  have hD_union : D₁ ∪ D₂ = D_set := union_sdiff_cancel (fun _ h => h.1)
  have hD_disj : Disjoint D₁ D₂ := disjoint_sdiff_right
  have hD₁_clique : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D₁ → IsLeThreeClique S₁.G (V(A) ∩ V(B)) :=
    fun _ _ h => h.2
  have hD₂_clique : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D₂ → IsLeThreeClique N₂.G (V(A) ∩ V(B)) := by
    intro A B ⟨hAB, hnot₁⟩
    rcases hK_all hAB with h1 | h2
    · exact (hnot₁ ⟨hAB, h1⟩).elim
    · exact h2
  have hD₁_sub : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D₁ → V(A) ∩ V(B) ⊆ V(S₁.G) :=
    fun _ _ h => (hD₁_clique h).1
  have hD₂_sub : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D₂ → V(A) ∩ V(B) ⊆ V(N₂.G) :=
    fun _ _ h => (hD₂_clique h).1
  have hΩ_sub_C₂ : S.Ω.bar ⊆ V(N₂.G) := hdecomp.Ω_eq ▸ N₂.bar_subset
  let C_star : Graph α β := (S.G.induce (V(S₁.G) ∩ V(N₂.G))).restrict ∅
  let A₀ : Graph α β := subgraphUnion S.G C_star (subgraphSUnion S.G (Prod.fst '' D₁))
  have hA₀_le : A₀ ≤ S.G :=
    (lemma_11_11_claim_2 hD hdecomp.C₁_le hdecomp.C₂_le hdecomp.union_eq hΩ_sub_C₂
      hdecomp.inter_eq_bar₀ hD_union hD_disj hD₁_sub hD₂_sub).1.1.1
  let S₀ : Society α β := ⟨A₀, S₁.Ω, S.finite_V.subset hA₀_le.vertexSet_mono,
    S.finite_E.subset hA₀_le.edgeSet_mono, hdecomp.inter_eq_bar₀ ▸ subset_union_left⟩
  have hno_large_S₀ : ∀ P_set : Set (Graph α β), S₀.IsTransaction P_set → P_set.ncard ≤ q :=
    lemma_11_11_claim_4 hD hdecomp.C₁_le hdecomp.C₂_le hdecomp.union_eq hΩ_sub_C₂
      hdecomp.inter_eq_bar₀ hD_union hD_disj hD₁_clique hD₂_sub hdecomp.no_large_transaction
  have hfin_D₂ : D₂.Finite := hD.finite.subset sdiff_subset
  let e_D₂ : Fin hfin_D₂.toFinset.card ≃ hfin_D₂.toFinset := hfin_D₂.toFinset.equivFin.symm
  let k := hfin_D₂.toFinset.card
  let p_idx : Fin k → Graph α β × Graph α β := fun i => (e_D₂ i).1
  have hp_inj : Function.Injective p_idx := Subtype.val_injective.comp e_D₂.injective
  have hp_mem_D₂ : ∀ i : Fin k, p_idx i ∈ D₂ := fun i => hfin_D₂.mem_toFinset.mp (e_D₂ i).2
  have hp_range : range p_idx = D₂ := by
    ext q; simp only [p_idx, mem_range]
    exact ⟨by rintro ⟨i, rfl⟩; exact hp_mem_D₂ i,
      fun hq => ⟨e_D₂.symm ⟨q, hfin_D₂.mem_toFinset.mpr hq⟩, by simp⟩⟩
  have hp_clique : ∀ i : Fin k, IsLeThreeClique N₂.G (V((p_idx i).1) ∩ V((p_idx i).2)) :=
    fun i => hD₂_clique (hp_mem_D₂ i)
  have hp_mem_D : ∀ i : Fin k, p_idx i ∈ D_set := fun i => (hp_mem_D₂ i).1
  let F : Set (Set α) := (fun q : Graph α β × Graph α β => V(q.1) ∩ V(q.2)) '' D₂
  have hC : IsCliqueFamily P F := by
    refine ⟨hfin_D₂.image _, ?_, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨⟨A, B⟩, h, rfl⟩
      exact hD₂_clique h
    · rintro _ ⟨⟨A, B⟩, h, rfl⟩
      by_contra hn
      rw [not_nonempty_iff_eq_empty] at hn
      refine h.2 ⟨h.1, ?_⟩
      have hn' : V(A) ∩ V(B) = ∅ := hn
      change IsLeThreeClique S₁.G (V(A) ∩ V(B))
      rw [hn']
      exact ⟨empty_subset _, by simp, fun _ hu => hu.elim⟩
    · rintro _ ⟨⟨A, B⟩, h, rfl⟩ _ ⟨⟨A', B'⟩, h', rfl⟩ hsub
      by_contra hne
      refine lemma_11_11_claim_1 hD hmin_card h.1 h'.1 ?_ (hsub.trans inter_subset_left)
      intro heq
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact hne rfl
    · rintro v ⟨⟨A, B⟩, h, heq⟩ hv₀
      refine h.2 ⟨h.1, ?_⟩
      have heq' : V(A) ∩ V(B) = {v} := heq
      change IsLeThreeClique S₁.G (V(A) ∩ V(B))
      rw [heq']
      exact ⟨singleton_subset_iff.mpr (S₁.bar_subset (hdecomp.Ω₀_eq ▸ hv₀)), by simp,
        fun u hu w hw hne => (hne (hu.trans hw.symm)).elim⟩
    · rintro _ ⟨⟨A, B⟩, h, rfl⟩ h3
      exact exists_emptyRegion hdecomp hCS_conn (hsimple.mono hdecomp.C₂_le) P hΔ₀c
        (hD₂_clique h) h3
  obtain ⟨Δ, Δ₀, α_pt, β_disc, Ω_clique, hΔ, hΔ₀, hbd_Δ, hbd_Δ₀, hinter_bd_Δ₀, hinj_α, hβ_disc,
    hbar_clique, hbd_β, hinter_Δ₀, hinter_bd_Δ, hinter_β⟩ := exists_selection hT hC
  have hF : ∀ i : Fin k, V((p_idx i).1) ∩ V((p_idx i).2) ∈ F := fun i =>
    mem_image_of_mem _ (hp_mem_D₂ i)
  let S_fam : Fin k → Society α β := fun i =>
    { G := (p_idx i).1
      Ω := Ω_clique (V((p_idx i).1) ∩ V((p_idx i).2))
      finite_V := S.finite_V.subset (hD.left_le (hp_mem_D i)).vertexSet_mono
      finite_E := S.finite_E.subset (hD.left_le (hp_mem_D i)).edgeSet_mono
      bar_subset := by rw [hbar_clique _ (hF i)]; exact inter_subset_left }
  have hseg : IsSocietySegregation S S₀ S_fam :=
    lemma_11_11_claim_5 hD hdecomp.C₁_le hdecomp.C₂_le hdecomp.union_eq hΩ_sub_C₂
      hdecomp.inter_eq_bar₀ hD_union hD_disj hD₁_sub hD₂_sub hp_inj hp_range rfl rfl
      (fun _ => rfl) (fun i => hbar_clique _ (hF i))
  have hN₂_Ω : N₂.Ω = S.Ω := hdecomp.Ω_eq
  have hN₂_Ω₀ : N₂.Ω₀ = S₁.Ω := hdecomp.Ω₀_eq
  have harr : IsDiscArrangement S S₀ S_fam Δ Δ₀
      (fun i => β_disc (V((p_idx i).1) ∩ V((p_idx i).2))) α_pt := by
    refine ⟨hΔ, hΔ₀, fun i => hβ_disc _ (hF i), ?_, fun i => hbd_β _ (hF i),
      ?_, fun i => ?_, fun i j hij => ?_, ?_, fun i => ?_, ?_⟩
    · change ∃ φ₀ : Circle ≃ₜ subBd Δ₀,
        IsClockwiseDiscHomeo Δ₀ φ₀ ∧ AgreesWithOArcHomeo α_pt S₁.Ω (subBd Δ₀) φ₀
      rwa [← hN₂_Ω₀]
    · rwa [← hN₂_Ω]
    · change Δ₀ ∩ β_disc (V((p_idx i).1) ∩ V((p_idx i).2)) ⊆
        α_pt '' (S₁.Ω.bar ∩ (Ω_clique (V((p_idx i).1) ∩ V((p_idx i).2))).bar)
      rw [← hN₂_Ω₀, hbar_clique _ (hF i)]
      exact hinter_Δ₀ _ (hF i)
    · change β_disc (V((p_idx i).1) ∩ V((p_idx i).2)) ∩
        β_disc (V((p_idx j).1) ∩ V((p_idx j).2)) ⊆
        α_pt '' ((Ω_clique (V((p_idx i).1) ∩ V((p_idx i).2))).bar ∩
          (Ω_clique (V((p_idx j).1) ∩ V((p_idx j).2))).bar)
      rw [hbar_clique _ (hF i), hbar_clique _ (hF j)]
      have hK_ne : V((p_idx i).1) ∩ V((p_idx i).2) ≠ V((p_idx j).1) ∩ V((p_idx j).2) :=
        fun heq => hij (hp_inj (eq_of_inter_eq_of_minimal_consolidation hD hmin_card
          (hp_mem_D i) (hp_mem_D j) heq))
      exact hinter_β _ (hF i) _ (hF j) hK_ne
    · change Δ₀ ∩ subBd Δ ⊆ α_pt '' (S₁.Ω.bar ∩ S.Ω.bar)
      rwa [← hN₂_Ω₀, ← hN₂_Ω]
    · change β_disc (V((p_idx i).1) ∩ V((p_idx i).2)) ∩ subBd Δ ⊆
        α_pt '' ((Ω_clique (V((p_idx i).1) ∩ V((p_idx i).2))).bar ∩ S.Ω.bar)
      rw [hbar_clique _ (hF i), ← hN₂_Ω]
      exact hinter_bd_Δ _ (hF i)
    · refine hinj_α.mono (union_subset ?_ (iUnion_subset fun i => ?_))
      · change S₁.Ω.bar ⊆ V(N₂.G)
        rw [← hN₂_Ω₀]; exact N₂.bar₀_subset
      · change (Ω_clique (V((p_idx i).1) ∩ V((p_idx i).2))).bar ⊆ V(N₂.G)
        rw [hbar_clique _ (hF i)]; exact (hp_clique i).1
  refine ⟨k, S₀, S_fam, ⟨hseg, Δ, Δ₀, _, α_pt, harr⟩, rfl, fun i => ?_, hno_large_S₀⟩
  change (Ω_clique (V((p_idx i).1) ∩ V((p_idx i).2))).bar.ncard ≤ 3
  rw [hbar_clique _ (hF i)]
  exact (hp_clique i).2.1

/-- **Graph Minors IX, (11.11)** (pages 74–77):
"Let $p \ge 2$, with $p \neq 3$. Let $(G, \Omega)$ be a society with no crooked transaction
of cardinality $p$. Then there is a feasible segregation $\{(A_0, \Omega_0), \dots, (A_k,
\Omega_k)\}$ of $(G, \Omega)$ such that $|\bar{\Omega}_1|, \dots, |\bar{\Omega}_k| \le 3$
and $(A_0, \Omega_0)$ has no transaction of cardinality $> 3p + 9$." -/
theorem theorem_11_11_proof (S : Society α β) (p : ℕ) (hp2 : 2 ≤ p) (hp3 : p ≠ 3)
    (hno_crooked : ∀ P_set : Set (Graph α β), S.IsCrookedTransaction P_set → P_set.ncard ≠ p) :
    ∃ (k : ℕ) (S₀ : Society α β) (S_fam : Fin k → Society α β),
      IsFeasibleSegregation S S₀ S_fam ∧
      (∀ i : Fin k, (S_fam i).Ω.bar.ncard ≤ 3) ∧
      (∀ P_set : Set (Graph α β), S₀.IsTransaction P_set → P_set.ncard ≤ 3 * p + 9) := by
  classical
  obtain ⟨D_set, hD, hmin_core, hmin_card⟩ := exists_minimal_consolidation S
  let CS := consolidationCoreSociety S D_set hD
  have hCS_conn : CS.IsKConnected 4 := theorem_11_9_proof S D_set hD hmin_core
  have hCS_no_crooked : ∀ Q_set : Set (Graph α (Sym2 α)),
      CS.IsCrookedTransaction Q_set → Q_set.ncard ≠ p :=
    no_crooked_transaction_consolidationCoreSociety hD hno_crooked
  have hsimple : IsSimpleGraph CS.G := isSimpleGraph_consolidationCore S D_set
  have hsoph : CS.HasSophisticationLE (3 * p + 7) :=
    (Society.theorem_6_1_proof hp2 hp3 (fun k' hk' => hCS_conn k' (by omega))
      (fun k' hk' G₁ G₂ h => hCS_conn k' hk' G₁ G₂ h.1) hCS_no_crooked).1
  obtain ⟨S₁, N₂, P, hdecomp, hT, hΔ₀c⟩ := exists_core_decomposition hCS_conn hsimple hsoph
  obtain ⟨k, S₀, S_fam, hF, -, hbar, hno⟩ :=
    exists_feasible_of_core_decomposition S hD hmin_card hCS_conn hsimple hdecomp hT hΔ₀c
  exact ⟨k, S₀, S_fam, hF, hbar, hno⟩

end GraphMinor.GM09
