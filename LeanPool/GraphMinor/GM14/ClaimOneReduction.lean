/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.SegregationReplace
public import LeanPool.GraphMinor.GM14.ForestClaim

/-!
# Claim (1) of (8.4)

"We proceed by induction on $|V(G_1)| + |E(G_1)|$. We claim that we may assume that (1) ..." (page
41).
`exists_reduced` is this induction. A member of the segregation with a smaller `A'` is replaced
(`exists_replacement`), and a crooked transaction survives by `claim_1_of_8_4`. At the end Claim (1)
holds, and the final graph is a subgraph of the first one, so a transaction in it is one in the
first.
-/


@[expose] public section

namespace GraphMinor.GM14

open Set Topology Graph GraphMinor GraphMinor.GM09 GraphMinor.Surface GraphMinor.GM11
  GraphMinor.GM06

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]

/-- Claim (1) of (8.4), for one member `S₀` of the segregation, with `H ∩ A` given by `η`. -/
def ClaimOne {G₁ : Graph α β} {H : Drawing S} (η : SpanEmbedding H G₁) (S₀ : Society α β) : Prop :=
  ∀ A' : Graph α β, A' ≤ S₀.G → S₀.Ω.bar ⊆ V(A') → pieceGraph η S₀.G ≤ A' → E(A').Nonempty →
    PreservesBarPaths S₀ A' → A' = S₀.G

/-- One step: a smaller segregation with the same arrangement. -/
theorem exists_reduction_step {H : Drawing S} {α_pt : α → S} {S₂ S_G : Society α β}
    {N : Neighborhood α β} {η : SpanEmbedding H N.G} {S_seg : Set (Society α β)}
    {α_disc : Society α β → Set S} {pi : ℕ}
    (hseg : IsThreeSegregation N.G S_seg) (harr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hcompat : IsCompatibleWith N.G H η S_seg α_disc α_pt)
    (hΩ : N.Ω.bar ⊆ segregationVertices S_seg) (hΩ₀ : N.Ω₀.bar ⊆ segregationVertices S_seg)
    (hcomp : S_G.IsComposition S₂ N)
    (hcr : ∃ P_set, S_G.IsCrookedTransaction P_set ∧ pi ≤ P_set.ncard)
    {S₀ : Society α β} (hS₀ : S₀ ∈ S_seg) {A' : Graph α β} (hA' : A' ≤ S₀.G)
    (hbar : S₀.Ω.bar ⊆ V(A')) (hH : pieceGraph η S₀.G ≤ A') (hE : E(A').Nonempty)
    (hpres : PreservesBarPaths S₀ A') (hne : A' ≠ S₀.G) :
    ∃ (N' : Neighborhood α β) (S_G' : Society α β) (η' : SpanEmbedding H N'.G)
      (S_seg' : Set (Society α β)) (α_disc' : Society α β → Set S),
      N'.G ≤ N.G ∧ N'.Ω = N.Ω ∧ N'.Ω₀ = N.Ω₀ ∧ S_G'.Ω = S_G.Ω ∧ S_G'.G ≤ S_G.G ∧
      IsThreeSegregation N'.G S_seg' ∧ IsSurfaceArrangement S_seg' α_disc' α_pt ∧
      IsCompatibleWith N'.G H η' S_seg' α_disc' α_pt ∧
      segregationVertices S_seg' = segregationVertices S_seg ∧
      η'.imageGraph = η.imageGraph ∧ η'.vMap = η.vMap ∧ η'.eMap = η.eMap ∧
      (∀ S' ∈ S_seg', ∃ S₁ ∈ S_seg, α_disc' S' = α_disc S₁) ∧
      V(N'.G).ncard + E(N'.G).ncard < V(N.G).ncard + E(N.G).ncard ∧
      S_G'.IsComposition S₂ N' ∧ ∃ P_set, S_G'.IsCrookedTransaction P_set ∧ pi ≤ P_set.ncard := by
  classical
  obtain ⟨⟨⟨hS₂G, hNG, hVun, hEun, hEdis⟩, hbarN⟩, hΩeq, hΩ₀eq, hS₂bar⟩ := hcomp
  obtain ⟨S_seg', α_disc', G₁', η', hG₁', hseg', harr', hcompat', hsegV, him, hvm, hem, hdisc,
    hdrop, hV', hE'⟩ := exists_replacement N.finite_V N.finite_E hseg harr hcompat hS₀ hA' hbar hH
      hE hne
  have hS₀N := hseg.1.le S₀ hS₀
  have hS₀G : S₀.G ≤ S_G.G := hS₀N.trans hNG
  have hrest : ∀ S₁ ∈ S_seg, S₁.G ≤ S_G.G := fun S₁ h => (hseg.1.le S₁ h).trans hNG
  -- A vertex of `V(S_seg)` is in `V(A)` only if it is in `ΩBar`.
  have hbar₀ : ∀ x ∈ segregationVertices S_seg, x ∈ V(S₀.G) →
      x ∈ S₀.Ω.bar ∨ ∃ S₁ ∈ S_seg, S₁ ≠ S₀ ∧ x ∈ V(S₁.G) := by
    intro x hx _
    obtain ⟨S₁, h₁, hx₁⟩ := mem_iUnion₂.mp hx
    by_cases h : S₁ = S₀
    · exact Or.inl (h ▸ hx₁)
    · exact Or.inr ⟨S₁, h₁, h, S₁.bar_subset hx₁⟩
  -- The rest of the graph.
  let barG : Graph α β := (S_G.G.induce S₀.Ω.bar).restrict ∅
  have hbarG : barG ≤ S_G.G :=
    restrict_le.trans (induce_le (S₀.bar_subset.trans hS₀G.vertexSet_mono))
  have hbarE : E(barG) = ∅ := by
    simp [barG]
  let T : Set (Graph α β) := insert barG (insert S₂.G ((fun S₁ : Society α β => S₁.G) ''
    (S_seg \ {S₀})))
  have hT : ∀ P ∈ T, P ≤ S_G.G := by
    rintro P (rfl | rfl | ⟨S₁, ⟨h₁, -⟩, rfl⟩)
    · exact hbarG
    · exact hS₂G
    · exact hrest S₁ h₁
  let B : Graph α β := subgraphSUnion S_G.G T
  have hB : B ≤ S_G.G := subgraphSUnion_le hT
  have hBV : V(B) = S₀.Ω.bar ∪ (V(S₂.G) ∪ ⋃ S₁ ∈ S_seg \ {S₀}, V(S₁.G)) := by
    simp only [B, T, vertexSet_subgraphSUnion, biUnion_insert, biUnion_image]
    rfl
  have hBE : E(B) = E(S₂.G) ∪ ⋃ S₁ ∈ S_seg \ {S₀}, E(S₁.G) := by
    simp only [B]
    rw [edgeSet_subgraphSUnion hT]
    simp only [T, biUnion_insert, biUnion_image, hbarE, empty_union]
  have hVS : V(S_G.G) = V(S₂.G) ∪ (V(S₀.G) ∪ ⋃ S₁ ∈ S_seg \ {S₀}, V(S₁.G)) := by
    rw [← hVun]
    congr 1
    conv_lhs => rw [← hseg.1.union_eq]
    simp only [vertexSet_subgraphSUnion, biUnion_image]
    rw [← biUnion_insert (t := fun S₁ : Society α β => V(S₁.G)) S₀, insert_sdiff_singleton,
      insert_eq_of_mem hS₀]
  have hES : E(S_G.G) = E(S₂.G) ∪ (E(S₀.G) ∪ ⋃ S₁ ∈ S_seg \ {S₀}, E(S₁.G)) := by
    rw [← hEun]
    congr 1
    conv_lhs => rw [← hseg.1.union_eq]
    rw [edgeSet_subgraphSUnion (by rintro _ ⟨S₁, hS₁, rfl⟩; exact hseg.1.le S₁ hS₁)]
    simp only [biUnion_image]
    rw [← biUnion_insert (t := fun S₁ : Society α β => E(S₁.G)) S₀, insert_sdiff_singleton,
      insert_eq_of_mem hS₀]
  have hSep : IsGraphSeparation S_G.G S₀.G B := by
    refine ⟨hS₀G, hB, ?_, ?_, ?_⟩
    · rw [hBV, hVS]
      ext x
      simp only [mem_union]
      have : x ∈ S₀.Ω.bar → x ∈ V(S₀.G) := fun h => S₀.bar_subset h
      tauto
    · rw [hBE, hES]
      ext x
      simp only [mem_union]
      tauto
    · rw [hBE]
      refine disjoint_union_right.mpr ⟨?_, disjoint_iUnion₂_right.mpr ?_⟩
      · exact (hEdis.mono_right hS₀N.edgeSet_mono).symm
      · rintro S₁ ⟨h₁, hn₁⟩
        exact hseg.1.edge_disjoint S₀ hS₀ S₁ h₁ (Ne.symm hn₁)
  have hInter : V(S₀.G) ∩ V(B) = S₀.Ω.bar := by
    refine Subset.antisymm ?_ fun x hx => ⟨S₀.bar_subset hx, hBV ▸ Or.inl hx⟩
    rintro x ⟨hx₀, hxB⟩
    rw [hBV] at hxB
    have hoth : ∀ S₁ ∈ S_seg, S₁ ≠ S₀ → x ∈ V(S₁.G) → x ∈ S₀.Ω.bar := fun S₁ h₁ hn hx₁ =>
      (hseg.1.vertex_inter_subset S₀ hS₀ S₁ h₁ (Ne.symm hn) ⟨hx₀, hx₁⟩).1
    rcases hxB with h | h | h
    · exact h
    · have hxb : x ∈ N.Ω₀.bar := by
        rw [hΩ₀eq, hS₂bar]
        exact ⟨h, hS₀N.vertexSet_mono hx₀⟩
      rcases hbar₀ x (hΩ₀ hxb) hx₀ with h' | ⟨S₁, h₁, hn, hx₁⟩
      · exact h'
      · exact hoth S₁ h₁ hn hx₁
    · obtain ⟨S₁, ⟨h₁, hn⟩, hx₁⟩ := mem_iUnion₂.mp h
      exact hoth S₁ h₁ hn hx₁
  have hΩ₁B : S_G.Ω.bar ⊆ V(B) := by
    intro x hx
    rw [hBV]
    obtain ⟨S₁, h₁, hx₁⟩ := mem_iUnion₂.mp (hΩ (hΩeq ▸ hx))
    by_cases h : S₁ = S₀
    · exact Or.inl (h ▸ hx₁)
    · exact Or.inr (Or.inr (mem_iUnion₂.mpr ⟨S₁, ⟨h₁, h⟩, S₁.bar_subset hx₁⟩))
  have hA'G : A' ≤ S_G.G := hA'.trans hS₀G
  let U : Graph α β := subgraphUnion S_G.G A' B
  have hUle : U ≤ S_G.G := subgraphUnion_le hA'G hB
  have hUV : V(U) = V(A') ∪ (V(S₂.G) ∪ ⋃ S₁ ∈ S_seg \ {S₀}, V(S₁.G)) := by
    simp only [U, vertexSet_subgraphUnion]
    rw [hBV]
    ext x
    simp only [mem_union]
    have : x ∈ S₀.Ω.bar → x ∈ V(A') := fun h => hbar h
    tauto
  have hUE : E(U) = E(A') ∪ (E(S₂.G) ∪ ⋃ S₁ ∈ S_seg \ {S₀}, E(S₁.G)) := by
    simp only [U]
    rw [edgeSet_subgraphUnion hA'G hB, hBE]
  have hG₁'le : G₁' ≤ U := by
    refine le_of_subset_of_subset (hG₁'.trans hNG) hUle ?_ ?_
    · rw [hV', hUV]
      exact union_subset_union_right _ subset_union_right
    · rw [hE', hUE]
      exact union_subset_union_right _ subset_union_right
  have hS₂U : S₂.G ≤ U := by
    refine le_of_subset_of_subset hS₂G hUle ?_ ?_
    · rw [hUV]
      exact subset_union_left.trans subset_union_right
    · rw [hUE]
      exact subset_union_left.trans subset_union_right
  -- A vertex of `V(S_seg)` stays in the new graph.
  have hsegG' : segregationVertices S_seg ⊆ V(G₁') := by
    intro x hx
    rw [← hsegV] at hx
    obtain ⟨S₁, h₁, hx₁⟩ := mem_iUnion₂.mp hx
    exact (hseg'.1.le S₁ h₁).vertexSet_mono (S₁.bar_subset hx₁)
  let N' : Neighborhood α β := ⟨G₁', N.Ω, N.Ω₀, N.finite_V.subset hG₁'.vertexSet_mono,
    N.finite_E.subset hG₁'.edgeSet_mono, hΩ.trans hsegG', hΩ₀.trans hsegG'⟩
  let S_G' : Society α β := ⟨U, S_G.Ω, S_G.finite_V.subset hUle.vertexSet_mono,
    S_G.finite_E.subset hUle.edgeSet_mono, hΩ₁B.trans subset_union_right⟩
  have hcomp' : S_G'.IsComposition S₂ N' := by
    refine ⟨⟨⟨hS₂U, hG₁'le, ?_, ?_, ?_⟩, ?_⟩, hΩeq, hΩ₀eq, ?_⟩
    · change V(S₂.G) ∪ V(G₁') = V(U)
      rw [hV', hUV]
      ext x
      simp only [mem_union]
      tauto
    · change E(S₂.G) ∪ E(G₁') = E(U)
      rw [hE', hUE]
      ext x
      simp only [mem_union]
      tauto
    · exact hEdis.mono_right hG₁'.edgeSet_mono
    · change S_G.Ω.bar ⊆ V(G₁')
      exact fun x hx => hsegG' (hΩ (hΩeq ▸ hx))
    · change S₂.Ω.bar = V(S₂.G) ∩ V(G₁')
      refine Subset.antisymm (fun x hx => ⟨?_, ?_⟩) ?_
      · rw [hS₂bar] at hx
        exact hx.1
      · exact hsegG' (hΩ₀ (hΩ₀eq ▸ hx))
      · rintro x ⟨h₁, h₂⟩
        rw [hS₂bar]
        exact ⟨h₁, hG₁'.vertexSet_mono h₂⟩
  obtain ⟨P_set, hP, hc⟩ := hcr
  obtain ⟨P', hP', hc'⟩ := claim_1_of_8_4 (S₁' := S_G') hSep hInter
    (S₀.finite_V.subset S₀.bar_subset) (hseg.2 S₀ hS₀) hA' hpres hΩ₁B rfl rfl hP hc
  exact ⟨N', S_G', η', S_seg', α_disc', hG₁', rfl, rfl, rfl, hUle, hseg', harr', hcompat', hsegV,
    him, hvm, hem, hdisc, hdrop, hcomp', P', hP', hc'⟩

/-- **Claim (1) of (8.4).** See the module docstring. -/
theorem exists_reduced {H : Drawing S} {α_pt : α → S} {S₂ : Society α β} {pi : ℕ} :
    ∀ (n : ℕ) (S_G : Society α β) (N : Neighborhood α β) (η : SpanEmbedding H N.G)
      (S_seg : Set (Society α β)) (α_disc : Society α β → Set S),
      V(N.G).ncard + E(N.G).ncard = n →
      IsThreeSegregation N.G S_seg → IsSurfaceArrangement S_seg α_disc α_pt →
      IsCompatibleWith N.G H η S_seg α_disc α_pt →
      N.Ω.bar ⊆ segregationVertices S_seg → N.Ω₀.bar ⊆ segregationVertices S_seg →
      S_G.IsComposition S₂ N →
      (∃ P_set, S_G.IsCrookedTransaction P_set ∧ pi ≤ P_set.ncard) →
      ∃ (N' : Neighborhood α β) (S_G' : Society α β) (η' : SpanEmbedding H N'.G)
        (S_seg' : Set (Society α β)) (α_disc' : Society α β → Set S),
        N'.G ≤ N.G ∧ N'.Ω = N.Ω ∧ N'.Ω₀ = N.Ω₀ ∧ S_G'.Ω = S_G.Ω ∧ S_G'.G ≤ S_G.G ∧
        IsThreeSegregation N'.G S_seg' ∧ IsSurfaceArrangement S_seg' α_disc' α_pt ∧
        IsCompatibleWith N'.G H η' S_seg' α_disc' α_pt ∧
        segregationVertices S_seg' = segregationVertices S_seg ∧
        η'.imageGraph = η.imageGraph ∧ η'.vMap = η.vMap ∧ η'.eMap = η.eMap ∧
        (∀ S' ∈ S_seg', ∃ S₁ ∈ S_seg, α_disc' S' = α_disc S₁) ∧
        S_G'.IsComposition S₂ N' ∧
        (∃ P_set, S_G'.IsCrookedTransaction P_set ∧ pi ≤ P_set.ncard) ∧
        ∀ S₀ ∈ S_seg', ClaimOne η' S₀ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S_G N η S_seg α_disc hn hseg harr hcompat hΩ hΩ₀ hcomp hcr
    by_cases hall : ∀ S₀ ∈ S_seg, ClaimOne η S₀
    · exact ⟨N, S_G, η, S_seg, α_disc, le_rfl, rfl, rfl, rfl, le_rfl, hseg, harr, hcompat, rfl,
        rfl, rfl, rfl, fun S' h => ⟨S', h, rfl⟩, hcomp, hcr, hall⟩
    · unfold ClaimOne at hall
      push Not at hall
      obtain ⟨S₀, hS₀, A', hA', hbar, hH, hE, hpres, hne⟩ := hall
      obtain ⟨N₁, S₁, η₁, seg₁, d₁, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄,
        h₁₅, h₁₆⟩ := exists_reduction_step hseg harr hcompat hΩ hΩ₀ hcomp hcr hS₀ hA' hbar hH hE
          hpres hne
      obtain ⟨N₂, S₂', η₂, seg₂, d₂, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, k₉, k₁₀, k₁₁, k₁₂, k₁₃, k₁₄,
        k₁₅, k₁₆⟩ := ih _ (hn ▸ h₁₄) S₁ N₁ η₁ seg₁ d₁ rfl h₆ h₇ h₈
          (h₂.symm ▸ h₉.symm ▸ hΩ) (h₃.symm ▸ h₉.symm ▸ hΩ₀) h₁₅ h₁₆
      refine ⟨N₂, S₂', η₂, seg₂, d₂, k₁.trans h₁, k₂.trans h₂, k₃.trans h₃, k₄.trans h₄,
        k₅.trans h₅, k₆, k₇, k₈, k₉.trans h₉, k₁₀.trans h₁₀, k₁₁.trans h₁₁, k₁₂.trans h₁₂, ?_, k₁₄,
        k₁₅, k₁₆⟩
      intro S' hS'
      obtain ⟨S₃, hS₃, e₁⟩ := k₁₃ S' hS'
      obtain ⟨S₄, hS₄, e₂⟩ := h₁₃ S₃ hS₃
      exact ⟨S₄, hS₄, e₁.trans e₂⟩

end GraphMinor.GM14
