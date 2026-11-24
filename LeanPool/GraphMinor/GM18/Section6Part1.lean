/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM04.Decomposition.Rotund
public import LeanPool.GraphMinor.GM04.Patchwork.Stars
public import LeanPool.GraphMinor.GM18.Section5
import LeanPool.GraphMinor.GM04.Patchwork.Menger
import LeanPool.GraphMinor.Thomas.RootedTree

/-!
# Graph Minors XVIII, Section 6 (Part 1): Well-Behavedness and Rooted Decompositions

This file formalizes (6.1)–(6.5) of Section 6 (pages 100–104) of Robertson and Seymour,
*Graph Minors. XVIII. Tree-decompositions and well-quasi-ordering*, J. Combin. Theory Ser. B 89
(2003), 77–108:

- `theorem_6_1` (6.1, page 100): the class of all rootings of rootless members of a well-behaved
  class is well-behaved.
- `theorem_6_2` (6.2, page 101): the class of all robust partial `Ω`-patchworks of tree-width `≤ w`
  is well-behaved (assuming Graph Minors IV, (9.1)).
- `theorem_6_3` (6.3, page 101): if `𝒞₁, 𝒞₂` are well-behaved classes of partial `Ω`-patchworks,
  then `enlargementClass 𝒞₁ 𝒞₂` is well-behaved.
- `theorem_6_4` (6.4, page 102): every rotund tree-decomposition `(S, σ)` of `‖P‖⁻` for a rootless
  robust `Ω`-patchwork `P` lifts to a rooted decomposition `(T, τ)` of `P` on any arborescence `T`
  with `T⁻ = S`.
- `theorem_6_5_1`, `theorem_6_5_2`, `theorem_6_5_3`, and `theorem_6_5` (6.5, page 103, with Claims
  (1)–(3) `lemma_6_5_claim_1`–`lemma_6_5_claim_3`): structural properties of subtrees, root sides,
  and child locations in a rooted decomposition of a rootless `Ω`-patchwork.
-/

public section

namespace GraphMinor.GM18

open SimpleGraph Hypergraph

universe u v w

variable {α : Type u} {β : Type v} {Ω : Type w}

/-! ## Disjoint unions of well-quasi-orders and basic properties of `WellBehaved` -/

/-- The left injection `Sum.inl` as an order embedding into `DisjointUnionQuasiOrder Ω₁ Ω₂`. -/
@[expose] def DisjointUnionQuasiOrder.inlEmb (Ω₁ Ω₂ : Type*) [Preorder Ω₁] [Preorder Ω₂] :
    Ω₁ ↪o DisjointUnionQuasiOrder Ω₁ Ω₂ where
  toFun := Sum.inl
  inj' _ _ h := Sum.inl.inj h
  map_rel_iff' := by
    intro a b
    constructor
    · intro h
      cases h with
      | inl hab => exact hab
    · exact DisjointUnionLE.inl

/-- The right injection `Sum.inr` as an order embedding into `DisjointUnionQuasiOrder Ω₁ Ω₂`. -/
@[expose] def DisjointUnionQuasiOrder.inrEmb (Ω₁ Ω₂ : Type*) [Preorder Ω₁] [Preorder Ω₂] :
    Ω₂ ↪o DisjointUnionQuasiOrder Ω₁ Ω₂ where
  toFun := Sum.inr
  inj' _ _ h := Sum.inr.inj h
  map_rel_iff' := by
    intro a b
    constructor
    · intro h
      cases h with
      | inr hab => exact hab
    · exact DisjointUnionLE.inr

/-- If `Ω₁` and `Ω₂` are well-quasi-orders, then their disjoint union `DisjointUnionQuasiOrder Ω₁
Ω₂`
is a well-quasi-order. -/
theorem wellQuasiOrderedLE_disjointUnion {Ω₁ Ω₂ : Type*} [Preorder Ω₁] [Preorder Ω₂]
    (h₁ : WellQuasiOrderedLE Ω₁) (h₂ : WellQuasiOrderedLE Ω₂) :
    WellQuasiOrderedLE (DisjointUnionQuasiOrder Ω₁ Ω₂) := by
  refine ⟨fun f ↦ ?_⟩
  let S₁ : Set ℕ := {n | ∃ a : Ω₁, f n = Sum.inl a}
  let S₂ : Set ℕ := {n | ∃ b : Ω₂, f n = Sum.inr b}
  have huniv : (Set.univ : Set ℕ) ⊆ S₁ ∪ S₂ := by
    intro n _
    rcases hfn : f n with a | b
    · exact Or.inl ⟨a, hfn⟩
    · exact Or.inr ⟨b, hfn⟩
  have hinf : (S₁ ∪ S₂).Infinite := Set.infinite_univ.mono huniv
  rcases Set.infinite_union.1 hinf with hS₁ | hS₂
  · have : Infinite S₁ := hS₁.to_subtype
    let e := Nat.Subtype.orderIsoOfNat S₁
    choose g hg using fun k : ℕ ↦ (e k).2
    obtain ⟨m, n, hmn, hle⟩ := h₁.wqo g
    refine ⟨(e m).1, (e n).1, e.strictMono hmn, ?_⟩
    change DisjointUnionLE (f (e m).1) (f (e n).1)
    rw [hg m, hg n]
    exact DisjointUnionLE.inl hle
  · have : Infinite S₂ := hS₂.to_subtype
    let e := Nat.Subtype.orderIsoOfNat S₂
    choose g hg using fun k : ℕ ↦ (e k).2
    obtain ⟨m, n, hmn, hle⟩ := h₂.wqo g
    refine ⟨(e m).1, (e n).1, e.strictMono hmn, ?_⟩
    change DisjointUnionLE (f (e m).1) (f (e n).1)
    rw [hg m, hg n]
    exact DisjointUnionLE.inr hle

/-- A subset of a well-behaved class is well-behaved. -/
theorem WellBehaved.mono [Preorder Ω] {𝒞₁ 𝒞₂ : Set (PartialPatchwork Ω α β)}
    (hsub : 𝒞₁ ⊆ 𝒞₂) (h₂ : WellBehaved 𝒞₂) : WellBehaved 𝒞₁ :=
  fun Ω' _ ι hΩ' Q hQ ↦
    h₂ Ω' ι hΩ' Q fun i ↦
      let ⟨P, hP, hcomp⟩ := hQ i
      ⟨P, hsub hP, hcomp⟩

/-- The union of two well-behaved classes is well-behaved (Graph Minors XVIII, page 105). -/
theorem WellBehaved.union [Preorder Ω] {𝒞₁ 𝒞₂ : Set (PartialPatchwork Ω α β)}
    (h₁ : WellBehaved 𝒞₁) (h₂ : WellBehaved 𝒞₂) : WellBehaved (𝒞₁ ∪ 𝒞₂) := by
  intro Ω' _ ι hΩ' Q hQ
  let S₁ : Set ℕ := {n | ∃ P ∈ 𝒞₁, IsCompletion ι P (Q n)}
  let S₂ : Set ℕ := {n | ∃ P ∈ 𝒞₂, IsCompletion ι P (Q n)}
  have huniv : (Set.univ : Set ℕ) ⊆ S₁ ∪ S₂ := by
    intro n _
    obtain ⟨P, hP₁ | hP₂, hcomp⟩ := hQ n
    · exact Or.inl ⟨P, hP₁, hcomp⟩
    · exact Or.inr ⟨P, hP₂, hcomp⟩
  rcases Set.infinite_union.1 (Set.infinite_univ.mono huniv) with hS₁ | hS₂
  · have : Infinite S₁ := hS₁.to_subtype
    let e := Nat.Subtype.orderIsoOfNat S₁
    obtain ⟨m, n, hmn, hsim⟩ := h₁ Ω' ι hΩ' (fun k ↦ Q (e k).1) (fun k ↦ (e k).2)
    exact ⟨(e m).1, (e n).1, e.strictMono hmn, hsim⟩
  · have : Infinite S₂ := hS₂.to_subtype
    let e := Nat.Subtype.orderIsoOfNat S₂
    obtain ⟨m, n, hmn, hsim⟩ := h₂ Ω' ι hΩ' (fun k ↦ Q (e k).1) (fun k ↦ (e k).2)
    exact ⟨(e m).1, (e n).1, e.strictMono hmn, hsim⟩

/-- Restricting a completion `Q` of `P` to `A ≤ P.G` yields a completion `Q | A` of `P | A`. -/
theorem IsCompletion.restrict {Ω' : Type*} [Preorder Ω] [Preorder Ω'] {ι : Ω ↪o Ω'}
    {P : PartialPatchwork Ω α β} {Q : GM04.Patchwork Ω' α β} (h : IsCompletion ι P Q)
    {A : RootedHypergraph α β} (hA : A.toHypergraph ≤ P.G.toHypergraph) :
    IsCompletion ι (P.restrict A) (Q.restrict A) where
  G_eq := rfl
  dom_eq := by
    have hA_Q : A.toHypergraph ≤ Q.G.toHypergraph := h.G_eq.symm ▸ hA
    rw [Q.restrict_dom hA_Q, P.restrict_dom hA, h.dom_eq]
  μ_eq e he := by
    rw [P.restrict_dom hA] at he
    exact h.μ_eq he.1
  Δ_eq e he := by
    have hA_Q : A.toHypergraph ≤ Q.G.toHypergraph := h.G_eq.symm ▸ hA
    rw [Q.restrict_Δ hA_Q he, P.restrict_Δ hA he]
    exact h.Δ_eq (hA.edgeSet_subset he)
  φ_eq e he ω hφ :=
    h.φ_eq (hA.edgeSet_subset he) hφ

/-! ## Theorem (6.1): Rootings of rootless members of a well-behaved class -/

/-- **Graph Minors XVIII, (6.1)** (page 100):
"Let $\Omega$ be a well-quasi-order, and let $\mathcal{C}$ be a well-behaved class of partial
$\Omega$-patchworks. Let $\mathcal{C}'$ be the class of all rootings of rootless members of
$\mathcal{C}$. Then $\mathcal{C}'$ is well-behaved." -/
theorem theorem_6_1_proof [Preorder Ω] {𝒞 : Set (PartialPatchwork Ω α β)} (h𝒞 : WellBehaved 𝒞) :
    WellBehaved {P' : PartialPatchwork Ω α β | ∃ P ∈ 𝒞, IsRooting P P'} := by
  classical
  intro Ω' _ ι hΩ' Q' hQ'
  let UnitType := PUnit.{max w (max u v) + 1}
  have hUnit_wqo : WellQuasiOrderedLE UnitType := Finite.to_wellQuasiOrderedLE
  let Ω'' := DisjointUnionQuasiOrder Ω' UnitType
  have hΩ''_wqo : WellQuasiOrderedLE Ω'' := wellQuasiOrderedLE_disjointUnion hΩ' hUnit_wqo
  let inlEmb := DisjointUnionQuasiOrder.inlEmb Ω' UnitType
  let ι'' : Ω ↪o Ω'' := ι.trans inlEmb
  choose P' hP'_mem hcomp' using hQ'
  choose P hP_mem hrooting using hP'_mem
  choose hrootless e he_dom he_φ hle hdel hroots hrestr using hrooting
  let Q : ℕ → GM04.Patchwork Ω'' α β := fun i ↦
    { G := (P i).G
      dom := (P i).dom
      μ := (P i).μ
      Δ := (P i).Δ
      φ := fun x ↦ if x = e i then Sum.inr PUnit.unit else Sum.inl ((Q' i).φ x)
      dom_subset := (P i).dom_subset
      μ_nodup := (P i).μ_nodup
      μ_set := (P i).μ_set
      Δ_verts := (P i).Δ_verts
      Δ_free := (P i).Δ_free }
  have hQ_comp : ∀ i, ∃ P₀ ∈ 𝒞, IsCompletion ι'' P₀ (Q i) := by
    intro i
    refine ⟨P i, hP_mem i, ⟨rfl, rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl, ?_⟩⟩
    intro x hx ω hx_φ
    have hx_ne : x ≠ e i := by
      rintro rfl
      rw [he_φ i] at hx_φ
      exact WithBot.coe_ne_bot hx_φ.symm
    have hx_P' : x ∈ (P' i).G.edgeSet := by
      rw [hdel i]
      exact ⟨hx, hx_ne⟩
    have hx_φ' : (P' i).φ x = (ω : WithBot Ω) := by
      rw [hrestr i]
      exact hx_φ
    have hQ'_φ : (Q' i).φ x = ι ω := (hcomp' i).φ_eq hx_P' hx_φ'
    change (if x = e i then Sum.inr PUnit.unit else Sum.inl ((Q' i).φ x)) = Sum.inl (ι ω)
    rw [ite_eq_right hx_ne, hQ'_φ]
  obtain ⟨i, j, hij, ηv, ηe, hexp, H, hH_real, hH_comp⟩ := h𝒞 Ω'' ι'' hΩ''_wqo Q hQ_comp
  have hei_edge : e i ∈ (Q i).G.edgeSet := (P i).dom_subset (he_dom i)
  have hη_ei_eq : ηe (e i) = e j := by
    have hφ_le := hexp.φ_le (e i) hei_edge
    change DisjointUnionLE (if e i = e i then Sum.inr PUnit.unit else Sum.inl ((Q' i).φ (e i)))
      (if ηe (e i) = e j then Sum.inr PUnit.unit else Sum.inl ((Q' j).φ (ηe (e i)))) at hφ_le
    rw [ite_eq_left rfl] at hφ_le
    by_cases hEq : ηe (e i) = e j
    · exact hEq
    · rw [ite_eq_right hEq] at hφ_le
      nomatch hφ_le
  have hV_eq : ∀ k, (Q' k).G.vertexSet = (Q k).G.vertexSet := by
    intro k
    rw [(hcomp' k).G_eq]
    change (P' k).G.toHypergraph.vertexSet = (P k).G.vertexSet
    rw [hdel k]
    rfl
  have hE_eq : ∀ k, (Q' k).G.edgeSet = (Q k).G.edgeSet \ {e k} := by
    intro k
    rw [(hcomp' k).G_eq]
    change (P' k).G.toHypergraph.edgeSet = (P k).G.edgeSet \ {e k}
    rw [hdel k]
    rfl
  have hdom_eq : ∀ k, (Q' k).dom = (Q k).dom ∩ (Q' k).G.edgeSet := by
    intro k
    rw [(hcomp' k).dom_eq, (hcomp' k).G_eq, hrestr k, (P k).restrict_dom (hle k)]
    rfl
  have hends_eq : ∀ k x, x ∈ (Q' k).G.edgeSet → (Q' k).G.ends x = (Q k).G.ends x := by
    intro k x hx
    rw [(hcomp' k).G_eq] at hx ⊢
    exact ((hle k).ends_eq x hx).symm
  have hμ_eq : ∀ k x, x ∈ (Q' k).dom → (Q' k).μ x = (Q k).μ x := by
    intro k x hx
    rw [(hcomp' k).dom_eq] at hx
    rw [(hcomp' k).μ_eq hx, hrestr k]
    rfl
  have hΔ_eq : ∀ k x, x ∈ (Q' k).G.edgeSet → (Q' k).Δ x = (Q k).Δ x := by
    intro k x hx
    rw [(hcomp' k).G_eq] at hx
    rw [(hcomp' k).Δ_eq hx, hrestr k, (P k).restrict_Δ (hle k) hx]
  have hηe_maps : ∀ x ∈ (Q' i).G.edgeSet, ηe x ∈ (Q' j).G.edgeSet := by
    intro x hx
    rw [hE_eq i] at hx
    rw [hE_eq j]
    refine ⟨hexp.edge_mem x hx.1, ?_⟩
    intro hEq
    exact hx.2 (hexp.edge_injOn hx.1 hei_edge (hEq.trans hη_ei_eq.symm))
  refine ⟨i, j, hij, ηv, ηe, ?_, H, ?_⟩
  · refine
      { vertex_nonempty := fun v hv ↦ hexp.vertex_nonempty v (hV_eq i ▸ hv)
        vertex_subset := fun v hv ↦ hV_eq j ▸ hexp.vertex_subset v (hV_eq i ▸ hv)
        edge_mem := hηe_maps
        vertex_disjoint := fun v₁ hv₁ v₂ hv₂ hne ↦
          hexp.vertex_disjoint v₁ (hV_eq i ▸ hv₁) v₂ (hV_eq i ▸ hv₂) hne
        edge_injOn := fun x₁ hx₁ x₂ hx₂ ↦
          hexp.edge_injOn ((hE_eq i ▸ hx₁).1) ((hE_eq i ▸ hx₂).1)
        mem_dom_iff := fun x hx ↦ by
          have hx_Qi : x ∈ (Q i).G.edgeSet := (hE_eq i ▸ hx).1
          have hηx_Q'j : ηe x ∈ (Q' j).G.edgeSet := hηe_maps x hx
          rw [hdom_eq i, hdom_eq j]
          exact ⟨fun ⟨hd, _⟩ ↦ ⟨(hexp.mem_dom_iff x hx_Qi).1 hd, hηx_Q'j⟩,
            fun ⟨hd', _⟩ ↦ ⟨(hexp.mem_dom_iff x hx_Qi).2 hd', hx⟩⟩
        ends_nonempty := fun x hx hnd v hinc ↦ by
          have hx_Qi : x ∈ (Q i).G.edgeSet := (hE_eq i ▸ hx).1
          have hnd_Qi : x ∉ (Q i).dom := fun hd ↦ hnd ((hdom_eq i).symm ▸ ⟨hd, hx⟩)
          have hinc_Qi : (Q i).G.Inc x v := by
            change v ∈ (Q i).G.ends x
            rw [← hends_eq i x hx]
            exact hinc
          obtain ⟨v', hv', hinc'⟩ := hexp.ends_nonempty x hx_Qi hnd_Qi v hinc_Qi
          refine ⟨v', hv', ?_⟩
          change v' ∈ (Q' j).G.ends (ηe x)
          rw [hends_eq j (ηe x) (hηe_maps x hx)]
          exact hinc'
        μ_length := fun x hx ↦ by
          have hx_E : x ∈ (Q' i).G.edgeSet := (Q' i).dom_subset hx
          have hx_Qi_dom : x ∈ (Q i).dom := ((hdom_eq i) ▸ hx).1
          have hηx_dom : ηe x ∈ (Q' j).dom := by
            rw [hdom_eq j]
            exact ⟨(hexp.mem_dom_iff x ((hE_eq i ▸ hx_E).1)).1 hx_Qi_dom, hηe_maps x hx_E⟩
          rw [hμ_eq i x hx, hμ_eq j (ηe x) hηx_dom]
          exact hexp.μ_length x hx_Qi_dom
        μ_mem := fun x hx k hk hk' ↦ by
          have hx_E : x ∈ (Q' i).G.edgeSet := (Q' i).dom_subset hx
          have hx_Qi_dom : x ∈ (Q i).dom := ((hdom_eq i) ▸ hx).1
          have hηx_dom : ηe x ∈ (Q' j).dom := by
            rw [hdom_eq j]
            exact ⟨(hexp.mem_dom_iff x ((hE_eq i ▸ hx_E).1)).1 hx_Qi_dom, hηe_maps x hx_E⟩
          have hk₁ : k < ((Q i).μ x).length := (hμ_eq i x hx) ▸ hk
          have hk₂ : k < ((Q j).μ (ηe x)).length := (hμ_eq j (ηe x) hηx_dom) ▸ hk'
          have hmem := hexp.μ_mem x hx_Qi_dom k hk₁ hk₂
          simpa [hμ_eq i x hx, hμ_eq j (ηe x) hηx_dom] using hmem
        roots_length := by
          rw [(hcomp' i).G_eq, (hcomp' j).G_eq, hroots i, hroots j, ← hη_ei_eq]
          exact hexp.μ_length (e i) (he_dom i)
        roots_mem := fun k hk hk' ↦ by
          have hri : (Q' i).G.roots = (Q i).μ (e i) := by
            rw [(hcomp' i).G_eq, hroots i]
          have hrj : (Q' j).G.roots = (Q j).μ (ηe (e i)) := by
            rw [(hcomp' j).G_eq, hroots j, hη_ei_eq]
          have hk₁ : k < ((Q i).μ (e i)).length := hri ▸ hk
          have hk₂ : k < ((Q j).μ (ηe (e i))).length := hrj ▸ hk'
          have hmem := hexp.μ_mem (e i) (he_dom i) k hk₁ hk₂
          simpa [hri, hrj] using hmem
        maps_Δ := fun x hx ↦ by
          have hx_E : x ∈ (Q' i).G.edgeSet := (Q' i).dom_subset hx
          have hx_Qi_dom : x ∈ (Q i).dom := ((hdom_eq i) ▸ hx).1
          have hηx_E : ηe x ∈ (Q' j).G.edgeSet := hηe_maps x hx_E
          have hηx_dom : ηe x ∈ (Q' j).dom := by
            rw [hdom_eq j]
            exact ⟨(hexp.mem_dom_iff x ((hE_eq i ▸ hx_E).1)).1 hx_Qi_dom, hηx_E⟩
          rw [hμ_eq i x hx, hμ_eq j (ηe x) hηx_dom, hΔ_eq i x hx_E, hΔ_eq j (ηe x) hηx_E]
          exact hexp.maps_Δ x hx_Qi_dom
        φ_le := fun x hx ↦ by
          have hx_Qi : x ∈ (Q i).G.edgeSet := (hE_eq i ▸ hx).1
          have hx_ne : x ≠ e i := (hE_eq i ▸ hx).2
          have hηx_ne : ηe x ≠ e j := (hE_eq j ▸ hηe_maps x hx).2
          have hφ_le := hexp.φ_le x hx_Qi
          change DisjointUnionLE (if x = e i then Sum.inr PUnit.unit else Sum.inl ((Q' i).φ x))
            (if ηe x = e j then Sum.inr PUnit.unit else Sum.inl ((Q' j).φ (ηe x))) at hφ_le
          rw [ite_eq_right hx_ne, ite_eq_right hηx_ne] at hφ_le
          cases hφ_le with
          | inl hle_φ => exact hle_φ }
  · refine ⟨?_, fun v hv ↦ hH_comp v (hV_eq i ▸ hv)⟩
    obtain ⟨δ, hδ, hH_eq⟩ := hH_real
    have hdiff_eq : (Q' j).G.edgeSet \ (ηe '' (Q' i).G.edgeSet) =
        (Q j).G.edgeSet \ (ηe '' (Q i).G.edgeSet) := by
      rw [hE_eq i, hE_eq j]
      ext y
      simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_image]
      constructor
      · rintro ⟨⟨hy_Qj, hy_ne_ej⟩, hnot⟩
        refine ⟨hy_Qj, ?_⟩
        rintro ⟨x, hx_Qi, rfl⟩
        by_cases hx_ei : x = e i
        · subst hx_ei; exact hy_ne_ej hη_ei_eq
        · exact hnot ⟨x, ⟨hx_Qi, hx_ei⟩, rfl⟩
      · rintro ⟨hy_Qj, hnot⟩
        refine ⟨⟨hy_Qj, ?_⟩, ?_⟩
        · rintro rfl
          exact hnot ⟨e i, hei_edge, hη_ei_eq⟩
        · rintro ⟨x, ⟨hx_Qi, _⟩, rfl⟩
          exact hnot ⟨x, hx_Qi, rfl⟩
    refine ⟨δ, fun y hy ↦ ?_, ?_⟩
    · have hy_Q'j : y ∈ (Q' j).G.edgeSet := hy.1
      have hy_diff : y ∈ (Q j).G.edgeSet \ (ηe '' (Q i).G.edgeSet) := hdiff_eq ▸ hy
      change δ y ∈ (Q' j).Δ y
      rw [hΔ_eq j y hy_Q'j]
      exact hδ y hy_diff
    · rw [hH_eq]
      change GM04.emptySubgraph (Q j).G.vertexSet ⊔
          (⨆ y ∈ (Q j).G.edgeSet \ (ηe '' (Q i).G.edgeSet), δ y) =
        GM04.emptySubgraph (Q' j).G.vertexSet ⊔
          (⨆ y ∈ (Q' j).G.edgeSet \ (ηe '' (Q' i).G.edgeSet), δ y)
      rw [hV_eq j, hdiff_eq]

/-! ## Theorem (6.2): Robust partial patchworks of bounded tree-width -/

/-- If a patchwork `P` has `HasPatchworkTreeWidthLE P w`, then its underlying rooted hypergraph
`P.G` satisfies `GM04.TreeWidthLE P.G w`. -/
theorem treeWidthLE_of_hasPatchworkTreeWidthLE {P : GM04.Patchwork Ω α β} {w : ℕ}
    (htw : HasPatchworkTreeWidthLE P w) : GM04.TreeWidthLE P.G w := by
  classical
  obtain ⟨ι, hfin, T, τ, t₀, htd, hw, hroots_sub⟩ := htw
  let : Fintype ι := hfin
  let m := Fintype.card ι
  have hm : 0 < m := Fintype.card_pos_iff.2 ⟨t₀⟩
  let e₀ : ι ≃ Fin m := Fintype.equivFin ι
  let zeroFin : Fin m := ⟨0, hm⟩
  let e : ι ≃ Fin m := e₀.trans (Equiv.swap (e₀ t₀) zeroFin)
  have he_t₀ : e t₀ = zeroFin := by
    simp [e, Equiv.swap_apply_left]
  have he_symm_zero : e.symm zeroFin = t₀ :=
    e.symm_apply_eq.2 he_t₀.symm
  let K : SimpleGraph (Fin m) := T.map e.toEmbedding
  have htd_K : GM10.IsTreeDecomposition P.G.toHypergraph K (τ ∘ e.symm) := htd.relabel e
  have hK : K.IsTree := htd_K.isTree
  let T_r : GM04.RootedTree ℕ := Thomas.rootedTreeOfIsTree hK
  let bagRoots : ℕ → List α := fun n ↦
    if hn : n < m then
      if n = 0 then P.G.roots
      else
        (((τ (e.symm ⟨n, hn⟩)).vertexSet_finite.subset Set.inter_subset_left :
          ((τ (e.symm ⟨n, hn⟩)).vertexSet ∩
            (τ (e.symm (Thomas.parentFin hK ⟨n, hn⟩))).vertexSet).Finite)).toFinset.toList
    else []
  let τ_r : ℕ → RootedHypergraph α β := fun n ↦
    if hn : n < m then
      { toHypergraph := τ (e.symm ⟨n, hn⟩)
        roots := bagRoots n
        roots_nodup := by
          dsimp only [bagRoots]
          rw [dite_eq_left hn]
          split_ifs with h0
          · exact P.G.roots_nodup
          · exact Finset.nodup_toList _
        roots_subset := by
          intro v hv
          dsimp only [bagRoots] at hv
          rw [dite_eq_left hn] at hv
          split_ifs at hv with h0
          · subst h0
            have hEq : (⟨0, hn⟩ : Fin m) = zeroFin := rfl
            rw [hEq, he_symm_zero]
            exact hroots_sub hv
          · rw [Finset.mem_toList, Set.Finite.mem_toFinset] at hv
            exact hv.1 }
    else
      { toHypergraph :=
          { vertexSet := ∅
            edgeSet := ∅
            Inc := fun _ _ ↦ False
            vertex_mem_of_inc := fun _ _ h ↦ h.elim
            edge_mem_of_inc := fun _ _ h ↦ h.elim
            vertexSet_finite := Set.finite_empty
            edgeSet_finite := Set.finite_empty }
        roots := []
        roots_nodup := List.nodup_nil
        roots_subset := fun _ h ↦ (List.not_mem_nil h).elim }
  have hτ_r_toH : ∀ {n : ℕ} (hn : n < m), (τ_r n).toHypergraph = τ (e.symm ⟨n, hn⟩) := by
    intro n hn
    dsimp only [τ_r]
    rw [dite_eq_left hn]
  have hτ_r_roots : ∀ {n : ℕ} (hn : n < m), (τ_r n).roots = bagRoots n := by
    intro n hn
    dsimp only [τ_r]
    split_ifs
    rfl
  have hverts_eq : T_r.verts = Finset.range m := rfl
  refine ⟨T_r, τ_r, ?_, ?_⟩
  · refine
      { le := fun n hn ↦ by
          have hn_lt : n < m := Finset.mem_range.1 hn
          rw [hτ_r_toH hn_lt]
          exact htd_K.le ⟨n, hn_lt⟩
        biUnion_eq := by
          refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
            (biUnion_le fun n hn ↦ by
              have hn_lt : n < m := Finset.mem_range.1 hn
              rw [hτ_r_toH hn_lt]
              exact htd_K.le ⟨n, hn_lt⟩)
            le_rfl ?_ ?_
          · rw [hverts_eq, ← htd_K.biUnion_eq]
            ext x
            simp only [Hypergraph.biUnion, Set.mem_iUnion, Finset.mem_range, Finset.mem_univ,
              exists_prop, true_and, Function.comp_apply]
            exact ⟨fun ⟨n, hn, hx⟩ ↦ ⟨⟨n, hn⟩, by rwa [← hτ_r_toH hn]⟩,
              fun ⟨t, hx⟩ ↦ ⟨t.1, t.2, by rw [hτ_r_toH t.2]; exact hx⟩⟩
          · rw [hverts_eq, ← htd_K.biUnion_eq]
            ext x
            simp only [Hypergraph.biUnion, Set.mem_iUnion, Finset.mem_range, Finset.mem_univ,
              exists_prop, true_and, Function.comp_apply]
            exact ⟨fun ⟨n, hn, hx⟩ ↦ ⟨⟨n, hn⟩, by rwa [← hτ_r_toH hn]⟩,
              fun ⟨t, hx⟩ ↦ ⟨t.1, t.2, by rw [hτ_r_toH t.2]; exact hx⟩⟩
        edgeSet_inter_eq := fun n₁ hn₁ n₂ hn₂ hne ↦ by
          have h₁ : n₁ < m := Finset.mem_range.1 hn₁
          have h₂ : n₂ < m := Finset.mem_range.1 hn₂
          rw [hτ_r_toH h₁, hτ_r_toH h₂]
          exact htd_K.edgeSet_inter_eq (fun hEq ↦ hne (congrArg Fin.val hEq))
        inter_le := fun n₁ hn₁ n₂ hn₂ n₃ hn₃ hon ↦ by
          have h₁ : n₁ < m := Finset.mem_range.1 hn₁
          have h₂ : n₂ < m := Finset.mem_range.1 hn₂
          have h₃ : n₃ < m := Finset.mem_range.1 hn₃
          rw [hτ_r_toH h₁, hτ_r_toH h₂, hτ_r_toH h₃]
          exact htd_K.inter_le
            ((Thomas.onPath_rootedTreeOfIsTree_iff hK ⟨n₁, hn₁⟩ ⟨n₃, hn₃⟩ ⟨n₂, hn₂⟩).1 hon)
        roots_root := by
          change (τ_r 0).roots = P.G.roots
          rw [hτ_r_roots hm]
          dsimp only [bagRoots]
          rw [dite_eq_left hm, ite_eq_left rfl]
        rootSet_edge := fun f hf ↦ by
          have hf_verts : f ∈ T_r.verts := Thomas.mem_verts_of_mem_edges T_r hf
          have hf_ne_0 : f ≠ 0 := Thomas.ne_root_of_mem_edges T_r hf
          have hf_lt : f < m := Finset.mem_range.1 hf_verts
          have hpar_lt : T_r.parent f < m :=
            Finset.mem_range.1 (T_r.parent_mem f hf_verts)
          have hpar_eq : (⟨T_r.parent f, hpar_lt⟩ : Fin m) = Thomas.parentFin hK ⟨f, hf_lt⟩ := by
            ext
            change (if hn : f < m then (Thomas.parentFin hK ⟨f, hn⟩).val else 0) = _
            rw [dite_eq_left hf_lt]
          rw [hτ_r_toH hf_lt, hτ_r_toH hpar_lt, hpar_eq]
          change {v | v ∈ (τ_r f).roots} = _
          rw [hτ_r_roots hf_lt]
          dsimp only [bagRoots]
          rw [dite_eq_left hf_lt, ite_eq_right hf_ne_0]
          ext v
          simp only [Set.mem_ofPred_eq, Finset.mem_toList, Set.Finite.mem_toFinset,
            Hypergraph.inter_vertexSet] }
  · intro n hn
    have hn_lt : n < m := Finset.mem_range.1 hn
    change (τ_r n).toHypergraph.vertexSet.ncard ≤ w + 1
    rw [hτ_r_toH hn_lt]
    have hle_t : (τ (e.symm ⟨n, hn_lt⟩)).vertexSet.ncard ≤ GM10.treeDecompWidthPlusOne τ :=
      le_csSup (Set.finite_range _).bddAbove ⟨e.symm ⟨n, hn_lt⟩, rfl⟩
    change (GM10.treeDecompWidthPlusOne τ : ℤ) - 1 ≤ (w : ℤ) at hw
    omega

/-- **Graph Minors XVIII, (6.2)** (page 101):
"If $\Omega$ is a well-quasi-order and $w \ge 0$, the class of all robust partial
$\Omega$-patchworks of tree-width $\le w$ is well-behaved." -/
theorem theorem_6_2_proof
    [Preorder Ω] (w : ℕ) :
    WellBehaved {P : PartialPatchwork Ω α β | P.IsRobust ∧ HasPatchworkTreeWidthLE P w} := by
  intro Ω' _ ι hΩ' Q hQ
  apply gm04Theorem91 w Q hΩ'
  · intro i
    obtain ⟨P, ⟨hrob, _⟩, hcomp⟩ := hQ i
    intro e he
    rw [hcomp.G_eq] at he
    rw [hcomp.Δ_eq he]
    exact hrob e he
  · intro i
    obtain ⟨P, ⟨_, htw⟩, hcomp⟩ := hQ i
    rw [hcomp.G_eq]
    exact treeWidthLE_of_hasPatchworkTreeWidthLE htw

/-! ## Theorem (6.3): Enlargements of well-behaved classes -/

/-- Viewing an `Ω'`-patchwork `P` as a partial `Ω'`-patchwork with total label function. -/
@[expose] def toPartialPatchwork {Ω' : Type*} (P : GM04.Patchwork Ω' α β) : PartialPatchwork Ω' α β
  where
  G := P.G
  dom := P.dom
  μ := P.μ
  Δ := P.Δ
  φ e := (P.φ e : WithBot Ω')
  dom_subset := P.dom_subset
  μ_nodup := P.μ_nodup
  μ_set := P.μ_set
  Δ_verts := P.Δ_verts
  Δ_free := P.Δ_free

/-- Simulation of `P₁` in `P₂` is equivalent to simulation of `toPartialPatchwork P₁` in
`toPartialPatchwork P₂`. -/
theorem simulated_toPartialPatchwork_iff {Ω' : Type*} [Preorder Ω']
    {P₁ P₂ : GM04.Patchwork Ω' α β} :
    GM04.Simulated (toPartialPatchwork P₁) (toPartialPatchwork P₂) ↔ GM04.Simulated P₁ P₂ := by
  refine ⟨fun ⟨ηv, ηe, hexp, hreal⟩ ↦ ⟨ηv, ηe, ⟨?_, hreal⟩⟩,
    fun ⟨ηv, ηe, hexp, hreal⟩ ↦ ⟨ηv, ηe, ⟨?_, hreal⟩⟩⟩
  · refine
      { vertex_nonempty := hexp.vertex_nonempty
        vertex_subset := hexp.vertex_subset
        edge_mem := hexp.edge_mem
        vertex_disjoint := hexp.vertex_disjoint
        edge_injOn := hexp.edge_injOn
        mem_dom_iff := hexp.mem_dom_iff
        ends_nonempty := hexp.ends_nonempty
        μ_length := hexp.μ_length
        μ_mem := hexp.μ_mem
        roots_length := hexp.roots_length
        roots_mem := hexp.roots_mem
        maps_Δ := hexp.maps_Δ
        φ_le := fun e he ↦ WithBot.coe_le_coe.1 (hexp.φ_le e he) }
  · refine
      { vertex_nonempty := hexp.vertex_nonempty
        vertex_subset := hexp.vertex_subset
        edge_mem := hexp.edge_mem
        vertex_disjoint := hexp.vertex_disjoint
        edge_injOn := hexp.edge_injOn
        mem_dom_iff := hexp.mem_dom_iff
        ends_nonempty := hexp.ends_nonempty
        μ_length := hexp.μ_length
        μ_mem := hexp.μ_mem
        roots_length := hexp.roots_length
        roots_mem := hexp.roots_mem
        maps_Δ := hexp.maps_Δ
        φ_le := fun e he ↦ WithBot.coe_le_coe.2 (hexp.φ_le e he) }

open Classical in
private noncomputable def completionHeart {Ω' : Type*}
    (P₁ : GM04.Patchwork Ω' α β) (P₃ : PartialPatchwork Ω α β)
    (ℒ : Set (RootedHypergraph α β)) : PartialPatchwork Ω' α β :=
  { G := P₃.G
    dom := P₃.dom
    μ := P₃.μ
    Δ := P₃.Δ
    φ := fun e ↦
      if e ∈ (rootedLocationCore P₁.G ℒ).edgeSet then (P₁.φ e : WithBot Ω') else ⊥
    dom_subset := P₃.dom_subset
    μ_nodup := P₃.μ_nodup
    μ_set := P₃.μ_set
    Δ_verts := P₃.Δ_verts
    Δ_free := P₃.Δ_free }

private theorem isPlaceHeart_completionHeart {Ω' : Type*} [Preorder Ω] [Preorder Ω']
    {ι : Ω ↪o Ω'} {P₁ : GM04.Patchwork Ω' α β} {P₂ P₃ : PartialPatchwork Ω α β}
    {ℒ : Set (RootedHypergraph α β)} {newEdge : RootedHypergraph α β → β}
    (hcomp : IsCompletion ι P₂ P₁) (hℒ : IsRootedLocation P₂.G ℒ)
    (hheart : IsPlaceHeart P₂ ℒ newEdge P₃) :
    IsPlaceHeart (toPartialPatchwork P₁) ℒ newEdge (completionHeart P₁ P₃ ℒ) := by
  classical
  have hG_eq : P₁.G = P₂.G := hcomp.G_eq
  refine
    { isRootedLocation := hG_eq ▸ hℒ
      injOn_newEdge := hheart.injOn_newEdge
      newEdge_notMem_core := hG_eq ▸ hheart.newEdge_notMem_core
      vertexSet_eq := hG_eq ▸ hheart.vertexSet_eq
      edgeSet_eq := hG_eq ▸ hheart.edgeSet_eq
      roots_eq := hG_eq ▸ hheart.roots_eq
      ends_core := hG_eq ▸ hheart.ends_core
      ends_newEdge := hheart.ends_newEdge
      dom_eq := by
        change P₃.dom =
          (rootedLocationCore P₁.G ℒ).edgeSet ∩ P₁.dom ∪ newEdge '' ℒ
        rw [hG_eq, hheart.dom_eq, hcomp.dom_eq]
      μ_core := fun e he ↦ by
        change e ∈ (rootedLocationCore P₁.G ℒ).edgeSet ∩ P₁.dom at he
        rw [hG_eq] at he
        have he₂ : e ∈ (rootedLocationCore P₂.G ℒ).edgeSet ∩ P₂.dom :=
          ⟨he.1, hcomp.dom_eq ▸ he.2⟩
        change P₃.μ e = P₁.μ e
        rw [hheart.μ_core he₂]
        exact (hcomp.μ_eq he₂.2).symm
      μ_newEdge := hheart.μ_newEdge
      Δ_core := fun e he ↦ by
        change e ∈ (rootedLocationCore P₁.G ℒ).edgeSet at he
        rw [hG_eq] at he
        have he_P₂ : e ∈ P₂.G.edgeSet := (mem_rootedLocationCore_edgeSet_iff.1 he).1
        change P₃.Δ e = P₁.Δ e
        rw [hheart.Δ_core he]
        exact (hcomp.Δ_eq he_P₂).symm
      Δ_newEdge := fun A hA ↦ by
        change P₃.Δ (newEdge A) = _
        rw [hheart.Δ_newEdge hA]
        have hle_A : A.toHypergraph ≤ P₂.G.toHypergraph := ((hℒ).isComplemented hA).le
        have hle_A₁ : A.toHypergraph ≤ P₁.G.toHypergraph := hG_eq ▸ hle_A
        have hreal_iff : ∀ H₀, (P₂.restrict A).IsRealization H₀ ↔
            ((toPartialPatchwork P₁).restrict A).IsRealization H₀ := by
          intro H₀
          refine ⟨fun ⟨δ₀, hδ₀, hH₀⟩ ↦ ⟨δ₀, fun e he ↦ ?_, hH₀⟩,
            fun ⟨δ₀, hδ₀, hH₀⟩ ↦ ⟨δ₀, fun e he ↦ ?_, hH₀⟩⟩
          · have h := hδ₀ e he
            change δ₀ e ∈ (P₂.restrict A).Δ e at h
            rw [P₂.restrict_Δ hle_A he] at h
            change δ₀ e ∈ ((toPartialPatchwork P₁).restrict A).Δ e
            rw [(toPartialPatchwork P₁).restrict_Δ hle_A₁ he]
            change δ₀ e ∈ P₁.Δ e
            rw [hcomp.Δ_eq (hle_A.edgeSet_subset he)]
            exact h
          · have h := hδ₀ e he
            change δ₀ e ∈ ((toPartialPatchwork P₁).restrict A).Δ e at h
            rw [(toPartialPatchwork P₁).restrict_Δ hle_A₁ he] at h
            change δ₀ e ∈ P₁.Δ e at h
            rw [hcomp.Δ_eq (hle_A.edgeSet_subset he)] at h
            change δ₀ e ∈ (P₂.restrict A).Δ e
            rw [P₂.restrict_Δ hle_A he]
            exact h
        have hfg_eq : {δ | IsFeasibleGrouping (P₂.restrict A) δ} =
            {δ | IsFeasibleGrouping ((toPartialPatchwork P₁).restrict A) δ} := by
          ext δ
          exact ⟨fun ⟨hgrp, hv, H₀, hH₀, hc⟩ ↦ ⟨hgrp, hv, H₀, (hreal_iff H₀).1 hH₀, hc⟩,
            fun ⟨hgrp, hv, H₀, hH₀, hc⟩ ↦ ⟨hgrp, hv, H₀, (hreal_iff H₀).2 hH₀, hc⟩⟩
        exact GM04.Patch.ext rfl hfg_eq
      φ_core := fun e he ↦ ite_eq_left he
      φ_newEdge := fun A hA ↦ by
        have hnot : newEdge A ∉ (rootedLocationCore P₁.G ℒ).edgeSet := by
          rw [hcomp.G_eq]
          exact hheart.newEdge_notMem_core hA
        exact ite_eq_right hnot }

/-- **Graph Minors XVIII, (6.3)** (page 101):
"Let $\Omega$ be a well-quasi-order, and let $\mathcal{C}_1, \mathcal{C}_2$ be well-behaved
classes of partial $\Omega$-patchworks. Then the class of all enlargements of members of
$\mathcal{C}_1$ by $\mathcal{C}_2$ is well-behaved." -/
theorem theorem_6_3_proof [Preorder Ω] {𝒞₁ 𝒞₂ : Set (PartialPatchwork Ω α β)}
    (h𝒞₁ : WellBehaved 𝒞₁) (h𝒞₂ : WellBehaved 𝒞₂) :
    WellBehaved (enlargementClass 𝒞₁ 𝒞₂) := by
  classical
  intro Ω' _ ι hΩ' P₁ hP₁
  -- `Ω''` is the subtype of `Ω'`-completions of members of `𝒞₂`, ordered by simulation.
  let Ω'' := {R : GM04.Patchwork Ω' α β // ∃ P ∈ 𝒞₂, IsCompletion ι P R}
  let : Preorder Ω'' :=
    { le := fun R₁ R₂ ↦ GM04.Simulated R₁.1 R₂.1
      le_refl := fun R ↦ GM04.Simulated.refl R.1
      le_trans := fun _ _ _ h₁₂ h₂₃ ↦ h₁₂.trans h₂₃ }
  have hΩ''_wqo : WellQuasiOrderedLE Ω'' :=
    ⟨fun f ↦ h𝒞₂ Ω' ι hΩ' (fun i ↦ (f i).1) (fun i ↦ (f i).2)⟩
  let Ω_star := DisjointUnionQuasiOrder Ω' Ω''
  have hΩ_star_wqo : WellQuasiOrderedLE Ω_star := wellQuasiOrderedLE_disjointUnion hΩ' hΩ''_wqo
  let inlEmb := DisjointUnionQuasiOrder.inlEmb Ω' Ω''
  let ι_star : Ω ↪o Ω_star := ι.trans inlEmb
  -- Unpack `P₂ i ∈ enlargementClass 𝒞₁ 𝒞₂`, `P₃ i ∈ 𝒞₁`, `ℒ i`, `newEdge i`.
  choose P₂ hP₂_enl hcomp₁ using hP₁
  choose P₃ hP₃_mem ℒ hℒ hheart₃_has hA_mem using hP₂_enl
  choose newEdge hheart₃ using hheart₃_has
  -- For each `i` and `A ∈ ℒ i`, `(P₁ i).restrict A` is an `Ω'`-completion of `(P₂ i).restrict A ∈
  -- 𝒞₂`.
  have hcomp_restrict : ∀ i ⦃A : RootedHypergraph α β⦄, A ∈ ℒ i →
      ∃ P ∈ 𝒞₂, IsCompletion ι P ((P₁ i).restrict A) := by
    intro i A hA
    exact ⟨(P₂ i).restrict A, hA_mem i A hA,
      (hcomp₁ i).restrict ((hℒ i).isComplemented hA).le⟩
  -- Construct `enc (P₁ i) = P₄ i : GM04.Patchwork Ω_star α β`.
  let P₄ : ℕ → GM04.Patchwork Ω_star α β := fun i ↦
    { G := (P₃ i).G
      dom := (P₃ i).dom
      μ := (P₃ i).μ
      Δ := (P₃ i).Δ
      φ := fun e ↦
        if h : ∃ A ∈ ℒ i, newEdge i A = e then
          Sum.inr ⟨(P₁ i).restrict h.choose, hcomp_restrict i h.choose_spec.1⟩
        else
          Sum.inl ((P₁ i).φ e)
      dom_subset := (P₃ i).dom_subset
      μ_nodup := (P₃ i).μ_nodup
      μ_set := (P₃ i).μ_set
      Δ_verts := (P₃ i).Δ_verts
      Δ_free := (P₃ i).Δ_free }
  -- `P₄ i` is an `Ω_star`-completion of `P₃ i ∈ 𝒞₁`.
  have hP₄_comp : ∀ i, ∃ P₀ ∈ 𝒞₁, IsCompletion ι_star P₀ (P₄ i) := by
    intro i
    refine ⟨P₃ i, hP₃_mem i, ⟨rfl, rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl, ?_⟩⟩
    intro e he ω hφ₃
    have hnot_new : ¬ ∃ A ∈ ℒ i, newEdge i A = e := by
      rintro ⟨A, hA, rfl⟩
      rw [(hheart₃ i).φ_newEdge hA] at hφ₃
      exact WithBot.coe_ne_bot hφ₃.symm
    have he_core : e ∈ (rootedLocationCore (P₂ i).G (ℒ i)).edgeSet := by
      rw [(hheart₃ i).edgeSet_eq] at he
      rcases he with he_c | ⟨A, hA, rfl⟩
      · exact he_c
      · exact (hnot_new ⟨A, hA, rfl⟩).elim
    have he_P₂ : e ∈ (P₂ i).G.edgeSet := (mem_rootedLocationCore_edgeSet_iff.1 he_core).1
    have hφ₂ : (P₂ i).φ e = (ω : WithBot Ω) := by
      rw [← (hheart₃ i).φ_core he_core, hφ₃]
    have hφ₁ : (P₁ i).φ e = ι ω := (hcomp₁ i).φ_eq he_P₂ hφ₂
    change (if h : ∃ A ∈ ℒ i, newEdge i A = e then _ else Sum.inl ((P₁ i).φ e)) = Sum.inl (ι ω)
    rw [dite_eq_right hnot_new, hφ₁]
  -- Since `𝒞₁` is well-behaved, `P₄ i` is simulated in `P₄ j` for some `i < j`.
  obtain ⟨i, j, hij, ηv, ηe, hexp, H, hH_real, hH_comp⟩ :=
    h𝒞₁ Ω_star ι_star hΩ_star_wqo P₄ hP₄_comp
  refine ⟨i, j, hij, ?_⟩
  let Q : ℕ → PartialPatchwork Ω' α β := fun k ↦ completionHeart (P₁ k) (P₃ k) (ℒ k)
  have hQ_heart (k : ℕ) : IsPlaceHeart (toPartialPatchwork (P₁ k)) (ℒ k) (newEdge k) (Q k) :=
    isPlaceHeart_completionHeart (hcomp₁ k) (hℒ k) (hheart₃ k)
  -- Verify that `(ηv, ηe)` is a realizable expansion of `Q i` in `Q j` satisfying
  -- `theorem_5_7_proof`.
  have hη_Q : GM04.IsRealizableExpansion (Q i) (Q j) ηv ηe := by
    refine ⟨?_, H, hH_real, hH_comp⟩
    refine
      { vertex_nonempty := hexp.vertex_nonempty
        vertex_subset := hexp.vertex_subset
        edge_mem := hexp.edge_mem
        vertex_disjoint := hexp.vertex_disjoint
        edge_injOn := hexp.edge_injOn
        mem_dom_iff := hexp.mem_dom_iff
        ends_nonempty := hexp.ends_nonempty
        μ_length := hexp.μ_length
        μ_mem := hexp.μ_mem
        roots_length := hexp.roots_length
        roots_mem := hexp.roots_mem
        maps_Δ := hexp.maps_Δ
        φ_le := fun e he ↦ by
          by_cases he_core : e ∈ (rootedLocationCore (P₁ i).G (ℒ i)).edgeSet
          · have hnot_new_i : ¬ ∃ A ∈ ℒ i, newEdge i A = e := by
              rintro ⟨A, hA, rfl⟩
              exact (hQ_heart i).newEdge_notMem_core hA he_core
            have hφ_le := hexp.φ_le e he
            change DisjointUnionLE
              (if h : ∃ A ∈ ℒ i, newEdge i A = e then _ else Sum.inl ((P₁ i).φ e))
              (if h : ∃ A ∈ ℒ j, newEdge j A = ηe e then _ else Sum.inl ((P₁ j).φ (ηe e))) at hφ_le
            rw [dite_eq_right hnot_new_i] at hφ_le
            by_cases hnew_j : ∃ A ∈ ℒ j, newEdge j A = ηe e
            · rw [dite_eq_left hnew_j] at hφ_le
              nomatch hφ_le
            · rw [dite_eq_right hnew_j] at hφ_le
              have hηe_edge : ηe e ∈ (Q j).G.edgeSet := hexp.edge_mem e he
              rw [(hQ_heart j).edgeSet_eq] at hηe_edge
              have hηe_core : ηe e ∈ (rootedLocationCore (P₁ j).G (ℒ j)).edgeSet := by
                rcases hηe_edge with hc | ⟨A', hA', hEq⟩
                · exact hc
                · exact (hnew_j ⟨A', hA', hEq⟩).elim
              rw [(hQ_heart i).φ_core he_core, (hQ_heart j).φ_core hηe_core]
              cases hφ_le with
              | inl hle_φ => exact WithBot.coe_le_coe.2 hle_φ
          · change (if e ∈ (rootedLocationCore (P₁ i).G (ℒ i)).edgeSet then _ else ⊥) ≤ _
            rw [ite_eq_right he_core]
            exact bot_le }
  have hpre : ∀ ⦃e : β⦄ ⦃A₂ : RootedHypergraph α β⦄,
      e ∈ (Q i).G.edgeSet → A₂ ∈ ℒ j → ηe e = newEdge j A₂ → ∃ A₁ ∈ ℒ i, e = newEdge i A₁ := by
    intro e A₂ he hA₂ hηe_eq
    have hφ_le := hexp.φ_le e he
    have hex_j : ∃ A ∈ ℒ j, newEdge j A = ηe e := ⟨A₂, hA₂, hηe_eq.symm⟩
    change DisjointUnionLE
      (if h : ∃ A ∈ ℒ i, newEdge i A = e then _ else Sum.inl ((P₁ i).φ e))
      (if h : ∃ A ∈ ℒ j, newEdge j A = ηe e then _ else Sum.inl ((P₁ j).φ (ηe e))) at hφ_le
    rw [dite_eq_left hex_j] at hφ_le
    by_cases hex_i : ∃ A ∈ ℒ i, newEdge i A = e
    · obtain ⟨A₁, hA₁, hEq₁⟩ := hex_i
      exact ⟨A₁, hA₁, hEq₁.symm⟩
    · rw [dite_eq_right hex_i] at hφ_le
      nomatch hφ_le
  have hsim : ∀ ⦃A₁ : RootedHypergraph α β⦄, A₁ ∈ ℒ i →
      ∃ A₂ ∈ ℒ j, ηe (newEdge i A₁) = newEdge j A₂ ∧
        GM04.Simulated ((toPartialPatchwork (P₁ i)).restrict A₁)
          ((toPartialPatchwork (P₁ j)).restrict A₂) := by
    intro A₁ hA₁
    have he₁ : newEdge i A₁ ∈ (Q i).G.edgeSet := by
      rw [(hQ_heart i).edgeSet_eq]
      exact Or.inr ⟨A₁, hA₁, rfl⟩
    have hex_i : ∃ A ∈ ℒ i, newEdge i A = newEdge i A₁ := ⟨A₁, hA₁, rfl⟩
    have hchoose_i : hex_i.choose = A₁ :=
      (hQ_heart i).injOn_newEdge hex_i.choose_spec.1 hA₁ hex_i.choose_spec.2
    have hφ_le := hexp.φ_le (newEdge i A₁) he₁
    change DisjointUnionLE
      (if h : ∃ A ∈ ℒ i, newEdge i A = newEdge i A₁ then _ else _)
      (if h : ∃ A ∈ ℒ j, newEdge j A = ηe (newEdge i A₁) then _ else _) at hφ_le
    rw [dite_eq_left hex_i] at hφ_le
    by_cases hex_j : ∃ A ∈ ℒ j, newEdge j A = ηe (newEdge i A₁)
    · rw [dite_eq_left hex_j] at hφ_le
      let A₂ := hex_j.choose
      have hA₂ : A₂ ∈ ℒ j := hex_j.choose_spec.1
      have hEq₂ : newEdge j A₂ = ηe (newEdge i A₁) := hex_j.choose_spec.2
      cases hφ_le with
      | inr hsim_sub =>
        change GM04.Simulated ((P₁ i).restrict hex_i.choose) ((P₁ j).restrict A₂) at hsim_sub
        rw [hchoose_i] at hsim_sub
        refine ⟨A₂, hA₂, hEq₂.symm, ?_⟩
        exact simulated_toPartialPatchwork_iff.2 hsim_sub
    · rw [dite_eq_right hex_j] at hφ_le
      nomatch hφ_le
  have hsim_part := theorem_5_7_proof (hQ_heart i) (hQ_heart j) hη_Q hpre hsim
  exact simulated_toPartialPatchwork_iff.1 hsim_part

/-! ## Theorem (6.4): Lifting rotund tree-decompositions to rooted decompositions -/

/-- Restricting a robust patchwork `P` to `G' ≤ P.G` yields a robust patchwork `P | G'`. -/
theorem isRobust_restrict {P : GM04.Patchwork Ω α β} (hrob : P.IsRobust)
    {G' : RootedHypergraph α β} (hle : G'.toHypergraph ≤ P.G.toHypergraph) :
    (P.restrict G').IsRobust := by
  intro e he
  rw [P.restrict_Δ hle he]
  exact hrob e (hle.edgeSet_subset he)

private theorem routes_between_root_sets
    {P : GM04.Patchwork Ω α β} {G G₁ G₂ : RootedHypergraph α β}
    (hsep : G.IsSeparation G₁ G₂)
    (hno_sep : ¬ ∃ H₁ H₂ : RootedHypergraph α β, G.IsSeparation H₁ H₂ ∧
      G₁.toHypergraph ≤ H₁.toHypergraph ∧
      separationOrder H₁.toHypergraph H₂.toHypergraph < G.roots.length) :
    GM04.Theorem61Cond1 (P.restrict G₂) G₁.rootSet G₂.rootSet G.roots.length := by
  classical
  let k := G.roots.length
  let X₁ := G₁.rootSet
  let X₂ := G₂.rootSet
  have hle₁ := hsep.isSeparation.left_le
  have hle₂ := hsep.isSeparation.right_le
  have hX₁_eq : X₁ = (G₁.toHypergraph ∩ G₂.toHypergraph).vertexSet := hsep.rootSet_left
  have hX₂_roots := hsep.roots_right
  intro J₁ J₂ hsepJ hX₁J₁ hX₂J₂
  by_contra! hlt
  let K₁_H := G₁.toHypergraph ∪ J₁
  let K₂_H := J₂
  have hK₁_le : K₁_H ≤ G.toHypergraph :=
    union_le hle₁ (hsepJ.left_le.trans hle₂)
  have hK₂_le : K₂_H ≤ G.toHypergraph := hsepJ.right_le.trans hle₂
  have hK_union : K₁_H ∪ K₂_H = G.toHypergraph := by
    have hsepJ_union : J₁ ∪ J₂ = G₂.toHypergraph := hsepJ.union_eq
    rw [GM10.union_assoc, hsepJ_union, hsep.isSeparation.union_eq]
  have hK_edge : (K₁_H ∩ K₂_H).edgeSet = ∅ := by
    ext e
    simp only [K₁_H, K₂_H, inter_edgeSet, union_edgeSet, Set.mem_inter_iff,
      Set.mem_union, Set.mem_empty_iff_false, iff_false, not_and]
    rintro (he₁ | heJ₁) heJ₂
    · have heG₂ : e ∈ G₂.edgeSet := hsepJ.right_le.edgeSet_subset heJ₂
      have he_inter : e ∈ (G₁.toHypergraph ∩ G₂.toHypergraph).edgeSet := ⟨he₁, heG₂⟩
      rw [hsep.isSeparation.edgeSet_inter_eq] at he_inter
      exact he_inter
    · have he_inter : e ∈ (J₁ ∩ J₂).edgeSet := ⟨heJ₁, heJ₂⟩
      rw [hsepJ.edgeSet_inter_eq] at he_inter
      exact he_inter
  have hK_inter_V : (K₁_H ∩ K₂_H).vertexSet = (J₁ ∩ J₂).vertexSet := by
    ext v
    simp only [K₁_H, K₂_H, inter_vertexSet, union_vertexSet, Set.mem_inter_iff,
      Set.mem_union]
    constructor
    · rintro ⟨hv₁ | hvJ₁, hvJ₂⟩
      · have hvG₂ : v ∈ G₂.vertexSet := hsepJ.right_le.vertexSet_subset hvJ₂
        have hvX₁ : v ∈ X₁ := hX₁_eq.symm ▸ ⟨hv₁, hvG₂⟩
        exact ⟨hX₁J₁ hvX₁, hvJ₂⟩
      · exact ⟨hvJ₁, hvJ₂⟩
    · exact fun ⟨hvJ₁, hvJ₂⟩ ↦ ⟨Or.inr hvJ₁, hvJ₂⟩
  let r₁ := (K₁_H.vertexSet_finite.subset Set.inter_subset_left :
    (K₁_H ∩ K₂_H).vertexSet.Finite).toFinset.toList
  let H₁ : RootedHypergraph α β :=
    { toHypergraph := K₁_H
      roots := r₁
      roots_nodup := Finset.nodup_toList _
      roots_subset := fun v hv ↦ by
        rw [Finset.mem_toList, Set.Finite.mem_toFinset] at hv
        exact hv.1 }
  let H₂ : RootedHypergraph α β :=
    { toHypergraph := K₂_H
      roots := G.roots
      roots_nodup := G.roots_nodup
      roots_subset := fun v hv ↦ hX₂J₂ (show v ∈ G₂.roots from hX₂_roots.symm ▸ hv) }
  have hsepH : G.IsSeparation H₁ H₂ :=
    { isSeparation := ⟨hK₁_le, hK₂_le, hK_union, hK_edge⟩
      roots_right := rfl
      rootSet_left := by
        ext v
        simp only [H₁, r₁, RootedHypergraph.rootSet, Set.mem_ofPred_eq, Finset.mem_toList,
          Set.Finite.mem_toFinset]
        rfl }
  have hordH : separationOrder H₁.toHypergraph H₂.toHypergraph < k := by
    change (K₁_H ∩ K₂_H).vertexSet.ncard < k
    rw [hK_inter_V]
    exact hlt
  exact hno_sep ⟨H₁, H₂, hsepH, le_union_left hle₁ (hsepJ.left_le.trans hle₂), hordH⟩

private theorem match_components_to_roots
    {G G₂ : RootedHypergraph α β} (hX₂_roots : G₂.roots = G.roots)
    {D : Fin G.roots.length → (⊤ : SimpleGraph α).Subgraph}
    (hX₂ : ∀ i, ((D i).verts ∩ G₂.rootSet).Nonempty)
    (hD_disj : ∀ {i j}, i ≠ j → Disjoint (D i).verts (D j).verts) :
    ∃ τ : Fin G.roots.length ≃ Fin G.roots.length,
      ∀ j : Fin G.roots.length, G.roots[j.1] ∈ (D (τ j)).verts := by
  let k := G.roots.length
  let X₂ := G₂.rootSet
  -- Each component `D i` contains a vertex of `X₂ = {v | v ∈ G.roots}`; since `G.roots` is nodup of
  -- length `k`, every `G.roots[j]` belongs to a unique `D i`.
  have hX₂_eq : X₂ = G.rootSet := by
    change {v | v ∈ G₂.roots} = {v | v ∈ G.roots}
    rw [hX₂_roots]
  choose x₂ hx₂_D hx₂_X₂ using fun i : Fin k ↦ hX₂ i
  have hx₂_mem_roots : ∀ i : Fin k, ∃ j : Fin k, G.roots[j.1] = x₂ i := by
    intro i
    have hmem : x₂ i ∈ G.roots := by
      change x₂ i ∈ G.rootSet
      rw [← hX₂_eq]
      exact hx₂_X₂ i
    obtain ⟨j, hj, hEq⟩ := List.getElem_of_mem hmem
    exact ⟨⟨j, hj⟩, hEq⟩
  choose idx hidx using hx₂_mem_roots
  have hidx_inj : Function.Injective idx := by
    intro i₁ i₂ hEq
    by_contra hne
    have hval : x₂ i₁ = x₂ i₂ := by
      rw [← hidx i₁, ← hidx i₂, hEq]
    exact Set.disjoint_left.1 (hD_disj hne) (hx₂_D i₁) (hval ▸ hx₂_D i₂)
  let σ : Fin k ≃ Fin k :=
    Equiv.ofBijective idx ((Fintype.bijective_iff_injective_and_card idx).2 ⟨hidx_inj, rfl⟩)
  refine ⟨σ.symm, fun j ↦ ?_⟩
  have hj_eq : idx (σ.symm j) = j := σ.apply_symm_apply j
  have h1 := hidx (σ.symm j)
  rw [hj_eq] at h1
  rw [h1]
  exact hx₂_D (σ.symm j)

private theorem isRealization_join_separation
    {P : GM04.Patchwork Ω α β} {G G₁ G₂ H_root : RootedHypergraph α β}
    {H_sub : (⊤ : SimpleGraph α).Subgraph}
    (hG : G.toHypergraph ≤ P.G.toHypergraph) (hsep : G.IsSeparation G₁ G₂)
    (hroot : H_root.toHypergraph = G₁.toHypergraph)
    (hH_sub : (P.restrict G₂).IsRealization H_sub) :
    ((P.restrict G).deleteEdges (id '' H_root.edgeSet)).IsRealization
      (GM04.emptySubgraph G₁.vertexSet ⊔ H_sub) := by
  have hle₂ := hsep.isSeparation.right_le
  obtain ⟨δ₂, hδ₂, hH_sub_eq⟩ := hH_sub
  have hroot_edges : H_root.edgeSet = G₁.edgeSet := congrArg Hypergraph.edgeSet hroot
  have hdiff_eq : G.edgeSet \ (id '' H_root.edgeSet) = G₂.edgeSet := by
    rw [Set.image_id, hroot_edges]
    ext e
    simp only [Set.mem_sdiff]
    constructor
    · rintro ⟨heG, he₁⟩
      rw [← hsep.isSeparation.union_eq, union_edgeSet] at heG
      rcases heG with h | h
      · exact (he₁ h).elim
      · exact h
    · intro he₂
      refine ⟨hle₂.edgeSet_subset he₂, fun he₁ ↦ ?_⟩
      have he_inter : e ∈ (G₁.toHypergraph ∩ G₂.toHypergraph).edgeSet := ⟨he₁, he₂⟩
      rw [hsep.isSeparation.edgeSet_inter_eq] at he_inter
      exact he_inter
  refine ⟨δ₂, fun e he ↦ ?_, ?_⟩
  · have he₂ : e ∈ G₂.edgeSet := hdiff_eq ▸ he
    have h := hδ₂ e he₂
    change δ₂ e ∈ (P.restrict G₂).Δ e at h
    rw [P.restrict_Δ (hle₂.trans hG) he₂] at h
    change δ₂ e ∈ (P.restrict G).Δ e
    rw [P.restrict_Δ hG (hle₂.edgeSet_subset he₂)]
    exact h
  · change GM04.emptySubgraph G₁.vertexSet ⊔ H_sub =
      GM04.emptySubgraph G.vertexSet ⊔ ⨆ e ∈ G.edgeSet \ (id '' H_root.edgeSet), δ₂ e
    rw [hH_sub_eq, hdiff_eq]
    change GM04.emptySubgraph G₁.vertexSet ⊔
        (GM04.emptySubgraph G₂.vertexSet ⊔ ⨆ e ∈ G₂.edgeSet, δ₂ e) = _
    have hempty_sup : GM04.emptySubgraph G₁.vertexSet ⊔ GM04.emptySubgraph G₂.vertexSet =
        GM04.emptySubgraph G.vertexSet := by
      ext u v
      · change u ∈ G₁.vertexSet ∪ G₂.vertexSet ↔ u ∈ G.vertexSet
        rw [GM04.isSeparation_vertexSet_union hsep.isSeparation]
      · simp [Subgraph.sup_adj]
    rw [← sup_assoc, hempty_sup]

/-- Verification of Graph Minors IV, Axiom 3 (`GM04.Axiom3`) for subhypergraphs of a robust
patchwork `P` (Graph Minors IV, Section 9, pages 251–252). -/
theorem axiom3_of_isRobust
     [Preorder Ω]
    {P : GM04.Patchwork Ω α β} (hrob : P.IsRobust) :
    GM04.Axiom3 {H : RootedHypergraph α β | H.toHypergraph ≤ P.G.toHypergraph}
      (fun H₁ H₂ ↦ GM04.Simulated (P.restrict H₁) (P.restrict H₂)) := by
  classical
  intro G hG G₁ G₂ hsep hord hno_sep
  let k := G.roots.length
  let X₁ := G₁.rootSet
  let X₂ := G₂.rootSet
  have hle₁ : G₁.toHypergraph ≤ G.toHypergraph := hsep.isSeparation.left_le
  have hle₂ : G₂.toHypergraph ≤ G.toHypergraph := hsep.isSeparation.right_le
  have hX₁_eq : X₁ = (G₁.toHypergraph ∩ G₂.toHypergraph).vertexSet := hsep.rootSet_left
  have hX₂_roots : G₂.roots = G.roots := hsep.roots_right
  have hX₁_sub : X₁ ⊆ G₂.vertexSet := by
    rw [hX₁_eq]; exact Set.inter_subset_right
  have hX₂_sub : X₂ ⊆ G₂.vertexSet := G₂.roots_subset
  have hX₁_card : X₁.ncard = k := by
    rw [hX₁_eq]; exact hord
  have hrob₂ : (P.restrict G₂).IsRobust := isRobust_restrict hrob (hle₂.trans hG)
  have hcond1 : GM04.Theorem61Cond1 (P.restrict G₂) X₁ X₂ k :=
    routes_between_root_sets hsep hno_sep
  -- Apply GM04 (6.1) to obtain a realization `H_sub` of `P | G₂` with `k` components joining `X₁`
  -- and `X₂`.
  have hcond2 : GM04.Theorem61Cond2 (P.restrict G₂) X₁ X₂ k :=
    ((GM04.theorem_6_1_proof menger hrob₂ hX₁_sub hX₂_sub k).1).1 hcond1
  obtain ⟨H_sub, D, hH_sub, hD_inj, hD⟩ := hcond2
  have hD_disj : ∀ {i j : Fin k}, i ≠ j → Disjoint (D i).verts (D j).verts := by
    intro i j hij
    exact (hD i).1.disjoint_verts_of_ne (hD j).1 (fun hEq ↦ hij (hD_inj hEq))
  obtain ⟨τ, hD'_root⟩ := match_components_to_roots (D := D) hX₂_roots
    (fun i ↦ (hD i).2.2) hD_disj
  let D' : Fin k → (⊤ : SimpleGraph α).Subgraph := fun j ↦ D (τ j)
  have hD'_comp (j : Fin k) : GM04.IsComponent H_sub (D' j) := (hD (τ j)).1
  have hD'_disj : ∀ {j₁ j₂ : Fin k}, j₁ ≠ j₂ → Disjoint (D' j₁).verts (D' j₂).verts :=
    fun hij ↦ hD_disj (τ.injective.ne hij)
  -- Choose `v_j ∈ (D' j).verts ∩ X₁` for each `j : Fin k`.
  choose v₁ hv₁_D' hv₁_X₁ using fun j : Fin k ↦ (hD (τ j)).2.1
  have hv₁_inj : Function.Injective v₁ := by
    intro j₁ j₂ hEq
    by_contra hne
    exact Set.disjoint_left.1 (hD'_disj hne) (hv₁_D' j₁) (hEq ▸ hv₁_D' j₂)
  let π₁ : List α := List.ofFn v₁
  have hπ₁_len : π₁.length = k := List.length_ofFn
  have hπ₁_nodup : π₁.Nodup := List.nodup_ofFn.2 hv₁_inj
  have hπ₁_sub : {v | v ∈ π₁} ⊆ X₁ := by
    intro v hv
    change v ∈ List.ofFn v₁ at hv
    rw [List.mem_ofFn] at hv
    obtain ⟨j, rfl⟩ := hv
    exact hv₁_X₁ j
  have hπ₁_set : {v | v ∈ π₁} = X₁ := by
    refine Set.eq_of_subset_of_ncard_le hπ₁_sub ?_ G₁.rootSet_finite
    have hcard_range : (Set.range v₁).ncard = k := by
      rw [Set.ncard_range_of_injective hv₁_inj, Nat.card_fin]
    have hset_eq : {v | v ∈ π₁} = Set.range v₁ := by
      ext v; simp [π₁, List.mem_ofFn]
    rw [hset_eq, hcard_range, hX₁_card]
  let H_root : RootedHypergraph α β :=
    { toHypergraph := G₁.toHypergraph
      roots := π₁
      roots_nodup := hπ₁_nodup
      roots_subset := fun v hv ↦ by
        have hvX₁ : v ∈ X₁ := hπ₁_set ▸ (show v ∈ {x | x ∈ π₁} from hv)
        exact G₁.roots_subset v hvX₁ }
  refine ⟨H_root, rfl, hπ₁_set, ?_⟩
  -- Define the expansion `(ηv, id)` of `P | H_root` in `P | G` as in GM IV Section 9 (page 252).
  let ηv : α → Set α := fun v ↦
    if h : ∃ j : Fin k, v₁ j = v then (D' h.choose).verts else {v}
  have hηv_of_v₁ : ∀ j : Fin k, ηv (v₁ j) = (D' j).verts := by
    intro j
    have hex : ∃ j' : Fin k, v₁ j' = v₁ j := ⟨j, rfl⟩
    have hchoose : hex.choose = j := hv₁_inj hex.choose_spec
    simp only [ηv, dite_eq_left hex, hchoose]
  have hv_mem_ηv : ∀ v ∈ G₁.vertexSet, v ∈ ηv v := by
    intro v hv
    by_cases hex : ∃ j : Fin k, v₁ j = v
    · obtain ⟨j, rfl⟩ := hex
      rw [hηv_of_v₁ j]
      exact hv₁_D' j
    · simp only [ηv, dite_eq_right hex, Set.mem_singleton_iff]
  have hH_sub_verts : H_sub.verts = G₂.vertexSet := hH_sub.verts_eq
  have hD'_sub_G₂ : ∀ j : Fin k, (D' j).verts ⊆ G₂.vertexSet := by
    intro j
    rw [← hH_sub_verts]
    exact (hD'_comp j).le.1
  -- Every component `D' j` meets `G₁.vertexSet` only at `{v₁ j}`!
  -- Because `X₁ = G₁.vertexSet ∩ G₂.vertexSet = Set.range v₁`, and `v₁` is injective with `v₁ j' ∈
  -- D' j'`.
  have hD'_inter_G₁ : ∀ (j : Fin k) {x : α}, x ∈ (D' j).verts → x ∈ G₁.vertexSet → x = v₁ j := by
    intro j x hxD hxG₁
    have hxG₂ : x ∈ G₂.vertexSet := hD'_sub_G₂ j hxD
    have hxX₁ : x ∈ X₁ := hX₁_eq.symm ▸ ⟨hxG₁, hxG₂⟩
    rw [← hπ₁_set] at hxX₁
    change x ∈ List.ofFn v₁ at hxX₁
    rw [List.mem_ofFn] at hxX₁
    obtain ⟨j', rfl⟩ := hxX₁
    by_cases hjj' : j' = j
    · subst hjj'; rfl
    · exact (Set.disjoint_left.1 (hD'_disj hjj') (hv₁_D' j') hxD).elim
  have hle_H_root : H_root.toHypergraph ≤ P.G.toHypergraph := hle₁.trans hG
  have hexp : GM04.IsExpansion (P.restrict H_root) (P.restrict G) ηv id :=
    { vertex_nonempty := fun v hv ↦ ⟨v, hv_mem_ηv v hv⟩
      vertex_subset := fun v hv x hx ↦ by
        by_cases hex : ∃ j : Fin k, v₁ j = v
        · obtain ⟨j, rfl⟩ := hex
          rw [hηv_of_v₁ j] at hx
          exact hle₂.vertexSet_subset (hD'_sub_G₂ j hx)
        · simp only [ηv, dite_eq_right hex, Set.mem_singleton_iff] at hx
          subst hx
          exact hle₁.vertexSet_subset hv
      edge_mem := fun e he ↦ hle₁.edgeSet_subset he
      vertex_disjoint := fun u₁ hu₁ u₂ hu₂ hne ↦ by
        rw [Set.disjoint_left]
        intro x hx₁ hx₂
        by_cases hex₁ : ∃ j : Fin k, v₁ j = u₁ <;> by_cases hex₂ : ∃ j : Fin k, v₁ j = u₂
        · obtain ⟨j₁, rfl⟩ := hex₁
          obtain ⟨j₂, rfl⟩ := hex₂
          rw [hηv_of_v₁ j₁] at hx₁
          rw [hηv_of_v₁ j₂] at hx₂
          have hj_ne : j₁ ≠ j₂ := fun hEq ↦ hne (congrArg v₁ hEq)
          exact Set.disjoint_left.1 (hD'_disj hj_ne) hx₁ hx₂
        · obtain ⟨j₁, rfl⟩ := hex₁
          rw [hηv_of_v₁ j₁] at hx₁
          simp only [ηv, dite_eq_right hex₂, Set.mem_singleton_iff] at hx₂
          subst hx₂
          exact hne (hD'_inter_G₁ j₁ hx₁ hu₂).symm
        · obtain ⟨j₂, rfl⟩ := hex₂
          rw [hηv_of_v₁ j₂] at hx₂
          simp only [ηv, dite_eq_right hex₁, Set.mem_singleton_iff] at hx₁
          subst hx₁
          exact hne (hD'_inter_G₁ j₂ hx₂ hu₁)
        · simp only [ηv, dite_eq_right hex₁, dite_eq_right hex₂, Set.mem_singleton_iff] at hx₁ hx₂
          exact hne (hx₁.symm.trans hx₂)
      edge_injOn := fun _ _ _ _ h ↦ h
      mem_dom_iff := fun e he ↦ by
        rw [P.restrict_dom hle_H_root, P.restrict_dom hG]
        exact ⟨fun ⟨hd, _⟩ ↦ ⟨hd, hle₁.edgeSet_subset he⟩, fun ⟨hd, _⟩ ↦ ⟨hd, he⟩⟩
      ends_nonempty := fun e he _ v hinc ↦ by
        have hv : v ∈ G₁.vertexSet := G₁.vertex_mem_of_inc hinc
        refine ⟨v, hv_mem_ηv v hv, ?_⟩
        exact inc_of_le hle₁ hinc
      μ_length := fun _ _ ↦ rfl
      μ_mem := fun e he i hi _ ↦ by
        rw [P.restrict_dom hle_H_root] at he
        change i < (P.μ e).length at hi
        have he₁ : e ∈ G₁.edgeSet := he.2
        have hv_inc : G₁.Inc e (P.μ e)[i] := by
          change (P.μ e)[i] ∈ G₁.ends e
          rw [← (hle₁.trans hG).ends_eq e he₁, ← P.μ_set e he.1]
          exact List.getElem_mem hi
        exact hv_mem_ηv (P.μ e)[i] (G₁.vertex_mem_of_inc hv_inc)
      roots_length := hπ₁_len
      roots_mem := fun i hi hi' ↦ by
        let j : Fin k := ⟨i, hi'⟩
        change i < (List.ofFn v₁).length at hi
        change G.roots[i] ∈ ηv (List.ofFn v₁)[i]
        rw [List.getElem_ofFn, hηv_of_v₁ j]
        exact hD'_root j
      maps_Δ := fun e he δ hδ ↦ by
        rw [P.restrict_dom hle_H_root] at he
        change δ ∈ (P.restrict H_root).Δ e at hδ
        rw [P.restrict_Δ hle_H_root he.2] at hδ
        change GM04.marchMapSubgraph (P.μ e) (P.μ e) δ ∈ (P.restrict G).Δ e
        rw [P.restrict_Δ hG (hle₁.edgeSet_subset he.2)]
        have hverts : δ.verts ⊆ {x | x ∈ P.μ e} := by
          rw [((P.Δ e).verts_eq δ hδ).trans (P.Δ_verts e ((hle₁.trans hG).edgeSet_subset he.2)),
            P.μ_set e he.1]
        rwa [GM04.marchMapSubgraph_id hverts]
      φ_le := fun _ _ ↦ le_rfl }
  -- Construct the realizing subgraph `H_real = emptySubgraph G₁.vertexSet ⊔ H_sub`.
  let H_real := GM04.emptySubgraph G₁.vertexSet ⊔ H_sub
  refine ⟨ηv, id, hexp, H_real, ?_, ?_⟩
  · exact isRealization_join_separation hG hsep rfl hH_sub
  · intro v hv
    have hH_real_verts : H_real.verts = G.vertexSet := by
      change G₁.vertexSet ∪ H_sub.verts = G.vertexSet
      rw [hH_sub_verts, GM04.isSeparation_vertexSet_union hsep.isSeparation]
    have hsub_verts : ηv v ⊆ H_real.verts := by
      rw [hH_real_verts]
      exact hexp.vertex_subset v hv
    rw [GM04.exists_isComponent_verts_eq_iff (hexp.vertex_nonempty v hv) hsub_verts]
    by_cases hex : ∃ j : Fin k, v₁ j = v
    · obtain ⟨j, rfl⟩ := hex
      rw [hηv_of_v₁ j]
      have hD'_sub_H : (D' j).verts ⊆ H_sub.verts := (hD'_comp j).le.1
      obtain ⟨hclosed, hconn⟩ :=
        (GM04.exists_isComponent_verts_eq_iff (hD'_comp j).verts_nonempty hD'_sub_H).1
          ⟨D' j, hD'_comp j, rfl⟩
      refine ⟨fun a ha b hab ↦ ?_, fun a ha b hb ↦ (hconn a ha b hb).mono le_sup_right⟩
      rcases Subgraph.sup_adj.1 hab with hab₁ | hab₂
      · exact False.elim hab₁
      · exact hclosed a ha b hab₂
    · have hηv_eq : ηv v = {v} := by simp only [ηv, dite_eq_right hex]
      rw [hηv_eq]
      have hv_not_G₂ : v ∉ G₂.vertexSet := by
        intro hv₂
        have hvX₁ : v ∈ X₁ := hX₁_eq.symm ▸ ⟨hv, hv₂⟩
        rw [← hπ₁_set] at hvX₁
        change v ∈ List.ofFn v₁ at hvX₁
        rw [List.mem_ofFn] at hvX₁
        exact hex hvX₁
      refine ⟨fun a ha b hab ↦ ?_, ?_⟩
      · rw [Set.mem_singleton_iff] at ha
        subst ha
        rcases Subgraph.sup_adj.1 hab with hab₁ | hab₂
        · exact False.elim hab₁
        · exact (hv_not_G₂ (hH_sub_verts ▸ H_sub.edge_vert hab₂)).elim
      · rintro a rfl b rfl
        exact GM04.sameComponent_iff.2 ⟨hH_real_verts.symm ▸ hle₁.vertexSet_subset hv,
          hH_real_verts.symm ▸ hle₁.vertexSet_subset hv, Reachable.refl _⟩

/-- In an arborescence `T` with `T.verts = Finset.univ`, removing an edge `e_f = s(f, T.parent f)`
(`f ∈ T.edges`) from `S = arborescenceUnderlying T` disconnects `S` into `T.subtreeAt f` (the
component of `f`) and `T.rootSide f` (the component of `T.parent f`). -/
theorem reachable_deleteEdges_arborescenceUnderlying_iff {ι : Type*} [Fintype ι]
    (T : GM04.RootedTree ι) (hT_verts : T.verts = Finset.univ) {f : ι} (hf : f ∈ T.edges) (t : ι) :
    ((arborescenceUnderlying T).deleteEdges {s(f, T.parent f)}).Reachable f t ↔
      t ∈ T.subtreeAt f := by
  classical
  let G' := (arborescenceUnderlying T).deleteEdges {s(f, T.parent f)}
  have hf_ne_root : f ≠ T.root := T.ne_root_of_mem_edges hf
  have hadj_sub : ∀ {u v : ι}, G'.Adj u v → (u ∈ T.subtreeAt f ↔ v ∈ T.subtreeAt f) := by
    intro u v hadj_G'
    rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff] at hadj_G'
    rcases hadj_G' with ⟨hadj, hne_e⟩
    rw [T.mem_subtreeAt, T.mem_subtreeAt]
    rcases hadj with ⟨hu, rfl⟩ | ⟨hv, rfl⟩
    · refine ⟨fun ⟨_, n, hn⟩ ↦ ?_, fun ⟨_, n, hn⟩ ↦ ⟨hT_verts ▸ Finset.mem_univ u, n + 1, ?_⟩⟩
      · rcases n with _ | n
        · exfalso
          subst hn
          exact hne_e rfl
        · rw [Function.iterate_succ_apply] at hn
          exact ⟨hT_verts ▸ Finset.mem_univ _, n, hn⟩
      · rw [Function.iterate_succ_apply, hn]
    · refine ⟨fun ⟨_, n, hn⟩ ↦ ⟨hT_verts ▸ Finset.mem_univ v, n + 1, ?_⟩, fun ⟨_, n, hn⟩ ↦ ?_⟩
      · rw [Function.iterate_succ_apply, hn]
      · rcases n with _ | n
        · exfalso
          subst hn
          exact hne_e Sym2.eq_swap
        · rw [Function.iterate_succ_apply] at hn
          exact ⟨hT_verts ▸ Finset.mem_univ _, n, hn⟩
  constructor
  · rintro ⟨w⟩
    suffices ∀ {a b : ι} (w : G'.Walk a b), a ∈ T.subtreeAt f → b ∈ T.subtreeAt f from
      this w (T.self_mem_subtreeAt (hT_verts ▸ Finset.mem_univ f))
    intro a b w ha
    induction w with
    | nil => exact ha
    | @cons u v z hadj _ ih => exact ih ((hadj_sub hadj).1 ha)
  · intro ht
    rw [T.mem_subtreeAt] at ht
    obtain ⟨_, n, hn⟩ := ht
    suffices ∀ (k : ℕ) (x : ι), T.parent^[k] x = f → G'.Reachable f x from this n t hn
    intro k
    induction k with
    | zero =>
      intro x hx
      rw [Function.iterate_zero_apply] at hx
      exact hx ▸ Reachable.refl x
    | succ k ih =>
      intro x hx
      rw [Function.iterate_succ_apply] at hx
      have hreach_par := ih (T.parent x) hx
      have hx_ne_root : x ≠ T.root := by
        intro hxr
        rw [hxr, T.parent_root, T.iterate_parent_root k] at hx
        exact hf_ne_root hx.symm
      have hx_edges : x ∈ T.edges :=
        T.mem_edges_iff.2 ⟨hT_verts ▸ Finset.mem_univ x, hx_ne_root⟩
      have hx_ne_f : x ≠ f := by
        intro hxf
        rw [hxf] at hx
        have h1 : T.parent^[k + 1] f = f := by rw [Function.iterate_succ_apply, hx]
        exact Thomas.not_iterate_succ_eq_self T (hT_verts ▸ Finset.mem_univ f) hf_ne_root k h1
      have hadj : G'.Adj x (T.parent x) := by
        rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
        refine ⟨Or.inl ⟨hx_edges, rfl⟩, ?_⟩
        rintro (⟨hEq₁, _⟩ | ⟨hEq₁, hEq₂⟩)
        · exact hx_ne_f hEq₁
        · exact T.not_reaches_parent hf ⟨hT_verts ▸ Finset.mem_univ _, 1,
            by rw [Function.iterate_one, ← hEq₁, hEq₂]⟩
      exact hreach_par.trans (Adj.reachable hadj.symm)

theorem reachable_parent_deleteEdges_arborescenceUnderlying_iff {ι : Type*} [Fintype ι]
    (T : GM04.RootedTree ι) (hT_verts : T.verts = Finset.univ) {f : ι} (hf : f ∈ T.edges) (t : ι) :
    ((arborescenceUnderlying T).deleteEdges {s(f, T.parent f)}).Reachable (T.parent f) t ↔
      t ∈ T.rootSide f := by
  classical
  let G' := (arborescenceUnderlying T).deleteEdges {s(f, T.parent f)}
  have hf_ne_root : f ≠ T.root := T.ne_root_of_mem_edges hf
  have hpar_not_sub : T.parent f ∉ T.subtreeAt f := by
    rw [T.mem_subtreeAt]
    exact T.not_reaches_parent hf
  have hreach_root : ∀ x : ι, x ∉ T.subtreeAt f → G'.Reachable T.root x := by
    intro x hx_not
    obtain ⟨n, hn⟩ := T.exists_iterate_eq_root x (hT_verts ▸ Finset.mem_univ x)
    induction n generalizing x with
    | zero =>
      change x = T.root at hn
      subst hn
      exact Reachable.refl T.root
    | succ n ih =>
      by_cases hx_root : x = T.root
      · subst hx_root; exact Reachable.refl T.root
      · rw [Function.iterate_succ_apply] at hn
        have hx_edges : x ∈ T.edges :=
          T.mem_edges_iff.2 ⟨hT_verts ▸ Finset.mem_univ x, hx_root⟩
        have hx_ne_f : x ≠ f := by
          rintro rfl
          exact hx_not (T.self_mem_subtreeAt (hT_verts ▸ Finset.mem_univ x))
        have hpar_not : T.parent x ∉ T.subtreeAt f := by
          rw [T.mem_subtreeAt]
          rintro ⟨_, k, hk⟩
          apply hx_not
          rw [T.mem_subtreeAt]
          exact ⟨hT_verts ▸ Finset.mem_univ x, k + 1,
            by rw [Function.iterate_succ_apply, hk]⟩
        have hadj : G'.Adj x (T.parent x) := by
          rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
          refine ⟨Or.inl ⟨hx_edges, rfl⟩, ?_⟩
          rintro (⟨hEq₁, _⟩ | ⟨hEq₁, hEq₂⟩)
          · exact hx_ne_f hEq₁
          · subst hEq₁
            exact hx_not (T.mem_subtreeAt.2 ⟨hT_verts ▸ Finset.mem_univ _, 1,
              by rw [Function.iterate_one, hEq₂]⟩)
        exact (ih (T.parent x) hpar_not hn).trans (Adj.reachable hadj.symm)
  rw [T.mem_rootSide, ← T.mem_subtreeAt, hT_verts]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro hreach ht_sub
    have hrf : G'.Reachable f t :=
      (reachable_deleteEdges_arborescenceUnderlying_iff T hT_verts hf t).2 ht_sub
    have hf_par : G'.Reachable f (T.parent f) := hrf.trans hreach.symm
    exact hpar_not_sub
      ((reachable_deleteEdges_arborescenceUnderlying_iff T hT_verts hf (T.parent f)).1 hf_par)
  · intro ht_not
    exact (hreach_root (T.parent f) hpar_not_sub).symm.trans (hreach_root t ht_not)

private theorem rooted_decomposition_isRotund {ι : Type*} [Fintype ι]
    {G : RootedHypergraph α β} {S : SimpleGraph ι} {σ : ι → Hypergraph α β}
    {T : GM04.RootedTree ι} {σ_plus : ι → RootedHypergraph α β}
    (hT_verts : T.verts = Finset.univ) (hT_S : arborescenceUnderlying T = S)
    (hrot : IsRotund G.toHypergraph S σ)
    (htd_plus : GM04.IsTreeDecomposition G T σ_plus)
    (hsubtree_eq_side : ∀ {g : ι} (_ : g ∈ T.edges),
      (GM04.cross σ_plus (T.subtreeAt g) g).toHypergraph =
        GM10.treeDecompSide S σ s(g, T.parent g) g)
    (hrootSide_eq_side : ∀ {g : ι} (_ : g ∈ T.edges),
      (GM04.cross σ_plus (T.rootSide g) T.root).toHypergraph =
        GM10.treeDecompSide S σ s(g, T.parent g) (T.parent g))
    (hmakes_edge : ∀ {g : ι} (_ : g ∈ T.edges),
      GM10.MakesSeparation S σ s(g, T.parent g)
        (GM04.cross σ_plus (T.subtreeAt g) g).toHypergraph
        (GM04.cross σ_plus (T.rootSide g) T.root).toHypergraph) :
    GM04.IsRotund T σ_plus (T.edges : Set ι) := by
  classical
  have hcross_verts := htd_plus.cross_verts_eq
  intro f₁ hf₁ f₂ hf₂ hreach hord hmin ⟨H₁, H₂, hsepH, hle₁, hle₂, hord_lt⟩
  rw [hcross_verts] at hsepH
  let iso : Thomas.toSimpleGraph T ≃g S :=
    { toFun := fun u ↦ u.1
      invFun := fun x ↦ ⟨x, hT_verts ▸ Finset.mem_univ x⟩
      left_inv := fun _ ↦ Subtype.ext rfl
      right_inv := fun _ ↦ rfl
      map_rel_iff' := by
        intro u v
        rw [← hT_S]
        simp only [Thomas.toSimpleGraph, arborescenceUnderlying, Equiv.coe_fn_mk,
          T.mem_edges_iff, u.2, v.2, true_and] }
  let u₁ : T.verts := ⟨f₁, T.edges_subset_verts hf₁⟩
  let u₂ : T.verts := ⟨T.parent f₂, T.parent_mem f₂ (T.edges_subset_verts hf₂)⟩
  let p_T := Thomas.treePath (Thomas.toSimpleGraph_isTree T) u₁ u₂
  have hp_T_path : p_T.IsPath := Thomas.treePath_isPath (Thomas.toSimpleGraph_isTree T) u₁ u₂
  let p : S.Walk f₁ (T.parent f₂) := p_T.map iso.toHom
  have hp_path : p.IsPath := hp_T_path.map iso.injective
  -- Every vertex `w` on `p_T` satisfies `T.Reaches w.1 f₁` and `T.Reaches (T.parent f₂) w.1`.
  have hp_T_support : ∀ w : T.verts, w ∈ p_T.support ↔
      T.Reaches w.1 f₁ ∧ T.Reaches (T.parent f₂) w.1 := by
    intro w
    rw [← Thomas.onTreePath_iff_mem_treePath (Thomas.toSimpleGraph_isTree T),
      Thomas.onTreePath_toSimpleGraph_iff T u₁ u₂ w]
    constructor
    · intro hon
      have hf₂_par : T.Reaches (T.parent f₂) f₂ := ⟨T.edges_subset_verts hf₂, 1, rfl⟩
      have hpar_f₁ : T.Reaches (T.parent f₂) f₁ := T.reaches_trans hf₂_par hreach
      rcases hon.1 with hwf₁ | hwf₂
      · exact ⟨hwf₁, hon.2 (T.parent f₂) hpar_f₁ (T.reaches_refl u₂.2)⟩
      · have h_eq : w.1 = T.parent f₂ :=
          T.reaches_antisymm hwf₂ (hon.2 (T.parent f₂) hpar_f₁ (T.reaches_refl u₂.2))
        rw [h_eq]
        exact ⟨hpar_f₁, T.reaches_refl u₂.2⟩
    · rintro ⟨hwf₁, hpar_w⟩
      refine ⟨Or.inl hwf₁, fun x hx₁ hx₂ ↦ ?_⟩
      exact T.reaches_trans hx₂ hpar_w
  have hK_tree := Thomas.toSimpleGraph_isTree T
  have hf₁_in_p : s(f₁, T.parent f₁) ∈ p.edges := by
    let u₁_par : T.verts := ⟨T.parent f₁, T.parent_mem f₁ u₁.2⟩
    have hadj₁ : (Thomas.toSimpleGraph T).Adj u₁_par u₁ :=
      Or.inr ⟨T.ne_root_of_mem_edges hf₁, rfl⟩
    have hpar₁_mem : u₁_par ∈ p_T.support := by
      rw [hp_T_support]
      refine ⟨⟨u₁.2, 1, rfl⟩, ?_⟩
      obtain ⟨_, n, hn⟩ := hreach
      exact ⟨T.parent_mem f₁ u₁.2, n, by rw [← Function.iterate_succ_apply,
        Function.iterate_succ_apply', hn]⟩
    have hpar₁_on : Thomas.OnTreePath (Thomas.toSimpleGraph T) u₂ u₁ u₁_par :=
      Thomas.onTreePath_symm ((Thomas.onTreePath_iff_mem_treePath hK_tree).2 hpar₁_mem)
    have he_self : Thomas.OnTreePathEdge (Thomas.toSimpleGraph T) u₁_par u₁ u₁_par u₁ := by
      rw [Thomas.onTreePathEdge_iff_mem_treePath hK_tree]
      refine ⟨hadj₁, ?_⟩
      rw [← Thomas.eq_treePath hK_tree hadj₁.toWalk hadj₁.isPath_toWalk]
      simp
    have he_T : Thomas.OnTreePathEdge (Thomas.toSimpleGraph T) u₁ u₂ u₁ u₁_par :=
      Thomas.onTreePathEdge_swap
        (Thomas.onTreePathEdge_symm_endpoints
          (Thomas.onTreePathEdge_of_onTreePath_right hK_tree hpar₁_on he_self))
    have he_mem := ((Thomas.onTreePathEdge_iff_mem_treePath hK_tree).1 he_T).2
    rw [Walk.edges_map, List.mem_map]
    exact ⟨s(u₁, u₁_par), he_mem, rfl⟩
  have hf₂_in_p : s(f₂, T.parent f₂) ∈ p.edges := by
    let v₂ : T.verts := ⟨f₂, T.edges_subset_verts hf₂⟩
    have hadj₂ : (Thomas.toSimpleGraph T).Adj v₂ u₂ :=
      Or.inl ⟨T.ne_root_of_mem_edges hf₂, rfl⟩
    have hf₂_mem : v₂ ∈ p_T.support := by
      rw [hp_T_support]
      exact ⟨hreach, ⟨T.edges_subset_verts hf₂, 1, rfl⟩⟩
    have hf₂_on : Thomas.OnTreePath (Thomas.toSimpleGraph T) u₁ u₂ v₂ :=
      (Thomas.onTreePath_iff_mem_treePath hK_tree).2 hf₂_mem
    have he_self : Thomas.OnTreePathEdge (Thomas.toSimpleGraph T) v₂ u₂ v₂ u₂ := by
      rw [Thomas.onTreePathEdge_iff_mem_treePath hK_tree]
      refine ⟨hadj₂, ?_⟩
      rw [← Thomas.eq_treePath hK_tree hadj₂.toWalk hadj₂.isPath_toWalk]
      simp
    have he_T : Thomas.OnTreePathEdge (Thomas.toSimpleGraph T) u₁ u₂ v₂ u₂ :=
      Thomas.onTreePathEdge_of_onTreePath_right hK_tree hf₂_on he_self
    have he_mem := ((Thomas.onTreePathEdge_iff_mem_treePath hK_tree).1 he_T).2
    rw [Walk.edges_map, List.mem_map]
    exact ⟨s(v₂, u₂), he_mem, rfl⟩
  have hmakes₁_symm : GM10.MakesSeparation S σ s(f₁, T.parent f₁)
      (GM04.cross σ_plus (T.rootSide f₁) T.root).toHypergraph
      (GM04.cross σ_plus (T.subtreeAt f₁) f₁).toHypergraph := by
    have hadj₁ : S.Adj f₁ (T.parent f₁) := by
      rw [← hT_S]; exact Or.inl ⟨hf₁, rfl⟩
    exact ⟨T.parent f₁, f₁, hadj₁.symm, Sym2.eq_swap,
      by rw [Sym2.eq_swap]; exact hrootSide_eq_side hf₁,
      by rw [Sym2.eq_swap]; exact hsubtree_eq_side hf₁⟩
  have hmakes₂ : GM10.MakesSeparation S σ s(f₂, T.parent f₂)
      (GM04.cross σ_plus (T.subtreeAt f₂) f₂).toHypergraph
      (GM04.cross σ_plus (T.rootSide f₂) T.root).toHypergraph :=
    hmakes_edge hf₂
  have hsub₁₂ : (GM04.cross σ_plus (T.subtreeAt f₁) f₁).toHypergraph ≤
      (GM04.cross σ_plus (T.subtreeAt f₂) f₂).toHypergraph :=
    htd_plus.cross_le_cross (T.subtreeAt_mono hreach) (T.subtreeAt_subset_verts f₂)
      (T.self_mem_subtreeAt u₁.2) (T.self_mem_subtreeAt (T.edges_subset_verts hf₂))
  have hroot₂₁ : (GM04.cross σ_plus (T.rootSide f₂) T.root).toHypergraph ≤
      (GM04.cross σ_plus (T.rootSide f₁) T.root).toHypergraph := by
    have hsub_root : T.rootSide f₂ ⊆ T.rootSide f₁ := by
      intro x hx
      rw [T.mem_rootSide] at hx ⊢
      exact ⟨hx.1, fun h₁ ↦ hx.2 (T.reaches_trans hreach h₁)⟩
    exact htd_plus.cross_le_cross hsub_root (T.rootSide_subset_verts f₁)
      (T.root_mem_rootSide hf₂) (T.root_mem_rootSide hf₁)
  have hord₁₂ : separationOrder
      (GM04.cross σ_plus (T.rootSide f₁) T.root).toHypergraph
      (GM04.cross σ_plus (T.subtreeAt f₁) f₁).toHypergraph =
    separationOrder
      (GM04.cross σ_plus (T.subtreeAt f₂) f₂).toHypergraph
      (GM04.cross σ_plus (T.rootSide f₂) T.root).toHypergraph := by
    rw [separationOrder_comm]
    exact hord
  have hord_H_lt : separationOrder H₁ H₂ <
      separationOrder (GM04.cross σ_plus (T.rootSide f₁) T.root).toHypergraph
        (GM04.cross σ_plus (T.subtreeAt f₁) f₁).toHypergraph := by
    rw [separationOrder_comm (GM04.cross σ_plus (T.rootSide f₁) T.root).toHypergraph]
    exact hord_lt
  obtain ⟨e, he_p, C, D, hmakes_e, hord_e_lt⟩ :=
    hrot p hp_path (Sym2.mem_mk_left _ _) (Sym2.mem_mk_right _ _) hf₁_in_p hf₂_in_p
      hmakes₁_symm hmakes₂ hroot₂₁ hsub₁₂ hord₁₂
      ⟨H₁, H₂, hsepH, hle₁, hle₂, hord_H_lt⟩
  rw [Walk.edges_map, List.mem_map] at he_p
  obtain ⟨e_T, he_T_mem, rfl⟩ := he_p
  induction e_T using Sym2.ind with
  | _ s s' =>
    have he_T : Thomas.OnTreePathEdge (Thomas.toSimpleGraph T) u₁ u₂ s s' :=
      (Thomas.onTreePathEdge_iff_mem_treePath hK_tree).2
        ⟨p_T.adj_of_mem_edges he_T_mem, he_T_mem⟩
    obtain ⟨g, hg_edges, _, h_orient⟩ := Thomas.exists_onPathEdge_of_onTreePathEdge T he_T
    have hs_in : s ∈ p_T.support := Walk.fst_mem_support_of_mem_edges p_T he_T_mem
    have hs'_in : s' ∈ p_T.support := Walk.snd_mem_support_of_mem_edges p_T he_T_mem
    rw [hp_T_support] at hs_in hs'_in
    have hg_reaches : T.Reaches g.1 f₁ ∧ T.Reaches (T.parent f₂) (T.parent g.1) := by
      rcases h_orient with ⟨hs_eq, hs'_par⟩ | ⟨hs'_eq, hs_par⟩
      · have hs'_val : s'.1 = T.parent g.1 := congrArg Subtype.val hs'_par
        rw [hs_eq] at hs_in
        rw [hs'_val] at hs'_in
        exact ⟨hs_in.1, hs'_in.2⟩
      · have hs_val : s.1 = T.parent g.1 := congrArg Subtype.val hs_par
        rw [hs'_eq] at hs'_in
        rw [hs_val] at hs_in
        exact ⟨hs'_in.1, hs_in.2⟩
    have hf₂_g : T.Reaches f₂ g.1 := by
      rcases T.reaches_total_of_reaches hreach hg_reaches.1 with h1 | h2
      · exact h1
      · by_cases hgf₂ : g.1 = f₂
        · subst hgf₂; exact T.reaches_refl g.2
        · exfalso
          have h3 := T.reaches_parent_of_reaches_of_ne h2 hgf₂
          exact T.not_reaches_parent hg_edges (T.reaches_trans h3 hg_reaches.2)
    have hg_pathEdges : g.1 ∈ T.pathEdges f₂ f₁ ∩ (T.edges : Set ι) :=
      ⟨⟨hf₂_g, hg_reaches.1⟩, hg_edges⟩
    have h_e_eq : (Sym2.map iso.toHom s(s, s')) = s(g.1, T.parent g.1) := by
      rcases h_orient with ⟨hs_eq, hs'_par⟩ | ⟨hs'_eq, hs_par⟩
      · change s(s.1, s'.1) = s(g.1, T.parent g.1)
        rw [congrArg Subtype.val hs_eq, congrArg Subtype.val hs'_par]
        rfl
      · change s(s.1, s'.1) = s(g.1, T.parent g.1)
        rw [congrArg Subtype.val hs'_eq, congrArg Subtype.val hs_par, Sym2.eq_swap]
        rfl
    rw [h_e_eq] at hmakes_e
    have hord_g_eq : separationOrder C D = GM04.edgeOrder T σ_plus g.1 := by
      obtain ⟨u, v, _, he_uv, rfl, rfl⟩ := hmakes_e
      rcases Sym2.eq_iff.1 he_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [← hsubtree_eq_side hg_edges, ← hrootSide_eq_side hg_edges]
        rfl
      · rw [Sym2.eq_swap, separationOrder_comm, ← hsubtree_eq_side hg_edges,
          ← hrootSide_eq_side hg_edges]
        rfl
    have hord_f₁_eq : separationOrder
        (GM04.cross σ_plus (T.rootSide f₁) T.root).toHypergraph
        (GM04.cross σ_plus (T.subtreeAt f₁) f₁).toHypergraph =
      GM04.edgeOrder T σ_plus f₁ := by
      rw [separationOrder_comm]
      rfl
    rw [hord_g_eq, hord_f₁_eq] at hord_e_lt
    exact not_lt.2 (hmin g.1 hg_pathEdges) hord_e_lt

/-- **Graph Minors XVIII, (6.4)** (page 102):
"Let $P = (G, \mu, \Delta, \phi)$ be a rootless, robust $\Omega$-patchwork, and let $(S,
\sigma)$ be a rotund tree-decomposition of $G^-$. Let $T$ be an arborescence with $T^- = S$.
Then there is a rooted decomposition $(T, \tau)$ of $P$ such that $\tau(t)^- = \sigma(t)$
for each $t \in V(T)$." -/
theorem theorem_6_4_proof
     [Preorder Ω] {ι : Type*} [Fintype ι]
    {P : GM04.Patchwork Ω α β} (hrootless : IsRootless P) (hrob : P.IsRobust)
    {S : SimpleGraph ι} {σ : ι → Hypergraph α β}
    (htd : GM10.IsTreeDecomposition P.G.toHypergraph S σ)
    (hrot : IsRotund P.G.toHypergraph S σ)
    (T : GM04.RootedTree ι) (hT_verts : T.verts = Finset.univ)
    (hT_S : arborescenceUnderlying T = S) :
    ∃ τ : ι → RootedHypergraph α β,
      IsRootedDecomposition P T τ ∧ ∀ t, (τ t).toHypergraph = σ t := by
  classical
  have hG_roots_nil : P.G.roots = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro v hv
    have hv_set : v ∈ P.G.rootSet := hv
    rw [hrootless] at hv_set
    exact hv_set
  -- Construct `σ⁺ : ι → RootedHypergraph α β` as in the proof of (6.4) (page 102).
  let σ_plus : ι → RootedHypergraph α β := fun t ↦
    { toHypergraph := σ t
      roots :=
        if t = T.root then []
        else
          (((σ t).vertexSet_finite.subset Set.inter_subset_left :
            ((σ t).vertexSet ∩ (σ (T.parent t)).vertexSet).Finite)).toFinset.toList
      roots_nodup := by
        split_ifs
        · exact List.nodup_nil
        · exact Finset.nodup_toList _
      roots_subset := by
        intro v hv
        split_ifs at hv
        · exact (List.not_mem_nil hv).elim
        · rw [Finset.mem_toList, Set.Finite.mem_toFinset] at hv
          exact hv.1 }
  have hσ_plus_toH : ∀ t, (σ_plus t).toHypergraph = σ t := fun _ ↦ rfl
  -- `(T, σ⁺)` is a `GM04.IsTreeDecomposition` of `P.G`.
  have htd_plus : GM04.IsTreeDecomposition P.G T σ_plus :=
    { le := fun t _ ↦ htd.le t
      biUnion_eq := by
        rw [hT_verts]
        exact htd.biUnion_eq
      edgeSet_inter_eq := fun _ _ _ _ hne ↦ htd.edgeSet_inter_eq hne
      inter_le := fun t₁ ht₁ t₂ ht₂ t₃ ht₃ hon ↦ by
        refine htd.inter_le fun w hw_path ↦ ?_
        let iso : Thomas.toSimpleGraph T ≃g S :=
          { toFun := fun u ↦ u.1
            invFun := fun x ↦ ⟨x, hT_verts ▸ Finset.mem_univ x⟩
            left_inv := fun _ ↦ Subtype.ext rfl
            right_inv := fun _ ↦ rfl
            map_rel_iff' := by
              intro u v
              rw [← hT_S]
              simp only [Thomas.toSimpleGraph, arborescenceUnderlying, Equiv.coe_fn_mk,
                T.mem_edges_iff, u.2, v.2, true_and] }
        let u₁ : T.verts := ⟨t₁, ht₁⟩
        let u₂ : T.verts := ⟨t₂, ht₂⟩
        let u₃ : T.verts := ⟨t₃, ht₃⟩
        have hon_T : Thomas.OnTreePath (Thomas.toSimpleGraph T) u₁ u₃ u₂ :=
          (Thomas.onTreePath_toSimpleGraph_iff T u₁ u₃ u₂).2 hon
        let w_T : (Thomas.toSimpleGraph T).Walk u₁ u₃ := w.map iso.symm.toHom
        have hw_T_path : w_T.IsPath := hw_path.map iso.symm.injective
        have hu₂_in : u₂ ∈ (w.map iso.symm.toHom).support := hon_T w_T hw_T_path
        rw [Walk.support_map, List.mem_map] at hu₂_in
        obtain ⟨x, hx, hx_eq⟩ := hu₂_in
        have hx_val : x = t₂ := congrArg Subtype.val hx_eq
        exact hx_val ▸ hx
      roots_root := by
        change (if T.root = T.root then [] else _) = P.G.roots
        rw [ite_eq_left rfl, hG_roots_nil]
      rootSet_edge := fun f hf ↦ by
        have hf_ne : f ≠ T.root := T.ne_root_of_mem_edges hf
        change {v | v ∈ (if f = T.root then [] else _)} = _
        rw [ite_eq_right hf_ne]
        ext v
        simp only [Set.mem_ofPred_eq, Finset.mem_toList, Set.Finite.mem_toFinset,
          inter_vertexSet]
        rfl }
  have hcross_verts : GM04.cross σ_plus T.verts T.root = P.G :=
    htd_plus.cross_verts_eq
  -- Relate `cross σ⁺ (T.subtreeAt g) g` and `cross σ⁺ (T.rootSide g) T.root` to
  -- `GM10.treeDecompSide S σ`.
  have hsubtree_eq_side : ∀ {g : ι} (hg : g ∈ T.edges),
      (GM04.cross σ_plus (T.subtreeAt g) g).toHypergraph =
        GM10.treeDecompSide S σ s(g, T.parent g) g := by
    intro g hg
    have hg_sub : g ∈ T.subtreeAt g := T.self_mem_subtreeAt (hT_verts ▸ Finset.mem_univ g)
    have hins : insert g (T.subtreeAt g) = T.subtreeAt g := Finset.insert_eq_of_mem hg_sub
    have hreach_eq : ∀ t : ι,
        (S.deleteEdges {s(g, T.parent g)}).Reachable g t ↔ t ∈ T.subtreeAt g := by
      intro t
      rw [← hT_S]
      exact reachable_deleteEdges_arborescenceUnderlying_iff T hT_verts hg t
    refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
      (biUnion_le fun t _ ↦ htd.le t)
      (biUnion_le fun t _ ↦ htd.le t) ?_ ?_
    · change (⋃ t ∈ insert g (T.subtreeAt g), (σ t).vertexSet) = _
      rw [hins]
      ext v
      simp only [GM10.treeDecompSide, biUnion, Set.mem_iUnion, Finset.mem_filter,
        Finset.mem_univ, true_and, hreach_eq]
    · change (⋃ t ∈ insert g (T.subtreeAt g), (σ t).edgeSet) = _
      rw [hins]
      ext e
      simp only [GM10.treeDecompSide, biUnion, Set.mem_iUnion, Finset.mem_filter,
        Finset.mem_univ, true_and, hreach_eq]
  have hrootSide_eq_side : ∀ {g : ι} (hg : g ∈ T.edges),
      (GM04.cross σ_plus (T.rootSide g) T.root).toHypergraph =
        GM10.treeDecompSide S σ s(g, T.parent g) (T.parent g) := by
    intro g hg
    have hroot_mem : T.root ∈ T.rootSide g := T.root_mem_rootSide hg
    have hins : insert T.root (T.rootSide g) = T.rootSide g := Finset.insert_eq_of_mem hroot_mem
    have hreach_eq : ∀ t : ι,
        (S.deleteEdges {s(g, T.parent g)}).Reachable (T.parent g) t ↔ t ∈ T.rootSide g := by
      intro t
      rw [← hT_S]
      exact reachable_parent_deleteEdges_arborescenceUnderlying_iff T hT_verts hg t
    refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
      (biUnion_le fun t _ ↦ htd.le t)
      (biUnion_le fun t _ ↦ htd.le t) ?_ ?_
    · change (⋃ t ∈ insert T.root (T.rootSide g), (σ t).vertexSet) = _
      rw [hins]
      ext v
      simp only [GM10.treeDecompSide, biUnion, Set.mem_iUnion, Finset.mem_filter,
        Finset.mem_univ, true_and, hreach_eq]
    · change (⋃ t ∈ insert T.root (T.rootSide g), (σ t).edgeSet) = _
      rw [hins]
      ext e
      simp only [GM10.treeDecompSide, biUnion, Set.mem_iUnion, Finset.mem_filter,
        Finset.mem_univ, true_and, hreach_eq]
  have hmakes_edge : ∀ {g : ι} (hg : g ∈ T.edges),
      GM10.MakesSeparation S σ s(g, T.parent g)
        (GM04.cross σ_plus (T.subtreeAt g) g).toHypergraph
        (GM04.cross σ_plus (T.rootSide g) T.root).toHypergraph := by
    intro g hg
    have hadj : S.Adj g (T.parent g) := by
      rw [← hT_S]
      exact Or.inl ⟨hg, rfl⟩
    exact ⟨g, T.parent g, hadj, rfl, hsubtree_eq_side hg, hrootSide_eq_side hg⟩
  have hrot_plus : GM04.IsRotund T σ_plus (T.edges : Set ι) :=
    rooted_decomposition_isRotund hT_verts hT_S hrot htd_plus
      hsubtree_eq_side hrootSide_eq_side hmakes_edge
  -- Apply GM04 (4.1) to `(T, σ⁺)`.
  let R : Set (RootedHypergraph α β) := {H | H.toHypergraph ≤ P.G.toHypergraph}
  let sim : RootedHypergraph α β → RootedHypergraph α β → Prop :=
    fun H₁ H₂ ↦ GM04.Simulated (P.restrict H₁) (P.restrict H₂)
  have hA1 : GM04.Axiom1 R := fun G hG H hH ↦ hH.trans hG
  have hA2 : GM04.Axiom2 R sim :=
    ⟨fun G _ ↦ GM04.Simulated.refl _, fun _ _ _ _ _ _ h₁₂ h₂₃ ↦ h₁₂.trans h₂₃⟩
  have hA3 : GM04.Axiom3 R sim := axiom3_of_isRobust hrob
  have htd_cross : GM04.IsTreeDecomposition (GM04.cross σ_plus T.verts T.root) T σ_plus := by
    rwa [hcross_verts]
  have hR_cross : GM04.cross σ_plus T.verts T.root ∈ R := by
    change (GM04.cross σ_plus T.verts T.root).toHypergraph ≤ P.G.toHypergraph
    rw [hcross_verts]
  obtain ⟨τ, htd_τ, hτ_toH, hlinked_τ⟩ :=
    GM04.theorem_4_1_proof hA1 hA2 hA3 T σ_plus htd_cross hR_cross (T.edges : Set ι)
      subset_rfl hrot_plus
  rw [hcross_verts] at htd_τ
  refine ⟨τ, ⟨htd_τ, hlinked_τ⟩, fun t ↦ ?_⟩
  exact hτ_toH t (hT_verts ▸ Finset.mem_univ t)

/-! ## Theorem (6.5): Subtrees, root sides, and child locations in rooted decompositions -/

/-- Every left side `A` of a rooted separation `(A, B)` of `G` (`G.IsSeparation A B`) is
complemented in `G`. -/
theorem isComplemented_of_isSeparation {G A B : RootedHypergraph α β}
    (hsep : G.IsSeparation A B) : IsComplemented G A where
  le := hsep.isSeparation.left_le
  roots_mem v hvA hvG := by
    rw [hsep.rootSet_left]
    have hvB_root : v ∈ B.rootSet := by
      change v ∈ B.roots
      rw [hsep.roots_right]
      exact hvG
    exact ⟨hvA, B.roots_subset v hvB_root⟩
  inc_diff_mem v e hvA he hinc := by
    rw [hsep.rootSet_left]
    have he_union : e ∈ A.edgeSet ∪ B.edgeSet := by
      rw [← union_edgeSet, hsep.isSeparation.union_eq]
      exact he.1
    have heB : e ∈ B.edgeSet := he_union.resolve_left he.2
    have hincB : B.Inc e v := (inc_iff_of_le hsep.isSeparation.right_le heB v).1 hinc
    exact ⟨hvA, B.vertex_mem_of_inc hincB⟩

/-- If `G.IsSeparation A B`, then `complement G A` equals `B`. -/
theorem complement_eq_of_isSeparation {G A B : RootedHypergraph α β}
    (hsep : G.IsSeparation A B) :
    complement G A (isComplemented_of_isSeparation hsep) = B := by
  have hcomp := isComplemented_of_isSeparation hsep
  refine RootedHypergraph.ext ?_ hsep.roots_right.symm
  refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
    hcomp.isSeparation.isSeparation.right_le hsep.isSeparation.right_le ?_ ?_
  · change (G.vertexSet \ A.vertexSet) ∪ A.rootSet = B.vertexSet
    rw [hsep.rootSet_left]
    ext v
    simp only [Set.mem_union, Set.mem_sdiff, inter_vertexSet, Set.mem_inter_iff]
    constructor
    · rintro (⟨hvG, hvA⟩ | ⟨_, hvB⟩)
      · rw [← hsep.isSeparation.union_eq, union_vertexSet] at hvG
        exact hvG.resolve_left hvA
      · exact hvB
    · intro hvB
      by_cases hvA : v ∈ A.vertexSet
      · exact Or.inr ⟨hvA, hvB⟩
      · exact Or.inl ⟨hsep.isSeparation.right_le.vertexSet_subset hvB, hvA⟩
  · change G.edgeSet \ A.edgeSet = B.edgeSet
    ext e
    simp only [Set.mem_sdiff]
    constructor
    · rintro ⟨heG, heA⟩
      rw [← hsep.isSeparation.union_eq, union_edgeSet] at heG
      exact heG.resolve_left heA
    · intro heB
      refine ⟨hsep.isSeparation.right_le.edgeSet_subset heB, fun heA ↦ ?_⟩
      have he_inter : e ∈ (A.toHypergraph ∩ B.toHypergraph).edgeSet := ⟨heA, heB⟩
      rw [hsep.isSeparation.edgeSet_inter_eq] at he_inter
      exact he_inter

/-- **Graph Minors XVIII, (6.5.1)** (page 103):
"Let $(T, \tau)$ be a rooted decomposition of a rootless $\Omega$-patchwork $P = (G, \mu,
\Delta, \phi)$.* 1. *If $f \in E(T)$, then $\tau \times T^f$ is complemented in $G$, and $G
\setminus \tau \times T^f = \tau \times T_f$." -/
theorem theorem_6_5_1 [Preorder Ω] {ι : Type*} {P : GM04.Patchwork Ω α β}
    {T : GM04.RootedTree ι} {τ : ι → RootedHypergraph α β}
    (hdec : IsRootedDecomposition P T τ) {f : ι} (hf : f ∈ T.edges) :
    ∃ hcomp : IsComplemented P.G (GM04.cross τ (T.subtreeAt f) f),
      complement P.G (GM04.cross τ (T.subtreeAt f) f) hcomp =
        GM04.cross τ (T.rootSide f) T.root := by
  have hsep := hdec.isTreeDecomposition.isSeparation_edge hf
  exact ⟨isComplemented_of_isSeparation hsep, complement_eq_of_isSeparation hsep⟩

/-- **Graph Minors XVIII, (6.5.2)** (page 103):
"2. *If $f \in E(T)$ then $\tau \times (T, f)$ is complemented in $G$ and
$G \setminus \tau \times (T, f)$ is the rooted hypergraph $H$ with $H^- = (\tau \times T^f)^-$ and
$\bar{\pi}(H) = \emptyset$.*" -/
theorem theorem_6_5_2 [Preorder Ω] {ι : Type*} {P : GM04.Patchwork Ω α β}
    (hrootless : IsRootless P)
    {T : GM04.RootedTree ι} {τ : ι → RootedHypergraph α β}
    (hdec : IsRootedDecomposition P T τ) {f : ι} (hf : f ∈ T.edges) :
    ∃ hcomp : IsComplemented P.G (rootedDecompRootSide hdec.isTreeDecomposition hf),
      (complement P.G (rootedDecompRootSide hdec.isTreeDecomposition hf) hcomp).toHypergraph =
        (GM04.cross τ (T.subtreeAt f) f).toHypergraph ∧
      (complement P.G (rootedDecompRootSide hdec.isTreeDecomposition hf) hcomp).rootSet = ∅ := by
  have hsep_edge := hdec.isTreeDecomposition.isSeparation_edge hf
  let G₀ := rootedDecompRootSide hdec.isTreeDecomposition hf
  let H : RootedHypergraph α β :=
    { toHypergraph := (GM04.cross τ (T.subtreeAt f) f).toHypergraph
      roots := P.G.roots
      roots_nodup := P.G.roots_nodup
      roots_subset := fun v hv ↦ by
        have hv_set : v ∈ P.G.rootSet := hv
        rw [hrootless] at hv_set
        exact hv_set.elim }
  have hsep_G₀ : P.G.IsSeparation G₀ H :=
    { isSeparation := hsep_edge.isSeparation.symm
      roots_right := rfl
      rootSet_left := by
        change (GM04.cross τ (T.subtreeAt f) f).rootSet =
          ((GM04.cross τ (T.rootSide f) T.root).toHypergraph ∩
            (GM04.cross τ (T.subtreeAt f) f).toHypergraph).vertexSet
        rw [hsep_edge.rootSet_left]
        exact Set.inter_comm _ _ }
  refine ⟨isComplemented_of_isSeparation hsep_G₀, ?_, ?_⟩
  · rw [complement_eq_of_isSeparation hsep_G₀]
  · rw [complement_eq_of_isSeparation hsep_G₀]
    exact hrootless

/-- **Graph Minors XVIII, (6.5), Claim (1)** (page 103):
"If $f \in E(T)$ has tail $t$ then $\tau \times T^f$ is complemented in $\tau \times T^t$,
and* $$ (\tau \times T^t \setminus \tau \times T^f)^- = (\tau \times T_f)^- \cap (\tau
\times T^t)^-." -/
theorem lemma_6_5_claim_1 {ι : Type*} {G : RootedHypergraph α β}
    {T : GM04.RootedTree ι} {τ : ι → RootedHypergraph α β}
    (htd : GM04.IsTreeDecomposition G T τ) {f t : ι} (hf : f ∈ T.edges) (ht : t ∈ T.verts)
    (hpar : T.parent f = t) :
    ∃ hcomp : IsComplemented (GM04.cross τ (T.subtreeAt t) t) (GM04.cross τ (T.subtreeAt f) f),
      (complement (GM04.cross τ (T.subtreeAt t) t) (GM04.cross τ (T.subtreeAt f) f)
        hcomp).toHypergraph =
        (GM04.cross τ (T.rootSide f) T.root).toHypergraph ∩
          (GM04.cross τ (T.subtreeAt t) t).toHypergraph := by
  have hsep_edge := htd.isSeparation_edge hf
  have hfv : f ∈ T.verts := T.edges_subset_verts hf
  have htf : T.Reaches t f := hpar ▸ T.reaches_parent hfv
  have hsub_ft : T.subtreeAt f ⊆ T.subtreeAt t := T.subtreeAt_mono htf
  have hle_ft : (GM04.cross τ (T.subtreeAt f) f).toHypergraph ≤
      (GM04.cross τ (T.subtreeAt t) t).toHypergraph :=
    htd.cross_le_cross hsub_ft (T.subtreeAt_subset_verts t)
      (T.self_mem_subtreeAt hfv) (T.self_mem_subtreeAt ht)
  have ht_rootSide : t ∈ T.rootSide f := hpar ▸ T.parent_mem_rootSide hf
  have hle_t_rootSide : (τ t).toHypergraph ≤
      (GM04.cross τ (T.rootSide f) T.root).toHypergraph :=
    htd.le_cross (T.rootSide_subset_verts f) (T.root_mem_rootSide hf) ht_rootSide
  let B_H := (GM04.cross τ (T.rootSide f) T.root).toHypergraph ∩
    (GM04.cross τ (T.subtreeAt t) t).toHypergraph
  have hB_le_t : B_H ≤ (GM04.cross τ (T.subtreeAt t) t).toHypergraph :=
    inter_le_right hsep_edge.isSeparation.right_le
      (htd.cross_le (T.subtreeAt_subset_verts t) (T.self_mem_subtreeAt ht))
  have hroots_in_B : ∀ v ∈ (GM04.cross τ (T.subtreeAt t) t).roots, v ∈ B_H.vertexSet := by
    intro v hv
    have hv_t : v ∈ (τ t).vertexSet := (τ t).roots_subset v hv
    refine ⟨hle_t_rootSide.vertexSet_subset hv_t, ?_⟩
    exact (htd.le_cross (T.subtreeAt_subset_verts t) (T.self_mem_subtreeAt ht)
      (T.self_mem_subtreeAt ht)).vertexSet_subset hv_t
  let B : RootedHypergraph α β :=
    { toHypergraph := B_H
      roots := (GM04.cross τ (T.subtreeAt t) t).roots
      roots_nodup := (GM04.cross τ (T.subtreeAt t) t).roots_nodup
      roots_subset := hroots_in_B }
  have hsep_t : (GM04.cross τ (T.subtreeAt t) t).IsSeparation
      (GM04.cross τ (T.subtreeAt f) f) B := by
    refine ⟨⟨hle_ft, hB_le_t, ?_, ?_⟩, rfl, ?_⟩
    · refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
        (union_le hle_ft hB_le_t) le_rfl ?_ ?_
      · ext v
        simp only [B, B_H, union_vertexSet, inter_vertexSet, Set.mem_union,
          Set.mem_inter_iff]
        refine ⟨fun h ↦ h.elim (fun hv ↦ hle_ft.vertexSet_subset hv) And.right, fun hvt ↦ ?_⟩
        by_cases hvf : v ∈ (GM04.cross τ (T.subtreeAt f) f).vertexSet
        · exact Or.inl hvf
        · have hvG : v ∈ G.vertexSet :=
            (htd.cross_le (T.subtreeAt_subset_verts t) (T.self_mem_subtreeAt ht)).vertexSet_subset
              hvt
          rw [← hsep_edge.isSeparation.union_eq, union_vertexSet] at hvG
          exact Or.inr ⟨hvG.resolve_left hvf, hvt⟩
      · ext e
        simp only [B, B_H, union_edgeSet, inter_edgeSet, Set.mem_union,
          Set.mem_inter_iff]
        refine ⟨fun h ↦ h.elim (fun he ↦ hle_ft.edgeSet_subset he) And.right, fun het ↦ ?_⟩
        by_cases hef : e ∈ (GM04.cross τ (T.subtreeAt f) f).edgeSet
        · exact Or.inl hef
        · have heG : e ∈ G.edgeSet :=
            (htd.cross_le (T.subtreeAt_subset_verts t) (T.self_mem_subtreeAt ht)).edgeSet_subset het
          rw [← hsep_edge.isSeparation.union_eq, union_edgeSet] at heG
          exact Or.inr ⟨heG.resolve_left hef, het⟩
    · ext e
      simp only [B, B_H, inter_edgeSet, Set.mem_inter_iff, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro hef her _
      have he_inter : e ∈ ((GM04.cross τ (T.subtreeAt f) f).toHypergraph ∩
          (GM04.cross τ (T.rootSide f) T.root).toHypergraph).edgeSet := ⟨hef, her⟩
      rw [hsep_edge.isSeparation.edgeSet_inter_eq] at he_inter
      exact he_inter
    · rw [hsep_edge.rootSet_left]
      ext v
      simp only [B, B_H, inter_vertexSet, Set.mem_inter_iff]
      exact ⟨fun ⟨hvf, hvr⟩ ↦ ⟨hvf, hvr, hle_ft.vertexSet_subset hvf⟩,
        fun ⟨hvf, hvr, _⟩ ↦ ⟨hvf, hvr⟩⟩
  refine ⟨isComplemented_of_isSeparation hsep_t, ?_⟩
  rw [complement_eq_of_isSeparation hsep_t]

/-- **Graph Minors XVIII, (6.5), Claim (2)** (pages 103–104):
"If distinct $f_1, f_2 \in E(T)$ have a common tail $t$, then $\tau \times T^{f_1} \subseteq
\tau \times T^t \setminus \tau \times T^{f_2}$." -/
theorem lemma_6_5_claim_2 {ι : Type*} {G : RootedHypergraph α β}
    {T : GM04.RootedTree ι} {τ : ι → RootedHypergraph α β}
    (htd : GM04.IsTreeDecomposition G T τ) {f₁ f₂ t : ι}
    (hf₁ : f₁ ∈ T.edges) (hf₂ : f₂ ∈ T.edges) (ht : t ∈ T.verts)
    (hpar₁ : T.parent f₁ = t) (hpar₂ : T.parent f₂ = t) (hne : f₁ ≠ f₂) :
    (GM04.cross τ (T.subtreeAt f₁) f₁).toHypergraph ≤
      (complement (GM04.cross τ (T.subtreeAt t) t) (GM04.cross τ (T.subtreeAt f₂) f₂)
        (lemma_6_5_claim_1 htd hf₂ ht hpar₂).choose).toHypergraph := by
  rw [(lemma_6_5_claim_1 htd hf₂ ht hpar₂).choose_spec]
  have hf₁c : f₁ ∈ T.children t := T.mem_children_iff.2 ⟨hf₁, hpar₁⟩
  have hf₂c : f₂ ∈ T.children t := T.mem_children_iff.2 ⟨hf₂, hpar₂⟩
  have hdisj := T.disjoint_subtreeAt_of_mem_children hf₁c hf₂c hne
  have hsub_root₂ : T.subtreeAt f₁ ⊆ T.rootSide f₂ := by
    intro x hx
    rw [T.mem_rootSide]
    exact ⟨T.subtreeAt_subset_verts f₁ hx,
      fun h₂ ↦ Finset.disjoint_left.1 hdisj hx (T.mem_subtreeAt.2 h₂)⟩
  have hsub_t : T.subtreeAt f₁ ⊆ T.subtreeAt t :=
    T.subtreeAt_mono (hpar₁ ▸ T.reaches_parent (T.edges_subset_verts hf₁))
  have hle_root₂ : (GM04.cross τ (T.subtreeAt f₁) f₁).toHypergraph ≤
      (GM04.cross τ (T.rootSide f₂) T.root).toHypergraph :=
    htd.cross_le_cross hsub_root₂ (T.rootSide_subset_verts f₂)
      (T.self_mem_subtreeAt (T.edges_subset_verts hf₁)) (T.root_mem_rootSide hf₂)
  have hle_t : (GM04.cross τ (T.subtreeAt f₁) f₁).toHypergraph ≤
      (GM04.cross τ (T.subtreeAt t) t).toHypergraph :=
    htd.cross_le_cross hsub_t (T.subtreeAt_subset_verts t)
      (T.self_mem_subtreeAt (T.edges_subset_verts hf₁)) (T.self_mem_subtreeAt ht)
  exact le_inter hle_root₂ hle_t

/-- **Graph Minors XVIII, (6.5), Claim (3)** (page 104):
"(3) *If $f_0, f_1 \in E(T)$ and the head of $f_0$ equals the tail of $f_1$, let
$G_0 = \tau \times (T, f)$; then $\tau \times T^{f_1} \subseteq G \setminus G_0$ and
$G_0 \subseteq G \setminus \tau \times T^{f_1}$.*"
(Note: the paper writes $\tau \times (T, f)$ as a typo for $\tau \times (T, f_0)$.) -/
theorem lemma_6_5_claim_3 [Preorder Ω] {ι : Type*} {P : GM04.Patchwork Ω α β}
    (hrootless : IsRootless P)
    {T : GM04.RootedTree ι} {τ : ι → RootedHypergraph α β}
    (hdec : IsRootedDecomposition P T τ) {f₀ f₁ : ι}
    (hf₀ : f₀ ∈ T.edges) (hf₁ : f₁ ∈ T.edges) (hpar : T.parent f₁ = f₀) :
    (GM04.cross τ (T.subtreeAt f₁) f₁).toHypergraph ≤
      (complement P.G (rootedDecompRootSide hdec.isTreeDecomposition hf₀)
        (theorem_6_5_2 hrootless hdec hf₀).choose).toHypergraph ∧
    (rootedDecompRootSide hdec.isTreeDecomposition hf₀).toHypergraph ≤
      (complement P.G (GM04.cross τ (T.subtreeAt f₁) f₁)
        (theorem_6_5_1 hdec hf₁).choose).toHypergraph := by
  have htd := hdec.isTreeDecomposition
  have hf₀_f₁ : T.Reaches f₀ f₁ := hpar ▸ T.reaches_parent (T.edges_subset_verts hf₁)
  refine ⟨?_, ?_⟩
  · rw [(theorem_6_5_2 hrootless hdec hf₀).choose_spec.1]
    exact htd.cross_le_cross (T.subtreeAt_mono hf₀_f₁) (T.subtreeAt_subset_verts f₀)
      (T.self_mem_subtreeAt (T.edges_subset_verts hf₁))
      (T.self_mem_subtreeAt (T.edges_subset_verts hf₀))
  · rw [(theorem_6_5_1 hdec hf₁).choose_spec]
    change (GM04.cross τ (T.rootSide f₀) T.root).toHypergraph ≤
      (GM04.cross τ (T.rootSide f₁) T.root).toHypergraph
    have hsub_root : T.rootSide f₀ ⊆ T.rootSide f₁ := by
      intro x hx
      rw [T.mem_rootSide] at hx ⊢
      exact ⟨hx.1, fun h₁ ↦ hx.2 (T.reaches_trans hf₀_f₁ h₁)⟩
    exact htd.cross_le_cross hsub_root (T.rootSide_subset_verts f₁)
      (T.root_mem_rootSide hf₀) (T.root_mem_rootSide hf₁)

/-- The core `M(G, ℒ)` of a rooted location `ℒ` in `G` is a subhypergraph of `G⁻`. -/
theorem rootedLocationCore_le {G : RootedHypergraph α β} {ℒ : Set (RootedHypergraph α β)}
    (hℒ : IsRootedLocation G ℒ) :
    rootedLocationCore G ℒ ≤ G.toHypergraph :=
  locationCore_le hℒ.isLocation

/-- For any vertex `t ∈ V(T)` in a rooted decomposition `(T, τ)`, the set of child subtrees
`ℒ = {τ × T^f : f ∈ T.children t}` is a rooted location in `τ × T^t`, with
`M(τ × T^t, ℒ) = τ(t)⁻`. -/
theorem isRootedLocation_children {ι : Type*} {G : RootedHypergraph α β}
    {T : GM04.RootedTree ι} {τ : ι → RootedHypergraph α β}
    (htd : GM04.IsTreeDecomposition G T τ) {t : ι} (ht : t ∈ T.verts) :
    let ℒ : Set (RootedHypergraph α β) :=
      {A | ∃ f ∈ T.children t, A = GM04.cross τ (T.subtreeAt f) f}
    IsRootedLocation (GM04.cross τ (T.subtreeAt t) t) ℒ ∧
      rootedLocationCore (GM04.cross τ (T.subtreeAt t) t) ℒ = (τ t).toHypergraph := by
  classical
  intro ℒ
  have hℒ_loc : IsRootedLocation (GM04.cross τ (T.subtreeAt t) t) ℒ :=
    { isComplemented := by
        rintro _ ⟨f, hfc, rfl⟩
        obtain ⟨hfe, hpar⟩ := T.mem_children_iff.1 hfc
        exact (lemma_6_5_claim_1 htd hfe ht hpar).choose
      le_complement := by
        rintro _ ⟨f₁, hf₁c, rfl⟩ _ ⟨f₂, hf₂c, rfl⟩ hne_A
        have hne_f : f₁ ≠ f₂ := fun hEq ↦ hne_A (by subst hEq; rfl)
        obtain ⟨hf₁e, hpar₁⟩ := T.mem_children_iff.1 hf₁c
        obtain ⟨hf₂e, hpar₂⟩ := T.mem_children_iff.1 hf₂c
        exact lemma_6_5_claim_2 htd hf₁e hf₂e ht hpar₁ hpar₂ hne_f }
  refine ⟨hℒ_loc, ?_⟩
  have hle_t : (τ t).toHypergraph ≤ (GM04.cross τ (T.subtreeAt t) t).toHypergraph :=
    htd.le_cross (T.subtreeAt_subset_verts t) (T.self_mem_subtreeAt ht) (T.self_mem_subtreeAt ht)
  refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
    ((rootedLocationCore_le hℒ_loc).trans
      (htd.cross_le (T.subtreeAt_subset_verts t) (T.self_mem_subtreeAt ht)))
    (htd.le t ht) ?_ ?_
  · ext v
    rw [mem_rootedLocationCore_vertexSet_iff hℒ_loc]
    constructor
    · rintro ⟨hvt, hv_all⟩
      rw [GM04.cross_toHypergraph_of_mem τ (T.self_mem_subtreeAt ht),
        biUnion_vertexSet, Set.mem_iUnion₂] at hvt
      obtain ⟨u, hu, hvu⟩ := hvt
      rcases (T.mem_subtreeAt_iff_eq_or_exists_children ht).1 hu with rfl | ⟨f, hfc, huf⟩
      · exact hvu
      · obtain ⟨hfe, hpar⟩ := T.mem_children_iff.1 hfc
        have hvf : v ∈ (GM04.cross τ (T.subtreeAt f) f).vertexSet :=
          (htd.le_cross (T.subtreeAt_subset_verts f)
            (T.self_mem_subtreeAt (T.edges_subset_verts hfe)) huf).vertexSet_subset hvu
        have hv_root := hv_all (GM04.cross τ (T.subtreeAt f) f) ⟨f, hfc, rfl⟩ hvf
        rw [(htd.isSeparation_edge hfe).rootSet_left, htd.subtreeAt_inter_rootSide_eq hfe,
          hpar] at hv_root
        exact hv_root.2
    · intro hvt
      refine ⟨hle_t.vertexSet_subset hvt, ?_⟩
      rintro _ ⟨f, hfc, rfl⟩ hvf
      obtain ⟨hfe, hpar⟩ := T.mem_children_iff.1 hfc
      rw [(htd.isSeparation_edge hfe).rootSet_left, htd.subtreeAt_inter_rootSide_eq hfe, hpar]
      have ht_root : t ∈ T.rootSide f := hpar ▸ T.parent_mem_rootSide hfe
      have hv_inter : v ∈ ((GM04.cross τ (T.subtreeAt f) f).toHypergraph ∩
          (GM04.cross τ (T.rootSide f) T.root).toHypergraph).vertexSet :=
        ⟨hvf, (htd.le_cross (T.rootSide_subset_verts f) (T.root_mem_rootSide hfe)
          ht_root).vertexSet_subset hvt⟩
      rwa [htd.subtreeAt_inter_rootSide_eq hfe, hpar] at hv_inter
  · ext e
    rw [mem_rootedLocationCore_edgeSet_iff]
    constructor
    · rintro ⟨het, he_all⟩
      rw [GM04.cross_toHypergraph_of_mem τ (T.self_mem_subtreeAt ht),
        biUnion_edgeSet, Set.mem_iUnion₂] at het
      obtain ⟨u, hu, heu⟩ := het
      rcases (T.mem_subtreeAt_iff_eq_or_exists_children ht).1 hu with rfl | ⟨f, hfc, huf⟩
      · exact heu
      · obtain ⟨hfe, _⟩ := T.mem_children_iff.1 hfc
        have hef : e ∈ (GM04.cross τ (T.subtreeAt f) f).edgeSet :=
          (htd.le_cross (T.subtreeAt_subset_verts f)
            (T.self_mem_subtreeAt (T.edges_subset_verts hfe)) huf).edgeSet_subset heu
        exact (he_all (GM04.cross τ (T.subtreeAt f) f) ⟨f, hfc, rfl⟩ hef).elim
    · intro het
      refine ⟨hle_t.edgeSet_subset het, ?_⟩
      rintro _ ⟨f, hfc, rfl⟩ hef
      obtain ⟨hfe, hpar⟩ := T.mem_children_iff.1 hfc
      have ht_root : t ∈ T.rootSide f := hpar ▸ T.parent_mem_rootSide hfe
      have her : e ∈ (GM04.cross τ (T.rootSide f) T.root).edgeSet :=
        (htd.le_cross (T.rootSide_subset_verts f) (T.root_mem_rootSide hfe) ht_root).edgeSet_subset
          het
      have he_inter : e ∈ ((GM04.cross τ (T.subtreeAt f) f).toHypergraph ∩
          (GM04.cross τ (T.rootSide f) T.root).toHypergraph).edgeSet := ⟨hef, her⟩
      rw [(htd.isSeparation_edge hfe).isSeparation.edgeSet_inter_eq] at he_inter
      exact he_inter

/-- **Graph Minors XVIII, (6.5.3)** (page 103):
"If $f_0 \in E(T)$ has head $t$ and $f_1, \dots, f_n$ are the edges of $T$ with tail $t$,
then* $$ \mathcal{L} = \{\tau \times T^{f_1}, \dots, \tau \times T^{f_n}\} $$ *is a rooted
location in $\tau \times T^t$ and $\mathcal{L}^* = \mathcal{L} \cup \{\tau \times (T,
f_0)\}$ is a rooted location in $G$ and $M(\tau \times T^t, \mathcal{L}) = M(G,
\mathcal{L}^*)$."
(In `GM04.RootedTree`, an edge `f₀ ∈ T.edges` has head `f₀`.) -/
theorem theorem_6_5_3 [Preorder Ω] {ι : Type*} {P : GM04.Patchwork Ω α β}
    (hrootless : IsRootless P)
    {T : GM04.RootedTree ι} {τ : ι → RootedHypergraph α β}
    (hdec : IsRootedDecomposition P T τ) {f₀ : ι} (hf₀ : f₀ ∈ T.edges) :
    let ℒ : Set (RootedHypergraph α β) :=
      {A | ∃ f ∈ T.children f₀, A = GM04.cross τ (T.subtreeAt f) f}
    let ℒ_star : Set (RootedHypergraph α β) :=
      insert (rootedDecompRootSide hdec.isTreeDecomposition hf₀) ℒ
    IsRootedLocation (GM04.cross τ (T.subtreeAt f₀) f₀) ℒ ∧
      IsRootedLocation P.G ℒ_star ∧
      rootedLocationCore (GM04.cross τ (T.subtreeAt f₀) f₀) ℒ =
        rootedLocationCore P.G ℒ_star := by
  classical
  intro ℒ ℒ_star
  have htd := hdec.isTreeDecomposition
  have hf₀v : f₀ ∈ T.verts := T.edges_subset_verts hf₀
  obtain ⟨hℒ_loc, _⟩ := isRootedLocation_children htd hf₀v
  have hℒ_star_loc : IsRootedLocation P.G ℒ_star :=
    { isComplemented := by
        rintro A (rfl | ⟨f, hfc, rfl⟩)
        · exact (theorem_6_5_2 hrootless hdec hf₀).choose
        · exact (theorem_6_5_1 hdec (T.children_subset_edges f₀ hfc)).choose
      le_complement := by
        rintro A₁ (rfl | ⟨f₁, hf₁c, rfl⟩) A₂ (rfl | ⟨f₂, hf₂c, rfl⟩) hne
        · exact (hne rfl).elim
        · obtain ⟨hf₂e, hpar₂⟩ := T.mem_children_iff.1 hf₂c
          exact (lemma_6_5_claim_3 hrootless hdec hf₀ hf₂e hpar₂).2
        · obtain ⟨hf₁e, hpar₁⟩ := T.mem_children_iff.1 hf₁c
          exact (lemma_6_5_claim_3 hrootless hdec hf₀ hf₁e hpar₁).1
        · obtain ⟨hf₁e, _⟩ := T.mem_children_iff.1 hf₁c
          obtain ⟨hf₂e, _⟩ := T.mem_children_iff.1 hf₂c
          have hne_f : f₁ ≠ f₂ := fun hEq ↦ hne (by subst hEq; rfl)
          rw [(theorem_6_5_1 hdec hf₂e).choose_spec]
          have hdisj := T.disjoint_subtreeAt_of_mem_children hf₁c hf₂c hne_f
          have hsub_root₂ : T.subtreeAt f₁ ⊆ T.rootSide f₂ := by
            intro x hx
            rw [T.mem_rootSide]
            exact ⟨T.subtreeAt_subset_verts f₁ hx,
              fun h₂ ↦ Finset.disjoint_left.1 hdisj hx (T.mem_subtreeAt.2 h₂)⟩
          exact htd.cross_le_cross hsub_root₂ (T.rootSide_subset_verts f₂)
            (T.self_mem_subtreeAt (T.edges_subset_verts hf₁e)) (T.root_mem_rootSide hf₂e) }
  refine ⟨hℒ_loc, hℒ_star_loc, ?_⟩
  have hsep₀ := htd.isSeparation_edge hf₀
  refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
    ((rootedLocationCore_le hℒ_loc).trans
      (htd.cross_le (T.subtreeAt_subset_verts f₀) (T.self_mem_subtreeAt hf₀v)))
    (rootedLocationCore_le hℒ_star_loc) ?_ ?_
  · ext v
    rw [mem_rootedLocationCore_vertexSet_iff hℒ_loc,
      mem_rootedLocationCore_vertexSet_iff hℒ_star_loc]
    constructor
    · rintro ⟨hvf₀, hv_all⟩
      refine ⟨hsep₀.isSeparation.left_le.vertexSet_subset hvf₀, ?_⟩
      rintro A (rfl | hA) hvA
      · change v ∈ (GM04.cross τ (T.subtreeAt f₀) f₀).rootSet
        rw [hsep₀.rootSet_left]
        exact ⟨hvf₀, hvA⟩
      · exact hv_all A hA hvA
    · rintro ⟨hvG, hv_all⟩
      refine ⟨?_, fun A hA hvA ↦ hv_all A (Or.inr hA) hvA⟩
      rw [← hsep₀.isSeparation.union_eq, union_vertexSet] at hvG
      rcases hvG with hvf₀ | hv_root
      · exact hvf₀
      · have h := hv_all (rootedDecompRootSide htd hf₀) (Or.inl rfl) hv_root
        exact (GM04.cross τ (T.subtreeAt f₀) f₀).roots_subset v h
  · ext e
    rw [mem_rootedLocationCore_edgeSet_iff, mem_rootedLocationCore_edgeSet_iff]
    constructor
    · rintro ⟨hef₀, he_all⟩
      refine ⟨hsep₀.isSeparation.left_le.edgeSet_subset hef₀, ?_⟩
      rintro A (rfl | hA) heA
      · have he_inter : e ∈ ((GM04.cross τ (T.subtreeAt f₀) f₀).toHypergraph ∩
            (GM04.cross τ (T.rootSide f₀) T.root).toHypergraph).edgeSet := ⟨hef₀, heA⟩
        rw [hsep₀.isSeparation.edgeSet_inter_eq] at he_inter
        exact he_inter
      · exact he_all A hA heA
    · rintro ⟨heG, he_all⟩
      refine ⟨?_, fun A hA ↦ he_all A (Or.inr hA)⟩
      rw [← hsep₀.isSeparation.union_eq, union_edgeSet] at heG
      exact heG.resolve_right (he_all (rootedDecompRootSide htd hf₀) (Or.inl rfl))

/-- **Graph Minors XVIII, (6.5)** (combined statement, page 103). -/
theorem theorem_6_5_proof [Preorder Ω] {ι : Type*} {P : GM04.Patchwork Ω α β}
    (hrootless : IsRootless P)
    {T : GM04.RootedTree ι} {τ : ι → RootedHypergraph α β}
    (hdec : IsRootedDecomposition P T τ) {f : ι} (hf : f ∈ T.edges) :
    (∃ hcomp : IsComplemented P.G (GM04.cross τ (T.subtreeAt f) f),
      complement P.G (GM04.cross τ (T.subtreeAt f) f) hcomp =
        GM04.cross τ (T.rootSide f) T.root) ∧
    (∃ hcomp : IsComplemented P.G (rootedDecompRootSide hdec.isTreeDecomposition hf),
      (complement P.G (rootedDecompRootSide hdec.isTreeDecomposition hf) hcomp).toHypergraph =
        (GM04.cross τ (T.subtreeAt f) f).toHypergraph ∧
      (complement P.G (rootedDecompRootSide hdec.isTreeDecomposition hf) hcomp).rootSet = ∅) ∧
    (let ℒ : Set (RootedHypergraph α β) :=
       {A | ∃ g ∈ T.children f, A = GM04.cross τ (T.subtreeAt g) g}
     let ℒ_star : Set (RootedHypergraph α β) :=
       insert (rootedDecompRootSide hdec.isTreeDecomposition hf) ℒ
     IsRootedLocation (GM04.cross τ (T.subtreeAt f) f) ℒ ∧
       IsRootedLocation P.G ℒ_star ∧
       rootedLocationCore (GM04.cross τ (T.subtreeAt f) f) ℒ =
         rootedLocationCore P.G ℒ_star) :=
  ⟨theorem_6_5_1 hdec hf, theorem_6_5_2 hrootless hdec hf, theorem_6_5_3 hrootless hdec hf⟩

end GraphMinor.GM18
end
