/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM06.Section3Dual
import LeanPool.GraphMinor.GM06.Section3InduceSingleton
import LeanPool.GraphMinor.GM06.RegionCurve
import LeanPool.GraphMinor.Surface.JordanDomain
import Mathlib.Analysis.Convex.PathConnected

/-!
# Graph Minors VI, Section 3: Separating Sets of Chains and Proof of Theorem (3.6)

This file proves the topological results of Graph Minors VI, Section 3 (pages 119–122):
- `exists_separatingSet_of_isXYChain`: every $(x, y)$-chain $A$ in a proper drawing $G$ on a closed
  disc space $S$ gives a compact connected separating set $F \subseteq S$ from $x$ to $y$ meeting
  $U(G)$ only at the vertex terms of $A$.
- `isCrossFree_of_isFeasible` and `chainRedundancy_nonneg_of_isFeasible`: necessity of conditions
  (i) and (ii) of (3.6), proved with zero unproved hypotheses using `disc_crossing` and
  `exists_region_curve`.
- `isFeasible_of_isCrossFree_of_chainRedundancy_nonneg` and
  `isFeasible_iff_of_exists_isDiscDualDrawing`: the full sufficiency induction of (3.6) on
  $|V(G)| + |R(G)|$ via the five cases of the paper (pages 121–122).
- `region_inter_segmentsOf_subsingleton`, `exists_dual_vertices_of_connected`, and
  `exists_isDiscDualDrawing_of_edges_empty`: boundary segment uniqueness, dual vertex placement,
  and the edgeless base case for disc dual drawings.
-/

public section

namespace GraphMinor.GM06

open Set Function Topology Graph GraphMinor.Surface GraphMinor.GM11

universe u

/-! ## 1. Separating Sets of $(x, y)$-Chains and Necessity in (3.6) -/

/-- Finite union of a non-empty list of connected sets where consecutive sets intersect is
connected. -/
private theorem isConnected_biUnion_fin {S : Type u} [TopologicalSpace S]
    (m : ℕ) (hm : 0 < m) (K : Fin m → Set S)
    (hconn : ∀ i : Fin m, IsConnected (K i))
    (hinter : ∀ i : Fin m, ∀ h : i.1 + 1 < m, (K i ∩ K ⟨i.1 + 1, h⟩).Nonempty) :
    IsConnected (⋃ i : Fin m, K i) := by
  induction m with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h_eq : (⋃ i : Fin 1, K i) = K ⟨0, zero_lt_one⟩ := by
        ext z
        simp only [mem_iUnion]
        constructor
        · rintro ⟨i, hi⟩
          have : i = ⟨0, zero_lt_one⟩ := Fin.ext (by omega)
          rwa [← this]
        · intro hz
          exact ⟨⟨0, zero_lt_one⟩, hz⟩
      rw [h_eq]
      exact hconn ⟨0, zero_lt_one⟩
    · let K' : Fin n → Set S := fun j => K ⟨j.1, Nat.lt_succ_of_lt j.2⟩
      have hconn' : ∀ j : Fin n, IsConnected (K' j) := fun j => hconn _
      have hinter' : ∀ j : Fin n, ∀ h : j.1 + 1 < n, (K' j ∩ K' ⟨j.1 + 1, h⟩).Nonempty := by
        intro j h
        exact hinter ⟨j.1, Nat.lt_succ_of_lt j.2⟩ (Nat.lt_succ_of_lt h)
      have ih_res := ih hn K' hconn' hinter'
      have hunion : (⋃ i : Fin (n + 1), K i) = (⋃ j : Fin n, K' j) ∪ K ⟨n, Nat.lt_succ_self n⟩ := by
        ext z
        simp only [mem_iUnion, mem_union, K']
        constructor
        · rintro ⟨i, hi⟩
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ i.2) with hlt | heq
          · exact Or.inl ⟨⟨i.1, hlt⟩, hi⟩
          · right
            have : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext heq
            rwa [← this]
        · rintro (⟨j, hj⟩ | hn_mem)
          · exact ⟨⟨j.1, Nat.lt_succ_of_lt j.2⟩, hj⟩
          · exact ⟨⟨n, Nat.lt_succ_self n⟩, hn_mem⟩
      rw [hunion]
      refine IsConnected.union ?_ ih_res (hconn ⟨n, Nat.lt_succ_self n⟩)
      let j_last : Fin n := ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩
      have h_step : j_last.1 + 1 < n + 1 := by
        dsimp [j_last]; omega
      have h_non := hinter ⟨j_last.1, Nat.lt_succ_of_lt j_last.2⟩ h_step
      rcases h_non with ⟨z, hz1, hz2⟩
      refine ⟨z, mem_iUnion.mpr ⟨j_last, hz1⟩, ?_⟩
      have h_idx : (⟨j_last.1 + 1, h_step⟩ : Fin (n + 1)) = ⟨n, Nat.lt_succ_self n⟩ := by
        ext; dsimp [j_last]; omega
      rwa [← h_idx]

private theorem not_mem_U_of_mem_region {S : Type u} [TopologicalSpace S]
    (G : Drawing S) {r : Set S} (hr : r ∈ G.R) {z : S} (hz : z ∈ r) : z ∉ G.U := by
  rcases hr with ⟨z₀, _, rfl⟩
  exact (connectedComponentIn_subset (univ \ G.U) z₀ hz).2

/-- Every $(x, y)$-chain $A$ in a proper drawing $G$ on a closed disc space $S$ yields a compact
connected set $F \subseteq S$ containing $x$ and $y$ such that
$F \cap U(G) \subseteq \{v \in V(G) \mid \text{Sum.inl } v \in A\}$. -/
theorem exists_separatingSet_of_isXYChain
    {S : Type u} [TopologicalSpace S] {G : Drawing S} {x y : S} {A : List (ChainTerm S)}
    (hDisc : IsClosedDiscSpace S) (hProper : G.IsProper)
    (hChain : IsXYChain G x y A) :
    ∃ F : Set S, IsCompact F ∧ IsConnected F ∧ x ∈ F ∧ y ∈ F ∧
      F ∩ G.U ⊆ {v ∈ G.V | Sum.inl v ∈ A} := by
  have hm : 0 < A.length := List.length_pos_of_ne_nil hChain.ne_nil
  -- For each index i : Fin A.length, define its left endpoint p(i) and right endpoint q(i)
  let leftPt : Fin A.length → S := fun i =>
    match A[i.1]'i.2 with
    | .inl v => v
    | .inr _ =>
      if hi0 : i.1 = 0 then x
      else
        match A[i.1 - 1]'(Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.2) with
        | .inl v => v
        | .inr _ => x
  let rightPt : Fin A.length → S := fun i =>
    match A[i.1]'i.2 with
    | .inl v => v
    | .inr _ =>
      if hi1 : i.1 + 1 = A.length then y
      else
        match A[i.1 + 1]'(Nat.lt_of_le_of_ne (Nat.succ_le_of_lt i.2) hi1) with
        | .inl v => v
        | .inr _ => y
  have h_chain_rel : ∀ (j : ℕ) (hj : j + 1 < A.length),
      ChainTerm.AreIncident G A[j] A[j + 1] :=
    fun j hj => List.isChain_iff_getElem.mp hChain.isChain j hj
  have h_left_closure : ∀ (i : Fin A.length) (r : Set S),
      A[i.1]'i.2 = .inr r → leftPt i ∈ closure r ∧
        (leftPt i ∈ G.U → leftPt i ∈ G.V ∧ Sum.inl (leftPt i) ∈ A) := by
    intro i r hir
    have hrR : r ∈ G.R := by
      have hv := hChain.valid (A[i.1]'i.2) (List.getElem_mem i.2)
      simpa [hir, ChainTerm.IsValid] using hv
    by_cases hi0 : i.1 = 0
    · have hhead : A.head hChain.ne_nil = A[i.1]'i.2 := by
        rw [List.head_eq_getElem_zero]
        congr 1; omega
      have hmatch := hChain.head_matches
      rw [hhead, hir] at hmatch
      change x ∈ r at hmatch
      have hleft : leftPt i = x := by
        dsimp [leftPt]
        rw [hir]
        simp [hi0]
      rw [hleft]
      refine ⟨subset_closure hmatch, fun hxU => ?_⟩
      exfalso
      exact not_mem_U_of_mem_region G hrR hmatch hxU
    · have hprev_lt : i.1 - 1 < A.length := Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.2
      have hstep : (i.1 - 1) + 1 < A.length := by omega
      have hinc := h_chain_rel (i.1 - 1) hstep
      have h_idx_eq : A[(i.1 - 1) + 1]'hstep = A[i.1]'i.2 := by congr 1; omega
      rw [h_idx_eq, hir] at hinc
      rcases h_prev : A[i.1 - 1]'hprev_lt with v | r'
      · rw [h_prev] at hinc
        rcases hinc with ⟨hvV, _, hv_cl⟩
        have hleft : leftPt i = v := by simp [leftPt, hir, hi0, h_prev]
        rw [hleft]
        refine ⟨hv_cl, fun _ => ⟨hvV, ?_⟩⟩
        rw [← h_prev]
        exact List.getElem_mem hprev_lt
      · rw [h_prev] at hinc
        exact False.elim hinc
  have h_right_closure : ∀ (i : Fin A.length) (r : Set S),
      A[i.1]'i.2 = .inr r → rightPt i ∈ closure r ∧
        (rightPt i ∈ G.U → rightPt i ∈ G.V ∧ Sum.inl (rightPt i) ∈ A) := by
    intro i r hir
    have hrR : r ∈ G.R := by
      have hv := hChain.valid (A[i.1]'i.2) (List.getElem_mem i.2)
      simpa [hir, ChainTerm.IsValid] using hv
    by_cases hi1 : i.1 + 1 = A.length
    · have hlast : A.getLast hChain.ne_nil = A[i.1]'i.2 := by
        rw [List.getLast_eq_getElem]
        congr 1; omega
      have hmatch := hChain.last_matches
      rw [hlast, hir] at hmatch
      change y ∈ r at hmatch
      have hright : rightPt i = y := by simp [rightPt, hir, hi1]
      rw [hright]
      refine ⟨subset_closure hmatch, fun hyU => ?_⟩
      exfalso
      exact not_mem_U_of_mem_region G hrR hmatch hyU
    · have hnext_lt : i.1 + 1 < A.length := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt i.2) hi1
      have hinc := h_chain_rel i.1 hnext_lt
      rw [hir] at hinc
      rcases h_next : A[i.1 + 1]'hnext_lt with v | r'
      · rw [h_next] at hinc
        rcases hinc with ⟨hvV, _, hv_cl⟩
        have hright : rightPt i = v := by simp [rightPt, hir, hi1, h_next]
        rw [hright]
        refine ⟨hv_cl, fun _ => ⟨hvV, ?_⟩⟩
        rw [← h_next]
        exact List.getElem_mem hnext_lt
      · rw [h_next] at hinc
        exact False.elim hinc
  -- Now construct K(i) for each i : Fin A.length
  have hK_exists : ∀ i : Fin A.length,
      ∃ K : Set S, IsCompact K ∧ IsConnected K ∧ leftPt i ∈ K ∧ rightPt i ∈ K ∧
        K ∩ G.U ⊆ {v ∈ G.V | Sum.inl v ∈ A} := by
    intro i
    rcases hir : A[i.1]'i.2 with v | r
    · refine ⟨{v}, isCompact_singleton, isConnected_singleton, ?_, ?_, ?_⟩
      · simp [leftPt, hir]
      · simp [rightPt, hir]
      · intro z hz
        have hzv : z = v := mem_singleton_iff.mp hz.1
        subst hzv
        have hvV : z ∈ G.V := by
          have hv := hChain.valid (A[i.1]'i.2) (List.getElem_mem i.2)
          simpa [hir, ChainTerm.IsValid] using hv
        refine ⟨hvV, ?_⟩
        have hmem : A[i.1]'i.2 ∈ A := List.getElem_mem i.2
        rwa [hir] at hmem
    · have hrR : r ∈ G.R := by
        have hv := hChain.valid (A[i.1]'i.2) (List.getElem_mem i.2)
        simpa [hir, ChainTerm.IsValid] using hv
      obtain ⟨hl_cl, hl_U⟩ := h_left_closure i r hir
      obtain ⟨hr_cl, hr_U⟩ := h_right_closure i r hir
      obtain ⟨γ, hγ0, hγ1, hγ_int⟩ :=
        exists_region_curve G hDisc hProper r hrR (leftPt i) hl_cl (rightPt i) hr_cl
      refine ⟨range γ, isCompact_range γ.continuous, isConnected_range γ.continuous,
        ⟨0, hγ0⟩, ⟨1, hγ1⟩, ?_⟩
      rintro z ⟨⟨t, rfl⟩, htU⟩
      by_cases ht0 : (t : ℝ) = 0
      · have hteq : t = 0 := Subtype.ext ht0
        rw [hteq, hγ0] at htU ⊢
        exact hl_U htU
      · by_cases ht1 : (t : ℝ) = 1
        · have hteq : t = 1 := Subtype.ext ht1
          rw [hteq, hγ1] at htU ⊢
          exact hr_U htU
        · have h_ioo : (t : ℝ) ∈ Ioo (0 : ℝ) 1 :=
            ⟨lt_of_le_of_ne t.2.1 (Ne.symm ht0), lt_of_le_of_ne t.2.2 ht1⟩
          have h_in_r : γ t ∈ r := hγ_int t h_ioo
          exfalso
          exact not_mem_U_of_mem_region G hrR h_in_r htU
  choose K hK_comp hK_conn hK_left hK_right hK_sub using hK_exists
  refine ⟨⋃ i : Fin A.length, K i, isCompact_iUnion hK_comp, ?_, ?_, ?_, ?_⟩
  · refine isConnected_biUnion_fin A.length hm K hK_conn ?_
    intro i hi
    have hinc := h_chain_rel i.1 hi
    rcases hir : A[i.1]'i.2 with v | r
    · rw [hir] at hinc
      rcases hir1 : A[i.1 + 1]'hi with v' | r'
      · rw [hir1] at hinc; exact False.elim hinc
      · refine ⟨v, ?_, ?_⟩
        · have hright : rightPt i = v := by simp [rightPt, hir]
          rw [← hright]; exact hK_right i
        · have hleft : leftPt ⟨i.1 + 1, hi⟩ = v := by
            simp [leftPt, hir1, hir]
          rw [← hleft]; exact hK_left ⟨i.1 + 1, hi⟩
    · rw [hir] at hinc
      rcases hir1 : A[i.1 + 1]'hi with v' | r'
      · refine ⟨v', ?_, ?_⟩
        · have hne_last : i.1 + 1 ≠ A.length := ne_of_lt hi
          have hright : rightPt i = v' := by simp [rightPt, hir, hne_last, hir1]
          rw [← hright]; exact hK_right i
        · have hleft : leftPt ⟨i.1 + 1, hi⟩ = v' := by simp [leftPt, hir1]
          rw [← hleft]; exact hK_left ⟨i.1 + 1, hi⟩
      · rw [hir1] at hinc; exact False.elim hinc
  · refine mem_iUnion.mpr ⟨⟨0, hm⟩, ?_⟩
    have hhead : A.head hChain.ne_nil = A[0]'hm := List.head_eq_getElem_zero _
    have hmatch := hChain.head_matches
    rw [hhead] at hmatch
    rcases hir0 : A[0]'hm with v | r
    · rw [hir0] at hmatch
      change v = x at hmatch
      have hleft : leftPt ⟨0, hm⟩ = x := by simp [leftPt, hir0, hmatch]
      rw [← hleft]; exact hK_left ⟨0, hm⟩
    · have hleft : leftPt ⟨0, hm⟩ = x := by simp [leftPt, hir0]
      rw [← hleft]; exact hK_left ⟨0, hm⟩
  · let i_last : Fin A.length := ⟨A.length - 1, Nat.sub_lt hm zero_lt_one⟩
    refine mem_iUnion.mpr ⟨i_last, ?_⟩
    have hlast : A.getLast hChain.ne_nil = A[i_last.1]'i_last.2 := by
      rw [List.getLast_eq_getElem]
    have hmatch := hChain.last_matches
    rw [hlast] at hmatch
    rcases hir_last : A[i_last.1]'i_last.2 with v | r
    · rw [hir_last] at hmatch
      change v = y at hmatch
      have hright : rightPt i_last = y := by simp [rightPt, hir_last, hmatch]
      rw [← hright]; exact hK_right i_last
    · have hi1 : i_last.1 + 1 = A.length := by dsimp [i_last]; omega
      have hright : rightPt i_last = y := by simp [rightPt, hir_last, hi1]
      rw [← hright]; exact hK_right i_last
  · rintro z ⟨hz_u, hzU⟩
    rcases mem_iUnion.mp hz_u with ⟨i, hzi⟩
    exact hK_sub i ⟨hzi, hzU⟩

/-- Necessity of (3.6)(i): If $\Delta$ is feasible in $G$ on a closed disc space $S$, then $\Delta$
is cross-free on $\operatorname{bd}(S)$. -/
theorem isCrossFree_of_isFeasible
    {S : Type u} [TopologicalSpace S] {G : Drawing S} {Δ : Set (Set S)}
    (hDisc : IsClosedDiscSpace S) (hFeas : IsFeasible G.toGraph Δ) :
    IsCrossFree (bd S) Δ := by
  rcases hFeas with ⟨H, _, _, hHG, _, H_comp, hInj, hComp, _⟩
  rintro ⟨δ₁, hδ₁, δ₂, hδ₂, hne, a, ha, c, hc, b, hb, d, hd, hcross⟩
  let C₁ := H_comp δ₁
  let C₂ := H_comp δ₂
  have hC_ne : C₁ ≠ C₂ := fun heq => hne (hInj hδ₁ hδ₂ heq)
  have hC₁ : IsGraphComponent C₁ H := (hComp δ₁ hδ₁).1
  have hC₂ : IsGraphComponent C₂ H := (hComp δ₂ hδ₂).1
  have haC₁ : a ∈ V(C₁) := (hComp δ₁ hδ₁).2 ha
  have hcC₁ : c ∈ V(C₁) := (hComp δ₁ hδ₁).2 hc
  have hbC₂ : b ∈ V(C₂) := (hComp δ₂ hδ₂).2 hb
  have hdC₂ : d ∈ V(C₂) := (hComp δ₂ hδ₂).2 hd
  obtain ⟨W₁⟩ := hC₁.2.1.2 a haC₁ c hcC₁
  obtain ⟨W₂⟩ := hC₂.2.1.2 b hbC₂ d hdC₂
  obtain ⟨K₁, hK₁_comp, hK₁_conn, haK₁, hcK₁, hK₁_sub, _, _⟩ :=
    exists_compact_connected_of_walk G (hC₁.1.trans hHG) W₁
  obtain ⟨K₂, hK₂_comp, hK₂_conn, hbK₂, hdK₂, hK₂_sub, _, _⟩ :=
    exists_compact_connected_of_walk G (hC₂.1.trans hHG) W₂
  have hmeet := discCrossing_of_isClosedDiscSpace hDisc
    hK₁_comp hK₂_comp hK₁_conn hK₂_conn haK₁ hcK₁ hbK₂ hdK₂ hcross
  rcases hmeet with ⟨z, hz1, hz2⟩
  have hV_disj : Disjoint V(C₁) V(C₂) :=
    hC₁.disjoint_vertexSet_of_ne hC₂ hC_ne
  have hE_disj : Disjoint E(C₁) E(C₂) :=
    hC₁.disjoint_edgeSet_of_ne hC₂ hC_ne
  have hz1_in : z ∈ V(C₁) ∪ ⋃ e ∈ E(C₁), e := hK₁_sub hz1
  have hz2_in : z ∈ V(C₂) ∪ ⋃ e ∈ E(C₂), e := hK₂_sub hz2
  rcases hz1_in with hzV1 | hzE1 <;> rcases hz2_in with hzV2 | hzE2
  · exact disjoint_left.mp hV_disj hzV1 hzV2
  · simp only [mem_iUnion, exists_prop] at hzE2
    rcases hzE2 with ⟨e₂, he₂C, hze₂⟩
    have he₂G : e₂ ∈ G.E := (hC₂.1.trans hHG).edgeSet_mono he₂C
    have hzV : z ∈ G.V := (hC₁.1.trans hHG).vertexSet_mono hzV1
    exact (he₂G.2.1 hze₂).2 hzV
  · simp only [mem_iUnion, exists_prop] at hzE1
    rcases hzE1 with ⟨e₁, he₁C, hze₁⟩
    have he₁G : e₁ ∈ G.E := (hC₁.1.trans hHG).edgeSet_mono he₁C
    have hzV : z ∈ G.V := (hC₂.1.trans hHG).vertexSet_mono hzV2
    exact (he₁G.2.1 hze₁).2 hzV
  · simp only [mem_iUnion, exists_prop] at hzE1 hzE2
    rcases hzE1 with ⟨e₁, he₁C, hze₁⟩
    rcases hzE2 with ⟨e₂, he₂C, hze₂⟩
    have he₁G : e₁ ∈ G.E := (hC₁.1.trans hHG).edgeSet_mono he₁C
    have he₂G : e₂ ∈ G.E := (hC₂.1.trans hHG).edgeSet_mono he₂C
    have he_ne : e₁ ≠ e₂ := by
      intro heq
      subst heq
      exact disjoint_left.mp hE_disj he₁C he₂C
    exact disjoint_left.mp (disjoint_edges_of_ne G he₁G he₂G he_ne) hze₁ hze₂

theorem ncard_inl_mem_le_chainLength {S : Type u} (A : List (ChainTerm S)) :
    {v : S | Sum.inl v ∈ A}.ncard ≤ chainLength A := by
  induction A with
  | nil => simp [chainLength]
  | cons hd tl ih =>
    rcases hd with v | r
    · have h_eq : {w : S | Sum.inl w ∈ (Sum.inl v : ChainTerm S) :: tl} =
          insert v {w : S | Sum.inl w ∈ tl} := by
        ext w; simp
      have h_len : chainLength ((Sum.inl v : ChainTerm S) :: tl) = chainLength tl + 1 := rfl
      rw [h_eq, h_len]
      exact (ncard_insert_le v _).trans (Nat.add_le_add_right ih 1)
    · have h_eq : {w : S | Sum.inl w ∈ (Sum.inr r : ChainTerm S) :: tl} =
          {w : S | Sum.inl w ∈ tl} := by
        ext w; simp
      have h_len : chainLength ((Sum.inr r : ChainTerm S) :: tl) = chainLength tl := rfl
      rw [h_eq, h_len]
      exact ih

theorem finite_inl_mem {S : Type u} (A : List (ChainTerm S)) :
    {v : S | Sum.inl v ∈ A}.Finite := by
  induction A with
  | nil => simp
  | cons hd tl ih =>
    rcases hd with v | r
    · have h_eq : {w : S | Sum.inl w ∈ (Sum.inl v : ChainTerm S) :: tl} =
          insert v {w : S | Sum.inl w ∈ tl} := by
        ext w; simp
      rw [h_eq]
      exact ih.insert v
    · have h_eq : {w : S | Sum.inl w ∈ (Sum.inr r : ChainTerm S) :: tl} =
          {w : S | Sum.inl w ∈ tl} := by
        ext w; simp
      rw [h_eq]
      exact ih

open Classical in
/-- Necessity of (3.6)(ii): If $\Delta$ is feasible in $G$ on a closed disc space $S$, then every
$(x, y)$-chain $A$ in $G$ has non-negative $\Delta$-redundancy. -/
theorem chainRedundancy_nonneg_of_isFeasible
    {S : Type u} [TopologicalSpace S] {G : Drawing S} {Δ : Set (Set S)} {x y : S}
    {A : List (ChainTerm S)}
    (hDisc : IsClosedDiscSpace S) (hProper : G.IsProper)
    (hUnion : divisionUnion Δ = G.V ∩ bd S)
    (hFeas : IsFeasible G.toGraph Δ)
    (hChain : IsXYChain G x y A) :
    0 ≤ chainRedundancy G Δ x y A := by
  unfold chainRedundancy
  suffices hle : divisionCount (bd S) Δ x y ≤ chainLength A by omega
  rcases hFeas with ⟨H, _, _, hHG, _, H_comp, hInj, hComp, _⟩
  obtain ⟨F, hF_comp, hF_conn, hxF, hyF, hF_sub⟩ :=
    exists_separatingSet_of_isXYChain hDisc hProper hChain
  let S_cnt : Set (Set S) :=
    {δ ∈ Δ | (δ ∩ {x, y}).Nonempty ∨ ∃ u ∈ δ, ∃ v ∈ δ, CrossesOn (bd S) u v x y}
  have h_hit : ∀ δ ∈ S_cnt, ∃ w : S, w ∈ V(H_comp δ) ∧ Sum.inl w ∈ A := by
    rintro δ ⟨hδΔ, hδ_cond⟩
    let C := H_comp δ
    have hC : IsGraphComponent C H := (hComp δ hδΔ).1
    have hδ_sub : δ ⊆ V(C) := (hComp δ hδΔ).2
    rcases hδ_cond with ⟨z, hzδ, hzxy⟩ | ⟨u, huδ, v, hvδ, hcross⟩
    · have hzC : z ∈ V(C) := hδ_sub hzδ
      have hzV : z ∈ G.V := by
        have : z ∈ divisionUnion Δ := mem_sUnion_of_mem hzδ hδΔ
        rw [hUnion] at this
        exact this.1
      refine ⟨z, hzC, ?_⟩
      rcases hzxy with rfl | rfl
      · have hmatch := hChain.head_matches
        rcases hhead : A.head hChain.ne_nil with w | r
        · rw [hhead] at hmatch
          change w = z at hmatch
          subst hmatch
          rw [← hhead]
          exact List.head_mem hChain.ne_nil
        · rw [hhead] at hmatch
          change z ∈ r at hmatch
          have hrR : r ∈ G.R := by
            have hv := hChain.valid (A.head hChain.ne_nil) (List.head_mem hChain.ne_nil)
            simpa [hhead, ChainTerm.IsValid] using hv
          exfalso
          exact not_mem_U_of_mem_region G hrR hmatch (G.V_subset_U hzV)
      · have hmatch := hChain.last_matches
        rcases hlast : A.getLast hChain.ne_nil with w | r
        · rw [hlast] at hmatch
          change w = z at hmatch
          subst hmatch
          rw [← hlast]
          exact List.getLast_mem hChain.ne_nil
        · rw [hlast] at hmatch
          change z ∈ r at hmatch
          have hrR : r ∈ G.R := by
            have hv := hChain.valid (A.getLast hChain.ne_nil) (List.getLast_mem hChain.ne_nil)
            simpa [hlast, ChainTerm.IsValid] using hv
          exfalso
          exact not_mem_U_of_mem_region G hrR hmatch (G.V_subset_U hzV)
    · have huC : u ∈ V(C) := hδ_sub huδ
      have hvC : v ∈ V(C) := hδ_sub hvδ
      obtain ⟨W⟩ := hC.2.1.2 u huC v hvC
      obtain ⟨KW, hKW_comp, hKW_conn, huKW, hvKW, _, hKW_U, hKW_V⟩ :=
        exists_compact_connected_of_walk G (hC.1.trans hHG) W
      have hmeet := discCrossing_of_isClosedDiscSpace hDisc
        hKW_comp hF_comp hKW_conn hF_conn huKW hvKW hxF hyF hcross
      rcases hmeet with ⟨w, hw_walk, hw_F⟩
      have hw_U : w ∈ G.U := hKW_U hw_walk
      have hw_in : w ∈ {v ∈ G.V | Sum.inl v ∈ A} := hF_sub ⟨hw_F, hw_U⟩
      have hwC : w ∈ V(C) := hKW_V ⟨hw_walk, hw_in.1⟩
      exact ⟨w, hwC, hw_in.2⟩
  choose f hf_comp hf_mem using h_hit
  have h_le1 : S_cnt.ncard ≤ {w : S | Sum.inl w ∈ A}.ncard := by
    have h_inj' : InjOn (fun δ : Set S => if h : δ ∈ S_cnt then f δ h else x) S_cnt := by
      intro δ₁ hδ₁ δ₂ hδ₂ heq
      simp only [hδ₁, hδ₂, ↓reduceDIte] at heq
      have hwC₁ : f δ₁ hδ₁ ∈ V(H_comp δ₁) := hf_comp δ₁ hδ₁
      have hwC₂ : f δ₂ hδ₂ ∈ V(H_comp δ₂) := hf_comp δ₂ hδ₂
      rw [heq] at hwC₁
      have hC₁ : IsGraphComponent (H_comp δ₁) H := (hComp δ₁ hδ₁.1).1
      have hC₂ : IsGraphComponent (H_comp δ₂) H := (hComp δ₂ hδ₂.1).1
      have hC_eq : H_comp δ₁ = H_comp δ₂ := hC₁.eq_of_mem_mem hC₂ hwC₁ hwC₂
      exact hInj hδ₁.1 hδ₂.1 hC_eq
    have h_maps' : MapsTo (fun δ : Set S => if h : δ ∈ S_cnt then f δ h else x)
        S_cnt {w : S | Sum.inl w ∈ A} := by
      intro δ hδ
      simp only [hδ, ↓reduceDIte]
      exact hf_mem δ hδ
    exact ncard_le_ncard_of_injOn _ h_maps' h_inj' (finite_inl_mem A)
  exact h_le1.trans (ncard_inl_mem_le_chainLength A)

/-! ## 2. Sufficiency and Proof of Theorem (3.6) -/

/-- If `a` and `b` lie in the same segment `s ∈ segmentsOf C (divisionUnion Δ)`, then
`divisionCount C Δ a b = 0`. -/
private lemma divisionCount_eq_zero_of_same_segment {S : Type u} [TopologicalSpace S]
    {C : Set S} {Δ : Set (Set S)} {s : Set S} (hs : s ∈ segmentsOf C (divisionUnion Δ))
    {a b : S} (ha : a ∈ s) (hb : b ∈ s) :
    divisionCount C Δ a b = 0 := by
  rcases hs.1 with ⟨z₀, _, rfl⟩
  have hs_sub : connectedComponentIn (C \ divisionUnion Δ) z₀ ⊆ C \ divisionUnion Δ :=
    connectedComponentIn_subset _ _
  have ha_not : a ∉ divisionUnion Δ := (hs_sub ha).2
  have hb_not : b ∉ divisionUnion Δ := (hs_sub hb).2
  unfold divisionCount
  have h_emp : {δ ∈ Δ | (δ ∩ {a, b}).Nonempty ∨ ∃ u ∈ δ, ∃ v ∈ δ, CrossesOn C u v a b} = ∅ := by
    refine eq_empty_of_forall_notMem fun δ ⟨hδ, hcond⟩ => ?_
    rcases hcond with ⟨w, hwδ, rfl | rfl⟩ | ⟨u, huδ, v, hvδ, hcr⟩
    · exact ha_not ⟨δ, hδ, hwδ⟩
    · exact hb_not ⟨δ, hδ, hwδ⟩
    · have hs_uv : connectedComponentIn (C \ divisionUnion Δ) z₀ ⊆ C \ {u, v} := by
        refine hs_sub.trans (sdiff_subset_sdiff subset_rfl ?_)
        rintro w (rfl | rfl)
        · exact ⟨δ, hδ, huδ⟩
        · exact ⟨δ, hδ, hvδ⟩
      have hb_cc : b ∈ connectedComponentIn (C \ {u, v}) a :=
        isPreconnected_connectedComponentIn.subset_connectedComponentIn ha hs_uv hb
      exact hcr.2.2.2.2.2.2.2.2.2.2 (connectedComponentIn_eq hb_cc)
  rw [h_emp, ncard_empty]

/-- If `x, x' ∈ C` either are equal or lie in the same segment of `C \ divisionUnion Δ`, and
similarly for `y, y' ∈ C`, then `divisionCount C Δ x' y' = divisionCount C Δ x y`. -/
private lemma divisionCount_eq_of_same_segment {S : Type u} [TopologicalSpace S]
    {C : Set S} (hC : IsOArc C) {Δ : Set (Set S)} (hΔ : IsDivision Δ)
    (hV_sub : divisionUnion Δ ⊆ C) {x x' y y' : S}
    (hx : x ∈ C) (hx' : x' ∈ C) (hy : y ∈ C) (hy' : y' ∈ C)
    (hxx' : x' = x ∨ ∃ s ∈ segmentsOf C (divisionUnion Δ), x ∈ s ∧ x' ∈ s)
    (hyy' : y' = y ∨ ∃ s ∈ segmentsOf C (divisionUnion Δ), y ∈ s ∧ y' ∈ s) :
    divisionCount C Δ x' y' = divisionCount C Δ x y := by
  have h1 : divisionCount C Δ x' y' = divisionCount C Δ x y' := by
    rcases hxx' with rfl | ⟨s, hs, hxs, hx's⟩
    · rfl
    · have hs_sub : s ⊆ C \ divisionUnion Δ := by
        rcases hs.1 with ⟨z₀, _, rfl⟩
        exact connectedComponentIn_subset _ _
      have hx_not : x ∉ divisionUnion Δ := (hs_sub hxs).2
      have hx'_not : x' ∉ divisionUnion Δ := (hs_sub hx's).2
      have h0_xx' := divisionCount_eq_zero_of_same_segment hs hxs hx's
      have h0_x'x := divisionCount_eq_zero_of_same_segment hs hx's hxs
      exact le_antisymm
        (divisionCount_le_of_left_eq_zero hC hΔ hV_sub hx' hx hy' hx_not h0_x'x)
        (divisionCount_le_of_left_eq_zero hC hΔ hV_sub hx hx' hy' hx'_not h0_xx')
  have h2 : divisionCount C Δ x y' = divisionCount C Δ x y := by
    rcases hyy' with rfl | ⟨s, hs, hys, hy's⟩
    · rfl
    · have hs_sub : s ⊆ C \ divisionUnion Δ := by
        rcases hs.1 with ⟨z₀, _, rfl⟩
        exact connectedComponentIn_subset _ _
      have hy_not : y ∉ divisionUnion Δ := (hs_sub hys).2
      have hy'_not : y' ∉ divisionUnion Δ := (hs_sub hy's).2
      have h0_yy' := divisionCount_eq_zero_of_same_segment hs hys hy's
      have h0_y'y := divisionCount_eq_zero_of_same_segment hs hy's hys
      exact le_antisymm
        (divisionCount_le_of_right_eq_zero hC hΔ hV_sub hx hy hy' hy_not h0_yy')
        (divisionCount_le_of_right_eq_zero hC hΔ hV_sub hx hy' hy hy'_not h0_y'y)
  exact h1.trans h2

/-- Transfer of non-negative chain redundancy between any two dual point sets `U` and `U'` for
`(bd S, divisionUnion Δ)`. -/
theorem chainRedundancy_nonneg_of_isDualPointSet {S : Type u} [TopologicalSpace S]
    (hS : IsClosedDiscSpace S) {G : Drawing S} (hProper : G.IsProper)
    {Δ : Set (Set S)} (hΔ : IsDivision Δ) (hΔ_eq : divisionUnion Δ = G.V ∩ bd S)
    {U U' : Set S} (hU : IsDualPointSet (bd S) (divisionUnion Δ) U)
    (hU' : IsDualPointSet (bd S) (divisionUnion Δ) U')
    (hRed : ∀ x ∈ U ∪ divisionUnion Δ, ∀ y ∈ U ∪ divisionUnion Δ,
      ∀ A : List (ChainTerm S), IsXYChain G x y A → 0 ≤ chainRedundancy G Δ x y A) :
    ∀ x' ∈ U' ∪ divisionUnion Δ, ∀ y' ∈ U' ∪ divisionUnion Δ,
      ∀ A : List (ChainTerm S), IsXYChain G x' y' A → 0 ≤ chainRedundancy G Δ x' y' A := by
  have hV_sub : divisionUnion Δ ⊆ bd S := hΔ_eq ▸ inter_subset_right
  have hV_fin : (divisionUnion Δ).Finite := hΔ_eq ▸ G.finite_V.inter_of_left _
  have hU_sub : U ⊆ bd S \ divisionUnion Δ := isDualPointSet_subset_diff hU
  have hU'_sub : U' ⊆ bd S \ divisionUnion Δ := isDualPointSet_subset_diff hU'
  have h_corr : ∀ z' ∈ U' ∪ divisionUnion Δ,
      ∃ z ∈ U ∪ divisionUnion Δ, z ∈ bd S ∧ z' ∈ bd S ∧
        (z' = z ∨ ∃ s ∈ segmentsOf (bd S) (divisionUnion Δ), z ∈ s ∧ z' ∈ s) ∧
        (∀ t : ChainTerm S, t.IsValid G → (t.MatchesEnd z' ↔ t.MatchesEnd z)) := by
    rintro z' (hz'U' | hz'V)
    · have hz'_diff : z' ∈ bd S \ divisionUnion Δ := hU'_sub hz'U'
      have hV_ne : (divisionUnion Δ).Nonempty := by
        by_contra hemp
        rw [not_nonempty_iff_eq_empty] at hemp
        have hU'_emp : U' = ∅ := hU'.1 hemp
        rw [hU'_emp] at hz'U'
        exact hz'U'
      let s := connectedComponentIn (bd S \ divisionUnion Δ) z'
      have hs_mem : s ∈ segmentsOf (bd S) (divisionUnion Δ) :=
        connectedComponentIn_mem_segmentsOf hS.isOArc_bd hV_fin hV_sub hV_ne hz'_diff
      have hz'_s : z' ∈ s := mem_connectedComponentIn hz'_diff
      obtain ⟨z, hz_eq⟩ := ncard_eq_one.mp ((hU.2 hV_ne).2 s hs_mem)
      have hz_mem : z ∈ U ∩ s := by rw [hz_eq]; exact mem_singleton z
      have hs_compl : s ⊆ univ \ G.U := by
        refine (connectedComponentIn_subset _ _).trans fun w hw => ⟨mem_univ w, fun hwU => ?_⟩
        apply hw.2
        rw [hΔ_eq]
        exact ⟨hProper ⟨hw.1, hwU⟩, hw.1⟩
      refine ⟨z, Or.inl hz_mem.1, (hU_sub hz_mem.1).1, hz'_diff.1,
        Or.inr ⟨s, hs_mem, hz_mem.2, hz'_s⟩, ?_⟩
      rintro (v | r) hval
      · change (v = z' ↔ v = z)
        have hvV : v ∈ G.V := hval
        have hz'_not_V : z' ∉ G.V := fun h => (hs_compl hz'_s).2 (G.V_subset_U h)
        have hz_not_V : z ∉ G.V := fun h => (hs_compl hz_mem.2).2 (G.V_subset_U h)
        exact ⟨fun h => (hz'_not_V (h ▸ hvV)).elim, fun h => (hz_not_V (h ▸ hvV)).elim⟩
      · change (z' ∈ r ↔ z ∈ r)
        have hrR : r ∈ G.R := hval
        rcases (mem_R_iff G).mp hrR with ⟨w₀, _, rfl⟩
        have hz_cc : z ∈ connectedComponentIn (univ \ G.U) z' :=
          isPreconnected_connectedComponentIn.subset_connectedComponentIn hz'_s hs_compl hz_mem.2
        constructor
        · intro hz'_r
          rw [connectedComponentIn_eq hz'_r]
          exact hz_cc
        · intro hz_r
          rw [connectedComponentIn_eq hz_r, ← connectedComponentIn_eq hz_cc]
          exact mem_connectedComponentIn (hs_compl hz'_s)
    · exact ⟨z', Or.inr hz'V, hV_sub hz'V, hV_sub hz'V, Or.inl rfl, fun _ _ => Iff.rfl⟩
  intro x' hx' y' hy' A hChain'
  obtain ⟨x, hx, hx_bd, hx'_bd, hxx', hm_x⟩ := h_corr x' hx'
  obtain ⟨y, hy, hy_bd, hy'_bd, hyy', hm_y⟩ := h_corr y' hy'
  have hChain : IsXYChain G x y A :=
    ⟨hChain'.ne_nil, hChain'.valid, hChain'.isChain,
      (hm_x _ (hChain'.valid _ (List.head_mem hChain'.ne_nil))).mp hChain'.head_matches,
      (hm_y _ (hChain'.valid _ (List.getLast_mem hChain'.ne_nil))).mp hChain'.last_matches,
      hChain'.peripheral_iff⟩
  have hdiv_eq := divisionCount_eq_of_same_segment hS.isOArc_bd hΔ hV_sub
    hx_bd hx'_bd hy_bd hy'_bd hxx' hyy'
  have hred := hRed x hx y hy A hChain
  unfold chainRedundancy at hred ⊢
  rw [hdiv_eq]
  exact hred

/-- For any one-way dual drawing `IsDiscDualDrawing G G_dual`, `G_dual.V.ncard = G.R.ncard`. -/
theorem IsDiscDualDrawing.ncard_dual_V_eq_ncard_R {S : Type u} [TopologicalSpace S]
    (hS : IsClosedDiscSpace S) {G G_dual : Drawing S} (hDual : IsDiscDualDrawing G G_dual) :
    G_dual.V.ncard = G.R.ncard := by
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hS
  let f : S → Set S := fun w => connectedComponentIn (univ \ G.U) w
  have hf_img : f '' G_dual.V = G.R := by
    ext r
    simp only [mem_image, f]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨r₀, hr₀, hwr₀⟩ := hDual.2.2.2.1 w hw
      have heq : r₀ = connectedComponentIn (univ \ G.U) w := by
        obtain ⟨z₀, _, rfl⟩ := (mem_R_iff G).mp hr₀
        exact connectedComponentIn_eq hwr₀
      exact heq ▸ hr₀
    · intro hr
      obtain ⟨w, ⟨hwr, hwV⟩, _⟩ := hDual.2.2.1 r hr
      refine ⟨w, hwV, ?_⟩
      obtain ⟨z₀, _, rfl⟩ := (mem_R_iff G).mp hr
      exact (connectedComponentIn_eq hwr).symm
  have hf_inj : InjOn f G_dual.V := by
    intro w₁ hw₁ w₂ hw₂ heq
    dsimp only [f] at heq
    obtain ⟨r₁, hr₁, hw₁_r⟩ := hDual.2.2.2.1 w₁ hw₁
    have hr₁_eq : r₁ = connectedComponentIn (univ \ G.U) w₁ := by
      obtain ⟨z₀, _, rfl⟩ := (mem_R_iff G).mp hr₁
      exact connectedComponentIn_eq hw₁_r
    have hw₂_r₁ : w₂ ∈ r₁ := by
      rw [hr₁_eq, heq]
      obtain ⟨r₂, hr₂, hw₂_r⟩ := hDual.2.2.2.1 w₂ hw₂
      exact mem_connectedComponentIn ⟨mem_univ w₂, region_subset hr₂ hw₂_r⟩
    exact (hDual.2.2.1 r₁ hr₁).unique ⟨hw₁_r, hw₁⟩ ⟨hw₂_r₁, hw₂⟩
  rw [← hf_img, hf_inj.ncard_image]

/-- For a connected proper drawing `G` on a closed disc space `S` and a dual drawing
`IsDiscDualDrawing G G_dual`, `G_dual.V.ncard + G_dual.R.ncard = G.V.ncard + G.R.ncard`. -/
theorem IsDiscDualDrawing.ncard_V_add_ncard_R_eq {S : Type u} [TopologicalSpace S]
    (hS : IsClosedDiscSpace S) {G G_dual : Drawing S} (hConn : IsGraphConnected G.toGraph)
    (hDual : IsDiscDualDrawing G G_dual) :
    G_dual.V.ncard + G_dual.R.ncard = G.V.ncard + G.R.ncard := by
  have h1 := hDual.ncard_dual_V_eq_ncard_R hS
  have h2 := (hDual.symm_of_connected hS hConn).ncard_dual_V_eq_ncard_R hS
  omega

/-- If `G.V` is nonempty and `G.toGraph` is not connected, then `2 ≤ (graphComponents
G.toGraph).ncard`. -/
private lemma two_le_ncard_graphComponents_of_not_connected {S : Type u} [TopologicalSpace S]
    (G : Drawing S) (hV_ne : G.V.Nonempty) (hNotConn : ¬ IsGraphConnected G.toGraph) :
    2 ≤ (graphComponents G.toGraph).ncard := by
  obtain ⟨v₀, hv₀⟩ := hV_ne
  have h_ex : ∃ v₁ ∈ G.V, compOf G.toGraph v₀ ≠ compOf G.toGraph v₁ := by
    by_contra h_all
    push Not at h_all
    apply hNotConn
    refine ⟨⟨v₀, hv₀⟩, fun u hu v hv => ?_⟩
    have hu_in : u ∈ reachSet G.toGraph v₀ := by
      have : u ∈ V(compOf G.toGraph u) := self_mem_reachSet hu
      rwa [← h_all u hu] at this
    have hv_in : v ∈ reachSet G.toGraph v₀ := by
      have : v ∈ V(compOf G.toGraph v) := self_mem_reachSet hv
      rwa [← h_all v hv] at this
    obtain ⟨_, ⟨Wu⟩⟩ := hu_in
    obtain ⟨_, ⟨Wv⟩⟩ := hv_in
    exact ⟨Wu.reverse.append Wv⟩
  obtain ⟨v₁, hv₁, hne⟩ := h_ex
  have h_pair_sub : ({compOf G.toGraph v₀, compOf G.toGraph v₁} : Set (Graph S (Set S))) ⊆
      graphComponents G.toGraph := by
    rintro C (rfl | rfl)
    · exact isGraphComponent_compOf hv₀
    · exact isGraphComponent_compOf hv₁
  have h_card_pair : ({compOf G.toGraph v₀, compOf G.toGraph v₁} : Set (Graph S (Set S))).ncard = 2
    :=
    ncard_pair hne
  rw [← h_card_pair]
  exact ncard_le_ncard h_pair_sub (finite_graphComponents G)

/-- Sufficiency half of **Graph Minors VI, (3.6)** (page 122), proved by strong induction on
`G.V.ncard + G.R.ncard` following the paper's five cases. -/
theorem isFeasible_of_isCrossFree_of_chainRedundancy_nonneg {S : Type u} [TopologicalSpace S]
    (hS : IsClosedDiscSpace S)
    (hDualExists : ∀ (G : Drawing S), G.IsProper → IsGraphConnected G.toGraph →
      ∃ G_dual : Drawing S, IsDiscDualDrawing G G_dual)
    {G : Drawing S} (hProper : G.IsProper)
    {Δ : Set (Set S)} (hΔ : IsDivision Δ) (hΔ_eq : divisionUnion Δ = G.V ∩ bd S)
    {U : Set S} (hU : IsDualPointSet (bd S) (divisionUnion Δ) U)
    (hCF : IsCrossFree (bd S) Δ)
    (hRed : ∀ x ∈ U ∪ divisionUnion Δ, ∀ y ∈ U ∪ divisionUnion Δ,
      ∀ A : List (ChainTerm S), IsXYChain G x y A → 0 ≤ chainRedundancy G Δ x y A) :
    IsFeasible G.toGraph Δ := by
  classical
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  induction hn : G.V.ncard + G.R.ncard using Nat.strong_induction_on generalizing G Δ U with
  | ind n ih =>
    -- Case 1: Δ = ∅
    by_cases hΔ_emp : Δ = ∅
    · subst hΔ_emp
      exact isFeasible_empty G.toGraph
    have hΔ_ne : Δ.Nonempty := nonempty_iff_ne_empty.mpr hΔ_emp
    obtain ⟨δ₀, hδ₀⟩ := hΔ_ne
    obtain ⟨v₀, hv₀⟩ := hΔ.2.1 δ₀ hδ₀
    have hv₀_bd : v₀ ∈ G.V ∩ bd S := hΔ_eq ▸ ⟨δ₀, hδ₀, hv₀⟩
    have hVG_ne : (G.V ∩ bd S).Nonempty := ⟨v₀, hv₀_bd⟩
    have hU_G : IsDualPointSet (bd S) (G.V ∩ bd S) U := hΔ_eq ▸ hU
    have hRed_G : ∀ a ∈ U ∪ (G.V ∩ bd S), ∀ b ∈ U ∪ (G.V ∩ bd S),
        ∀ A : List (ChainTerm S), IsXYChain G a b A → 0 ≤ chainRedundancy G Δ a b A := by
      simpa [hΔ_eq] using hRed
    -- Case 2: |δ| = 1 for some δ ∈ Δ
    by_cases h_sing : ∃ v : S, {v} ∈ Δ
    · obtain ⟨v, hv⟩ := h_sing
      obtain ⟨hProper', _, hlt, hΔ', hΔ'_eq, ⟨U', _, hU'_dual, hRed'⟩, hFeas_imp⟩ :=
        exists_reduction_of_singleton_mem hS hProper hΔ hΔ_eq hv hU_G hRed_G
      let G' := induceDrawing G (G.V \ {v})
      let Δ' := Δ \ {{v}}
      have hCF' : IsCrossFree (bd S) Δ' :=
        fun ⟨δ₁, hδ₁, δ₂, hδ₂, rest⟩ => hCF ⟨δ₁, hδ₁.1, δ₂, hδ₂.1, rest⟩
      exact hFeas_imp (ih (G'.V.ncard + G'.R.ncard) (hn ▸ hlt) hProper' hΔ' hΔ'_eq
        (hΔ'_eq.symm ▸ hU'_dual) hCF' (by simpa [hΔ'_eq] using hRed') rfl)
    -- Case 3: Some component of G has no vertex in bd(S)
    by_cases h_int : ∃ C₀ ∈ graphComponents G.toGraph, V(C₀) ∩ bd S = ∅
    · obtain ⟨C₀, hC₀, hC₀_disj⟩ := h_int
      obtain ⟨G', hProper', _, hlt, hV'_bd_eq, hRed', hFeas_imp⟩ :=
        exists_reduction_of_internal_component hS hProper hVG_ne hC₀ hC₀_disj hU_G hRed_G
      have hΔ_eq' : divisionUnion Δ = G'.V ∩ bd S := hΔ_eq.trans hV'_bd_eq.symm
      exact hFeas_imp (ih (G'.V.ncard + G'.R.ncard) (hn ▸ hlt) hProper' hΔ hΔ_eq'
        hU hCF (by simpa [hΔ_eq'] using hRed') rfl)
    -- Case 4: G is not connected
    by_cases hConn : IsGraphConnected G.toGraph
    · -- Case 5: G is connected and |δ| ≥ 2 for all δ ∈ Δ
      obtain ⟨G_dual, hDual⟩ := hDualExists G hProper hConn
      let U_dual := G_dual.V ∩ bd S
      let Δ_dual := dualDivision (bd S) U_dual Δ
      have hC : IsOArc (bd S) := hS.isOArc_bd
      have hV_fin : (divisionUnion Δ).Finite := hΔ_eq ▸ G.finite_V.inter_of_left _
      have hV_sub : divisionUnion Δ ⊆ bd S := hΔ_eq ▸ inter_subset_right
      have hU_dual : IsDualPointSet (bd S) (divisionUnion Δ) U_dual := hΔ_eq ▸ hDual.2.2.2.2.1
      have hRed_dual := chainRedundancy_nonneg_of_isDualPointSet hS hProper hΔ hΔ_eq hU hU_dual hRed
      have hΔ_dual_div : IsDivision Δ_dual := isDivision_dualDivision hC hV_fin hV_sub hU_dual
      have hΔ_dual_eq : divisionUnion Δ_dual = G_dual.V ∩ bd S :=
        divisionUnion_dualDivision (bd S) U_dual Δ
      have hCF_dual : IsCrossFree (bd S) Δ_dual :=
        theorem_2_1_proof (bd S) U_dual Δ hC hΔ hV_sub hU_dual
      have hW_ne : (divisionUnion Δ ∪ U_dual).Nonempty := ⟨v₀, Or.inl (hΔ_eq.symm ▸ hv₀_bd)⟩
      obtain ⟨γ, hγ_mem, hγ_card⟩ := theorem_2_3_proof (bd S) U_dual Δ hC hΔ hV_fin hV_sub hU_dual
        hW_ne
      obtain ⟨u, rfl⟩ := ncard_eq_one.mp hγ_card
      have hu_dual : {u} ∈ Δ_dual := hγ_mem.resolve_left fun huΔ => h_sing ⟨u, huΔ⟩
      have hSymm := hDual.symm_of_connected hS hConn
      have hU_symm : IsDualPointSet (bd S) (G_dual.V ∩ bd S) (G.V ∩ bd S) := hSymm.2.2.2.2.1
      have hRed_G_dual : ∀ a ∈ (G.V ∩ bd S) ∪ (G_dual.V ∩ bd S),
          ∀ b ∈ (G.V ∩ bd S) ∪ (G_dual.V ∩ bd S),
          ∀ A_dual : List (ChainTerm S), IsXYChain G_dual a b A_dual →
            0 ≤ chainRedundancy G_dual Δ_dual a b A_dual := by
        intro a ha b hb A_dual hChain_dual
        have ha' : a ∈ U_dual ∪ divisionUnion Δ := by
          rw [hΔ_eq]; exact ha.symm
        have hb' : b ∈ U_dual ∪ divisionUnion Δ := by
          rw [hΔ_eq]; exact hb.symm
        obtain ⟨A, hChainA, hred_eq⟩ :=
          theorem_3_5_proof G G_dual Δ a b A_dual hS hConn hΔ hΔ_eq hCF hDual ha' hb' hChain_dual
        rw [hred_eq]
        exact hRed_dual a ha' b hb' A hChainA
      obtain ⟨hProper_d', _, hlt_d, hΔ_d', hΔ_d'_eq, ⟨U_d', _, hU_d'_dual, hRed_d'⟩, hFeas_d_imp⟩ :=
        exists_reduction_of_singleton_mem hS hDual.2.1 hΔ_dual_div hΔ_dual_eq hu_dual hU_symm
          hRed_G_dual
      let G_dual' := induceDrawing G_dual (G_dual.V \ {u})
      let Δ_dual' := Δ_dual \ {{u}}
      have hcard_eq := hDual.ncard_V_add_ncard_R_eq hS hConn
      have hlt_n : G_dual'.V.ncard + G_dual'.R.ncard < n := by
        dsimp only [G_dual']
        omega
      have hCF_d' : IsCrossFree (bd S) Δ_dual' :=
        fun ⟨δ₁, hδ₁, δ₂, hδ₂, rest⟩ => hCF_dual ⟨δ₁, hδ₁.1, δ₂, hδ₂.1, rest⟩
      have hFeas_d' := ih (G_dual'.V.ncard + G_dual'.R.ncard) hlt_n hProper_d' hΔ_d' hΔ_d'_eq
        (hΔ_d'_eq.symm ▸ hU_d'_dual) hCF_d' (by simpa [hΔ_d'_eq] using hRed_d') rfl
      have hFeas_dual : IsFeasible G_dual.toGraph Δ_dual := hFeas_d_imp hFeas_d'
      exact (theorem_3_2_proof G G_dual Δ hS hConn hΔ hΔ_eq hCF hDual).mpr hFeas_dual
    · -- G is not connected
      have h2_le : 2 ≤ (graphComponents G.toGraph).ncard :=
        two_le_ncard_graphComponents_of_not_connected G ⟨v₀, hv₀_bd.1⟩ hConn
      have h_comps_fin : (graphComponents G.toGraph).Finite := finite_graphComponents G
      let k := (graphComponents G.toGraph).ncard
      have hk : 2 ≤ k := h2_le
      have h_card_coe : Nat.card (graphComponents G.toGraph) = k :=
        Nat.card_coe_set_eq (graphComponents G.toGraph)
      have : Finite (graphComponents G.toGraph) := h_comps_fin.to_subtype
      let enum : Fin k ≃ graphComponents G.toGraph :=
        (Finite.equivFinOfCardEq h_card_coe).symm
      let G_comp : Fin k → Graph S (Set S) := fun i => (enum i).1
      let Δ_part : Fin k → Set (Set S) := fun i => {δ ∈ Δ | δ ⊆ V(G_comp i)}
      have hinj_G : InjOn G_comp univ := by
        intro i _ j _ heq
        exact enum.injective (Subtype.ext heq)
      have hG_comps : graphComponents G.toGraph = range G_comp := by
        ext C
        simp only [mem_range, G_comp]
        exact ⟨fun hC => ⟨enum.symm ⟨C, hC⟩, congrArg Subtype.val (enum.apply_symm_apply ⟨C, hC⟩)⟩,
          by rintro ⟨i, rfl⟩; exact (enum i).2⟩
      have hΔ_cov : ∀ δ ∈ Δ, ∃ i : Fin k, δ ⊆ V(G_comp i) := by
        intro δ hδ
        obtain ⟨a, haδ⟩ := hΔ.2.1 δ hδ
        have ha_bd : a ∈ G.V ∩ bd S := hΔ_eq ▸ ⟨δ, hδ, haδ⟩
        let C_a := compOf G.toGraph a
        have hCa_mem : C_a ∈ graphComponents G.toGraph := isGraphComponent_compOf ha_bd.1
        let i := enum.symm ⟨C_a, hCa_mem⟩
        have hGi_eq : G_comp i = C_a := congrArg Subtype.val (enum.apply_symm_apply ⟨C_a, hCa_mem⟩)
        refine ⟨i, fun b hbδ => ?_⟩
        by_contra hb_not
        have hb_bd : b ∈ G.V ∩ bd S := hΔ_eq ▸ ⟨δ, hδ, hbδ⟩
        let C_b := compOf G.toGraph b
        have hCb_mem : C_b ∈ graphComponents G.toGraph := isGraphComponent_compOf hb_bd.1
        have hCa_ne_Cb : C_a ≠ C_b := by
          intro heq
          apply hb_not
          rw [hGi_eq, heq]
          exact self_mem_reachSet hb_bd.1
        exact not_component_split_of_chainRedundancy_nonneg hS hProper hΔ hΔ_eq.subset hU_G hRed_G
          hδ hCa_mem hCb_mem hCa_ne_Cb
          ⟨a, haδ, self_mem_reachSet ha_bd.1⟩ ⟨b, hbδ, self_mem_reachSet hb_bd.1⟩
      refine (theorem_3_3_iv G Δ k G_comp Δ_part hk hΔ hΔ_eq hinj_G hG_comps
        (fun _ => rfl) hΔ_cov).mpr fun i => ?_
      have hCi_mem : G_comp i ∈ graphComponents G.toGraph := (enum i).2
      have hCi_bd : (V(G_comp i) ∩ bd S).Nonempty := by
        by_contra hemp
        rw [not_nonempty_iff_eq_empty] at hemp
        exact h_int ⟨G_comp i, hCi_mem, hemp⟩
      let G_i := induceDrawing G V(G_comp i)
      have hGi_toGraph : G_i.toGraph = G_comp i :=
        induceDrawing_toGraph_of_component G hCi_mem
      have hProper_i : G_i.IsProper :=
        induceDrawing_isProper G hProper hCi_mem.1.vertexSet_mono
      have hSub_i : G_i.IsSubdrawing G :=
        induceDrawing_isSubdrawing G hCi_mem.1.vertexSet_mono
      have hGi_V : G_i.V = V(G_comp i) :=
        induceDrawing_V G hCi_mem.1.vertexSet_mono
      have hlt_i : G_i.V.ncard + G_i.R.ncard < n := by
        let j : Fin k := ⟨(i.1 + 1) % k, Nat.mod_lt _ (by omega)⟩
        have hij : i ≠ j := by
          intro heq
          have hval : i.1 = (i.1 + 1) % k := congrArg Fin.val heq
          have hi_lt : i.1 < k := i.2
          by_cases h_last : i.1 + 1 = k
          · rw [h_last, Nat.mod_self] at hval; omega
          · rw [Nat.mod_eq_of_lt (by omega)] at hval; omega
        have hCj_mem : G_comp j ∈ graphComponents G.toGraph := (enum j).2
        obtain ⟨w_j, hw_j⟩ := hCj_mem.2.1.1
        have hw_j_G : w_j ∈ G.V := hCj_mem.1.vertexSet_mono hw_j
        have hw_j_not : w_j ∉ G_i.V := by
          rw [hGi_V]
          intro hw_i
          have heq := hCi_mem.eq_of_mem_mem hCj_mem hw_i hw_j
          exact hij (hinj_G trivial trivial heq)
        have hV_lt : G_i.V.ncard < G.V.ncard :=
          ncard_lt_ncard ⟨hSub_i.1, fun h => hw_j_not (h hw_j_G)⟩ G.finite_V
        have hR_le : G_i.R.ncard ≤ G.R.ncard :=
          disc_region_ncard_le_of_isSubdrawing hS hProper hSub_i
        omega
      have hΔi_sub : Δ_part i ⊆ Δ := fun _ h => h.1
      have hΔi_div : IsDivision (Δ_part i) :=
        ⟨hΔ.1.subset hΔi_sub, fun δ hδ => hΔ.2.1 δ hδ.1, hΔ.2.2.subset hΔi_sub⟩
      have hΔi_eq : divisionUnion (Δ_part i) = G_i.V ∩ bd S := by
        rw [hGi_V]
        ext x
        simp only [divisionUnion, Δ_part, mem_sUnion, mem_ofPred_eq, mem_inter_iff]
        constructor
        · rintro ⟨δ, ⟨hδ, hδ_sub⟩, hxδ⟩
          have hx_bd : x ∈ G.V ∩ bd S := hΔ_eq ▸ ⟨δ, hδ, hxδ⟩
          exact ⟨hδ_sub hxδ, hx_bd.2⟩
        · rintro ⟨hx_Ci, hx_bd⟩
          have hx_union : x ∈ divisionUnion Δ := hΔ_eq.symm ▸ ⟨hCi_mem.1.vertexSet_mono hx_Ci,
            hx_bd⟩
          obtain ⟨δ, hδ, hxδ⟩ := hx_union
          obtain ⟨j, hj⟩ := hΔ_cov δ hδ
          have heq_ij : G_comp i = G_comp j :=
            hCi_mem.eq_of_mem_mem (enum j).2 hx_Ci (hj hxδ)
          exact ⟨δ, ⟨hδ, heq_ij ▸ hj⟩, hxδ⟩
      have hCF_i : IsCrossFree (bd S) (Δ_part i) :=
        fun ⟨δ₁, hδ₁, δ₂, hδ₂, rest⟩ => hCF ⟨δ₁, hδ₁.1, δ₂, hδ₂.1, rest⟩
      obtain ⟨U_i, _, hUi_dual, hRed_i⟩ :=
        exists_dualPointSet_and_chainRedundancy_of_component hS hProper hCi_mem hCi_bd
          hΔ hΔi_sub hU_G hRed_G
      rw [← hGi_toGraph]
      exact ih (G_i.V.ncard + G_i.R.ncard) hlt_i hProper_i hΔi_div hΔi_eq
        (hΔi_eq.symm ▸ hUi_dual) hCF_i (by simpa [hΔi_eq] using hRed_i) rfl

/-! ## 3. Boundary Segments, Dual Vertices, and Base Case of Dual Drawing Existence -/

/-- Every segment `s ∈ segmentsOf C V` is non-empty. -/
theorem segment_nonempty {S : Type u} [TopologicalSpace S] {C V s : Set S}
    (hs : s ∈ segmentsOf C V) : s.Nonempty := by
  obtain ⟨⟨x, hx, rfl⟩, _⟩ := hs
  exact ⟨x, mem_connectedComponentIn hx⟩

/-- Distinct segments `s₁ ≠ s₂` of `segmentsOf C V` are disjoint. -/
theorem disjoint_of_mem_segmentsOf_ne {S : Type u} [TopologicalSpace S] {C V s₁ s₂ : Set S}
    (hs₁ : s₁ ∈ segmentsOf C V) (hs₂ : s₂ ∈ segmentsOf C V) (hne : s₁ ≠ s₂) :
    Disjoint s₁ s₂ := by
  obtain ⟨⟨x₁, _, rfl⟩, _⟩ := hs₁
  obtain ⟨⟨x₂, _, rfl⟩, _⟩ := hs₂
  refine disjoint_left.mpr fun z hz₁ hz₂ => hne ?_
  exact (connectedComponentIn_eq hz₁).trans (connectedComponentIn_eq hz₂).symm

/-- On `Circle`, points `u₁ ∈ s₁` and `u₂ ∈ s₂` in distinct segments `s₁ ≠ s₂` of
`segmentsOf univ V` are separated by a pair of vertices `v₁, v₂ ∈ V` with
`CrossesOn univ v₁ v₂ u₁ u₂`. -/
theorem exists_crossesOn_univ_of_mem_segmentsOf_ne {V s₁ s₂ : Set Circle}
    (hV_fin : V.Finite) (hs₁ : s₁ ∈ segmentsOf (univ : Set Circle) V)
    (hs₂ : s₂ ∈ segmentsOf (univ : Set Circle) V) (hne : s₁ ≠ s₂)
    {u₁ u₂ : Circle} (hu₁ : u₁ ∈ s₁) (hu₂ : u₂ ∈ s₂) :
    ∃ v₁ ∈ V, ∃ v₂ ∈ V, CrossesOn (univ : Set Circle) v₁ v₂ u₁ u₂ := by
  have hV_ne : V.Nonempty := nonempty_of_mem_segmentsOf isOArc_univ_circle hs₁
  have hu₁_compl : u₁ ∈ Vᶜ := by
    obtain ⟨⟨x₁, _, rfl⟩, _⟩ := hs₁
    exact (connectedComponentIn_subset _ _ hu₁).2
  have hu₂_compl : u₂ ∈ Vᶜ := by
    obtain ⟨⟨x₂, _, rfl⟩, _⟩ := hs₂
    exact (connectedComponentIn_subset _ _ hu₂).2
  have hu₂_not_s₁ : u₂ ∉ s₁ :=
    disjoint_left.mp (disjoint_of_mem_segmentsOf_ne hs₂ hs₁ hne.symm) hu₂
  obtain ⟨v₁, hv₁, rfl⟩ := (mem_segmentsOf_univ_iff hV_fin hV_ne).mp hs₁
  have hu₂_ne_v₁ : u₂ ≠ v₁ := fun h => hu₂_compl (h ▸ hv₁)
  simp only [nextSegment, mem_ofPred_eq, not_and, not_forall, not_lt] at hu₂_not_s₁
  obtain ⟨v₂, hv₂, hle⟩ := hu₂_not_s₁ hu₂_ne_v₁
  have hv₁_ne_v₂ : v₁ ≠ v₂ := Ne.symm hv₂.2
  have hu₁_ne_u₂ : u₁ ≠ u₂ := fun h =>
    disjoint_left.mp (disjoint_of_mem_segmentsOf_ne hs₁ hs₂ hne) hu₁ (h ▸ hu₂)
  have hv₁_ne_u₁ : v₁ ≠ u₁ := Ne.symm hu₁.1
  have hv₁_ne_u₂ : v₁ ≠ u₂ := Ne.symm hu₂_ne_v₁
  have hv₂_ne_u₁ : v₂ ≠ u₁ := fun h => hu₁_compl (h ▸ hv₂.1)
  have hv₂_ne_u₂ : v₂ ≠ u₂ := fun h => hu₂_compl (h ▸ hv₂.1)
  have hlt₁ : v₁.angleDiff u₁ < v₁.angleDiff v₂ := hu₁.2 v₂ hv₂
  refine ⟨v₁, hv₁, v₂, hv₂.1, crossesOn_univ_iff_angleDiff.mpr
    ⟨hv₁_ne_v₂, hu₁_ne_u₂, hv₁_ne_u₁, hv₁_ne_u₂, hv₂_ne_u₁, hv₂_ne_u₂, ?_⟩⟩
  exact ⟨fun _ => not_lt.mpr hle, fun _ => hlt₁⟩

/-- On any `O`-arc `C`, points `u₁ ∈ s₁` and `u₂ ∈ s₂` in distinct segments `s₁ ≠ s₂` of
`segmentsOf C V` are separated by a pair of vertices `v₁, v₂ ∈ V` with `CrossesOn C v₁ v₂ u₁ u₂`. -/
theorem exists_crossesOn_of_mem_segmentsOf_ne {S : Type u} [TopologicalSpace S]
    {C V s₁ s₂ : Set S} (hC : IsOArc C) (hV_fin : V.Finite) (hV_sub : V ⊆ C)
    (hs₁ : s₁ ∈ segmentsOf C V) (hs₂ : s₂ ∈ segmentsOf C V) (hne : s₁ ≠ s₂)
    {u₁ u₂ : S} (hu₁ : u₁ ∈ s₁) (hu₂ : u₂ ∈ s₂) :
    ∃ v₁ ∈ V, ∃ v₂ ∈ V, CrossesOn C v₁ v₂ u₁ u₂ := by
  obtain ⟨φ⟩ := hC
  have hinj := injective_oArcMap φ
  let V₀ := oArcMap φ ⁻¹' V
  have hV_eq : oArcMap φ '' V₀ = V :=
    image_preimage_eq_of_subset (hV_sub.trans (range_oArcMap φ).symm.subset)
  have hV₀_fin : V₀.Finite := by
    refine Finite.of_finite_image ?_ hinj.injOn
    rwa [hV_eq]
  rw [← hV_eq, segmentsOf_oArcMap φ] at hs₁ hs₂
  obtain ⟨s₁₀, hs₁₀, rfl⟩ := hs₁
  obtain ⟨s₂₀, hs₂₀, rfl⟩ := hs₂
  have hne₀ : s₁₀ ≠ s₂₀ := fun h => hne (congrArg _ h)
  obtain ⟨u₁₀, hu₁₀, rfl⟩ := hu₁
  obtain ⟨u₂₀, hu₂₀, rfl⟩ := hu₂
  obtain ⟨v₁₀, hv₁₀, v₂₀, hv₂₀, hcr₀⟩ :=
    exists_crossesOn_univ_of_mem_segmentsOf_ne hV₀_fin hs₁₀ hs₂₀ hne₀ hu₁₀ hu₂₀
  refine ⟨oArcMap φ v₁₀, ?_, oArcMap φ v₂₀, ?_, (crossesOn_oArcMap_iff φ).mpr hcr₀⟩
  · rw [← hV_eq]; exact mem_image_of_mem _ hv₁₀
  · rw [← hV_eq]; exact mem_image_of_mem _ hv₂₀

/-- In a connected proper drawing `G` on a closed disc `S`, every region `r ∈ G.R` intersects
at most one boundary segment `s ∈ segmentsOf (bd S) (G.V ∩ bd S)`. -/
theorem region_inter_segmentsOf_subsingleton {S : Type u} [TopologicalSpace S]
    (hS : IsClosedDiscSpace S) {G : Drawing S} (hProper : G.IsProper)
    (hConn : IsGraphConnected G.toGraph) {r s₁ s₂ : Set S} (hr : r ∈ G.R)
    (hs₁ : s₁ ∈ segmentsOf (bd S) (G.V ∩ bd S))
    (hs₂ : s₂ ∈ segmentsOf (bd S) (G.V ∩ bd S))
    (h₁ : (r ∩ s₁).Nonempty) (h₂ : (r ∩ s₂).Nonempty) : s₁ = s₂ := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  by_contra hne
  obtain ⟨u₁, hu₁r, hu₁s⟩ := h₁
  obtain ⟨u₂, hu₂r, hu₂s⟩ := h₂
  obtain ⟨v₁, hv₁, v₂, hv₂, hcr⟩ :=
    exists_crossesOn_of_mem_segmentsOf_ne hS.isOArc_bd
      (G.finite_V.subset inter_subset_left) inter_subset_right hs₁ hs₂ hne hu₁s hu₂s
  obtain ⟨W⟩ := hConn.2 v₁ hv₁.1 v₂ hv₂.1
  obtain ⟨K_G, hKG_comp, hKG_conn, hv₁_KG, hv₂_KG, _, hKG_U, _⟩ :=
    exists_compact_connected_of_walk G le_rfl W
  obtain ⟨γ, hγ0, hγ1, hγ_int⟩ :=
    exists_region_curve G hS hProper r hr u₁ (subset_closure hu₁r) u₂ (subset_closure hu₂r)
  have hγ_sub_r : range γ ⊆ r := by
    rintro z ⟨t, rfl⟩
    by_cases ht0 : (t : ℝ) = 0
    · have hteq : t = 0 := Subtype.ext ht0
      rwa [hteq, hγ0]
    · by_cases ht1 : (t : ℝ) = 1
      · have hteq : t = 1 := Subtype.ext ht1
        rwa [hteq, hγ1]
      · exact hγ_int t ⟨lt_of_le_of_ne t.2.1 (Ne.symm ht0), lt_of_le_of_ne t.2.2 ht1⟩
  obtain ⟨z, hzG, hzγ⟩ := discCrossing_of_isClosedDiscSpace hS
    hKG_comp (isCompact_range γ.continuous) hKG_conn (isConnected_range γ.continuous)
    hv₁_KG hv₂_KG ⟨0, hγ0⟩ ⟨1, hγ1⟩ hcr
  exact not_mem_U_of_mem_region G hr (hγ_sub_r hzγ) (hKG_U hzG)

/-- If `G` is a connected proper drawing on a closed disc `S` with `G.E = ∅`, then `G` has a
disc dual drawing `G_dual` satisfying `IsDiscDualDrawing G G_dual`. -/
theorem exists_isDiscDualDrawing_of_edges_empty {S : Type u} [TopologicalSpace S]
    (hS : IsClosedDiscSpace S) {G : Drawing S} (hProper : G.IsProper)
    (hConn : IsGraphConnected G.toGraph) (hE : G.E = ∅) :
    ∃ G_dual : Drawing S, IsDiscDualDrawing G G_dual := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hS
  obtain ⟨φ_disc⟩ := hS
  have : ConnectedSpace ClosedUnitDisc :=
    Subtype.connectedSpace ((convex_closedBall (0 : EuclideanPlane) 1).isConnected ⟨0, by simp⟩)
  have : PreconnectedSpace S := (φ_disc.surjective.connectedSpace
    φ_disc.continuous).toPreconnectedSpace
  have hS : IsClosedDiscSpace S := ⟨φ_disc⟩
  obtain ⟨v₀, hv₀⟩ := hConn.1
  have hv₀_V : v₀ ∈ G.V := hv₀
  have hV_eq : G.V = {v₀} := by
    ext v
    simp only [mem_singleton_iff]
    constructor
    · intro hv
      obtain ⟨W⟩ := hConn.2 v hv v₀ hv₀
      cases W with
      | nil => rfl
      | cons hlink _ =>
        have he : _ ∈ G.E := hlink.edge_mem
        rw [hE] at he
        exact False.elim he
    · rintro rfl
      exact hv₀_V
  have hU_eq : G.U = {v₀} := by
    rw [G.U_eq, hE, hV_eq]
    simp
  have hcompl_conn : IsPreconnected (univ \ G.U) := by
    rw [hU_eq]
    exact disc_isPreconnected_sdiff_finite hS isOpen_univ isPreconnected_univ (finite_singleton v₀)
  have hw₀_exists : ∃ w₀ : S, w₀ ∈ univ \ G.U ∧
      IsDualPointSet (bd S) (G.V ∩ bd S) ({w₀} ∩ bd S) := by
    by_cases hv₀_bd : v₀ ∈ bd S
    · have hV_bd : G.V ∩ bd S = {v₀} := by
        rw [hV_eq, inter_eq_left.mpr (singleton_subset_iff.mpr hv₀_bd)]
      obtain ⟨φ⟩ := hS.isOArc_bd
      have hinj := injective_oArcMap φ
      let z₀ := φ.symm ⟨v₀, hv₀_bd⟩
      have hz₀_map : oArcMap φ '' {z₀} = {v₀} := by
        rw [image_singleton]
        simp [oArcMap, z₀]
      have hnext_eq : nextSegment ({z₀} : Set Circle) z₀ = ({z₀} : Set Circle)ᶜ := by
        ext z
        simp [nextSegment, compl_eq_univ_sdiff]
      have hseg_univ : segmentsOf (univ : Set Circle) {z₀} = {({z₀} : Set Circle)ᶜ} := by
        ext seg
        rw [mem_segmentsOf_univ_iff (finite_singleton z₀) (singleton_nonempty z₀)]
        simp [hnext_eq]
      have hseg_bd : segmentsOf (bd S) (G.V ∩ bd S) = {bd S \ {v₀}} := by
        rw [hV_bd, ← hz₀_map, segmentsOf_oArcMap φ, hseg_univ, image_singleton,
          ← diff_image_oArcMap φ, hz₀_map]
      have hmem_seg : bd S \ {v₀} ∈ segmentsOf (bd S) (G.V ∩ bd S) := by
        rw [hseg_bd]; exact mem_singleton _
      obtain ⟨w₀, hw₀_bd, hw₀_ne⟩ := segment_nonempty hmem_seg
      have hw₀_compl : w₀ ∈ univ \ G.U := by
        rw [hU_eq]; exact ⟨trivial, hw₀_ne⟩
      have hw₀_inter : ({w₀} : Set S) ∩ bd S = {w₀} :=
        inter_eq_left.mpr (singleton_subset_iff.mpr hw₀_bd)
      refine ⟨w₀, hw₀_compl, ?_⟩
      refine ⟨?_, ?_⟩
      · intro hemp
        rw [hV_bd] at hemp
        exact absurd hemp (singleton_ne_empty v₀)
      · intro _
        have hw₀_sub : ({w₀} : Set S) ⊆ bd S \ {v₀} :=
          singleton_subset_iff.mpr ⟨hw₀_bd, hw₀_ne⟩
        rw [hw₀_inter, hseg_bd, hV_bd]
        refine ⟨hw₀_sub, fun seg hseg => ?_⟩
        rw [mem_singleton_iff.mp hseg, inter_eq_left.mpr hw₀_sub]
        exact ncard_singleton w₀
    · have hV_bd : G.V ∩ bd S = ∅ := by
        rw [hV_eq, singleton_inter_eq_empty]
        exact hv₀_bd
      obtain ⟨D, D', hD, _, hv₀_D', _, hD_sub, hD_bd⟩ :=
        disc_exists_closedDisc_nbhd hS (isOpen_univ.sdiff (isClosed_bd_of_isClosedDiscSpace hS))
          ⟨mem_univ v₀, hv₀_bd⟩ hv₀_bd
      obtain ⟨ψ⟩ := IsClosedDisc.isOArc_discBd hD
      let w₀ : S := (ψ 1).1
      have hw₀_discBd : w₀ ∈ discBd D := (ψ 1).2
      have hw₀_diff : w₀ ∈ D \ D' := hD_bd.symm ▸ hw₀_discBd
      have hw₀_ne_v₀ : w₀ ≠ v₀ := fun h => hw₀_diff.2 (h ▸ hv₀_D')
      have hw₀_not_bd : w₀ ∉ bd S := (hD_sub hw₀_diff.1).2
      have hw₀_compl : w₀ ∈ univ \ G.U := by
        rw [hU_eq]; exact ⟨trivial, mem_singleton_iff.not.mpr hw₀_ne_v₀⟩
      have hw₀_inter : ({w₀} : Set S) ∩ bd S = ∅ :=
        singleton_inter_eq_empty.mpr hw₀_not_bd
      refine ⟨w₀, hw₀_compl, ?_⟩
      rw [hV_bd, hw₀_inter]
      exact ⟨fun _ => rfl, fun h => False.elim (not_nonempty_empty h)⟩
  obtain ⟨w₀, hw₀_compl, hDualPt⟩ := hw₀_exists
  have hR_eq : G.R = {univ \ G.U} := by
    ext r
    simp only [Drawing.R, componentsIn, mem_singleton_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact Subset.antisymm (connectedComponentIn_subset _ _)
        (hcompl_conn.subset_connectedComponentIn hz subset_rfl)
    · rintro rfl
      exact ⟨w₀, hw₀_compl, Subset.antisymm (connectedComponentIn_subset _ _)
        (hcompl_conn.subset_connectedComponentIn hw₀_compl subset_rfl)⟩
  let G_dual : Drawing S := {
    U := {w₀}
    V := {w₀}
    V_subset_U := Subset.rfl
    isClosed_U := isClosed_singleton
    finite_V := finite_singleton w₀
    finite_edges := by
      refine finite_empty.subset ?_
      rintro C ⟨⟨x, hx⟩, hsub, -⟩
      exact False.elim ((hsub hx).2 (hsub hx).1)
    edge_cond := by
      rintro C ⟨⟨x, hx⟩, hsub, -⟩
      exact False.elim ((hsub hx).2 (hsub hx).1)
  }
  have hGd_V : G_dual.V = {w₀} := rfl
  have hGd_U : G_dual.U = {w₀} := rfl
  have hGd_E : G_dual.E = ∅ := by
    ext C
    simp only [mem_empty_iff_false, iff_false]
    rintro ⟨⟨x, hx⟩, hsub, -⟩
    exact (hsub hx).2 (hsub hx).1
  refine ⟨G_dual, hProper, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨_, hxU⟩
    rwa [hGd_U] at hxU
  · intro r hr
    rw [hR_eq, mem_singleton_iff] at hr
    subst hr
    refine ⟨w₀, ⟨hw₀_compl, rfl⟩, fun w hw => mem_singleton_iff.mp hw.2⟩
  · intro w hw
    rw [hGd_V, mem_singleton_iff] at hw
    subst hw
    exact ⟨univ \ G.U, by rw [hR_eq]; exact mem_singleton _, hw₀_compl⟩
  · rwa [hGd_V]
  · intro v₁ hv₁ v₂ hv₂ _
    rw [hV_eq, mem_singleton_iff] at hv₁ hv₂
    exact hv₁.trans hv₂.symm
  · have : IsEmpty G.E := hE ▸ isEmpty_coe_sort.mpr rfl
    have : IsEmpty G_dual.E := hGd_E ▸ isEmpty_coe_sort.mpr rfl
    exact ⟨Equiv.equivOfIsEmpty G.E G_dual.E, fun e => isEmptyElim e⟩

/-- Every non-empty open subset `O` of a closed disc space `S` contains a point outside `bd S`. -/
theorem open_sdiff_bd_nonempty {S : Type u} [TopologicalSpace S] (hS : IsClosedDiscSpace S)
    {O : Set S} (hO : IsOpen O) (hne : O.Nonempty) : (O \ bd S).Nonempty := by
  obtain ⟨z, hz⟩ := hne
  by_cases hz_bd : z ∈ bd S
  · obtain ⟨φ⟩ := hS
    have hbd_img := image_bd_homeomorph φ
    rw [bd_closedUnitDisc] at hbd_img
    let c : ClosedUnitDisc := φ.symm z
    have hc_in : c ∈ φ ⁻¹' O := by
      change φ c ∈ O
      rw [φ.apply_symm_apply]
      exact hz
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hO.preimage φ.continuous) c hc_in
    let δ : ℝ := min (ε / 2) (1 / 2)
    have hδ_pos : 0 < δ := lt_min (half_pos hε) (by norm_num)
    have hδ_lt_one : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have hδ_lt_ε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
    have hc_norm : ‖(c : EuclideanPlane)‖ ≤ 1 := mem_closedBall_zero_iff.mp c.2
    let t : ℝ := 1 - δ
    have ht_nonneg : 0 ≤ t := by linarith
    have ht_lt_one : t < 1 := by dsimp [t]; linarith
    have hy_mem : t • (c : EuclideanPlane) ∈ ClosedUnitDisc := by
      change t • (c : EuclideanPlane) ∈ Metric.closedBall 0 1
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg ht_nonneg]
      nlinarith
    let y : ClosedUnitDisc := ⟨t • (c : EuclideanPlane), hy_mem⟩
    have hy_in_O : φ y ∈ O := by
      apply hball
      rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]
      have hdiff : y.1 - c.1 = (-δ) • c.1 := by
        dsimp [y, t]
        rw [sub_smul, one_smul, sub_sub_cancel_left, neg_smul]
      rw [hdiff, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hδ_pos]
      nlinarith
    have hy_not_bd : φ y ∉ bd S := by
      rw [← hbd_img]
      rintro ⟨c', hc', hφc'⟩
      have heq : c' = y := φ.injective hφc'
      subst heq
      have h1 : ‖y.1‖ = 1 := by simpa [UnitCircle] using hc'
      have hlt : ‖y.1‖ < 1 := by
        dsimp [y]
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_nonneg]
        nlinarith
      linarith
    exact ⟨φ y, hy_in_O, hy_not_bd⟩
  · exact ⟨z, hz, hz_bd⟩

/-- For any connected proper drawing `G` on a closed disc `S`, there exists a finite set `W` of
dual vertices containing a unique vertex in each region `r ∈ G.R` such that `W ∩ bd S` is a dual
point set for `(bd S, G.V ∩ bd S)`. -/
theorem exists_dual_vertices_of_connected {S : Type u} [TopologicalSpace S]
    (hS : IsClosedDiscSpace S) {G : Drawing S} (hProper : G.IsProper)
    (hConn : IsGraphConnected G.toGraph) :
    ∃ W : Set S, W.Finite ∧
      (∀ r ∈ G.R, ∃! w, w ∈ r ∧ w ∈ W) ∧
      (∀ w ∈ W, ∃ r ∈ G.R, w ∈ r) ∧
      IsDualPointSet (bd S) (G.V ∩ bd S) (W ∩ bd S) := by
  classical
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hS
  have hseg_sub_compl : ∀ s ∈ segmentsOf (bd S) (G.V ∩ bd S), s ⊆ univ \ G.U := by
    intro s hs z hz
    obtain ⟨⟨x, _, rfl⟩, _⟩ := hs
    have hz_diff : z ∈ bd S \ (G.V ∩ bd S) := connectedComponentIn_subset _ _ hz
    exact ⟨trivial, fun hzU => hz_diff.2 ⟨hProper ⟨hz_diff.1, hzU⟩, hz_diff.1⟩⟩
  have hseg_sub_region : ∀ r ∈ G.R, ∀ s ∈ segmentsOf (bd S) (G.V ∩ bd S),
      (r ∩ s).Nonempty → s ⊆ r := by
    rintro r hr s hs ⟨u, hur, hus⟩ z hz
    have hs' := hs
    obtain ⟨⟨x, _, rfl⟩, _⟩ := hs'
    exact subset_region hr isPreconnected_connectedComponentIn
      (disjoint_left.mpr fun q hq => (hseg_sub_compl _ hs hq).2) hus hur hz
  have hw_exists : ∀ r : G.R, ∃ w : S, w ∈ r.1 ∧
      ((∃ s ∈ segmentsOf (bd S) (G.V ∩ bd S), (r.1 ∩ s).Nonempty) →
        ∃ s ∈ segmentsOf (bd S) (G.V ∩ bd S), w ∈ s) ∧
      (¬ (∃ s ∈ segmentsOf (bd S) (G.V ∩ bd S), (r.1 ∩ s).Nonempty) → w ∉ bd S) := by
    intro r
    by_cases h_seg : ∃ s ∈ segmentsOf (bd S) (G.V ∩ bd S), (r.1 ∩ s).Nonempty
    · have h_seg' := h_seg
      obtain ⟨s, hs, hrs⟩ := h_seg'
      obtain ⟨w, hws⟩ := segment_nonempty hs
      exact ⟨w, hseg_sub_region r.1 r.2 s hs hrs hws, fun _ => ⟨s, hs, hws⟩,
        fun hnot => False.elim (hnot h_seg)⟩
    · obtain ⟨w, hwr, hw_not_bd⟩ :=
        open_sdiff_bd_nonempty hS (region_isOpen r.2) (region_nonempty r.2)
      exact ⟨w, hwr, fun h => False.elim (h_seg h), fun _ => hw_not_bd⟩
  choose w_of hw_in hw_seg hw_not_bd using hw_exists
  let W : Set S := range w_of
  have hR_fin : G.R.Finite := disc_finite_R hS G hProper
  have : Finite G.R := hR_fin.to_subtype
  refine ⟨W, finite_range w_of, ?_, ?_, ?_⟩
  · intro r hr
    let r_sub : G.R := ⟨r, hr⟩
    refine ⟨w_of r_sub, ⟨hw_in r_sub, mem_range_self r_sub⟩, ?_⟩
    rintro w ⟨hwr, ⟨r', rfl⟩⟩
    have heq : r' = r_sub := Subtype.ext (region_eq_of_mem r'.2 hr (hw_in r') hwr)
    rw [heq]
  · rintro _ ⟨r, rfl⟩
    exact ⟨r.1, r.2, hw_in r⟩
  · refine ⟨?_, ?_⟩
    · intro hV_emp
      ext x
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      rintro ⟨r, rfl⟩ hx_bd
      have h_no_seg : ¬ ∃ s ∈ segmentsOf (bd S) (G.V ∩ bd S), (r.1 ∩ s).Nonempty := by
        rintro ⟨s, hs, _⟩
        have hne := nonempty_of_mem_segmentsOf hS.isOArc_bd hs
        rw [hV_emp] at hne
        exact not_nonempty_empty hne
      exact hw_not_bd r h_no_seg hx_bd
    · intro _
      refine ⟨?_, fun seg hseg => ?_⟩
      · rintro x ⟨⟨r, rfl⟩, hx_bd⟩
        exact ⟨hx_bd, fun hxV => region_subset r.2 (hw_in r) (G.V_subset_U hxV.1)⟩
      · obtain ⟨u, hus⟩ := segment_nonempty hseg
        obtain ⟨r, hr, hur⟩ := exists_region_of_notMem (hseg_sub_compl seg hseg hus).2
        let r_sub : G.R := ⟨r, hr⟩
        have h_non : (r ∩ seg).Nonempty := ⟨u, hur, hus⟩
        obtain ⟨s', hs', hws'⟩ := hw_seg r_sub ⟨seg, hseg, h_non⟩
        have hs'_eq : s' = seg :=
          region_inter_segmentsOf_subsingleton hS hProper hConn hr hs' hseg
            ⟨w_of r_sub, hw_in r_sub, hws'⟩ h_non
        rw [hs'_eq] at hws'
        have hw_bd : w_of r_sub ∈ bd S := by
          obtain ⟨⟨x, _, rfl⟩, _⟩ := hseg
          exact (connectedComponentIn_subset _ _ hws').1
        have hw_mem_inter : w_of r_sub ∈ (W ∩ bd S) ∩ seg :=
          ⟨⟨mem_range_self r_sub, hw_bd⟩, hws'⟩
        rw [ncard_eq_one]
        refine ⟨w_of r_sub, Subset.antisymm ?_ (singleton_subset_iff.mpr hw_mem_inter)⟩
        rintro x ⟨⟨⟨r', rfl⟩, _⟩, hx_seg⟩
        rw [mem_singleton_iff]
        have hx_in_r : w_of r' ∈ r := hseg_sub_region r hr seg hseg h_non hx_seg
        have hr'_eq : r' = r_sub := Subtype.ext (region_eq_of_mem r'.2 hr (hw_in r') hx_in_r)
        rw [hr'_eq]

/-- Complete equivalence of **Graph Minors VI, (3.6)** (pages 121–122), combining necessity
(`isCrossFree_of_isFeasible` and `chainRedundancy_nonneg_of_isFeasible`) and the sufficiency
induction (`isFeasible_of_isCrossFree_of_chainRedundancy_nonneg`). -/
theorem isFeasible_iff_of_exists_isDiscDualDrawing {S : Type u} [TopologicalSpace S]
    (hS : IsClosedDiscSpace S)
    (hDualExists : ∀ (G : Drawing S), G.IsProper → IsGraphConnected G.toGraph →
      ∃ G_dual : Drawing S, IsDiscDualDrawing G G_dual)
    (G : Drawing S) (Δ : Set (Set S)) {U : Set S}
    (hProper : G.IsProper) (hΔ : IsDivision Δ) (hΔ_eq : divisionUnion Δ = G.V ∩ bd S)
    (hU : IsDualPointSet (bd S) (divisionUnion Δ) U) :
    IsFeasible G.toGraph Δ ↔
      IsCrossFree (bd S) Δ ∧
      ∀ x ∈ U ∪ divisionUnion Δ, ∀ y ∈ U ∪ divisionUnion Δ,
        ∀ A : List (ChainTerm S), IsXYChain G x y A → 0 ≤ chainRedundancy G Δ x y A :=
  ⟨fun hFeas =>
    ⟨isCrossFree_of_isFeasible hS hFeas,
     fun _ _ _ _ _ hChain =>
       chainRedundancy_nonneg_of_isFeasible hS hProper hΔ_eq hFeas hChain⟩,
   fun ⟨hCF, hRed⟩ =>
     isFeasible_of_isCrossFree_of_chainRedundancy_nonneg hS hDualExists hProper hΔ hΔ_eq hU hCF
       hRed⟩

end GraphMinor.GM06
