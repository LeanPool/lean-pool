/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM06.Defs
import LeanPool.GraphMinor.GM12.Section3InternalRegionCurve
import LeanPool.GraphMinor.GM12.Section3DiscChainBoundary
import LeanPool.GraphMinor.GM11.Regions
import Mathlib.Analysis.Convex.PathConnected

/-!
# A path-connected normal carrier of a disc chain

To apply VI (3.6) in the last case of XII (3.2), pages 247--248,
realize each vertex term by its point and each region term by a
path between its incident vertices or boundary endpoints. Adjacent
pieces meet, so their finite union is path connected. It meets the
drawing only at vertex terms of the chain. This supplies the carrier
from which to extract a normal separator line.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM06

universe u

private theorem isPathConnected_biUnion_fin {S : Type u} [TopologicalSpace S]
    (m : ℕ) (hm : 0 < m) (K : Fin m → Set S)
    (hconn : ∀ i : Fin m, IsPathConnected (K i))
    (hinter : ∀ i : Fin m, ∀ h : i.1 + 1 < m, (K i ∩ K ⟨i.1 + 1, h⟩).Nonempty) :
    IsPathConnected (⋃ i : Fin m, K i) := by
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
      have hconn' : ∀ j : Fin n, IsPathConnected (K' j) := fun j => hconn _
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
      refine ih_res.union (hconn ⟨n, Nat.lt_succ_self n⟩) ?_
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
    (G : Drawing S) {r : Set S} (hr : r ∈ G.R) {z : S} (hz : z ∈ r) : z ∉ G.U :=
  region_subset hr hz

private theorem discChain_left_mem_closure
    {S : Type u} [TopologicalSpace S] {G : Drawing S} {x y : S} {A : List (ChainTerm S)}
    (hChain : IsXYChain G x y A) :
    let leftPt : Fin A.length → S := fun i =>
      match A[i.1]'i.2 with
      | .inl v => v
      | .inr _ =>
        if _hi0 : i.1 = 0 then x
        else
          match A[i.1 - 1]'(Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.2) with
          | .inl v => v
          | .inr _ => x
    ∀ (i : Fin A.length) (r : Set S),
        A[i.1]'i.2 = .inr r → leftPt i ∈ closure r ∧
          (leftPt i ∈ G.U → leftPt i ∈ G.V ∧ Sum.inl (leftPt i) ∈ A) := by
  intro leftPt
  have h_chain_rel : ∀ (j : ℕ) (hj : j + 1 < A.length),
      ChainTerm.AreIncident G A[j] A[j + 1] :=
    fun j hj => List.isChain_iff_getElem.mp hChain.isChain j hj
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

private theorem discChain_right_mem_closure
    {S : Type u} [TopologicalSpace S] {G : Drawing S} {x y : S} {A : List (ChainTerm S)}
    (hChain : IsXYChain G x y A) :
    let rightPt : Fin A.length → S := fun i =>
      match A[i.1]'i.2 with
      | .inl v => v
      | .inr _ =>
        if hi1 : i.1 + 1 = A.length then y
        else
          match A[i.1 + 1]'(Nat.lt_of_le_of_ne (Nat.succ_le_of_lt i.2) hi1) with
          | .inl v => v
          | .inr _ => y
    ∀ (i : Fin A.length) (r : Set S),
        A[i.1]'i.2 = .inr r → rightPt i ∈ closure r ∧
          (rightPt i ∈ G.U → rightPt i ∈ G.V ∧ Sum.inl (rightPt i) ∈ A) := by
  intro rightPt
  have h_chain_rel : ∀ (j : ℕ) (hj : j + 1 < A.length),
      ChainTerm.AreIncident G A[j] A[j + 1] :=
    fun j hj => List.isChain_iff_getElem.mp hChain.isChain j hj
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

/-- Realize a VI (3.6) chain by a compact path-connected normal
carrier, for its application in XII (3.2), pages 247--248. -/
theorem exists_path_connected_carrier_of_disc_chain
    {S : Type u} [TopologicalSpace S] {G : Drawing S} {x y : S} {A : List (ChainTerm S)}
    (hDisc : IsClosedDiscSpace S) (hProper : G.IsProper)
    (hChain : IsXYChain G x y A) :
    ∃ F : Set S, IsCompact F ∧ IsPathConnected F ∧ x ∈ F ∧ y ∈ F ∧
      (F ∩ G.U ⊆ {v ∈ G.V | Sum.inl v ∈ A}) ∧ F ∩ bd S ⊆ {x, y} := by
  let : PathConnectedSpace unitInterval := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, by simp⟩)
  have hm : 0 < A.length := List.length_pos_of_ne_nil hChain.ne_nil
  let leftPt : Fin A.length → S := fun i =>
    match A[i.1]'i.2 with
    | .inl v => v
    | .inr _ =>
      if i.1 = 0 then x
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
  have h_left_closure := discChain_left_mem_closure hChain
  have h_right_closure := discChain_right_mem_closure hChain
  have hleftBd : ∀ i, leftPt i ∈ bd S → leftPt i = x ∨ leftPt i = y := by
    intro i hb
    rcases hir : A[i.1]'i.2 with v | r
    · simp only [leftPt, hir] at hb ⊢
      exact disc_chain_boundary_vertex_eq_endpoint hChain (hir ▸ List.getElem_mem i.2) hb
    · by_cases hi0 : i.val = 0
      · left
        dsimp only [leftPt]
        rw [hir]
        simp only [hi0, ↓reduceIte]
      · rcases hprev : A[i.val - 1]'(Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.2) with v | r'
        · simp only [leftPt, hir, hi0, hprev, ite_false] at hb ⊢
          exact disc_chain_boundary_vertex_eq_endpoint hChain
            (hprev ▸ List.getElem_mem (Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.2)) hb
        · simp [leftPt, hir, hi0, hprev]
  have hrightBd : ∀ i, rightPt i ∈ bd S → rightPt i = x ∨ rightPt i = y := by
    intro i hb
    rcases hir : A[i.1]'i.2 with v | r
    · simp only [rightPt, hir] at hb ⊢
      exact disc_chain_boundary_vertex_eq_endpoint hChain (hir ▸ List.getElem_mem i.2) hb
    · by_cases hi1 : i.val + 1 = A.length
      · simp [rightPt, hir, hi1]
      · rcases hnext : A[i.val + 1]'(Nat.lt_of_le_of_ne (Nat.succ_le_of_lt i.2) hi1) with v | r'
        · simp only [rightPt, hir, hi1, hnext] at hb ⊢
          exact disc_chain_boundary_vertex_eq_endpoint hChain
            (hnext ▸ List.getElem_mem (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt i.2) hi1)) hb
        · simp [rightPt, hir, hi1, hnext]
  have hK_exists : ∀ i : Fin A.length,
      ∃ K : Set S, IsCompact K ∧ IsPathConnected K ∧ leftPt i ∈ K ∧ rightPt i ∈ K ∧
        (K ∩ G.U ⊆ {v ∈ G.V | Sum.inl v ∈ A}) ∧ K ∩ bd S ⊆ {x, y} := by
    intro i
    rcases hir : A[i.1]'i.2 with v | r
    · refine ⟨{v}, isCompact_singleton, isPathConnected_singleton v, ?_, ?_, ?_, ?_⟩
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
      · intro z hz
        have hzv : z = v := hz.1
        subst z
        exact disc_chain_boundary_vertex_eq_endpoint hChain (hir ▸ List.getElem_mem i.2) hz.2
    · have hrR : r ∈ G.R := by
        have hv := hChain.valid (A[i.1]'i.2) (List.getElem_mem i.2)
        simpa [hir, ChainTerm.IsValid] using hv
      obtain ⟨hl_cl, hl_U⟩ := h_left_closure i r hir
      obtain ⟨hr_cl, hr_U⟩ := h_right_closure i r hir
      obtain ⟨γ, hγ0, hγ1, hγ_int⟩ :=
        exists_internal_region_curve G hDisc hProper r hrR (leftPt i) hl_cl (rightPt i) hr_cl
      refine ⟨range γ, isCompact_range γ.continuous, isPathConnected_range γ.continuous,
        ⟨0, hγ0⟩, ⟨1, hγ1⟩, ?_, ?_⟩
      · rintro z ⟨⟨t, rfl⟩, htU⟩
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
            have h_in_r : γ t ∈ r := (hγ_int t h_ioo.1 h_ioo.2).1
            exfalso
            exact not_mem_U_of_mem_region G hrR h_in_r htU
      · rintro z ⟨⟨t, rfl⟩, htbd⟩
        by_cases ht0 : t = 0
        · rw [ht0, hγ0] at htbd ⊢
          exact hleftBd i htbd
        by_cases ht1 : t = 1
        · rw [ht1, hγ1] at htbd ⊢
          exact hrightBd i htbd
        have ht0' : 0 < t.val := lt_of_le_of_ne t.property.1 (fun h => ht0 (Subtype.ext h.symm))
        have ht1' : t.val < 1 := lt_of_le_of_ne t.property.2 (fun h => ht1 (Subtype.ext h))
        exact False.elim ((hγ_int t ht0' ht1').2 htbd)
  choose K hK_comp hK_conn hK_left hK_right hK_sub hK_bd using hK_exists
  refine ⟨⋃ i : Fin A.length, K i, isCompact_iUnion hK_comp, ?_, ?_, ?_, ?_, ?_⟩
  · refine isPathConnected_biUnion_fin A.length hm K hK_conn ?_
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
  · rintro z ⟨hz, hzb⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact hK_bd i ⟨hi, hzb⟩


end GraphMinor.GM12
