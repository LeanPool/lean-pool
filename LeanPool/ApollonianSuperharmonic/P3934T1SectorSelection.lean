/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3889T1TwoRaySectorDecomposition

-- [TABLET NODE: P3934T1SectorSelection]

/-!
# P3934T1SectorSelection

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3934T1SectorSelection (U : Set (Real × Real))
    (x : Real × Real) (r : Real) (u v : Real × Real)
    (E : P3889T1TwoRaySectorDecomposition x r u v)
    (hr : 0 < r) (hU : IsOpen U)
    (hx : x ∈ frontier U) (hV : frontier (closure U)ᶜ = frontier U)
    (hchart : frontier U ∩ Metric.ball x r =
      ({p | ∃ t : Real, 0 ≤ t ∧ p = x + t • u} ∪
        {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • v}) ∩ Metric.ball x r) :
    (U ∩ Metric.ball x r = E.left ∧ (closure U)ᶜ ∩ Metric.ball x r = E.right) ∨
    (U ∩ Metric.ball x r = E.right ∧ (closure U)ᶜ ∩ Metric.ball x r = E.left) := by
-- BODY
  let V := (closure U)ᶜ
  let B := Metric.ball x r
  have hUV : Disjoint U V := Set.disjoint_left.mpr (fun _ hu hv => hv (subset_closure hu))
  have partition : (frontier U)ᶜ = U ∪ V := by
    ext q
    rw [frontier, hU.interior_eq]
    simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_union, V]
    constructor
    · intro h
      by_cases hq : q ∈ U
      · exact Or.inl hq
      · exact Or.inr (fun hc => h ⟨hc, hq⟩)
    · rintro (hu | hv) ⟨hc, hn⟩
      · exact hn hu
      · exact hv hc
  have cover : E.left ∪ E.right = (U ∪ V) ∩ B := by
    rw [← partition, E.cover]
    ext q
    constructor
    · rintro ⟨hb, hn⟩
      refine ⟨?_, hb⟩
      intro hf
      have hm : q ∈ frontier U ∩ Metric.ball x r := ⟨hf, hb⟩
      rw [hchart] at hm
      exact hn hm.1
    · rintro ⟨hf, hb⟩
      refine ⟨hb, ?_⟩
      intro hn
      have hm : q ∈ frontier U ∩ Metric.ball x r := by
        rw [hchart]
        exact ⟨hn, hb⟩
      exact hf hm.1
  have classify (C : Set (Real × Real)) (hC : IsConnected C)
      (hsub : C ⊆ E.left ∪ E.right) : C ⊆ U ∨ C ⊆ V := by
    have hs : C ⊆ U ∪ V := by
      intro q hq
      have hm := hsub hq
      rw [cover] at hm
      exact hm.1
    by_cases hm : (C ∩ U).Nonempty
    · exact Or.inl (hC.isPreconnected.subset_left_of_subset_union hU
        isClosed_closure.isOpen_compl hUV hs hm)
    · right
      intro q hq
      rcases hs hq with hu | hv
      · exact (hm ⟨q, hq, hu⟩).elim
      · exact hv
  have meet (W : Set (Real × Real)) (hw : x ∈ closure W) : (W ∩ B).Nonempty := by
    obtain ⟨q, hq, hd⟩ := Metric.mem_closure_iff.mp hw r hr
    exact ⟨q, hq, by simpa only [B, Metric.mem_ball, dist_comm] using hd⟩
  have hUm := meet U (frontier_subset_closure hx)
  have hVm := meet V (frontier_subset_closure (hV.symm ▸ hx))
  have equations (C D : Set (Real × Real))
      (hc : C ∪ D = (U ∪ V) ∩ B) (hCU : C ⊆ U) (hDV : D ⊆ V) :
      U ∩ B = C ∧ V ∩ B = D := by
    constructor
    · apply Set.Subset.antisymm
      · intro q hq
        have hm : q ∈ C ∪ D := hc.symm ▸ ⟨Or.inl hq.1, hq.2⟩
        rcases hm with hC | hD
        · exact hC
        · exact (Set.disjoint_left.mp hUV hq.1 (hDV hD)).elim
      · intro q hq
        have hm : q ∈ (U ∪ V) ∩ B := hc ▸ (Or.inl hq : q ∈ C ∪ D)
        exact ⟨hCU hq, hm.2⟩
    · apply Set.Subset.antisymm
      · intro q hq
        have hm : q ∈ C ∪ D := hc.symm ▸ ⟨Or.inr hq.1, hq.2⟩
        rcases hm with hC | hD
        · exact (Set.disjoint_left.mp hUV (hCU hC) hq.1).elim
        · exact hD
      · intro q hq
        have hm : q ∈ (U ∪ V) ∩ B := hc ▸ (Or.inr hq : q ∈ C ∪ D)
        exact ⟨hDV hq, hm.2⟩
  rcases classify E.left E.left_connected Set.subset_union_left with hLU | hLV
  · rcases classify E.right E.right_connected Set.subset_union_right with hRU | hRV
    · obtain ⟨q, hqV, hqB⟩ := hVm
      have hm : q ∈ E.left ∪ E.right := cover.symm ▸ ⟨Or.inr hqV, hqB⟩
      exact (Set.disjoint_left.mp hUV (hm.elim (fun h => hLU h) (fun h => hRU h)) hqV).elim
    · exact Or.inl (equations E.left E.right cover hLU hRV)
  · rcases classify E.right E.right_connected Set.subset_union_right with hRU | hRV
    · exact Or.inr (equations E.right E.left (by rw [Set.union_comm, cover]) hRU hLV)
    · obtain ⟨q, hqU, hqB⟩ := hUm
      have hm : q ∈ E.left ∪ E.right := cover.symm ▸ ⟨Or.inl hqU, hqB⟩
      exact (Set.disjoint_left.mp hUV hqU (hm.elim (fun h => hLV h) (fun h => hRV h))).elim

end ApollonianSuperharmonic

end
