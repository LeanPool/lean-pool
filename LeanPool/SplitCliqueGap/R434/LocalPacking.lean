/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.LocalTriangleLift
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-! One uncovered pair of each color type would itself be a triangle. -/

@[expose] public section

open Finset

namespace GapExtremal.R434.H54

private def layer (i : Fin 3) := edges.filter fun e => e.1 = i

private theorem in_layer {t : Triangle} (ht : t ∈ triangles) (i : Fin 3) :
    onTriangleIndex t i ∈ layer i := by
  obtain ⟨_,h0,h1,h2⟩ := mem_filter.mp ht
  apply mem_filter.mpr
  refine ⟨?_, onTriangleIndex_kind t i⟩
  fin_cases i <;> assumption

/-- The three coordinates telescope around a triangle. The base five records
each role separately when a single edge is missing from each layer. -/
private def boundary (e : Edge) : ℤ :=
  let a : ℤ := e.2.1.val
  let b : ℤ := e.2.2.val
  if e.1 = 0 then 25*a + 5*b else if e.1 = 1 then b-5*a else -25*a-b

private theorem layer_balance :
    (∑ e ∈ layer 0, boundary e) + (∑ e ∈ layer 1, boundary e) +
    (∑ e ∈ layer 2, boundary e) = 0 := by decide +kernel

private theorem triangle_balance (t : Triangle) :
    boundary (onTriangleIndex t 0) + boundary (onTriangleIndex t 1) +
      boundary (onTriangleIndex t 2) = 0 := by
  simp [boundary,onTriangleIndex]

private theorem impossible_full (S : Finset Triangle) (hs : S ⊆ triangles)
    (hi : ∀ i : Fin 3, Set.InjOn (fun t => onTriangleIndex t i) S)
    (hfull : ∀ i, S.image (fun t => onTriangleIndex t i) = layer i) : False := by
  classical
  apply no_integral_cover (fun t => if t ∈ S then 1 else 0) (by intro t _; split <;> decide)
  intro e he
  have hm : e ∈ S.image (fun t => onTriangleIndex t e.1) := by
    rw [hfull]; exact mem_filter.mpr ⟨he,rfl⟩
  obtain ⟨t,ht,hidx⟩ := mem_image.mp hm
  have ht' : t ∈ triangles.filter (onEdge · e) := mem_filter.mpr
    ⟨hs ht, (onEdge_iff_index t e).mpr hidx.symm⟩
  unfold load
  rw [sum_eq_single t]
  · simp [ht]
  · intro u hu hne
    have hu' : u ∉ S := fun huS => hne (hi e.1 huS ht
      (((onEdge_iff_index u e).mp (mem_filter.mp hu).2).symm.trans hidx.symm))
    simp [hu']
  · exact fun hn => (hn ht').elim

theorem local_packing_le_sixteen (S : Finset Triangle) (hs : S ⊆ triangles)
    (hi : ∀ i : Fin 3, Set.InjOn (fun t => onTriangleIndex t i) S) : S.card ≤ 16 := by
  classical
  let P (i : Fin 3) := S.image fun t => onTriangleIndex t i
  have hsub (i) : P i ⊆ layer i := by
    rintro _ he
    obtain ⟨t,ht,rfl⟩ := mem_image.mp he
    exact in_layer (hs ht) i
  have hcard (i) : (P i).card = S.card := card_image_of_injOn (hi i)
  have hsize (i) : (layer i).card = 18 := balanced_edge_counts i
  have hle := card_le_card (hsub 0)
  rw [hcard, hsize] at hle
  by_contra! hn
  by_cases h18 : S.card = 18
  · exact impossible_full S hs hi (fun i => eq_of_subset_of_card_le (hsub i)
      (by rw [hsize,hcard,h18]))
  have hmiss (i) : ∃ e, layer i \ P i = {e} := by
    apply card_eq_one.mp
    rw [card_sdiff_of_subset (hsub i), hsize, hcard]
    omega
  choose e he using hmiss
  have hem (i) : e i ∈ layer i ∧ e i ∉ P i := mem_sdiff.mp (he i ▸ mem_singleton_self _)
  have hsum (i) : (∑ k ∈ layer i, boundary k) =
      (∑ t ∈ S, boundary (onTriangleIndex t i)) + boundary (e i) := by
    have h := sum_sdiff (f := boundary) (hsub i)
    rw [he, sum_singleton] at h
    dsimp [P] at h
    rw [sum_image (hi i)] at h
    linarith
  have hbal := layer_balance
  rw [hsum 0, hsum 1, hsum 2] at hbal
  have hs0 : (∑ t ∈ S, boundary (onTriangleIndex t 0)) +
      (∑ t ∈ S, boundary (onTriangleIndex t 1)) +
      (∑ t ∈ S, boundary (onTriangleIndex t 2)) = 0 := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    simp only [triangle_balance, sum_const_zero]
  have he0 : boundary (e 0) + boundary (e 1) + boundary (e 2) = 0 := by linarith
  have hk (i) : (e i).1 = i := (mem_filter.mp (hem i).1).2
  let t : Triangle := ((e 0).2.1, (e 0).2.2, (e 1).2.2)
  have hroles : (e 0).2.1 = (e 2).2.1 ∧ (e 0).2.2 = (e 1).2.1 ∧ (e 1).2.2 = (e 2).2.2 := by
    simp [boundary,hk] at he0
    have hv (i : Fin 3) : (e i).2.1.val < 5 ∧ (e i).2.2.val < 5 :=
      ⟨(e i).2.1.isLt, (e i).2.2.isLt⟩
    obtain ⟨_,_⟩ := hv 0
    obtain ⟨_,_⟩ := hv 1
    obtain ⟨_,_⟩ := hv 2
    constructor
    · apply Fin.ext; omega
    constructor <;> apply Fin.ext <;> omega
  have hidx (i : Fin 3) : onTriangleIndex t i = e i := by
    apply Prod.ext
    · exact (onTriangleIndex_kind ..).trans (hk i).symm
    · fin_cases i <;> apply Prod.ext <;> first | rfl | exact hroles.1 | exact hroles.2.1 |
      exact hroles.2.2
  have hin (i) : onTriangleIndex t i ∈ edges := by rw [hidx]; exact (mem_filter.mp (hem i).1).1
  have ht : t ∈ triangles := mem_filter.mpr ⟨mem_univ _, hin 0, hin 1, hin 2⟩
  have hnew (i) (v) (hv : v ∈ S) : onTriangleIndex v i ≠ onTriangleIndex t i := by
    rw [hidx]; exact fun h => (hem i).2 (mem_image.mpr ⟨v,hv,h⟩)
  apply impossible_full (insert t S) (insert_subset ht hs)
  · intro i u hu v hv heq
    rcases mem_insert.mp hu with rfl | hu <;> rcases mem_insert.mp hv with rfl | hv
    · rfl
    · exact False.elim (hnew i v hv heq.symm)
    · exact False.elim (hnew i u hu heq)
    · exact hi i hu hv heq
  · intro i
    rw [image_insert, hidx]
    change insert (e i) (P i) = layer i
    rw [← singleton_union, ← he, sdiff_union_of_subset (hsub i)]

theorem packing_of_sixteen : ∃ S : Finset Triangle, S ⊆ triangles ∧ S.card = 16 ∧
    ∀ i : Fin 3, Set.InjOn (fun t => onTriangleIndex t i) S := by
  let S : Finset Triangle :=
    {(0,0,4),(0,1,2),(0,2,3),(1,0,0),(1,1,3),(1,3,4),(1,4,2),(2,0,1),
     (2,4,3),(3,0,2),(3,2,0),(3,3,3),(3,4,1),(4,1,0),(4,3,2),(4,4,4)}
  refine ⟨S, by decide +kernel, by decide +kernel, ?_⟩
  have h : ∀ i : Fin 3, ∀ t ∈ S, ∀ u ∈ S,
      onTriangleIndex t i = onTriangleIndex u i → t = u := by decide +kernel
  exact fun i t ht u hu => h i t ht u hu

end GapExtremal.R434.H54
