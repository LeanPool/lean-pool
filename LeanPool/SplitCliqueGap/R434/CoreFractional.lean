/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.CoreDefect
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-! Lifting the half-integral H54 witness to a residual packing. -/

@[expose] public section

open Finset
open scoped BigOperators

namespace GapExtremal.R434

/-- The unordered vertex set underlying an ordered triangle. -/
def triangleVertices {V : Type} [DecidableEq V] (t : OrderedTriangle V) : Finset V :=
  {t.1, t.2.1, t.2.2}

theorem pair_mem_triangleVertices {V : Type} [DecidableEq V]
    {t : OrderedTriangle V} {u v : V} (hne : u ≠ v) :
    u ∈ triangleVertices t ∧ v ∈ triangleVertices t ↔ s(u,v) ∈ triangleEdges t := by
  simp only [triangleVertices, triangleEdges, mem_insert, mem_singleton, Sym2.eq_iff]
  constructor
  · rintro ⟨hu,hv⟩
    rcases hu with h | h | h <;> rcases hv with h' | h' | h' <;>
      first | exact (hne (h.trans h'.symm)).elim | tauto
  · tauto

namespace H54

variable {R : Type} [Fintype R] [DecidableEq R] [CommRing R]

omit [Fintype R] in
theorem blockTriangle_vertices_card (a x : R) (t : Triangle) :
    (triangleVertices (blockTriangle a x t)).card = 3 := by
  let u := affineVertex a x (0,t.1)
  let v := affineVertex a x (1,t.2.1)
  let z := affineVertex a x (2,t.2.2)
  have huv : u ≠ v := fun h => (by decide : (0 : Fin 3) ≠ 1)
    (congrArg (fun q : Role × R => q.1.1) h)
  have huz : u ≠ z := fun h => (by decide : (0 : Fin 3) ≠ 2)
    (congrArg (fun q : Role × R => q.1.1) h)
  have hvz : v ≠ z := fun h => (by decide : (1 : Fin 3) ≠ 2)
    (congrArg (fun q : Role × R => q.1.1) h)
  change ({u,v,z} : Finset (Role × R)).card = 3
  rw [card_insert_of_notMem (by simp [huv,huz]), card_pair hvz]

theorem blockTriangle_edges_core (h : R) (hh : 2 * h = 1) {A : Finset R}
    {a x : R} {t : Triangle} (ha : a ∈ A) (ht : t ∈ triangles) :
    triangleEdges (blockTriangle a x t) ⊆ (coreGraph h A).edgeFinset := by
  intro f hf
  rw [triangleEdges_block] at hf
  obtain ⟨i, _, rfl⟩ := mem_image.mp hf
  have he := (mem_filter.mp ht).2
  apply (blockEdge_mem_core h hh A _ _ _).mpr
  refine ⟨ha, ?_⟩
  fin_cases i
  · exact he.1
  · exact he.2.1
  · exact he.2.2

theorem blockTriangle_score (h : R) (hh : 2 * h = 1) {A : Finset R}
    {a x : R} {t : Triangle} (ha : a ∈ A) (ht : t ∈ triangles) :
    w (coreGraph h A) (triangleVertices (blockTriangle a x t)) = 2 := by
  let T := blockTriangle a x t
  let Q := triangleVertices T
  let B := coreGraph h A
  have hE : (inducedOn B Q).edgeFinset = triangleEdges T := by
    ext f
    induction f using Sym2.inductionOn with
    | _ u v =>
      constructor
      · intro hf
        have hp : B.Adj u v ∧ u ∈ Q ∧ v ∈ Q := SimpleGraph.mem_edgeFinset.mp hf
        exact (pair_mem_triangleVertices hp.1.ne).mp hp.2
      · intro hf
        have hAdj : B.Adj u v := SimpleGraph.mem_edgeFinset.mp (blockTriangle_edges_core h hh ha
          ht hf)
        obtain ⟨hu,hv⟩ := (pair_mem_triangleVertices hAdj.ne).mpr hf
        exact SimpleGraph.mem_edgeFinset.mpr ⟨hAdj,hu,hv⟩
  have hinj : Function.Injective (fun k => blockEdge a x (onTriangleIndex t k)) := by
    intro i j he
    have heq : ((a,x,onTriangleIndex t i) : R × R × Edge) = (a,x,onTriangleIndex t j) :=
      blockEdge_injective h hh he
    simpa only [onTriangleIndex_kind] using congrArg (fun q : R × R × Edge => q.2.2.1) heq
  have he : e B Q = 3 := by
    unfold e
    rw [hE, triangleEdges_block, card_image_of_injective _ hinj]
    simp
  change w B Q = 2
  rw [w, he, blockTriangle_vertices_card]
  decide

theorem core_fractional_score_small (h : R) (hh : 2 * h = 1) (A : Finset R) :
    ∃ y : Finset (Role × R) → ℝ, ResPack y ∧ (∀ S, y S ≠ 0 → S.card ≤ 3) ∧
      (∑ Q, y Q * (w (coreGraph h A) Q : ℝ)) =
        36 * ((A.card * Fintype.card R : ℕ) : ℝ) := by
  classical
  let B := coreGraph h A
  let D := A ×ˢ ((univ : Finset R) ×ˢ support)
  let Q (k : R × R × Triangle) := triangleVertices (blockTriangle k.1 k.2.1 k.2.2)
  let y (S : Finset (Role × R)) : ℝ := ∑ k ∈ D, if Q k = S then (1 : ℝ) / 2 else 0
  have hp (k : R × R × Triangle) (hk : k ∈ D) :
      k.1 ∈ A ∧ k.2.2 ∈ triangles := by
    exact ⟨(mem_product.mp hk).1, support_valid (mem_product.mp (mem_product.mp hk).2).2⟩
  have supportCard (S : Finset (Role × R)) (hs : y S ≠ 0) : S.card = 3 := by
    by_contra hcard
    apply hs
    apply sum_eq_zero
    intro k _
    have hne : Q k ≠ S := fun he => hcard (he ▸ blockTriangle_vertices_card _ _ _)
    simp [hne]
  refine ⟨y, ⟨?_, ?_, ?_⟩, fun S hs => (supportCard S hs).le, ?_⟩
  · intro S
    exact sum_nonneg fun k _ => by split <;> norm_num
  · intro S hs
    rw [supportCard S hs]
    norm_num
  · intro u v huv
    have hsum : ∑ S, (if u ∈ S ∧ v ∈ S then y S else 0) =
        ∑ k ∈ D, (if s(u,v) ∈ triangleEdges (blockTriangle k.1 k.2.1 k.2.2) then (1 : ℝ) / 2 else
          0) := by
      simp only [y, ite_sum_zero]
      rw [sum_comm]
      apply sum_congr rfl
      intro k _
      change ∑ S, (if u ∈ S ∧ v ∈ S then if Q k = S then (1 : ℝ) / 2 else 0 else 0) =
        if s(u,v) ∈ triangleEdges (blockTriangle k.1 k.2.1 k.2.2) then (1 : ℝ) / 2 else 0
      rw [sum_eq_single (Q k)]
      · simp only
        exact if_congr (pair_mem_triangleVertices huv) rfl rfl
      · intro S _ hne
        simp [hne.symm]
      · simp
    rw [hsum]
    by_cases hB : s(u,v) ∈ B.edgeFinset
    · obtain ⟨a,ha,x,e,he,heq⟩ := blockEdge_of_adj h hh (SimpleGraph.mem_edgeFinset.mp hB)
      have hfilter :
          (D.filter fun k => s(u,v) ∈ triangleEdges (blockTriangle k.1 k.2.1 k.2.2)) =
            {a} ×ˢ ({x} ×ˢ support.filter (onEdge · e)) := by
        ext k
        simp only [← heq, mem_filter, mem_product, mem_singleton, D, mem_univ, true_and,
          blockEdge_mem_blockTriangle h hh]
        constructor
        · rintro ⟨⟨_,hs⟩,ha',hx',hon⟩
          exact ⟨ha'.symm,hx'.symm,hs,hon⟩
        · rintro ⟨ha',hx',hs,hon⟩
          exact ⟨⟨ha'.symm ▸ ha,hs⟩,ha'.symm,hx'.symm,hon⟩
      rw [← sum_filter (s := D)
        (fun k => s(u,v) ∈ triangleEdges (blockTriangle k.1 k.2.1 k.2.2)) (fun _ => (1 : ℝ) / 2),
        hfilter]
      simp only [sum_const, nsmul_eq_mul, card_product, card_singleton, twice_on_each_edge e he]
      norm_num
    · have hzero : ∑ k ∈ D, (if s(u,v) ∈ triangleEdges (blockTriangle k.1 k.2.1 k.2.2)
          then (1 : ℝ) / 2 else 0) = 0 := by
        apply sum_eq_zero
        intro k hk
        have hne : s(u,v) ∉ triangleEdges (blockTriangle k.1 k.2.1 k.2.2) :=
          fun hm => hB (blockTriangle_edges_core h hh (hp k hk).1 (hp k hk).2 hm)
        simp [hne]
      rw [hzero]
      norm_num
  · simp only [y, sum_mul, ite_mul, zero_mul]
    rw [sum_comm]
    have hval : ∑ k ∈ D, ∑ S, (if Q k = S then (1 : ℝ) / 2 * (w B S : ℝ) else 0) =
        ∑ _k ∈ D, (1 : ℝ) := by
      apply sum_congr rfl
      intro k hk
      have hscore : w B (Q k) = 2 := blockTriangle_score h hh (hp k hk).1 (hp k hk).2
      simp [hscore]
    change ∑ k ∈ D, ∑ S, (if Q k = S then (1 : ℝ) / 2 * (w B S : ℝ) else 0) = _
    rw [hval]
    simp only [D, sum_const, nsmul_eq_mul, mul_one, card_product, card_univ, support_count,
      Nat.cast_mul]
    ring

theorem core_fractional_score (h : R) (hh : 2 * h = 1) (A : Finset R) :
    ∃ y : Finset (Role × R) → ℝ, ResPack y ∧
      (∑ Q, y Q * (w (coreGraph h A) Q : ℝ)) =
        36 * ((A.card * Fintype.card R : ℕ) : ℝ) := by
  obtain ⟨y, hy, _, hscore⟩ := core_fractional_score_small h hh A
  exact ⟨y, hy, hscore⟩

end H54

end GapExtremal.R434
