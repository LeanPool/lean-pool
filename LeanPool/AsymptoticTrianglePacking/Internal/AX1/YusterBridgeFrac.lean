/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Fractional bridge for triangle packings

Identifies the edge-set formulation of `nu3star` with nonnegative weights on
triangle vertex-sets subject to the usual per-edge capacity constraints.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterEdge
public import Mathlib.Tactic.IntervalCases

/-! # YusterBridgeFrac -/

@[expose] public section

open Finset SimpleGraph Hypergraph

namespace Nibble.YusterE

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- PaperIII-style fractional triangle packing, with weights on vertex-sets. -/
def IsTriangleFracPacking (w : Finset V → ℝ) : Prop :=
  (∀ t, 0 ≤ w t) ∧
    (∀ t, w t ≠ 0 → G.IsNClique 3 t) ∧
    ∀ e : Finset V, e.card = 2 →
      (∑ t ∈ (G.cliqueFinset 3).filter (fun t => e ⊆ t), w t) ≤ 1

/-- Taking all two-element subsets is injective on triangles. -/
theorem triangle_powersetCard_two_injOn :
    Set.InjOn (fun t : Finset V => t.powersetCard 2)
      (G.cliqueFinset 3 : Set (Finset V)) := by
  intro t1 ht1 t2 ht2 heq
  simp only [Finset.mem_coe, SimpleGraph.mem_cliqueFinset_iff] at ht1 ht2
  simp only at heq
  apply Finset.Subset.antisymm
  · intro a ha
    obtain ⟨b, hb, hab⟩ : ∃ b ∈ t1, b ≠ a := by
      have hne : (t1.erase a).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem ha, ht1.2]; omega
      obtain ⟨b, hbm⟩ := hne
      exact ⟨b, Finset.mem_of_mem_erase hbm, Finset.ne_of_mem_erase hbm⟩
    have hmem : ({a, b} : Finset V) ∈ t1.powersetCard 2 := by
      rw [Finset.mem_powersetCard]
      refine ⟨by intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz; rcases hz with rfl | rfl; exact ha; exact hb,
              Finset.card_pair (fun h => hab h.symm)⟩
    rw [heq] at hmem
    rw [Finset.mem_powersetCard] at hmem
    exact hmem.1 (by simp)
  · intro a ha
    obtain ⟨b, hb, hab⟩ : ∃ b ∈ t2, b ≠ a := by
      have hne : (t2.erase a).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem ha, ht2.2]; omega
      obtain ⟨b, hbm⟩ := hne
      exact ⟨b, Finset.mem_of_mem_erase hbm, Finset.ne_of_mem_erase hbm⟩
    have hmem : ({a, b} : Finset V) ∈ t2.powersetCard 2 := by
      rw [Finset.mem_powersetCard]
      refine ⟨by intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz; rcases hz with rfl | rfl; exact ha; exact hb,
              Finset.card_pair (fun h => hab h.symm)⟩
    rw [← heq] at hmem
    rw [Finset.mem_powersetCard] at hmem
    exact hmem.1 (by simp)

/-- The union of the two-element subsets of a triangle recovers its vertices. -/
theorem triangle_powersetCard_two_sup {t : Finset V} (ht : G.IsNClique 3 t) :
    (t.powersetCard 2).sup id = t := by
  apply Finset.ext
  intro v
  simp [Finset.mem_sup]
  constructor
  · rintro ⟨s, hs, hv⟩
    exact hs.1 hv
  · intro hv
    have hcard : t.card = 3 := ht.card_eq
    have hne : (t.erase v).Nonempty := by
      have h2 : (t.erase v).card = 2 := by rw [Finset.card_erase_of_mem hv]; omega
      exact Finset.card_pos.mp (by omega)
    obtain ⟨u, hu⟩ := hne
    use {v, u}
    refine ⟨⟨?subset, ?card⟩, ?mem⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hv
      · exact Finset.mem_of_mem_erase hu
    · rw [Finset.card_pair]; exact fun h => Finset.ne_of_mem_erase hu h.symm
    · simp

/-- For a two-element set `e`, membership among a triangle's edges is inclusion
in the triangle. -/
theorem mem_powersetCard_two_iff_subset {e t : Finset V} (he : e.card = 2) :
    e ∈ t.powersetCard 2 ↔ e ⊆ t := by
  simp [Finset.mem_powersetCard, he]

/-- Filtering the edge-set triangle hypergraph at an edge is the image of the
vertex-set triangles containing that edge. -/
theorem triangleHypergraphE_filter_eq_image (e : Finset V) (he : e.card = 2) :
    (triangleHypergraphE G).filter (fun T => e ∈ T) =
      ((G.cliqueFinset 3).filter (fun t => e ⊆ t)).image
        (fun t => t.powersetCard 2) := by
  ext T
  simp only [triangleHypergraphE, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, heT⟩
    exact ⟨t, ⟨ht, by rw [mem_powersetCard_two_iff_subset he] at heT; exact heT⟩, rfl⟩
  · rintro ⟨t, ⟨ht, ht_sub⟩, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, by rw [mem_powersetCard_two_iff_subset he]; exact ht_sub⟩

/-- Reindex the fractional objective from triangle vertex-sets to triangle
edge-sets. -/
theorem sum_triangleHypergraphE_sup (w : Finset V → ℝ) :
    ∑ T ∈ triangleHypergraphE G, w (T.sup id) =
      ∑ t ∈ G.cliqueFinset 3, w t := by
  rw [triangleHypergraphE]
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [SimpleGraph.mem_cliqueFinset_iff] at ht
    rw [triangle_powersetCard_two_sup G ht]
  · exact triangle_powersetCard_two_injOn G

/-- Reindex the fractional objective from triangle edge-sets to triangle
vertex-sets. -/
theorem sum_clique_powersetCard_two (w : Finset (Finset V) → ℝ) :
    ∑ t ∈ G.cliqueFinset 3, w (t.powersetCard 2) =
      ∑ T ∈ triangleHypergraphE G, w T := by
  rw [triangleHypergraphE, Finset.sum_image (triangle_powersetCard_two_injOn G)]

/-- A fractional packing on triangle edge-sets transports to one on triangle
vertex-sets, preserving its objective. -/
theorem fracPacking_to_triangleFracPacking
    {w' : Finset (Finset V) → ℝ} (hw' : IsFracPacking G w') :
    IsTriangleFracPacking G (fun t => w' (t.powersetCard 2)) ∧
      (∑ t ∈ G.cliqueFinset 3, w' (t.powersetCard 2)) =
        ∑ T ∈ triangleHypergraphE G, w' T := by
  refine ⟨⟨?nneg, ?ncard, ?cap⟩, ?sum⟩
  case nneg =>
    intro t
    exact hw'.1 _
  case ncard =>
    intro t ht
    by_contra hnot
    apply ht
    have : t.powersetCard 2 ∉ triangleHypergraphE G := by
      rw [triangleHypergraphE, Finset.mem_image]
      intro ⟨s, hs, hs_eq⟩
      rw [SimpleGraph.mem_cliqueFinset_iff] at hs
      have hscard : s.card = 3 := hs.card_eq
      have htcard : t.card = 3 := by
        have h1 : (powersetCard 2 s).card = 3 := by simp [hscard]
        rw [hs_eq] at h1
        simp [Finset.card_powersetCard] at h1
        have hle : t.card ≤ 3 := by
          by_contra h
          push Not at h
          have : (t.card).choose 2 ≥ (4).choose 2 := Nat.choose_le_choose _ (by omega : (4 : ℕ) ≤ t.card)
          simp [Nat.choose] at this
          omega
        interval_cases t.card <;> simp at h1 ⊢
      have hs2 : 2 ≤ s.card := by omega
      have ht2 : 2 ≤ t.card := by omega
      have hst : s = t := powersetCard_two_inj hs2 ht2 hs_eq
      exact hnot (hst ▸ ⟨hs.isClique, hs.card_eq⟩)
    exact hw'.2.1 _ this
  case cap =>
    intro e he
    have hfilter := triangleHypergraphE_filter_eq_image G e he
    have hinj := triangle_powersetCard_two_injOn G
    have hset_eq : ((G.cliqueFinset 3).filter (fun t => e ⊆ t) : Set (Finset V)) =
        {t | t ∈ G.cliqueFinset 3 ∧ e ⊆ t} := by ext; simp
    have hinj' : Set.InjOn (fun t => t.powersetCard 2)
        ((G.cliqueFinset 3).filter (fun t => e ⊆ t) : Set (Finset V)) := by
      rw [hset_eq]
      exact hinj.mono (fun x hx => hx.1)
    have heq : ∑ t ∈ (G.cliqueFinset 3).filter (fun t => e ⊆ t), w' (t.powersetCard 2) =
               ∑ T ∈ (triangleHypergraphE G).filter (fun T => e ∈ T), w' T := by
      rw [hfilter]
      rw [Finset.sum_image hinj']
    rw [heq]
    exact hw'.2.2 e
  case sum =>
    exact sum_clique_powersetCard_two G w'

/-- A fractional packing on triangle vertex-sets transports to one on triangle
edge-sets, preserving its objective. -/
theorem triangleFracPacking_to_fracPacking
    {w : Finset V → ℝ} (hw : IsTriangleFracPacking G w) :
    let w' : Finset (Finset V) → ℝ :=
      fun T => if T ∈ triangleHypergraphE G then w (T.sup id) else 0
    IsFracPacking G w' ∧
      (∑ T ∈ triangleHypergraphE G, w' T) =
        ∑ t ∈ G.cliqueFinset 3, w t := by
  refine ⟨⟨?nneg, ?zero_outside, ?edge_constr⟩, ?sum_eq⟩
  case nneg =>
    intro T
    simp only
    split_ifs with h <;> [exact hw.1 _; exact le_refl 0]
  case zero_outside =>
    intro T hT
    simp [hT]
  case edge_constr =>
    intro e
    have hsimp : ∀ T ∈ (triangleHypergraphE G).filter (fun T => e ∈ T),
        (if T ∈ triangleHypergraphE G then w (T.sup id) else 0) = w (T.sup id) := by
      intro T hT
      simp only [Finset.mem_filter] at hT
      simp [hT.1]
    rw [Finset.sum_congr rfl hsimp]
    by_cases he : e.card = 2
    · rw [triangleHypergraphE_filter_eq_image G e he]
      have hinj : Set.InjOn (fun t => t.powersetCard 2)
          ((G.cliqueFinset 3).filter (fun t => e ⊆ t) : Set (Finset V)) :=
        (triangle_powersetCard_two_injOn G).mono (fun t ht => by simp_all)
      rw [Finset.sum_image hinj]
      have hconv : ∀ t ∈ (G.cliqueFinset 3).filter (fun t => e ⊆ t),
          (t.powersetCard 2).sup id = t := by
        intro t ht
        simp only [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
        exact triangle_powersetCard_two_sup G ht.1
      rw [Finset.sum_congr rfl (fun t ht => congr_arg w (hconv t ht))]
      exact hw.2.2 e he
    · have hempty : (triangleHypergraphE G).filter (fun T => e ∈ T) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro T hT
        rw [triangleHypergraphE, Finset.mem_image] at hT
        obtain ⟨t, ht, hTe⟩ := hT
        simp only [SimpleGraph.mem_cliqueFinset_iff] at ht
        rw [← hTe]
        rw [Finset.mem_powersetCard]
        exact fun h => he h.2
      simp [hempty]
  case sum_eq =>
    conv_lhs =>
      simp only [Finset.sum_ite_mem, Finset.inter_self]
    exact sum_triangleHypergraphE_sup G w

/-- The Nibble edge-set fractional triangle-packing optimum is exactly the
PaperIII-style optimum over weights on triangle vertex-sets. -/
theorem nu3star_eq_triangleFrac_sSup :
    nu3star G =
      sSup {x : ℝ | ∃ w : Finset V → ℝ, IsTriangleFracPacking G w ∧
        x = ∑ t ∈ G.cliqueFinset 3, w t} := by
  unfold nu3star
  congr 1
  ext x
  constructor
  · rintro ⟨w', hw', rfl⟩
    obtain ⟨hpack, hsum⟩ := fracPacking_to_triangleFracPacking G hw'
    exact ⟨fun t => w' (t.powersetCard 2), hpack, hsum.symm⟩
  · rintro ⟨w, hw, rfl⟩
    let w' : Finset (Finset V) → ℝ :=
      fun T => if T ∈ triangleHypergraphE G then w (T.sup id) else 0
    obtain ⟨hpack, hsum⟩ := triangleFracPacking_to_fracPacking G hw
    exact ⟨w', hpack, hsum.symm⟩

end Nibble.YusterE
