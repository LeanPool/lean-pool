/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.ResidualArithmetic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Energy and owner counts for a set of edge-disjoint triangles. -/

@[expose] public section

open Finset
open scoped BigOperators

namespace GapExtremal.R434

variable {E T K : Type} [DecidableEq E] [DecidableEq K]

theorem edge_partition_gap_of_count (B X : Finset E) (P Z : Finset T)
    (edges : T → Finset E) (mass : ℕ)
    (price : E → ℝ) (R δ loss : ℝ) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hpart : X ∪ P.biUnion edges = B) (hdisj : Disjoint X (P.biUnion edges))
    (hpack : (P : Set T).PairwiseDisjoint edges) (hZ : Z ⊆ P)
    (hcard : mass ≤ X.card + 3 * Z.card)
    (htotal : ∑ e ∈ B, price e = 0)
    (hprice : ∀ e ∈ X, -(2 * R / 3) ≤ price e)
    (hzero : ∀ t ∈ P, t ∉ Z → ∑ e ∈ edges t, price e = 0)
    (hmixed : ∀ t ∈ Z, δ ≤ ∑ e ∈ edges t, price e)
    (hslack : (X.card : ℝ) ≤ 27 * loss) :
    (mass : ℝ) / (27 * (1 + 2 * R / δ)) ≤ loss := by
  have hZsum : ∑ t ∈ Z, ∑ e ∈ edges t, price e =
      ∑ t ∈ P, ∑ e ∈ edges t, price e :=
    sum_subset hZ hzero
  have hbalance :
      0 = (∑ e ∈ X, price e) + ∑ t ∈ Z, ∑ e ∈ edges t, price e := by
    rw [hZsum, ← sum_biUnion hpack, ← sum_union hdisj, hpart, htotal]
  have hx : -(2 * R / 3) * (X.card : ℝ) ≤ ∑ e ∈ X, price e := by
    calc
      _ = ∑ _e ∈ X, -(2 * R / 3) := by simp [mul_comm]
      _ ≤ _ := sum_le_sum hprice
  have hz : δ * (Z.card : ℝ) ≤ ∑ t ∈ Z, ∑ e ∈ edges t, price e := by
    calc
      _ = ∑ _t ∈ Z, δ := by simp [mul_comm]
      _ ≤ _ := sum_le_sum hmixed
  apply signed_gap_of_budgets (mass : ℝ) (X.card : ℝ) (Z.card : ℝ) R δ loss hR hδ
  · exact_mod_cast hcard
  · linarith only [hbalance, hx, hz]
  · exact hslack

theorem edge_partition_gap (B X : Finset E) (P Z : Finset T)
    (edges : T → Finset E) (owners : Finset K) (owner : E → K)
    (price : E → ℝ) (R δ loss : ℝ) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hpart : X ∪ P.biUnion edges = B) (hdisj : Disjoint X (P.biUnion edges))
    (hpack : (P : Set T).PairwiseDisjoint edges) (hZ : Z ⊆ P)
    (hsize : ∀ t ∈ Z, (edges t).card ≤ 3)
    (hcover : owners ⊆ (X ∪ Z.biUnion edges).image owner)
    (htotal : ∑ e ∈ B, price e = 0)
    (hprice : ∀ e ∈ X, -(2 * R / 3) ≤ price e)
    (hzero : ∀ t ∈ P, t ∉ Z → ∑ e ∈ edges t, price e = 0)
    (hmixed : ∀ t ∈ Z, δ ≤ ∑ e ∈ edges t, price e)
    (hslack : (X.card : ℝ) ≤ 27 * loss) :
    (owners.card : ℝ) / (27 * (1 + 2 * R / δ)) ≤ loss := by
  have hcard : owners.card ≤ X.card + 3 * Z.card := calc
    owners.card ≤ ((X ∪ Z.biUnion edges).image owner).card := card_le_card hcover
    _ ≤ (X ∪ Z.biUnion edges).card := card_image_le
    _ ≤ X.card + (Z.biUnion edges).card := card_union_le _ _
    _ ≤ X.card + 3 * Z.card := by
      have hz := card_biUnion_le_card_mul Z edges 3 hsize
      omega
  exact edge_partition_gap_of_count B X P Z edges owners.card price R δ loss hR hδ hpart
    hdisj hpack hZ hcard htotal hprice hzero hmixed hslack

end GapExtremal.R434
