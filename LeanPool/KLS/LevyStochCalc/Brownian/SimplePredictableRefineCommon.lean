/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0, with
-- source adaptations (deprecated names, proof-context visibility) listed in vendor/port.patch.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.SimplePredictableRefineInvariance

/-!
# Common refinement of two simple predictables and the difference isometry

The common refinement of two `SimplePredictable Ω T` sharing an endpoint: the
merged set of partition points, the merged partition `SimplePredictable.mergedπ`
with its two refining index maps, the induced refinements
`SimplePredictable.commonRefinement_left`/`_right` and their difference
`SimplePredictable.sub_on_common`. These give the difference isometry for simple
integrals (`SimplePredictable.diff_isometry_simple`) and the Cauchy property of
the simple integrals of an `L²`-Cauchy sequence of simple predictables
(`cauchy_of_L2_dense_simple`).
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- **C0b.4-pre1: Merged partition points.** The union of the two
SimplePredictables' partition images, as a `Finset ℝ`. The cardinality
of this Finset will become `M + 1` for the common refinement. -/
noncomputable def SimplePredictable.mergedPartitionPoints
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) : Finset ℝ :=
  (Finset.univ.image H₁.partition) ∪ (Finset.univ.image H₂.partition)

/-- **C0b.4-pre2: `0` is in the merged set.** Both partitions start at
`0` (`partition_zero`), so `0 = H₁.partition 0` is a member. -/
lemma SimplePredictable.zero_mem_mergedPartitionPoints
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) :
    (0 : ℝ) ∈ H₁.mergedPartitionPoints H₂ := by
  rw [SimplePredictable.mergedPartitionPoints]
  exact Finset.mem_union.mpr (Or.inl
    (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, H₁.partition_zero⟩))

/-- **C0b.4-pre3a: every `H₁.partition i` is in the merged set.** -/
lemma SimplePredictable.partition_mem_mergedPartitionPoints_left
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) (i : Fin (H₁.N + 1)) :
    H₁.partition i ∈ H₁.mergedPartitionPoints H₂ := by
  rw [SimplePredictable.mergedPartitionPoints]
  exact Finset.mem_union.mpr (Or.inl
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))

/-- **C0b.4-pre3b: every `H₂.partition i` is in the merged set.** -/
lemma SimplePredictable.partition_mem_mergedPartitionPoints_right
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) (i : Fin (H₂.N + 1)) :
    H₂.partition i ∈ H₁.mergedPartitionPoints H₂ := by
  rw [SimplePredictable.mergedPartitionPoints]
  exact Finset.mem_union.mpr (Or.inr
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))

/-- **C0b.4-pre4: number of tiles in the common refinement.** Equals
the cardinality of the merged set minus one. -/
noncomputable def SimplePredictable.mergedM
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) : ℕ :=
  (H₁.mergedPartitionPoints H₂).card - 1

/-- **C0b.4-pre5: cardinality vs. `mergedM`.** Since `0` is in the
merged set, the cardinality is at least 1, so
`card = mergedM + 1` (rearranging `mergedM = card - 1`). -/
lemma SimplePredictable.mergedM_card_eq
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) :
    (H₁.mergedPartitionPoints H₂).card = H₁.mergedM H₂ + 1 := by
  have h_pos : 0 < (H₁.mergedPartitionPoints H₂).card :=
    Finset.card_pos.mpr ⟨0, H₁.zero_mem_mergedPartitionPoints H₂⟩
  rw [SimplePredictable.mergedM]
  omega

/-- **C0b.4-pre6: the common-refinement partition function.** The
strictly-monotone enumeration of the merged Finset, with domain
`Fin (mergedM + 1)`. -/
noncomputable def SimplePredictable.mergedπ
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) :
    Fin (H₁.mergedM H₂ + 1) → ℝ :=
  fun k => (H₁.mergedPartitionPoints H₂).orderEmbOfFin (H₁.mergedM_card_eq H₂) k

/-- **C0b.4-pre7: `mergedπ` is strictly monotone.** Direct from
`orderEmbOfFin` being an order embedding. -/
lemma SimplePredictable.mergedπ_strictMono
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) :
    StrictMono (H₁.mergedπ H₂) :=
  ((H₁.mergedPartitionPoints H₂).orderEmbOfFin (H₁.mergedM_card_eq H₂)).strictMono

/-- **C0b.4-pre8: every partition value is non-negative.** Since
`partition 0 = 0` and `partition` is strictly monotone, every later
value dominates `0`. -/
lemma SimplePredictable.partition_nonneg
    {T : ℝ} (H : SimplePredictable Ω T) (i : Fin (H.N + 1)) :
    0 ≤ H.partition i := by
  rw [← H.partition_zero]
  exact H.partition_strictMono.monotone (Fin.zero_le i)

/-- **C0b.4-pre9: every element of the merged set is non-negative.** -/
lemma SimplePredictable.mem_mergedPartitionPoints_nonneg
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) {x : ℝ}
    (hx : x ∈ H₁.mergedPartitionPoints H₂) : 0 ≤ x := by
  rcases Finset.mem_union.mp hx with h | h
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    rw [← hi]; exact H₁.partition_nonneg i
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    rw [← hi]; exact H₂.partition_nonneg i

/-- **C0b.4-pre10: `mergedπ 0 = 0`.** Apply `orderEmbOfFin_zero` to
reduce to `min' = 0`; the latter follows since `0` is in the merged
set and is a lower bound. -/
lemma SimplePredictable.mergedπ_zero
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) :
    H₁.mergedπ H₂ 0 = 0 := by
  unfold SimplePredictable.mergedπ
  have hz : (0 : ℕ) < H₁.mergedM H₂ + 1 := Nat.succ_pos _
  have h_zero_eq : (0 : Fin (H₁.mergedM H₂ + 1)) = ⟨0, hz⟩ := rfl
  rw [h_zero_eq]
  rw [Finset.orderEmbOfFin_zero (H₁.mergedM_card_eq H₂) hz]
  -- Now goal: min' (mergedPartitionPoints) ⋯ = 0
  have h_zero_mem : (0 : ℝ) ∈ H₁.mergedPartitionPoints H₂ :=
    H₁.zero_mem_mergedPartitionPoints H₂
  apply le_antisymm
  · exact Finset.min'_le _ _ h_zero_mem
  · exact H₁.mem_mergedPartitionPoints_nonneg H₂
      (Finset.min'_mem _ _)

/-- **C0b.4-pre11: every element ≤ the (shared) endpoint.** Under
the assumption that both partitions end at the same point. -/
lemma SimplePredictable.mem_mergedPartitionPoints_le_endpoint
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    {x : ℝ} (hx : x ∈ H₁.mergedPartitionPoints H₂) :
    x ≤ H₁.partition (Fin.last H₁.N) := by
  rcases Finset.mem_union.mp hx with h | h
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    rw [← hi]
    exact H₁.partition_strictMono.monotone (Fin.le_last i)
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    rw [← hi]
    rw [h_eq]
    exact H₂.partition_strictMono.monotone (Fin.le_last i)

/-- **C0b.4-pre12: `mergedπ` at the last index equals the (shared)
endpoint.** Apply `orderEmbOfFin_last` to reduce to `max' = endpoint`;
the latter follows since the endpoint is in the merged set and is an
upper bound (via `mem_mergedPartitionPoints_le_endpoint`). -/
lemma SimplePredictable.mergedπ_last
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N)) :
    H₁.mergedπ H₂ (Fin.last (H₁.mergedM H₂)) =
      H₁.partition (Fin.last H₁.N) := by
  unfold SimplePredictable.mergedπ
  have hz : (0 : ℕ) < H₁.mergedM H₂ + 1 := Nat.succ_pos _
  have h_last_eq : (Fin.last (H₁.mergedM H₂) : Fin (H₁.mergedM H₂ + 1))
      = ⟨H₁.mergedM H₂ + 1 - 1, by omega⟩ := by
    apply Fin.ext; simp
  rw [h_last_eq]
  rw [Finset.orderEmbOfFin_last (H₁.mergedM_card_eq H₂) hz]
  -- Goal: max' (mergedPartitionPoints) ⋯ = H₁.partition (Fin.last H₁.N)
  have h_endpt_mem : H₁.partition (Fin.last H₁.N) ∈ H₁.mergedPartitionPoints H₂ :=
    H₁.partition_mem_mergedPartitionPoints_left H₂ (Fin.last H₁.N)
  apply le_antisymm
  · -- max' ≤ endpoint, since endpoint is an upper bound
    apply Finset.max'_le
    intro x hx
    exact H₁.mem_mergedPartitionPoints_le_endpoint H₂ h_eq hx
  · -- endpoint ≤ max', since endpoint is a member
    exact Finset.le_max' _ _ h_endpt_mem

/-- **C0b.4-pre13: every `H₁.partition i` is in the range of `mergedπ`.**
The range of `orderEmbOfFin` is the underlying Finset (via
`Finset.range_orderEmbOfFin`). -/
lemma SimplePredictable.mergedπ_refines_left
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) (i : Fin (H₁.N + 1)) :
    ∃ k : Fin (H₁.mergedM H₂ + 1), H₁.mergedπ H₂ k = H₁.partition i := by
  unfold SimplePredictable.mergedπ
  have h_in_range : H₁.partition i ∈ Set.range
      ⇑((H₁.mergedPartitionPoints H₂).orderEmbOfFin (H₁.mergedM_card_eq H₂)) := by
    rw [Finset.range_orderEmbOfFin]
    exact_mod_cast H₁.partition_mem_mergedPartitionPoints_left H₂ i
  exact h_in_range

/-- **C0b.4-pre14: every `H₂.partition i` is in the range of `mergedπ`.** -/
lemma SimplePredictable.mergedπ_refines_right
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) (i : Fin (H₂.N + 1)) :
    ∃ k : Fin (H₁.mergedM H₂ + 1), H₁.mergedπ H₂ k = H₂.partition i := by
  unfold SimplePredictable.mergedπ
  have h_in_range : H₂.partition i ∈ Set.range
      ⇑((H₁.mergedPartitionPoints H₂).orderEmbOfFin (H₁.mergedM_card_eq H₂)) := by
    rw [Finset.range_orderEmbOfFin]
    exact_mod_cast H₁.partition_mem_mergedPartitionPoints_right H₂ i
  exact h_in_range

/-- **C0b.4-pre15: existence of left index map.** For each merged tile `j`,
there is an `H₁` tile `i` whose interval contains the merged tile.

Proof: apply `strictMono_partition_tiles` to `H₁.partition` with
`s = mergedπ j.succ` to get `i` with `H₁.partition i.castSucc < s` and
`s ≤ H₁.partition i.succ`. This gives the right inclusion.
For the left inclusion, suppose for contradiction
`mergedπ j.castSucc < H₁.partition i.castSucc`. Since `H₁.partition i.castSucc`
is in the merged set, it equals `mergedπ k` for some `k`. Then
`mergedπ j.castSucc < mergedπ k < mergedπ j.succ`, so `j.castSucc < k < j.succ`,
contradicting `j.succ.val = j.castSucc.val + 1`. -/
private lemma SimplePredictable.exists_mergedIdxMap_left
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (j : Fin (H₁.mergedM H₂)) :
    ∃ i : Fin H₁.N,
      H₁.partition i.castSucc ≤ H₁.mergedπ H₂ j.castSucc ∧
      H₁.mergedπ H₂ j.succ ≤ H₁.partition i.succ := by
  -- Bounds on s = mergedπ j.succ to apply strictMono_partition_tiles
  have h_pos : H₁.partition 0 < H₁.mergedπ H₂ j.succ := by
    rw [H₁.partition_zero, ← H₁.mergedπ_zero H₂]
    exact (H₁.mergedπ_strictMono H₂) (Fin.succ_pos j)
  have h_le_endpt : H₁.mergedπ H₂ j.succ ≤ H₁.partition (Fin.last H₁.N) := by
    rw [← H₁.mergedπ_last H₂ h_eq]
    exact (H₁.mergedπ_strictMono H₂).monotone (Fin.le_last j.succ)
  obtain ⟨i, h_lt, h_le⟩ :=
    strictMono_partition_tiles H₁.partition_strictMono h_pos h_le_endpt
  refine ⟨i, ?_, h_le⟩
  by_contra h_not
  push Not at h_not
  -- h_not : H₁.mergedπ H₂ j.castSucc < H₁.partition i.castSucc
  obtain ⟨k, hk⟩ := H₁.mergedπ_refines_left H₂ i.castSucc
  rw [← hk] at h_not h_lt
  have h_jcs_lt_k : j.castSucc < k :=
    (H₁.mergedπ_strictMono H₂).lt_iff_lt.mp h_not
  have h_k_lt_jsc : k < j.succ :=
    (H₁.mergedπ_strictMono H₂).lt_iff_lt.mp h_lt
  have hj_cs_val : j.castSucc.val = j.val := Fin.val_castSucc j
  have hj_succ_val : j.succ.val = j.val + 1 := Fin.val_succ j
  have h1 : j.castSucc.val < k.val := h_jcs_lt_k
  have h2 : k.val < j.succ.val := h_k_lt_jsc
  omega

/-- **C0b.4-pre16: existence of right index map.** Mirror of
`exists_mergedIdxMap_left` for the second SimplePredictable. -/
private lemma SimplePredictable.exists_mergedIdxMap_right
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (j : Fin (H₁.mergedM H₂)) :
    ∃ i : Fin H₂.N,
      H₂.partition i.castSucc ≤ H₁.mergedπ H₂ j.castSucc ∧
      H₁.mergedπ H₂ j.succ ≤ H₂.partition i.succ := by
  have h_pos : H₂.partition 0 < H₁.mergedπ H₂ j.succ := by
    rw [H₂.partition_zero, ← H₁.mergedπ_zero H₂]
    exact (H₁.mergedπ_strictMono H₂) (Fin.succ_pos j)
  have h_le_endpt : H₁.mergedπ H₂ j.succ ≤ H₂.partition (Fin.last H₂.N) := by
    rw [← h_eq, ← H₁.mergedπ_last H₂ h_eq]
    exact (H₁.mergedπ_strictMono H₂).monotone (Fin.le_last j.succ)
  obtain ⟨i, h_lt, h_le⟩ :=
    strictMono_partition_tiles H₂.partition_strictMono h_pos h_le_endpt
  refine ⟨i, ?_, h_le⟩
  by_contra h_not
  push Not at h_not
  obtain ⟨k, hk⟩ := H₁.mergedπ_refines_right H₂ i.castSucc
  rw [← hk] at h_not h_lt
  have h_jcs_lt_k : j.castSucc < k :=
    (H₁.mergedπ_strictMono H₂).lt_iff_lt.mp h_not
  have h_k_lt_jsc : k < j.succ :=
    (H₁.mergedπ_strictMono H₂).lt_iff_lt.mp h_lt
  have hj_cs_val : j.castSucc.val = j.val := Fin.val_castSucc j
  have hj_succ_val : j.succ.val = j.val + 1 := Fin.val_succ j
  have h1 : j.castSucc.val < k.val := h_jcs_lt_k
  have h2 : k.val < j.succ.val := h_k_lt_jsc
  omega

/-- **C0b.4-pre17: left index map.** For each merged tile `j`, the
unique `H₁` tile whose interval contains it. Extracted via Choice
from `exists_mergedIdxMap_left`. -/
noncomputable def SimplePredictable.mergedIdxMap_left
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (j : Fin (H₁.mergedM H₂)) : Fin H₁.N :=
  (show ∃ i : Fin H₁.N,
      H₁.partition i.castSucc ≤ H₁.mergedπ H₂ j.castSucc ∧
      H₁.mergedπ H₂ j.succ ≤ H₁.partition i.succ by
    exact H₁.exists_mergedIdxMap_left H₂ h_eq j).choose

/-- **C0b.4-pre18: left idxMap inclusion (left endpoint).** -/
lemma SimplePredictable.mergedIdxMap_left_idx_le
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (j : Fin (H₁.mergedM H₂)) :
    H₁.partition (H₁.mergedIdxMap_left H₂ h_eq j).castSucc
      ≤ H₁.mergedπ H₂ j.castSucc :=
  (H₁.exists_mergedIdxMap_left H₂ h_eq j).choose_spec.1

/-- **C0b.4-pre19: left idxMap inclusion (right endpoint).** -/
lemma SimplePredictable.mergedIdxMap_left_idx_ge
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (j : Fin (H₁.mergedM H₂)) :
    H₁.mergedπ H₂ j.succ
      ≤ H₁.partition (H₁.mergedIdxMap_left H₂ h_eq j).succ :=
  (H₁.exists_mergedIdxMap_left H₂ h_eq j).choose_spec.2

/-- **C0b.4-pre20: right index map.** Mirror of `mergedIdxMap_left`. -/
noncomputable def SimplePredictable.mergedIdxMap_right
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (j : Fin (H₁.mergedM H₂)) : Fin H₂.N :=
  (show ∃ i : Fin H₂.N,
      H₂.partition i.castSucc ≤ H₁.mergedπ H₂ j.castSucc ∧
      H₁.mergedπ H₂ j.succ ≤ H₂.partition i.succ by
    exact H₁.exists_mergedIdxMap_right H₂ h_eq j).choose

/-- **C0b.4-pre21: right idxMap inclusion (left endpoint).** -/
lemma SimplePredictable.mergedIdxMap_right_idx_le
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (j : Fin (H₁.mergedM H₂)) :
    H₂.partition (H₁.mergedIdxMap_right H₂ h_eq j).castSucc
      ≤ H₁.mergedπ H₂ j.castSucc :=
  (H₁.exists_mergedIdxMap_right H₂ h_eq j).choose_spec.1

/-- **C0b.4-pre22: right idxMap inclusion (right endpoint).** -/
lemma SimplePredictable.mergedIdxMap_right_idx_ge
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (j : Fin (H₁.mergedM H₂)) :
    H₁.mergedπ H₂ j.succ
      ≤ H₂.partition (H₁.mergedIdxMap_right H₂ h_eq j).succ :=
  (H₁.exists_mergedIdxMap_right H₂ h_eq j).choose_spec.2

/-- **C0b.4: common refinement of `H₁` (the left input).** Refine
`H₁` onto the merged partition `mergedπ`, using `mergedIdxMap_left`
to map merged tiles back to `H₁`-tiles. The resulting SimplePredictable
has `N = H₁.mergedM H₂`, partition `mergedπ`, and `ξ_j = H₁.ξ (idxMap j)`. -/
noncomputable def SimplePredictable.commonRefinement_left
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N)) :
    SimplePredictable Ω T :=
  H₁.refine (H₁.mergedM H₂) (H₁.mergedπ H₂)
    (H₁.mergedπ_zero H₂)
    (H₁.mergedπ_last H₂ h_eq)
    (H₁.mergedπ_strictMono H₂)
    (H₁.mergedIdxMap_left H₂ h_eq)
    (H₁.mergedIdxMap_left_idx_le H₂ h_eq)
    (H₁.mergedIdxMap_left_idx_ge H₂ h_eq)

/-- **C0b.4: common refinement of `H₂` (the right input).** Mirror of
`commonRefinement_left`, refining `H₂` onto the same `mergedπ`. The
two refinements share `N` and `partition` but differ in `ξ`. -/
noncomputable def SimplePredictable.commonRefinement_right
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N)) :
    SimplePredictable Ω T :=
  H₂.refine (H₁.mergedM H₂) (H₁.mergedπ H₂)
    (H₁.mergedπ_zero H₂)
    (h_eq ▸ H₁.mergedπ_last H₂ h_eq)
    (H₁.mergedπ_strictMono H₂)
    (H₁.mergedIdxMap_right H₂ h_eq)
    (H₁.mergedIdxMap_right_idx_le H₂ h_eq)
    (H₁.mergedIdxMap_right_idx_ge H₂ h_eq)

/-- **C0b.5: compatibility of the two common refinements.** They have
the same `N` (both equal to `mergedM`) and the same `partition` function
(both equal to `mergedπ`). This is what allows pointwise subtraction
of their `ξ` values to form `sub_on_common`. -/
lemma SimplePredictable.commonRefinement_compat
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N)) :
    (H₁.commonRefinement_left H₂ h_eq).N
        = (H₁.commonRefinement_right H₂ h_eq).N
      ∧ HEq (H₁.commonRefinement_left H₂ h_eq).partition
            (H₁.commonRefinement_right H₂ h_eq).partition := by
  refine ⟨rfl, HEq.rfl⟩

/-- **C0b.6: subtraction on common refinement.** Given two
SimplePredictables sharing endpoint, the difference SimplePredictable
on the common refinement: same partition (`mergedπ`), with
`ξ_j ω = H₁.ξ (idxMap_left j) ω - H₂.ξ (idxMap_right j) ω`.

Boundedness uses `abs_sub` (`|a-b| ≤ |a|+|b|`) with the sum of bounds.
Measurability uses `Measurable.sub`. -/
noncomputable def SimplePredictable.sub_on_common
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N)) :
    SimplePredictable Ω T where
  N := H₁.mergedM H₂
  partition := H₁.mergedπ H₂
  partition_zero := H₁.mergedπ_zero H₂
  partition_le_T := (H₁.mergedπ_last H₂ h_eq) ▸ H₁.partition_le_T
  partition_strictMono := H₁.mergedπ_strictMono H₂
  ξ := fun j ω => H₁.ξ (H₁.mergedIdxMap_left H₂ h_eq j) ω
    - H₂.ξ (H₁.mergedIdxMap_right H₂ h_eq j) ω
  ξ_bounded := fun j => by
    obtain ⟨C₁, hC₁⟩ := H₁.ξ_bounded (H₁.mergedIdxMap_left H₂ h_eq j)
    obtain ⟨C₂, hC₂⟩ := H₂.ξ_bounded (H₁.mergedIdxMap_right H₂ h_eq j)
    exact ⟨C₁ + C₂, fun ω =>
      (abs_sub _ _).trans (add_le_add (hC₁ ω) (hC₂ ω))⟩
  ξ_measurable := fun j =>
    (H₁.ξ_measurable _).sub (H₂.ξ_measurable _)

/-- **C0b.7: linearity on common refinement.** The simple integral of
`sub_on_common H₁ H₂` equals the difference of the simple integrals of
`H₁` and `H₂`.

Proof: expand both `simpleIntegral`s via `simpleIntegral_eq_sum`,
distribute `(a-b)·c = a·c - b·c`, split the sum, then recognize each
sub-sum as the simple integral of `H_i` via `simpleIntegral_refine`
applied with the appropriate `idxMap`. -/
lemma SimplePredictable.simpleIntegral_sub_on_common
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (ω : Ω) :
    simpleIntegral W (H₁.sub_on_common H₂ h_eq) T ω
      = simpleIntegral W H₁ T ω - simpleIntegral W H₂ T ω := by
  rw [simpleIntegral_eq_sum]
  change (∑ j : Fin (H₁.mergedM H₂),
        (H₁.ξ (H₁.mergedIdxMap_left H₂ h_eq j) ω
          - H₂.ξ (H₁.mergedIdxMap_right H₂ h_eq j) ω)
        * (W.W (H₁.mergedπ H₂ j.succ) ω - W.W (H₁.mergedπ H₂ j.castSucc) ω))
      = simpleIntegral W H₁ T ω - simpleIntegral W H₂ T ω
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  · -- LHS sum = simpleIntegral W H₁ T ω
    have h_left := H₁.simpleIntegral_refine W (H₁.mergedM H₂) (H₁.mergedπ H₂)
      (H₁.mergedπ_zero H₂) (H₁.mergedπ_last H₂ h_eq) (H₁.mergedπ_strictMono H₂)
      (H₁.mergedIdxMap_left H₂ h_eq) (H₁.mergedIdxMap_left_idx_le H₂ h_eq)
      (H₁.mergedIdxMap_left_idx_ge H₂ h_eq) (H₁.mergedπ_refines_left H₂) ω
    rw [← h_left, simpleIntegral_eq_sum]
    exact Finset.sum_congr rfl (fun _ _ => rfl)
  · -- RHS sum = simpleIntegral W H₂ T ω
    have h_right := H₂.simpleIntegral_refine W (H₁.mergedM H₂) (H₁.mergedπ H₂)
      (H₁.mergedπ_zero H₂) (h_eq ▸ H₁.mergedπ_last H₂ h_eq)
      (H₁.mergedπ_strictMono H₂)
      (H₁.mergedIdxMap_right H₂ h_eq) (H₁.mergedIdxMap_right_idx_le H₂ h_eq)
      (H₁.mergedIdxMap_right_idx_ge H₂ h_eq) (H₁.mergedπ_refines_right H₂) ω
    rw [← h_right, simpleIntegral_eq_sum]
    exact Finset.sum_congr rfl (fun _ _ => rfl)

/-- **General-time linearity on common refinement.** The `min (·) t`-clamped
analogue of `simpleIntegral_sub_on_common`: the simple integral of `sub_on_common`
equals the difference of the simple integrals at *every* time `t`. Uses
`simpleIntegral_refine_intermediate`. -/
lemma SimplePredictable.simpleIntegral_sub_on_common_intermediate
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (t : ℝ) (ω : Ω) :
    simpleIntegral W (H₁.sub_on_common H₂ h_eq) t ω
      = simpleIntegral W H₁ t ω - simpleIntegral W H₂ t ω := by
  unfold simpleIntegral
  change (∑ j : Fin (H₁.mergedM H₂),
        (H₁.ξ (H₁.mergedIdxMap_left H₂ h_eq j) ω
          - H₂.ξ (H₁.mergedIdxMap_right H₂ h_eq j) ω)
        * (W.W (min (H₁.mergedπ H₂ j.succ) t) ω
            - W.W (min (H₁.mergedπ H₂ j.castSucc) t) ω))
      = simpleIntegral W H₁ t ω - simpleIntegral W H₂ t ω
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  · have h_left := H₁.simpleIntegral_refine_intermediate W (H₁.mergedM H₂) (H₁.mergedπ H₂)
      (H₁.mergedπ_zero H₂) (H₁.mergedπ_last H₂ h_eq) (H₁.mergedπ_strictMono H₂)
      (H₁.mergedIdxMap_left H₂ h_eq) (H₁.mergedIdxMap_left_idx_le H₂ h_eq)
      (H₁.mergedIdxMap_left_idx_ge H₂ h_eq) (H₁.mergedπ_refines_left H₂) t ω
    rw [← h_left]
    exact Finset.sum_congr rfl (fun _ _ => rfl)
  · have h_right := H₂.simpleIntegral_refine_intermediate W (H₁.mergedM H₂) (H₁.mergedπ H₂)
      (H₁.mergedπ_zero H₂) (h_eq ▸ H₁.mergedπ_last H₂ h_eq)
      (H₁.mergedπ_strictMono H₂)
      (H₁.mergedIdxMap_right H₂ h_eq) (H₁.mergedIdxMap_right_idx_le H₂ h_eq)
      (H₁.mergedIdxMap_right_idx_ge H₂ h_eq) (H₁.mergedπ_refines_right H₂) t ω
    rw [← h_right]
    exact Finset.sum_congr rfl (fun _ _ => rfl)

/-- **C0b.7-aux: pointwise evaluation of `sub_on_common`.** The eval
of the difference SimplePredictable equals the pointwise difference of
the evals.

Proof: rewrite both `H₁.eval` and `H₂.eval` as evals of their respective
common refinements (via `refine_eval`), so all three `.eval` expressions
share the partition `mergedπ`. Then both sides are sums of if-then-else
indexed by `Fin (mergedM)`; case-splitting on the if-condition reduces
to a trivial arithmetic equality. -/
lemma SimplePredictable.eval_sub_on_common
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (s : ℝ) (ω : Ω) :
    (H₁.sub_on_common H₂ h_eq).eval s ω
      = H₁.eval s ω - H₂.eval s ω := by
  rw [← H₁.refine_eval (H₁.mergedM H₂) (H₁.mergedπ H₂)
        (H₁.mergedπ_zero H₂) (H₁.mergedπ_last H₂ h_eq)
        (H₁.mergedπ_strictMono H₂) (H₁.mergedIdxMap_left H₂ h_eq)
        (H₁.mergedIdxMap_left_idx_le H₂ h_eq)
        (H₁.mergedIdxMap_left_idx_ge H₂ h_eq) s ω]
  rw [← H₂.refine_eval (H₁.mergedM H₂) (H₁.mergedπ H₂)
        (H₁.mergedπ_zero H₂) (h_eq ▸ H₁.mergedπ_last H₂ h_eq)
        (H₁.mergedπ_strictMono H₂) (H₁.mergedIdxMap_right H₂ h_eq)
        (H₁.mergedIdxMap_right_idx_le H₂ h_eq)
        (H₁.mergedIdxMap_right_idx_ge H₂ h_eq) s ω]
  unfold SimplePredictable.eval
  change (∑ j : Fin (H₁.mergedM H₂),
        if H₁.mergedπ H₂ j.castSucc < s ∧ s ≤ H₁.mergedπ H₂ j.succ
        then (H₁.ξ (H₁.mergedIdxMap_left H₂ h_eq j) ω
              - H₂.ξ (H₁.mergedIdxMap_right H₂ h_eq j) ω)
        else 0)
      = (∑ j : Fin (H₁.mergedM H₂),
          if H₁.mergedπ H₂ j.castSucc < s ∧ s ≤ H₁.mergedπ H₂ j.succ
          then H₁.ξ (H₁.mergedIdxMap_left H₂ h_eq j) ω else 0)
        - (∑ j : Fin (H₁.mergedM H₂),
          if H₁.mergedπ H₂ j.castSucc < s ∧ s ≤ H₁.mergedπ H₂ j.succ
          then H₂.ξ (H₁.mergedIdxMap_right H₂ h_eq j) ω else 0)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h_cond : H₁.mergedπ H₂ j.castSucc < s ∧ s ≤ H₁.mergedπ H₂ j.succ
  · simp [h_cond]
  · simp [h_cond]

/-- **C0b.8-pre: adaptedness of `sub_on_common`.** If both inputs are
adapted to a filtration `ℱ`, so is `sub_on_common`. The
proof: for each merged tile `j`, the input adaptedness gives StronglyMeas
at `H_k.partition (idxMap_k j).castSucc`. By `Filtration.mono` and
`mergedIdxMap_k_idx_le` (which says `H_k.partition (idxMap_k j).castSucc
≤ mergedπ j.castSucc`), this upgrades to StronglyMeas at the merged
partition point. The difference is StronglyMeas via `StronglyMeasurable.sub`. -/
lemma SimplePredictable.sub_on_common_adapt
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (h_adapt₁ : ∀ i : Fin H₁.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H₁.partition i.castSucc)) (H₁.ξ i))
    (h_adapt₂ : ∀ i : Fin H₂.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H₂.partition i.castSucc)) (H₂.ξ i)) :
    ∀ j : Fin (H₁.sub_on_common H₂ h_eq).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ ((H₁.sub_on_common H₂ h_eq).partition j.castSucc))
        ((H₁.sub_on_common H₂ h_eq).ξ j) := by
  intro j
  have h_mono₁ := ℱ.mono
    (H₁.mergedIdxMap_left_idx_le H₂ h_eq j)
  have h_mono₂ := ℱ.mono
    (H₁.mergedIdxMap_right_idx_le H₂ h_eq j)
  have h₁ := (h_adapt₁ (H₁.mergedIdxMap_left H₂ h_eq j)).mono h_mono₁
  have h₂ := (h_adapt₂ (H₁.mergedIdxMap_right H₂ h_eq j)).mono h_mono₂
  exact h₁.sub h₂

/-- **C0b.8: L² isometry on the difference of simples (`diff isometry`).**
For two adapted simple integrands `H₁, H₂` sharing endpoint, the L² norm
squared of `∫H₁ dW − ∫H₂ dW` equals the (joint) L² norm squared of
`H₁.eval − H₂.eval` over `[0,T] × Ω`.

Direct consequence of `simpleIntegral_isometry` applied to `sub_on_common`,
combined with `simpleIntegral_sub_on_common` (LHS rewrite) and
`eval_sub_on_common` (RHS rewrite). The adaptedness of `sub_on_common`
follows from `sub_on_common_adapt`. -/
theorem SimplePredictable.diff_isometry_simple
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (hT : 0 < T) (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (h_adapt₁ : ∀ i : Fin H₁.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H₁.partition i.castSucc)) (H₁.ξ i))
    (h_adapt₂ : ∀ i : Fin H₂.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H₂.partition i.castSucc)) (H₂.ξ i)) :
    ∫⁻ ω, (‖simpleIntegral W H₁ T ω - simpleIntegral W H₂ T ω‖₊ : ℝ≥0∞) ^ 2
      ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H₁.eval s ω - H₂.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have h_LHS :
      ∫⁻ ω, (‖simpleIntegral W H₁ T ω - simpleIntegral W H₂ T ω‖₊
              : ℝ≥0∞) ^ 2 ∂P
        = ∫⁻ ω, (‖simpleIntegral W (H₁.sub_on_common H₂ h_eq) T ω‖₊
              : ℝ≥0∞) ^ 2 ∂P := by
    refine MeasureTheory.lintegral_congr (fun ω => ?_)
    rw [SimplePredictable.simpleIntegral_sub_on_common W H₁ H₂ h_eq ω]
  have h_RHS :
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H₁.eval s ω - H₂.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖((H₁.sub_on_common H₂ h_eq).eval s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        by
    refine MeasureTheory.lintegral_congr (fun ω => ?_)
    refine MeasureTheory.setLIntegral_congr_fun measurableSet_Icc
      (fun s _ => ?_)
    rw [SimplePredictable.eval_sub_on_common H₁ H₂ h_eq s ω]
  rw [h_LHS, h_RHS]
  exact simpleIntegral_isometry W ℱ hℱ hT (H₁.sub_on_common H₂ h_eq)
    (SimplePredictable.sub_on_common_adapt ℱ H₁ H₂ h_eq h_adapt₁ h_adapt₂)

/-- **C0b.9: Cauchy preservation for `simpleIntegral`.** If an
eval-sequence of adapted simple integrands sharing a common endpoint is
`L²(λ⊗P)`-Cauchy (in ε-`N` form on the squared `lintegral`), then the
sequence of `simpleIntegral`s is `L²(P)`-Cauchy.

Direct corollary of `diff_isometry_simple` applied pairwise: each
pairwise distance on the integral side equals the corresponding pairwise
distance on the eval side, so the eval-Cauchy ε-`N` witness `N` works
verbatim for the integrals. -/
theorem cauchy_of_L2_dense_simple
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (hT : 0 < T)
    (G : ℕ → SimplePredictable Ω T)
    (h_eq : ∀ n m : ℕ,
      (G n).partition (Fin.last (G n).N)
        = (G m).partition (Fin.last (G m).N))
    (h_adapt : ∀ n : ℕ, ∀ i : Fin (G n).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ ((G n).partition i.castSucc)) ((G n).ξ i))
    (h_cauchy_eval : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ,
      N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(G n).eval s ω - (G m).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ,
      N ≤ n → N ≤ m →
      ∫⁻ ω, (‖simpleIntegral W (G n) T ω - simpleIntegral W (G m) T ω‖₊
              : ℝ≥0∞) ^ 2 ∂P < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := h_cauchy_eval ε hε
  refine ⟨N, fun n m hn hm => ?_⟩
  rw [SimplePredictable.diff_isometry_simple W ℱ hℱ hT (G n) (G m)
        (h_eq n m) (h_adapt n) (h_adapt m)]
  exact hN n m hn hm

end LevyStochCalc.Brownian.Ito
