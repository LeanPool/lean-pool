/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Tactic.LinearCombination
public import LeanPool.AaronsonAmbainis.RowDefs

/-!
# Duality between packings and rows: the three sets

* `massSet ι K`  — the polytope `P = {a ≥ 0, ∑ a ≤ K}` in `ι → ℝ` (compact, convex);
* `slack t`      — the affine map `a ↦ (S ↦ a(S) - t S)` into `Finset ι → ℝ`;
* `orthant ι`    — the closed convex cone `V₊ = {v ≥ 0}` in `Finset ι → ℝ`.

They are used in the proof of the duality statement (Proposition 6.7 of the paper), which is
`Dual.exists_cover` in `Dual/Cover.lean`. The image of `P` under the slack map is the set `C` of
the proof in the paper.
-/

@[expose] public section

namespace AaronsonAmbainis
namespace Dual

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `P = {a : a ≥ 0, ∑ a ≤ K}`. -/
def massSet (ι : Type*) [Fintype ι] (K : ℝ) : Set (ι → ℝ) :=
  {a | (∀ i, 0 ≤ a i) ∧ ∑ i, a i ≤ K}

/-- The slack of `a` against the demands `t`: `S ↦ a(S) - t S`. -/
def slack (t : Finset ι → ℝ) (a : ι → ℝ) : Finset ι → ℝ :=
  fun S => ∑ i ∈ S, a i - t S

/-- The nonnegative orthant of `Finset ι → ℝ`. -/
def orthant (ι : Type*) : Set (Finset ι → ℝ) := {v | ∀ S, 0 ≤ v S}

omit [DecidableEq ι] in
theorem massSet_convex (K : ℝ) : Convex ℝ (massSet ι K) := by
  rintro a ⟨ha0, haK⟩ b ⟨hb0, hbK⟩ s r hs hr hsr
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hs (ha0 i)) (mul_nonneg hr (hb0 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    calc s * ∑ i, a i + r * ∑ i, b i
        ≤ s * K + r * K :=
          add_le_add (mul_le_mul_of_nonneg_left haK hs) (mul_le_mul_of_nonneg_left hbK hr)
      _ = K := by rw [← add_mul, hsr, one_mul]

omit [DecidableEq ι] in
theorem massSet_isClosed (K : ℝ) : IsClosed (massSet ι K) := by
  have h : massSet ι K = (⋂ i, {a : ι → ℝ | 0 ≤ a i}) ∩ {a : ι → ℝ | ∑ i, a i ≤ K} := by
    ext a
    simp [massSet]
  rw [h]
  exact IsClosed.inter
    (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i))
    (isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)

omit [DecidableEq ι] in
theorem massSet_isCompact (K : ℝ) : IsCompact (massSet ι K) := by
  have hsub : massSet ι K ⊆ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) K) := by
    intro a ha i _
    exact ⟨ha.1 i,
      le_trans (Finset.single_le_sum (fun j _ => ha.1 j) (Finset.mem_univ i)) ha.2⟩
  exact IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ => isCompact_Icc)
    (massSet_isClosed K) hsub

omit [Fintype ι] [DecidableEq ι] in
theorem slack_continuous (t : Finset ι → ℝ) : Continuous (slack t) :=
  continuous_pi fun _ =>
    (continuous_finsetSum _ fun i _ => continuous_apply i).sub continuous_const

omit [DecidableEq ι] in
theorem slackImage_convex (t : Finset ι → ℝ) (K : ℝ) :
    Convex ℝ (slack t '' massSet ι K) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ s r hs hr hsr
  refine ⟨s • a + r • b, massSet_convex K ha hb hs hr hsr, ?_⟩
  funext S
  simp only [slack, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  linear_combination (t S) * hsr

omit [DecidableEq ι] in
theorem slackImage_isCompact (t : Finset ι → ℝ) (K : ℝ) :
    IsCompact (slack t '' massSet ι K) :=
  (massSet_isCompact K).image (slack_continuous t)

omit [Fintype ι] [DecidableEq ι] in
theorem orthant_convex : Convex ℝ (orthant ι) := by
  intro v hv w hw s r hs hr _ S
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg hs (hv S)) (mul_nonneg hr (hw S))

omit [Fintype ι] [DecidableEq ι] in
theorem orthant_isClosed : IsClosed (orthant ι) := by
  have h : orthant ι = ⋂ S : Finset ι, {v : Finset ι → ℝ | 0 ≤ v S} := by
    ext v
    simp [orthant]
  rw [h]
  exact isClosed_iInter fun S => isClosed_le continuous_const (continuous_apply S)

end Dual
end AaronsonAmbainis
