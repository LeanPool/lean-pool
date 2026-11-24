/-
Copyright (c) 2026 Mike Lady. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Lady
-/

-- Modified for Lean Pool.

module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Convex.Measure

/-!
# Volume of an interior-disjoint union of convex pieces

The boundary of each convex piece has Haar measure zero. Replace each piece
by its interior, preserving the volume of the countable union and the
individual volumes. The interiors are measurable and pairwise disjoint,
so their volumes add.
-/

@[expose] public section

namespace TetrahedronPacking

open Filter MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise Topology

theorem measure_iUnion_of_disjoint_convex_interiors
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ]
    {ι : Type*} [Countable ι] (s : ι → Set E) (hc : ∀ i, Convex ℝ (s i))
    (hd : Pairwise fun i j => Disjoint (interior (s i)) (interior (s j))) :
    μ (⋃ i, s i) = ∑' i, μ (s i) := by
  have heq (i : ι) : interior (s i) =ᵐ[μ] s i :=
    interior_ae_eq_of_null_frontier ((hc i).addHaar_frontier μ)
  calc
    μ (⋃ i, s i) = μ (⋃ i, interior (s i)) :=
      (measure_congr (EventuallyEqSet.countable_iUnion heq)).symm
    _ = ∑' i, μ (interior (s i)) :=
      measure_iUnion hd (fun _ => isOpen_interior.measurableSet)
    _ = ∑' i, μ (s i) := tsum_congr (fun i => measure_congr (heq i))

/-- To bound coverage of a ball of radius `R`, count whole copies for
translations of norm at most `R - d` and discard translations of norm
greater than `R + d`, where every motif is contained in the radius-`d` ball.
For the sup norm on coordinate space the balls are cubes. -/
theorem covered_window_sandwich
    {E : Type*} [NormedAddCommGroup E] {ι κ : Type*}
    (s : ι → Set E) (t : κ → E) (R d : ℝ)
    (hs : ∀ i x, x ∈ s i → ‖x‖ ≤ d) :
    let inside := ⋃ p : ι × {j // ‖t j‖ ≤ R - d}, t p.2.val +ᵥ s p.1
    let covered := (⋃ p : ι × κ, t p.2 +ᵥ s p.1) ∩ Metric.closedBall 0 R
    let outside := ⋃ p : ι × {j // ‖t j‖ ≤ R + d}, t p.2.val +ᵥ s p.1
    inside ⊆ covered ∧ covered ⊆ outside := by
  dsimp only
  constructor
  · intro x hx
    simp only [mem_iUnion, mem_vadd_set, vadd_eq_add] at hx
    obtain ⟨⟨i, j⟩, y, hy, rfl⟩ := hx
    refine ⟨mem_iUnion.mpr ⟨(i, j.val), mem_vadd_set.mpr ⟨y, hy, rfl⟩⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖t j.val + y‖ ≤ ‖t j.val‖ + ‖y‖ := norm_add_le _ _
      _ ≤ R - d + d := add_le_add j.property (hs i y hy)
      _ = R := sub_add_cancel _ _
  · intro x hx
    obtain ⟨hu, hR⟩ := hx
    simp only [mem_iUnion, mem_vadd_set, vadd_eq_add] at hu
    obtain ⟨⟨i, j⟩, y, hy, rfl⟩ := hu
    rw [Metric.mem_closedBall, dist_zero_right] at hR
    have hj : ‖t j‖ ≤ R + d := calc
      ‖t j‖ = ‖(t j + y) - y‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖t j + y‖ + ‖y‖ := norm_sub_le _ _
      _ ≤ R + d := add_le_add hR (hs i y hy)
    exact mem_iUnion.mpr ⟨(i, ⟨j, hj⟩), mem_vadd_set.mpr ⟨y, hy, rfl⟩⟩

/-- Lattice point counts in coordinate cubes, along real radii. Apply
Mathlib's homogeneous-sublevel counting theorem to the dimensionth power
of the sup norm, then substitute the same power of the radius. -/
theorem lattice_count_in_coordinate_cubes
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L] :
    Tendsto (fun R : ℝ =>
      (Nat.card ((Metric.closedBall (0 : κ → ℝ) R) ∩ L : Set (κ → ℝ)) : ℝ) /
        R ^ Fintype.card κ) atTop
      (𝓝 (volume.real (Metric.closedBall (0 : κ → ℝ) 1) / ZLattice.covolume L)) := by
  let n := Fintype.card κ
  have hn : n ≠ 0 := Fintype.card_ne_zero
  have hball (R : ℝ) (hR : 0 ≤ R) :
      {x : κ → ℝ | x ∈ (univ : Set (κ → ℝ)) ∧ ‖x‖ ^ n ≤ R ^ n} =
        Metric.closedBall 0 R := by
    ext x
    simp only [mem_ofPred_eq, mem_univ, true_and, Metric.mem_closedBall, dist_zero_right]
    exact pow_le_pow_iff_left₀ (norm_nonneg x) hR hn
  have hball_one : {x : κ → ℝ | x ∈ (univ : Set (κ → ℝ)) ∧ ‖x‖ ^ n ≤ 1} =
      Metric.closedBall 0 1 := by simpa using hball 1 zero_le_one
  have h := ZLattice.covolume.tendsto_card_le_div L
    (X := univ) (F := fun x => ‖x‖ ^ n)
    (fun _ _ _ _ => mem_univ _)
    (fun x R hR => by
      change ‖R • x‖ ^ n = R ^ n * ‖x‖ ^ n
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hR, mul_pow])
    (hball_one ▸ Metric.isBounded_closedBall) (hball_one ▸ Metric.isClosed_closedBall.measurableSet)
    (hball_one ▸ (convex_closedBall (0 : κ → ℝ) 1).addHaar_frontier volume)
  rw [hball_one] at h
  refine (h.comp (tendsto_pow_atTop hn)).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  simp only [Function.comp_apply, hball R hR, n]

end TetrahedronPacking
