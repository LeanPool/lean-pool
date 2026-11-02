/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Geometry.IntegerLatticeBallBound
public import LeanPool.NairTenenbaum.Geometry.LipschitzCubeCover
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Positivity

/-! # Lattice points near an expanding Lipschitz chart

A chart with `m` real parameters has `O(t^m)` integer lattice points within a
fixed distance of its dilation by `t`. This is the boundary-cell estimate
needed for quantitative lattice counting.
-/

@[expose] public section

namespace NairTenenbaum

open Finset
open scoped NNReal

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem card_integerLattice_near_scaled_chart_le {f : (ι → ℝ) → (κ → ℝ)} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc (fun _ : ι => (0 : ℝ)) (fun _ => 1)))
    {R t : ℝ} (hR : 0 ≤ R) (ht : 1 ≤ t) (A : Finset (κ → ℤ))
    (hA : ∀ m ∈ A, ∃ x ∈ Set.Icc (fun _ : ι => (0 : ℝ)) (fun _ => 1),
      dist (integerLatticePoint m) (t • f x) ≤ R) :
    (A.card : ℝ) ≤ (3 * t) ^ Fintype.card ι *
      ((⌈2 * (R + (L : ℝ))⌉₊ + 1 : ℕ) : ℝ) ^ Fintype.card κ := by
  obtain ⟨S, hcard, _, hcover⟩ := exists_finset_scaled_lipschitz_cube_cover hf ht
  have H := card_integerLattice_near_cover_le A S (add_nonneg hR L.coe_nonneg) (fun m hm => ?_)
  · calc
      _ ≤ (S.card : ℝ) * ((⌈2 * (R + (L : ℝ))⌉₊ + 1 : ℕ) : ℝ) ^ Fintype.card κ := by
        exact_mod_cast H
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
  · obtain ⟨x, hx, hmx⟩ := hA m hm
    obtain ⟨z, hz, hxz⟩ := hcover (t • f x) ⟨x, hx, rfl⟩
    exact ⟨z, hz, (dist_triangle _ _ _).trans (add_le_add hmx hxz)⟩

theorem exists_integerLattice_near_scaled_chart_bound {f : (ι → ℝ) → (κ → ℝ)} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc (fun _ : ι => (0 : ℝ)) (fun _ => 1)))
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → ∀ A : Finset (κ → ℤ),
      (∀ m ∈ A, ∃ x ∈ Set.Icc (fun _ : ι => (0 : ℝ)) (fun _ => 1),
        dist (integerLatticePoint m) (t • f x) ≤ R) →
      (A.card : ℝ) ≤ C * t ^ Fintype.card ι := by
  refine ⟨3 ^ Fintype.card ι *
    ((⌈2 * (R + (L : ℝ))⌉₊ + 1 : ℕ) : ℝ) ^ Fintype.card κ,
    by positivity, fun t ht A hA => ?_⟩
  convert card_integerLattice_near_scaled_chart_le hf hR ht A hA using 1
  rw [mul_pow]
  ring

end NairTenenbaum
