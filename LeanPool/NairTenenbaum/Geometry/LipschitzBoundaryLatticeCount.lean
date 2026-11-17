/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Geometry.IntegerLatticeBoundary
public import LeanPool.NairTenenbaum.Geometry.LatticePointsNearChart
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Quantitative lattice counting for a finite Lipschitz boundary

A bounded subset of real coordinate space whose boundary is covered by finitely
many `m`-parameter Lipschitz charts has lattice discrepancy `O(t^m)` under
dilation by `t`. All chart and boundedness hypotheses are explicit.
-/

@[expose] public section

namespace NairTenenbaum

open Finset MeasureTheory
open scoped NNReal Pointwise

variable {ι κ J : Type*} [Fintype ι] [Fintype κ] [Fintype J]

/-- The number of integer lattice points in a set. -/
noncomputable def integerLatticeCount (s : Set (ι → ℝ)) : ℕ :=
  Nat.card {m : ι → ℤ // integerLatticePoint m ∈ s}

omit [Fintype ι] [Fintype κ] [Fintype J] in
theorem integerLatticeCount_eq_card {s : Set (ι → ℝ)} (A : Finset (ι → ℤ))
    (hA : ∀ m, m ∈ A ↔ integerLatticePoint m ∈ s) : integerLatticeCount s = A.card := by
  unfold integerLatticeCount
  calc
    _ = Nat.card {m : ι → ℤ // m ∈ A} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun m => (hA m).symm))
    _ = _ := by simp

omit [Fintype κ] [Fintype J] in
theorem volume_real_smul_coordinate_set {t : ℝ} (ht : 0 ≤ t) (s : Set (ι → ℝ)) :
    volume.real (t • s) = t ^ Fintype.card ι * volume.real s := by
  rw [measureReal_def, Measure.addHaar_smul_of_nonneg volume ht,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg ht _)]
  simp only [Module.finrank_fintype_fun_eq_card, measureReal_def]

omit [Fintype J] in
theorem exists_lipschitz_boundary_lattice_discrepancy [Finite J] {s : Set (ι → ℝ)}
    (hs : Bornology.IsBounded s) (f : J → (κ → ℝ) → (ι → ℝ)) (L : J → ℝ≥0)
    (hf : ∀ j, LipschitzOnWith (L j) (f j) (Set.Icc (fun _ : κ => (0 : ℝ)) (fun _ => 1)))
    (hcover : ∀ y ∈ frontier s, ∃ j x,
      x ∈ Set.Icc (fun _ : κ => (0 : ℝ)) (fun _ => 1) ∧ f j x = y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      |(integerLatticeCount (t • s) : ℝ) - t ^ Fintype.card ι * volume.real s| ≤
        C * t ^ Fintype.card κ := by
  classical
  cases nonempty_fintype J
  choose C hC HC using fun j => exists_integerLattice_near_scaled_chart_bound (hf j) zero_le_one
  refine ⟨∑ j, C j, sum_nonneg (fun j _ => hC j), fun t ht => ?_⟩
  obtain ⟨A, B, hA, herror, hB⟩ := exists_integerLattice_boundary_error (hs.smul₀ t)
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  let P := fun (j : J) (m : ι → ℤ) =>
    ∃ x ∈ Set.Icc (fun _ : κ => (0 : ℝ)) (fun _ => 1),
      dist (integerLatticePoint m) (t • f j x) ≤ 1
  have hBcover : ∀ m ∈ B, ∃ j, P j m := by
    intro m hm
    obtain ⟨y, hy, hmy⟩ := hB m hm
    have Heq : (fun z : ι → ℝ => t • z) '' frontier s = frontier (t • s) :=
      (Homeomorph.smulOfNeZero t ht0.ne').image_frontier s
    rw [← Heq] at hy
    obtain ⟨z, hzf, rfl⟩ := hy
    obtain ⟨j, x, hx, rfl⟩ := hcover z hzf
    exact ⟨j, x, hx, hmy⟩
  have hBsub : B ⊆ univ.biUnion (fun j : J => B.filter (P j)) := by
    intro m hm
    obtain ⟨j, hj⟩ := hBcover m hm
    exact mem_biUnion.mpr ⟨j, mem_univ _, mem_filter.mpr ⟨hm, hj⟩⟩
  have hBcard : (B.card : ℝ) ≤ (∑ j, C j) * t ^ Fintype.card κ := by
    calc
      _ ≤ ((univ.biUnion (fun j : J => B.filter (P j))).card : ℝ) :=
        Nat.cast_le.mpr (card_le_card hBsub)
      _ ≤ ∑ j : J, ((B.filter (P j)).card : ℝ) := by
        exact_mod_cast (card_biUnion_le (s := (univ : Finset J)) (t := fun j => B.filter (P j)))
      _ ≤ ∑ j : J, C j * t ^ Fintype.card κ := by
        apply sum_le_sum
        intro j _
        exact HC j t ht (B.filter (P j)) (fun m hm => (mem_filter.mp hm).2)
      _ = _ := by rw [sum_mul]
  rw [integerLatticeCount_eq_card A hA, ← volume_real_smul_coordinate_set ht0.le]
  exact herror.trans hBcard

end NairTenenbaum
