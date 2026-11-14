/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.Arithmetic
import Mathlib.Tactic.Positivity

/-! # Finite covers of Lipschitz images of a cube

A mesh with denominator `N` covers the unit cube within distance `1/N`.
This supplies explicit covering cardinalities for the boundary charts used in
quantitative lattice counting.
-/

@[expose] public section

namespace NairTenenbaum

open Finset
open scoped NNReal

variable {ι : Type*} [Fintype ι]

/-- The grid point associated with an index in the subdivision of the unit cube. -/
noncomputable def cubeGridPoint (N : ℕ) (j : ι → Fin (N + 1)) : ι → ℝ :=
  fun i => (j i : ℕ) / (N : ℝ)

omit [Fintype ι] in
theorem cubeGridPoint_mem {N : ℕ} (hN : 0 < N) (j : ι → Fin (N + 1)) :
    cubeGridPoint N j ∈ Set.Icc (fun _ : ι => (0 : ℝ)) (fun _ => 1) := by
  constructor
  · intro i
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro i
    apply (div_le_one (Nat.cast_pos.mpr hN)).mpr
    change ((j i : ℕ) : ℝ) ≤ (N : ℝ)
    exact Nat.cast_le.mpr (Nat.le_of_lt_succ (j i).isLt)

theorem exists_cubeGridPoint_dist_le {N : ℕ} (hN : 0 < N) {x : ι → ℝ}
    (hx : x ∈ Set.Icc (fun _ : ι => (0 : ℝ)) (fun _ => 1)) :
    ∃ j : ι → Fin (N + 1), dist x (cubeGridPoint N j) ≤ 1 / (N : ℝ) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hfloor (i : ι) : ⌊(N : ℝ) * x i⌋₊ ≤ N := by
    have H := Nat.floor_mono (mul_le_mul_of_nonneg_left (hx.2 i) hN0.le)
    simpa only [mul_one, Nat.floor_natCast] using H
  let j : ι → Fin (N + 1) := fun i => ⟨⌊(N : ℝ) * x i⌋₊, Nat.lt_succ_of_le (hfloor i)⟩
  refine ⟨j, ?_⟩
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  have hlo := Nat.floor_le (mul_nonneg hN0.le (hx.1 i))
  have hhi := Nat.lt_floor_add_one ((N : ℝ) * x i)
  change dist (x i) ((⌊(N : ℝ) * x i⌋₊ : ℝ) / N) ≤ 1 / N
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ((div_le_iff₀ hN0).mpr (by nlinarith)))]
  apply (le_div_iff₀ hN0).mpr
  have hcancel := div_mul_cancel₀ (⌊(N : ℝ) * x i⌋₊ : ℝ) hN0.ne'
  nlinarith

theorem exists_finset_lipschitz_cube_cover {E : Type*} [PseudoMetricSpace E]
    {f : (ι → ℝ) → E} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc (fun _ : ι => (0 : ℝ)) (fun _ => 1)))
    {N : ℕ} (hN : 0 < N) :
    ∃ S : Finset E, S.card ≤ (N + 1) ^ Fintype.card ι ∧
      (↑S : Set E) ⊆ f '' Set.Icc (fun _ : ι => (0 : ℝ)) (fun _ => 1) ∧
      ∀ y ∈ f '' Set.Icc (fun _ : ι => (0 : ℝ)) (fun _ => 1),
        ∃ z ∈ S, dist y z ≤ (L : ℝ) / N := by
  classical
  let S := Finset.univ.image (fun j : ι → Fin (N + 1) => f (cubeGridPoint N j))
  refine ⟨S, ?_, ?_, ?_⟩
  · exact (Finset.card_image_le).trans_eq (by simp)
  · intro z hz
    obtain ⟨j, _, rfl⟩ := mem_image.mp hz
    exact ⟨cubeGridPoint N j, cubeGridPoint_mem hN j, rfl⟩
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨j, hj⟩ := exists_cubeGridPoint_dist_le hN hx
    refine ⟨f (cubeGridPoint N j), mem_image.mpr ⟨j, mem_univ _, rfl⟩, ?_⟩
    calc
      _ ≤ (L : ℝ) * dist x (cubeGridPoint N j) := hf.dist_le_mul x hx _ (cubeGridPoint_mem hN j)
      _ ≤ (L : ℝ) * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_left hj L.coe_nonneg
      _ = _ := by ring

theorem exists_finset_scaled_lipschitz_cube_cover {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : (ι → ℝ) → E} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc (fun _ : ι => (0 : ℝ)) (fun _ => 1)))
    {t : ℝ} (ht : 1 ≤ t) :
    ∃ S : Finset E, (S.card : ℝ) ≤ (3 * t) ^ Fintype.card ι ∧
      (↑S : Set E) ⊆ (fun x => t • f x) '' Set.Icc (fun _ : ι => (0 : ℝ)) (fun _ => 1) ∧
      ∀ y ∈ (fun x => t • f x) '' Set.Icc (fun _ : ι => (0 : ℝ)) (fun _ => 1),
        ∃ z ∈ S, dist y z ≤ (L : ℝ) := by
  classical
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hN : 0 < ⌈t⌉₊ := Nat.ceil_pos.mpr ht0
  obtain ⟨S, hcard, hsub, hcover⟩ := exists_finset_lipschitz_cube_cover hf hN
  refine ⟨S.image (fun z => t • z), ?_, ?_, ?_⟩
  · calc
      _ ≤ (S.card : ℝ) := Nat.cast_le.mpr card_image_le
      _ ≤ ((⌈t⌉₊ + 1 : ℕ) : ℝ) ^ Fintype.card ι := by exact_mod_cast hcard
      _ ≤ _ := by
        apply pow_le_pow_left₀ (Nat.cast_nonneg _)
        rw [Nat.cast_add, Nat.cast_one]
        have H := Nat.ceil_lt_add_one ht0.le
        linarith
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    obtain ⟨x, hx, rfl⟩ := hsub hw
    exact ⟨x, hx, rfl⟩
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hdist⟩ := hcover (f x) ⟨x, hx, rfl⟩
    refine ⟨t • z, mem_image.mpr ⟨z, hz, rfl⟩, ?_⟩
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos ht0]
    calc
      _ ≤ t * ((L : ℝ) / ⌈t⌉₊) := mul_le_mul_of_nonneg_left hdist ht0.le
      _ ≤ (⌈t⌉₊ : ℝ) * ((L : ℝ) / ⌈t⌉₊) :=
        mul_le_mul_of_nonneg_right (Nat.le_ceil t) (div_nonneg L.coe_nonneg (Nat.cast_nonneg _))
      _ = _ := mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hN.ne')

end NairTenenbaum
