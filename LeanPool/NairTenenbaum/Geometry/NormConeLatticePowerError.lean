/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Geometry.LatticeCoordinateCount
public import LeanPool.NairTenenbaum.Geometry.NormLeOneBoundaryCharts
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

/-! # Power-saving lattice count in the number-field fundamental cone

A norm cutoff `x` is a dilation of the norm-one region by `x^(1/degree)`.
The boundary count therefore has exponent `(degree-1)/degree`.
-/

@[expose] public section

namespace NairTenenbaum

open NumberField NumberField.mixedEmbedding fundamentalCone Module MeasureTheory
open scoped Pointwise

variable (K : Type*) [Field K] [NumberField K]

theorem smul_normLeOne {t : ℝ} (ht : 0 < t) :
    t • normLeOne K = {x : mixedSpace K | x ∈ fundamentalCone K ∧
      mixedEmbedding.norm x ≤ t ^ Module.finrank ℚ K} := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne', mem_normLeOne,
    smul_mem_iff_mem (inv_ne_zero ht.ne'), mixedEmbedding.norm_smul,
    abs_inv, abs_of_pos ht, inv_pow, inv_mul_le_iff₀ (pow_pos ht _), mul_one]
  rfl

open Classical in
theorem exists_normCone_lattice_power_error
    {L : Submodule ℤ (mixedSpace K)} [DiscreteTopology L] [IsZLattice ℝ (E := mixedSpace K) L]
    {ι : Type*} [Finite ι] (b : Basis ι ℤ L) :
    ∃ V C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |(Nat.card {a : L // (a : mixedSpace K) ∈ fundamentalCone K ∧
          mixedEmbedding.norm (a : mixedSpace K) ≤ x} : ℝ) - V * x| ≤
        C * x ^ ((Module.finrank ℚ K - 1 : ℕ) / (Module.finrank ℚ K : ℝ)) := by
  cases nonempty_fintype ι
  let e := (b.ofZLatticeBasis ℝ).equivFunL
  obtain ⟨C, hC, HC⟩ := exists_coordinate_normLeOne_lattice_error K e
  have hdim : Fintype.card ι = Module.finrank ℚ K :=
    (Module.finrank_eq_card_basis (b.ofZLatticeBasis ℝ)).symm.trans (mixedEmbedding.finrank K)
  refine ⟨volume.real (e '' normLeOne K), C, hC, fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hd : Module.finrank ℚ K ≠ 0 := Module.finrank_pos.ne'
  have hdR : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  let t : ℝ := x ^ (Module.finrank ℚ K : ℝ)⁻¹
  have ht0 : 0 < t := Real.rpow_pos_of_pos hx0 _
  have ht : 1 ≤ t := Real.one_le_rpow hx (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hpow : t ^ Module.finrank ℚ K = x := Real.rpow_inv_natCast_pow hx0.le hd
  have hset : t • normLeOne K = {a : mixedSpace K | a ∈ fundamentalCone K ∧ mixedEmbedding.norm a
      ≤ x} := by
    rw [smul_normLeOne K ht0, hpow]
  have H := HC t ht
  rw [hdim, hpow, ← image_smul_set e t (normLeOne K), hset] at H
  have hcount : integerLatticeCount (e '' {a : mixedSpace K |
      a ∈ fundamentalCone K ∧ mixedEmbedding.norm a ≤ x}) =
      Nat.card {a : L // (a : mixedSpace K) ∈ fundamentalCone K ∧
        mixedEmbedding.norm (a : mixedSpace K) ≤ x} := integerLatticeCount_basis_image b _
  rw [hcount] at H
  have herrorpow : t ^ (Module.finrank ℚ K - 1) =
      x ^ ((Module.finrank ℚ K - 1 : ℕ) / (Module.finrank ℚ K : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1
    ring
  rw [herrorpow, mul_comm x] at H
  exact H

end NairTenenbaum
