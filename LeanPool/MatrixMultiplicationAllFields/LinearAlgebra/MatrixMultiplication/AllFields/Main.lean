/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
module

/-
Copyright 2026 Jeroen Zuiddam. Licensed under the Apache License, Version 2.0 (see LICENSE).
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AllFields.Descent
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Main
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Data.ZMod.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# `ω(F) ≤ 9/4` over every field

The auxiliary-separation argument is carried out over an arbitrary
algebraically closed field `K` (`AuxiliarySeparation.omega_le_nine_quarters`;
the only characteristic-dependent step, the Fourier separation, uses a period
`L ∈ {3M - 2, 3M - 1}` that is nonzero in `K` instead of the paper's `5M`).

For an arbitrary field `F` let `P` be its prime field (`ℚ` or `ZMod p`) and
`K = AlgebraicClosure P`.  A near-optimal decomposition of `⟨u,u,u⟩` over `K`
has its coefficients in a finite extension `E / P` of some degree `m`; tensor
powering over `E` and descending to `P` gives decompositions of
`⟨uʲ,uʲ,uʲ⟩` over `P` of size `m³ rʲ`, which map into `F`.  The constant
`m³` is absorbed by taking `j` large.  The field-generic block recursion then
gives the arithmetic bound over `F`.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AllFields

open AuxiliarySeparation

/-- If `F` receives a ring homomorphism from a field `P`, then `ω(F) ≤ 9/4`. -/
theorem omega_le_nine_quarters_of_ringHom (P : Type) [Field P] {F : Type*} [Field F]
    (f : P →+* F) : Arithmetic.omega F ≤ (9 : ℝ) / 4 := by
  classical
  apply omega_le_of_arbitrarily_close_rankBounds (by norm_num)
  intro δ hδ
  obtain ⟨u, r, hu, hrank, hr⟩ :=
    exists_rankAtMost_of_exponent_slack (K := AlgebraicClosure P) (half_pos hδ)
  have hu1 : (1 : ℝ) < u := by exact_mod_cast (show 1 < u by omega)
  have hr' : (r : ℝ) ≤ (u : ℝ) ^ ((9 : ℝ) / 4 + δ / 2) :=
    hr.trans (Real.rpow_le_rpow_of_exponent_le hu1.le
      (by linarith [exactRankExponent_le_nine_quarters (K := AlgebraicClosure P)]))
  have hK : Tensor.RankAtMost
      (fun x y z => algebraMap P (AlgebraicClosure P) (Tensor.matMul P u u u x y z)) r := by
    rw [matMul_map]
    exact hrank
  obtain ⟨E, hE, hrankE⟩ := exists_finiteDimensional_rankAtMost hK
  rw [matMul_map] at hrankE
  set m := Module.finrank P E with hm
  have hbase : (1 : ℝ) < (u : ℝ) ^ (δ / 2) := Real.one_lt_rpow hu1 (by linarith)
  obtain ⟨j0, hj0⟩ := pow_unbounded_of_one_lt ((m : ℝ) ^ 3) hbase
  set j := j0 + 1 with hj
  have hpowE := rankAtMost_matMul_pow hrankE j
  have hP : Tensor.RankAtMost (Tensor.matMul P (u ^ j) (u ^ j) (u ^ j)) (m ^ 3 * r ^ j) := by
    apply rankAtMost_of_map (E := E)
    rw [matMul_map]
    exact hpowE
  have hF := hP.map f
  rw [matMul_map] at hF
  refine ⟨u ^ j, m ^ 3 * r ^ j, ?_, hF, ?_⟩
  · exact hu.trans (Nat.le_self_pow (by omega) u)
  · have hm3 : (m : ℝ) ^ 3 ≤ ((u : ℝ) ^ (δ / 2)) ^ j :=
      hj0.le.trans (pow_le_pow_right₀ hbase.le (by omega))
    have hrj : (r : ℝ) ^ j ≤ ((u : ℝ) ^ ((9 : ℝ) / 4 + δ / 2)) ^ j :=
      pow_le_pow_left₀ (Nat.cast_nonneg r) hr' j
    have hu0 : (0 : ℝ) ≤ u := by positivity
    calc ((m ^ 3 * r ^ j : ℕ) : ℝ) = (m : ℝ) ^ 3 * (r : ℝ) ^ j := by push_cast; ring
      _ ≤ ((u : ℝ) ^ (δ / 2)) ^ j * ((u : ℝ) ^ ((9 : ℝ) / 4 + δ / 2)) ^ j :=
        mul_le_mul hm3 hrj (by positivity) (by positivity)
      _ = ((u : ℝ) ^ ((9 : ℝ) / 4 + δ)) ^ j := by
        rw [← mul_pow, ← Real.rpow_add (by positivity)]
        ring_nf
      _ = ((u ^ j : ℕ) : ℝ) ^ ((9 : ℝ) / 4 + δ) := by
        rw [Nat.cast_pow, Real.rpow_pow_comm hu0]

end MatrixMultiplication.AllFields

namespace MatrixMultiplication

/-- **The matrix multiplication exponent is at most `9/4` over every field.** -/
theorem omega_le_nine_quarters_all_fields (F : Type*) [Field F] :
    Arithmetic.omega F ≤ (9 : ℝ) / 4 := by
  rcases CharP.exists' F with h | ⟨p, hp, hc⟩
  · exact AllFields.omega_le_nine_quarters_of_ringHom ℚ (Rat.castHom F)
  · exact AllFields.omega_le_nine_quarters_of_ringHom (ZMod p) (ZMod.castHom (dvd_refl p) F)

/-- Non-vacuity: over every field the exponent `9/4` is itself admissible, i.e.
for every `ε > 0` one constant `C` bounds the cost of correct division-free
programs for `n × n` matrix multiplication by `C n^(9/4 + ε)` at every size. -/
theorem admissibleExponent_nine_quarters_all_fields (F : Type*) [Field F] :
    Arithmetic.AdmissibleExponent F ((9 : ℝ) / 4) :=
  Arithmetic.admissibleExponent_iff_omega_le.mpr (omega_le_nine_quarters_all_fields F)

/-- The unfolded form of the all-fields statement. -/
theorem matrix_multiplication_cost_le_all_fields (F : Type*) [Field F]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ P : Arithmetic.MatrixAlgorithm F n n n,
        P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ ((9 : ℝ) / 4 + ε) :=
  admissibleExponent_nine_quarters_all_fields F ε hε

end MatrixMultiplication

end

end MatrixMultiplicationAllFields
