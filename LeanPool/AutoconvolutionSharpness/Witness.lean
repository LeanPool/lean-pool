/-
Copyright (c) 2026 Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić
-/
module

public import LeanPool.AutoconvolutionSharpness.BlockExpansion
public import LeanPool.AutoconvolutionSharpness.Estimate
public import LeanPool.AutoconvolutionSharpness.Flat

/-!
# The polynomial witness for autoconvolution sharpness
-/

@[expose] public section

open Finset Polynomial
open scoped BigOperators

namespace Autoconvolutions.Construction

/-- The actual polynomial F of §2 for a pair of alphabets. -/
noncomputable def witness {m : ℕ} (D n K : ℕ) (I J : Finset (Fin m)) : Polynomial ℝ :=
  family Flat.P (Blocks.gen D I) (Blocks.gen D J) n K

/-- The evaluation of the witness at one is the mass before autoconvolution. -/
theorem eval_witness {m n K D : ℕ} (I J : Finset (Fin m)) (hK : K ≤ n) (hI : 0 < I.card) :
    (witness D n K I J).eval 1 =
    ((I.card : ℝ) * J.card) ^ n * ∑ i ∈ range (K + 1), ((J.card : ℝ) / I.card) ^ i := by
  unfold witness
  rw [eval_family_one _ _ _ hK Flat.P_eval_one (by simpa using hI.ne')]
  simp

theorem witness_nonneg {m n K D : ℕ} (I J : Finset (Fin m)) (k : ℕ) :
    0 ≤ (witness D n K I J).coeff k := by
  have gen_pos (S : Finset (Fin m)) (j : ℕ) : 0 ≤ (Blocks.gen D S).coeff j := by
    simp only [Blocks.gen, finsetSum_coeff, coeff_X_pow]
    apply sum_nonneg
    intro i _
    split <;> simp
  exact family_nonneg_coeff Flat.P Flat.P_coeff_nonneg (gen_pos I) (gen_pos J) n K k

theorem eval_witness_pos {m n K D : ℕ} (I J : Finset (Fin m))
    (hK : K ≤ n) (hI : 0 < I.card) (hJ : 0 < J.card) : 0 < (witness D n K I J).eval 1 := by
  rw [eval_witness I J hK hI]
  apply mul_pos (by positivity)
  have hq : 0 ≤ (J.card : ℝ) / I.card := by positivity
  exact lt_of_lt_of_le (by positivity) (single_le_sum (f := fun i : ℕ => ((J.card : ℝ) / I.card) ^
      i)
    (fun i _ => pow_nonneg hq i) (a := 0) (by simp))

end Autoconvolutions.Construction
