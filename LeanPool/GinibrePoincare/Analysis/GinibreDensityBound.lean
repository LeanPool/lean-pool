/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreDensityBound.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreDistributionalGradient

/-! # Global boundedness of the actual Ginibre density

A polynomial bound for the Vandermonde square, absorbed by the Gaussian
exponential, yields finite domination by Lebesgue measure.
-/


@[expose] public section


open MeasureTheory Filter
open scoped BigOperators ENNReal
namespace GinibrePoincare
noncomputable section

/-- A convenient polynomial upper bound for the squared Vandermonde. -/
theorem vandermondeWeight_le_radius_bound (n : ℕ) (z : Configuration n) :
    vandermondeWeight z ≤ (4 * (configurationNormSq z + 1)) ^ (n * n) := by
  classical
  let S := configurationNormSq z
  let B := 4 * (S + 1)
  have hS : 0 ≤ S := configurationNormSq_nonneg z
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hi (i : Fin n) : ‖z i‖ ^ 2 ≤ S := by
    rw [Complex.sq_norm]
    exact Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (z j)) (Finset.mem_univ i)
  have hd (i j : Fin n) : Complex.normSq (z j - z i) ≤ B := by
    rw [← Complex.sq_norm]
    have h := norm_sub_le (z j) (z i)
    have hsq := sq_le_sq₀ (norm_nonneg (z j - z i)) (add_nonneg (norm_nonneg _) (norm_nonneg _))
      |>.mpr h
    have hh := sq_nonneg (‖z j‖ - ‖z i‖)
    have hii := hi i
    have hjj := hi j
    dsimp [B]
    nlinarith
  rw [vandermondeWeight, vandermonde_eq_product]
  simp_rw [map_prod]
  calc
    _ ≤ ∏ i : Fin n, B ^ n := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Finset.prod_nonneg (fun j _ => Complex.normSq_nonneg _)
      · intro i _
        calc
          _ ≤ ∏ j ∈ Finset.Ioi i, B :=
            Finset.prod_le_prod₀ (fun j _ => Complex.normSq_nonneg _) (fun j _ => hd i j)
          _ = B ^ (Finset.Ioi i).card := by simp
          _ ≤ B ^ n := pow_le_pow_right₀ hB (by
            simpa using Finset.card_le_card (Finset.subset_univ (Finset.Ioi i)))
    _ = _ := by simp [B, S, ← pow_mul]

/-- The actual real Ginibre density is bounded globally by a finite constant. -/
theorem ginibreLebesgueDensityReal_bounded (n : ℕ) (hn : 0 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ginibreLebesgueDensityReal n z ≤ C := by
  let d := n * n
  let A := ((n : ℝ) / Real.pi) ^ n
  let C := A * (4 ^ d * (d.factorial : ℝ) * Real.exp 1)
  have hA : 0 ≤ A := pow_nonneg (div_nonneg (Nat.cast_nonneg n) Real.pi_pos.le) _
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro z
  let S := configurationNormSq z
  have hS : 0 ≤ S := configurationNormSq_nonneg z
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hf : (S + 1) ^ d ≤ (d.factorial : ℝ) * Real.exp (S + 1) := by
    have ht := Real.pow_div_factorial_le_exp (S + 1) (by linarith : 0 ≤ S + 1) d
    exact (div_le_iff₀ (by positivity : 0 < (d.factorial : ℝ))).mp ht |>.trans_eq (mul_comm _ _)
  have he : Real.exp (S + 1) * Real.exp (-(n : ℝ) * S) ≤ Real.exp 1 := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hw := vandermondeWeight_le_radius_bound n z
  change ginibreLebesgueDensityReal n z ≤ A * (4 ^ d * (d.factorial : ℝ) * Real.exp 1)
  unfold ginibreLebesgueDensityReal gaussianWeight
  calc
    _ ≤ A * (4 * (S + 1)) ^ d * Real.exp (-(n : ℝ) * S) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw hA) (Real.exp_pos _).le
    _ ≤ A * (4 ^ d * ((d.factorial : ℝ) * Real.exp (S + 1))) * Real.exp (-(n : ℝ) * S) := by
      rw [mul_pow]
      gcongr
    _ = A * (4 ^ d * (d.factorial : ℝ)) *
        (Real.exp (S + 1) * Real.exp (-(n : ℝ) * S)) := by ring
    _ ≤ _ := by
      have hp : 0 ≤ A * (4 ^ d * (d.factorial : ℝ)) := by positivity
      calc
        _ ≤ A * (4 ^ d * (d.factorial : ℝ)) * Real.exp 1 :=
          mul_le_mul_of_nonneg_left he hp
        _ = _ := by ring

/-- The normalized Ginibre measure is bounded by a finite multiple of Lebesgue
measure, including on the collision locus. -/
theorem ginibreMeasure_le_finite_smul_volume (n : ℕ) (hn : 0 < n) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ ginibreMeasure n ≤ c • (volume : Measure (Configuration n)) := by
  obtain ⟨C, hC, hb⟩ := ginibreLebesgueDensityReal_bounded n hn
  refine ⟨(ginibreNormalizingMass n)⁻¹ * ENNReal.ofReal C, ?_, ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (ginibreMassEvaluation n hn).1.ne')
      ENNReal.ofReal_ne_top
  · rw [ginibreMeasure_eq_real_withDensity hn, mul_smul]
    apply _root_.smul_le_smul_left
    rw [← withDensity_const]
    exact withDensity_mono (ae_of_all _ (fun z => ENNReal.ofReal_le_ofReal (hb z)))

/-- Every ordinary Lebesgue L² function belongs to actual Ginibre L². -/
theorem memLp_ginibre_of_volume (n : ℕ) (hn : 0 < n)
    {V : Type*} [NormedAddCommGroup V] (f : Configuration n → V)
    (hf : MemLp f 2 volume) : MemLp f 2 (ginibreMeasure n) := by
  obtain ⟨c, hc, hm⟩ := ginibreMeasure_le_finite_smul_volume n hn
  exact hf.of_measure_le_smul hc hm

end
end GinibrePoincare
