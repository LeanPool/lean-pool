/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliarySlaterGroundState.lean.
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

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliarySlaterLabels
public import LeanPool.GinibrePoincare.Analysis.GinibreCenterProjectionGaussian

/-!
# Correspondence auxiliary Slater ground state

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `slater_minimal_ground_eq_signed_normalized`.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- The exceptional increasing Slater tuple is exactly the normalized
Vandermonde ground state `U1`, including its actual measure normalization. -/
theorem slater_canonical_ground_eq_normalized {n : ℕ} (hn : 0 < n)
    (z : Configuration n) :
    slaterDeterminant hn ((fun i : Fin n => i.val), 0) z =
      normalizedVandermondeTransform n (fun _ => 1) z := by
  let c : ℝ := (Real.sqrt (slaterMultiplicity n))⁻¹ *
    ∏ i : Fin n, ComplexHermite.oneDimNormalization n i.val
  have hc : 0 < c := by
    apply mul_pos
    · exact inv_pos.mpr (Real.sqrt_pos.mpr (slaterMultiplicity_pos n))
    · apply Finset.prod_pos
      intro i hi
      unfold ComplexHermite.oneDimNormalization
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
  have hg : 0 < groundStateNormalization n := by
    apply Real.sqrt_pos.mpr
    exact ENNReal.toReal_pos (ginibreMassEvaluation n hn).1.ne'
      (ginibreMassEvaluation n hn).2.ne
  have hpoint (w : Configuration n) :
      slaterDeterminant hn ((fun i : Fin n => i.val), 0) w = (c : ℂ)*vandermonde w := by
    rw [slater_canonical_ground_determinant]
    simp [c, Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_inv]
  have heq : slaterL2 hn ((fun i : Fin n => i.val), 0) =
      ((c * groundStateNormalization n : ℝ) : ℂ) •
        normalizedVandermondeGroundStateL2 n hn := by
    apply Lp.ext
    filter_upwards [slaterL2_ae hn ((fun i : Fin n => i.val), 0),
      Lp.coeFn_smul ((c * groundStateNormalization n : ℝ) : ℂ)
        (normalizedVandermondeGroundStateL2 n hn),
      normalizedVandermondeGroundStateL2_coeFn n hn] with w hs hmul hv
    rw [hs, hmul, hpoint]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hv]
    simp only [ normalizedVandermondeMultiplier,
      Complex.ofReal_mul]
    field_simp [Complex.ofReal_ne_zero.mpr hg.ne']
  have hd : SlaterDistinct ((fun i : Fin n => i.val), (0 : Fin n → ℕ)) := by
    intro i j h
    exact Fin.val_injective (congrArg Prod.fst h)
  have hnorm := slaterL2_norm_eq_one hn ((fun i : Fin n => i.val), 0) hd
  have hgnorm : ‖normalizedVandermondeGroundStateL2 n hn‖ = 1 := by
    have h := normalizedVandermondeGroundState_norm_sq n hn
    nlinarith [norm_nonneg (normalizedVandermondeGroundStateL2 n hn)]
  rw [heq, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos hc hg), hgnorm, mul_one] at hnorm
  rw [hpoint, normalizedVandermondeTransform_apply]
  simp only [mul_one]
  congr 1
  rw [← Complex.ofReal_inv]
  have hc_inv : c = (groundStateNormalization n)⁻¹ := by
    apply (mul_right_cancel₀ hg.ne')
    rw [inv_mul_cancel₀ hg.ne', hnorm]
  exact congrArg Complex.ofReal hc_inv

/-- Reordering orbital rows multiplies the actual determinant by the
permutation sign. -/
theorem slater_holomorphic_labels_permute {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℕ) (σ : ParticlePermutation n) (z : Configuration n) :
    slaterDeterminant hn (p ∘ σ, 0) z =
      permutationSign σ * slaterDeterminant hn (p, 0) z := by
  unfold slaterDeterminant
  let M := Matrix.of (fun i j : Fin n =>
    ComplexHermite.normalizedEval n hn (p i) 0 (z j))
  change (Real.sqrt (slaterMultiplicity n) : ℂ)⁻¹ * (M.submatrix σ id).det =
    permutationSign σ * ((Real.sqrt (slaterMultiplicity n) : ℂ)⁻¹ * M.det)
  rw [Matrix.det_permute]
  simp only [permutationSign]
  ring

/-- Every exceptional minimal tuple is `U1` with exactly the sign of its
orbital ordering, as asserted after equation (4.6). -/
theorem slater_minimal_ground_eq_signed_normalized {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℕ) (hp : Function.Injective p)
    (hdegree : (∑ i, p i) = n * (n - 1) / 2) :
    ∃ σ : ParticlePermutation n, (∀ i, p i = (σ i).val) ∧
      ∀ z : Configuration n, slaterDeterminant hn (p, 0) z =
        permutationSign σ * normalizedVandermondeTransform n (fun _ => 1) z := by
  classical
  have hrange := (slater_minimal_degree_iff p hp).mp hdegree
  have hlt (i : Fin n) : p i < n := by
    have hmem : p i ∈ Finset.univ.image p := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    rw [hrange] at hmem
    exact Finset.mem_range.mp hmem
  let f : Fin n → Fin n := fun i => ⟨p i, hlt i⟩
  have hf : Function.Injective f := by
    intro i j h
    apply hp
    exact congrArg Fin.val h
  let σ : ParticlePermutation n := Equiv.ofBijective f
    ⟨hf, (Finite.surjective_of_injective hf)⟩
  refine ⟨σ, fun i => rfl,?_⟩
  intro z
  have hlabel : p = Fin.val ∘ σ := rfl
  rw [hlabel, slater_holomorphic_labels_permute,
    slater_canonical_ground_eq_normalized]

end
end GinibrePoincare
