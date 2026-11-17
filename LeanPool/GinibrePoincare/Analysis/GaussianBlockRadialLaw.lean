/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianBlockRadialLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.RadialGradientTransfer
public import LeanPool.GinibrePoincare.Analysis.GinibreRadialGamma

/-!
# Gaussian Block Radial Law
-/


@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Pointwise
namespace GinibrePoincare
noncomputable section

/-- A `k`-dimensional complex Gaussian block with real variance `1/(2n)`. -/
def gaussianBlockMeasure (n k : ℕ) : Measure (Configuration k) :=
  Measure.pi (fun _ : Fin k => (complexCoordinateGaussianProbability n : Measure ℂ))

instance (n k : ℕ) : IsProbabilityMeasure (gaussianBlockMeasure n k) := by
  unfold gaussianBlockMeasure
  infer_instance

def gaussianBlockRadius (n k : ℕ) (x : Configuration k) : ℝ :=
  (n : ℝ) * configurationNormSq x

theorem continuous_gaussianBlockRadius (n k : ℕ) : Continuous (gaussianBlockRadius n k) := by
  unfold gaussianBlockRadius configurationNormSq
  fun_prop

private theorem volume_gaussianBlockRadius (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (volume : Measure (Configuration k)).map (gaussianBlockRadius n k) =
      ((k : ℝ≥0∞) * volume ((gaussianBlockRadius n k) ⁻¹' Iic 1)) • radialPowerMeasure k := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hcompact : IsCompact ((gaussianBlockRadius n k) ⁻¹' Iic 1) := by
    apply (isCompact_closedBall (0 : Configuration k) 1).of_isClosed_subset
      (isClosed_le (continuous_gaussianBlockRadius n k) continuous_const)
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    have hs := configurationNormSq_nonneg x
    have hi : Complex.normSq (x i) ≤ configurationNormSq x :=
      Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (x j)) (Finset.mem_univ i)
    change (n : ℝ) * configurationNormSq x ≤ 1 at hx
    rw [Complex.normSq_eq_norm_sq] at hi
    have := norm_nonneg (x i)
    nlinarith
  have hzero : (volume : Measure (Configuration k)) ((gaussianBlockRadius n k) ⁻¹' {0}) = 0 := by
    let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    have hs : (gaussianBlockRadius n k) ⁻¹' {0} = {0} := by
      ext x
      simp only [mem_preimage, mem_singleton_iff]
      constructor
      · intro h
        have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        have hsum : ∑ i, Complex.normSq (x i) = 0 := (mul_eq_zero.mp h).resolve_left hn'
        ext i
        exact Complex.normSq_eq_zero.mp
          ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (x j))).mp
            hsum i (Finset.mem_univ i))
      · rintro rfl
        simp [gaussianBlockRadius, configurationNormSq]
    rw [hs]
    exact measure_singleton _
  apply map_quadratic_homogeneous_measure _ _ (continuous_gaussianBlockRadius n k).measurable
    (fun x => mul_nonneg (Nat.cast_nonneg _) (configurationNormSq_nonneg x)) _ hk _ _ hzero
    hcompact.measure_lt_top
  · intro t ht x
    unfold gaussianBlockRadius
    rw [configurationNormSq_real_smul]
    ring
  · intro t ht s
    rw [Measure.addHaar_smul (volume : Measure (Configuration k)) t]
    have hd : Module.finrank ℝ (Configuration k) = 2 * k := by
      simp [Configuration, Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
    rw [hd, abs_of_nonneg (pow_nonneg ht.le _)]

/-- Explicit Gaussian density in an arbitrary block dimension. -/
theorem gaussianBlockMeasure_density (n k : ℕ) (hn : 0 < n) :
    gaussianBlockMeasure n k =
      ENNReal.ofReal (((n : ℝ) / Real.pi) ^ k) •
        (volume : Measure (Configuration k)).withDensity
          (fun x => ENNReal.ofReal (Real.exp (-gaussianBlockRadius n k x))) := by
  unfold gaussianBlockMeasure
  simp_rw [complexCoordinateGaussianMeasure_eq_withDensity hn]
  have hsf : ∀ i : Fin k, SigmaFinite
      ((volume : Measure ℂ).withDensity (complexCoordinateGaussianDensity n)) := by
    intro i
    rw [← complexCoordinateGaussianMeasure_eq_withDensity hn]
    infer_instance
  have hpi := @Measure.pi_withDensity _ _ _ _
    (fun _ : Fin k => (volume : Measure ℂ)) (by intro i; infer_instance)
    (fun _ : Fin k => complexCoordinateGaussianDensity n)
    (fun _ => measurable_complexCoordinateGaussianDensity n) hsf
  rw [hpi,
    ← volume_pi, ← withDensity_smul _ (by unfold gaussianBlockRadius configurationNormSq; fun_prop)]
  congr 1
  funext x
  simp only [complexCoordinateGaussianDensity, Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity),
    ← ENNReal.ofReal_mul (by positivity), Finset.prod_mul_distrib, Finset.prod_const,
    ← Real.exp_sum]
  congr 1
  simp [gaussianBlockRadius, configurationNormSq, ← Finset.mul_sum, neg_mul]

/-- The squared norm of a `k`-dimensional block has the required Gamma law. -/
theorem gaussianBlockRadius_gamma (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (gaussianBlockMeasure n k).map (gaussianBlockRadius n k) = gammaMeasure (k : ℝ) 1 := by
  have hm : (gaussianBlockMeasure n k).map (gaussianBlockRadius n k) =
      (ENNReal.ofReal (((n : ℝ) / Real.pi) ^ k) *
        ((k : ℝ≥0∞) * volume ((gaussianBlockRadius n k) ⁻¹' Iic 1))) •
          (radialPowerMeasure k).withDensity (fun r => ENNReal.ofReal (Real.exp (-r))) := by
    rw [gaussianBlockMeasure_density n k hn, Measure.map_smul _ (continuous_gaussianBlockRadius n
      k).measurable.aemeasurable]
    change _ • ((volume : Measure (Configuration k)).withDensity
      ((fun r => ENNReal.ofReal (Real.exp (-r))) ∘ gaussianBlockRadius n k)).map _ = _
    rw [map_withDensity_comp_measurable _ _ (continuous_gaussianBlockRadius n k).measurable
      _ (by fun_prop), volume_gaussianBlockRadius n k hn hk, withDensity_smul_measure, smul_smul]
  have hp : IsProbabilityMeasure ((gaussianBlockMeasure n k).map (gaussianBlockRadius n k)) :=
    (by infer_instance)
  rw [hm] at hp ⊢
  exact normalized_gaussian_tilt_gamma k hk _ hp

/-- The independent block lift used in the Gaussian proof of radial LSI. -/
abbrev GaussianRadialBlocks (n : ℕ) := (i : Fin n) → Configuration (i.val + 1)

/-- The real dimension of the lift is exactly the paper's `n(n+1)`. -/
theorem gaussianRadialBlocks_finrank (n : ℕ) :
    Module.finrank ℝ (GaussianRadialBlocks n) = n * (n + 1) := by
  have hs : ∀ m : ℕ, (∑ j ∈ Finset.range m, 2 * (j + 1)) = m * (m + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m hm => rw [Finset.sum_range_succ, hm]; ring
  rw [Module.finrank_pi_fintype]
  simp only [Configuration, Module.finrank_pi_fintype, Complex.finrank_real_complex,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (j + 1) * 2) n]
  simpa only [mul_comm] using hs n

def gaussianRadialBlockMeasure (n : ℕ) : Measure (GaussianRadialBlocks n) :=
  Measure.pi (fun i : Fin n => gaussianBlockMeasure n (i.val + 1))

instance (n : ℕ) : IsProbabilityMeasure (gaussianRadialBlockMeasure n) := by
  unfold gaussianRadialBlockMeasure
  infer_instance

def gaussianBlockRadii (n : ℕ) (x : GaussianRadialBlocks n) : Fin n → ℝ :=
  fun i => gaussianBlockRadius n (i.val + 1) (x i)

/-- The block Gaussian radial lift pushes forward to the exact Kostlan product. -/
theorem gaussianRadialBlockMeasure_map (n : ℕ) (hn : 0 < n) :
    (gaussianRadialBlockMeasure n).map (gaussianBlockRadii n) = kostlanGammaProduct n := by
  have hp : ∀ i : Fin n, IsProbabilityMeasure
      ((gaussianBlockMeasure n (i.val + 1)).map (gaussianBlockRadius n (i.val + 1))) :=
    fun i => (by infer_instance)
  let := hp
  unfold gaussianRadialBlockMeasure gaussianBlockRadii kostlanGammaProduct
  rw [Measure.pi_map_pi (fun i => (continuous_gaussianBlockRadius n _).measurable.aemeasurable)]
  simp_rw [gaussianBlockRadius_gamma n _ hn (Nat.succ_pos _)]

end
end GinibrePoincare
