/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/VandermondeL2Inverse.lean.
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

public import LeanPool.GinibrePoincare.Analysis.VandermondeSymmetryL2

/-! # Inverse of normalized Vandermonde multiplication on `L²` -/


@[expose] public section


open MeasureTheory
open scoped ENNReal

namespace GinibrePoincare

noncomputable section

/-- Measurable pointwise inverse multiplier; its value on collisions is
irrelevant because that locus is Gaussian-null. -/
def inverseVandermondeMultiplier (n : ℕ) (z : Configuration n) : ℂ :=
  (groundStateNormalization n : ℂ) * (vandermonde z)⁻¹

theorem measurable_inverseVandermondeMultiplier (n : ℕ) :
    Measurable (inverseVandermondeMultiplier n) := by
  unfold inverseVandermondeMultiplier
  exact measurable_const.mul continuous_vandermonde.measurable.inv

theorem inverse_mul_normalizedVandermondeMultiplier {n : ℕ}
    (h : GinibreMassIsValid n) {z : Configuration n}
    (hz : z ∉ collisionSet n) :
    inverseVandermondeMultiplier n z * normalizedVandermondeMultiplier n z = 1 := by
  have hV : vandermonde z ≠ 0 := by
    exact fun hv ↦ hz ((vandermonde_eq_zero_iff z).mp hv)
  have hN : groundStateNormalization n ≠ 0 := by
    unfold groundStateNormalization
    rw [Real.sqrt_ne_zero']
    exact ENNReal.toReal_pos h.1.ne' h.2.ne
  unfold inverseVandermondeMultiplier normalizedVandermondeMultiplier
  field_simp
  exact div_self (Complex.ofReal_ne_zero.mpr hN)

theorem normalized_mul_inverseVandermondeMultiplier {n : ℕ}
    (h : GinibreMassIsValid n) {z : Configuration n}
    (hz : z ∉ collisionSet n) :
    normalizedVandermondeMultiplier n z * inverseVandermondeMultiplier n z = 1 := by
  rw [mul_comm]
  exact inverse_mul_normalizedVandermondeMultiplier h hz

/-- Ginibre measure is always absolutely continuous with respect to the
Gaussian reference measure. -/
theorem ginibreMeasure_absolutelyContinuous_complexGaussianMeasure (n : ℕ) :
    ginibreMeasure n ≪ complexGaussianMeasure n := by
  unfold ginibreMeasure rawGinibreMeasure
  exact (Measure.smul_absolutelyContinuous.trans
    (withDensity_absolutelyContinuous _ _))

/-- The inverse multiplier applied to a Gaussian `L²` representative. -/
def inverseVandermondeFunction (n : ℕ)
    (v : Lp ℂ 2 (complexGaussianMeasure n)) : Configuration n → ℂ :=
  fun z ↦ inverseVandermondeMultiplier n z * v z

theorem inverseVandermondeFunction_aestronglyMeasurable (n : ℕ)
    (v : Lp ℂ 2 (complexGaussianMeasure n)) :
    AEStronglyMeasurable (inverseVandermondeFunction n v)
      (ginibreMeasure n) := by
  exact (measurable_inverseVandermondeMultiplier n).aestronglyMeasurable.mul
    ((Lp.aestronglyMeasurable v).mono_ac
      (ginibreMeasure_absolutelyContinuous_complexGaussianMeasure n))

/-- Pointwise inverse cancellation holds Gaussian-almost everywhere. -/
theorem normalized_inverse_cancel_ae {n : ℕ} (h : GinibreMassIsValid n)
    (v : Lp ℂ 2 (complexGaussianMeasure n)) :
    (fun z ↦ normalizedVandermondeMultiplier n z *
      inverseVandermondeFunction n v z) =ᵐ[complexGaussianMeasure n] v := by
  have houtside : ∀ᵐ z ∂complexGaussianMeasure n, z ∉ collisionSet n := by
    rw [ae_iff]
    rw [show {z : Configuration n | ¬z ∉ collisionSet n} = collisionSet n by
      ext z
      simp]
    exact complexGaussianMeasure_collisionSet n
  filter_upwards [houtside] with z hz
  unfold inverseVandermondeFunction
  rw [← mul_assoc, normalized_mul_inverseVandermondeMultiplier h hz]
  simp

/-- The inverse transform respects the expected permutation character: an
alternating input produces a symmetric pointwise transform away from the
collision locus. -/
theorem inverseMultiplier_permute {n : ℕ} (σ : ParticlePermutation n)
    {z : Configuration n} (hz : z ∉ collisionSet n) :
    inverseVandermondeMultiplier n (permute σ z) =
      permutationSign σ * inverseVandermondeMultiplier n z := by
  have hs : permutationSign σ * permutationSign σ = 1 := by
    unfold permutationSign
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have hV : vandermonde z ≠ 0 :=
    fun hv ↦ hz ((vandermonde_eq_zero_iff z).mp hv)
  have hs0 : permutationSign σ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hs
    exact zero_ne_one hs
  unfold inverseVandermondeMultiplier
  rw [vandermonde_permute]
  field_simp
  have hs' : permutationSign σ ^ 2 = 1 := by simpa [pow_two] using hs
  rw [hs']
  simp

/-- Exact squared extended norm of the inverse multiplier away from the
collision locus. -/
theorem enorm_inverseVandermondeMultiplier_sq {n : ℕ}
    (h : GinibreMassIsValid n) {z : Configuration n}
    (hz : z ∉ collisionSet n) :
    ‖inverseVandermondeMultiplier n z‖ₑ ^ (2 : ℝ) =
      ginibreNormalizingMass n * (vandermondeDensity z)⁻¹ := by
  have hV : vandermonde z ≠ 0 :=
    fun hv ↦ hz ((vandermonde_eq_zero_iff z).mp hv)
  have htop : ginibreNormalizingMass n ≠ ⊤ := h.2.ne
  have hsqrt :
      (ENNReal.ofReal (Real.sqrt (ginibreNormalizingMass n).toReal)) ^ 2 =
        ginibreNormalizingMass n := by
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal htop
  unfold inverseVandermondeMultiplier groundStateNormalization
  rw [ENNReal.rpow_two, eNorm_mul, mul_pow]
  simp only [eNorm_eq_nnNorm]
  rw [show (↑‖(Real.sqrt (ginibreNormalizingMass n).toReal : ℂ)‖₊ : ℝ≥0∞) =
      ENNReal.ofReal (Real.sqrt (ginibreNormalizingMass n).toReal) by
    rw [ENNReal.coe_nnreal_eq]
    congr 1
    simp]
  rw [hsqrt]
  simp only [nnNorm_inv]
  unfold vandermondeDensity vandermondeWeight
  rw [show ENNReal.ofReal (Complex.normSq (vandermonde z)) =
      (‖vandermonde z‖₊ : ℝ≥0∞) ^ 2 by
    rw [Complex.normSq_eq_norm_sq]
    simp [ENNReal.ofReal_pow, eNorm_eq_nnNorm]]
  rw [ENNReal.coe_inv (by simpa using hV)]
  congr 1
  exact ENNReal.inv_pow.symm

/-- The inverse multiplier transports the Gaussian squared norm back to the
Ginibre squared norm. -/
theorem inverseVandermonde_lintegral {n : ℕ}
    (h : GinibreMassIsValid n) (v : Lp ℂ 2 (complexGaussianMeasure n)) :
    (∫⁻ z, ‖inverseVandermondeFunction n v z‖ₑ ^ (2 : ℝ)
      ∂ginibreMeasure n) =
      ∫⁻ z, ‖v z‖ₑ ^ (2 : ℝ) ∂complexGaussianMeasure n := by
  have houtside : ∀ᵐ z ∂complexGaussianMeasure n, z ∉ collisionSet n := by
    rw [ae_iff]
    rw [show {z : Configuration n | ¬z ∉ collisionSet n} = collisionSet n by
      ext z
      simp]
    exact complexGaussianMeasure_collisionSet n
  have hinvmeas : AEStronglyMeasurable (inverseVandermondeFunction n v)
      (complexGaussianMeasure n) := by
    exact (measurable_inverseVandermondeMultiplier n).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable v)
  have hfmeas : AEMeasurable (fun z ↦ vandermondeDensity z *
      ‖inverseVandermondeFunction n v z‖ₑ ^ (2 : ℝ))
      (complexGaussianMeasure n) :=
    measurable_vandermondeDensity.aemeasurable.mul
      (hinvmeas.eNorm.pow_const 2)
  unfold ginibreMeasure rawGinibreMeasure
  rw [lintegral_smul_measure]
  change (ginibreNormalizingMass n)⁻¹ *
      (∫⁻ z, ‖inverseVandermondeFunction n v z‖ₑ ^ (2 : ℝ)
        ∂(complexGaussianMeasure n).withDensity vandermondeDensity) = _
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable]
  · change (ginibreNormalizingMass n)⁻¹ *
        (∫⁻ z, vandermondeDensity z *
          ‖inverseVandermondeFunction n v z‖ₑ ^ (2 : ℝ)
          ∂complexGaussianMeasure n) = _
    rw [← lintegral_const_mul'' _ hfmeas]
    apply lintegral_congr_ae
    filter_upwards [houtside] with z hz
    unfold inverseVandermondeFunction
    rw [eNorm_mul, ENNReal.mul_rpow_of_nonneg]
    · rw [enorm_inverseVandermondeMultiplier_sq h hz]
      have hd0 : vandermondeDensity z ≠ 0 := by
        unfold vandermondeDensity vandermondeWeight
        exact (ENNReal.ofReal_pos.mpr
          (Complex.normSq_pos.mpr
            (fun hv ↦ hz ((vandermonde_eq_zero_iff z).mp hv)))).ne'
      rw [show (ginibreNormalizingMass n)⁻¹ * (vandermondeDensity z *
          (ginibreNormalizingMass n * (vandermondeDensity z)⁻¹ * ‖v z‖ₑ ^ (2 : ℝ))) =
          ((ginibreNormalizingMass n)⁻¹ * ginibreNormalizingMass n) *
            (vandermondeDensity z * (vandermondeDensity z)⁻¹) *
              ‖v z‖ₑ ^ (2 : ℝ) by ac_rfl]
      rw [ENNReal.inv_mul_cancel h.1.ne' h.2.ne,
        ENNReal.mul_inv_cancel hd0 (by simp [vandermondeDensity])]
      simp
    · positivity
  · exact measurable_vandermondeDensity
  · exact Filter.Eventually.of_forall fun z ↦ by
      unfold vandermondeDensity
      exact ENNReal.ofReal_ne_top.lt_top

/-- The inverse Vandermonde transform of a Gaussian `L²` function belongs to
Ginibre `L²`. -/
theorem inverseVandermonde_memLp {n : ℕ}
    (h : GinibreMassIsValid n) (v : Lp ℂ 2 (complexGaussianMeasure n)) :
    MemLp (inverseVandermondeFunction n v) 2 (ginibreMeasure n) := by
  have hf := inverseVandermondeFunction_aestronglyMeasurable n v
  rw [memLp_iff]
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hf,
    eLpNorm'_eq_lintegral_eNorm]
  norm_num only [ENNReal.toReal_ofNat]
  rw [inverseVandermonde_lintegral h v]
  have hv := (Lp.memLp v).eLpNorm_lt_top
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) (Lp.aestronglyMeasurable v),
    eLpNorm'_eq_lintegral_eNorm] at hv
  exact hv

theorem inverseVandermonde_norm {n : ℕ}
    (h : GinibreMassIsValid n) (v : Lp ℂ 2 (complexGaussianMeasure n)) :
    ‖(inverseVandermonde_memLp h v).toLp (inverseVandermondeFunction n v)‖ = ‖v‖ := by
  simp only [Lp.norm_def]
  congr 1
  rw [eLpNorm_congr_ae (inverseVandermonde_memLp h v).coeFn_toLp]
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) (inverseVandermonde_memLp h
    v).aestronglyMeasurable,
    eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) (Lp.aestronglyMeasurable v),
    eLpNorm'_eq_lintegral_eNorm, eLpNorm'_eq_lintegral_eNorm]
  norm_num only [ENNReal.toReal_ofNat]
  rw [inverseVandermonde_lintegral h v]

/-- Multiplication by the normalized inverse Vandermonde as a complex linear
isometry from Gaussian `L²` to Ginibre `L²`. -/
def inverseVandermondeL2 (n : ℕ) (hn : 0 < n) :
    Lp ℂ 2 (complexGaussianMeasure n) →ₗᵢ[ℂ] Lp ℂ 2 (ginibreMeasure n) := by
  let h := ginibreMassEvaluation n hn
  exact
    { toFun := fun v ↦ (inverseVandermonde_memLp h v).toLp
          (inverseVandermondeFunction n v)
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [(inverseVandermonde_memLp h (u + v)).coeFn_toLp,
          (inverseVandermonde_memLp h u).coeFn_toLp,
          (inverseVandermonde_memLp h v).coeFn_toLp,
          (ginibreMeasure_absolutelyContinuous_complexGaussianMeasure n).ae_eq
            (Lp.coeFn_add u v),
          Lp.coeFn_add ((inverseVandermonde_memLp h u).toLp _)
            ((inverseVandermonde_memLp h v).toLp _)] with z huv hu hv hadd hout
        rw [huv, hout]
        simp only [Pi.add_apply] at hadd ⊢
        rw [hu, hv]
        change inverseVandermondeMultiplier n z * (u + v) z =
          inverseVandermondeMultiplier n z * u z +
            inverseVandermondeMultiplier n z * v z
        rw [hadd]
        exact mul_add _ _ _
      map_smul' := by
        intro c v
        apply Lp.ext
        filter_upwards [(inverseVandermonde_memLp h (c • v)).coeFn_toLp,
          (inverseVandermonde_memLp h v).coeFn_toLp,
          (ginibreMeasure_absolutelyContinuous_complexGaussianMeasure n).ae_eq
            (Lp.coeFn_smul c v),
          Lp.coeFn_smul c ((inverseVandermonde_memLp h v).toLp _)] with z hcv hv hin hout
        rw [hcv]
        simp only [RingHom.id_apply]
        rw [hout]
        simp only [Pi.smul_apply] at hin ⊢
        rw [hv]
        change inverseVandermondeMultiplier n z * (c • v) z =
          c * (inverseVandermondeMultiplier n z * v z)
        rw [hin]
        simp only [smul_eq_mul]
        ring
      norm_map' := inverseVandermonde_norm h }

/-- The inverse Vandermonde isometry agrees almost everywhere with its defining multiplier. -/
theorem inverseVandermondeL2_coeFn {n : ℕ} (hn : 0 < n)
    (v : Lp ℂ 2 (complexGaussianMeasure n)) :
    inverseVandermondeL2 n hn v =ᵐ[ginibreMeasure n]
      inverseVandermondeFunction n v := by
  exact (inverseVandermonde_memLp (ginibreMassEvaluation n hn) v).coeFn_toLp

private theorem forwardVandermondeL2_coeFn {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (ginibreMeasure n)) :
    normalizedVandermondeL2 n hn u =ᵐ[complexGaussianMeasure n]
      fun z ↦ normalizedVandermondeMultiplier n z * u z := by
  exact normalizedVandermondeL2_coeFn_public n hn u

theorem normalizedVandermondeL2_inverseVandermondeL2 {n : ℕ} (hn : 0 < n)
    (v : Lp ℂ 2 (complexGaussianMeasure n)) :
    normalizedVandermondeL2 n hn (inverseVandermondeL2 n hn v) = v := by
  apply Lp.ext
  have h := ginibreMassEvaluation n hn
  filter_upwards [forwardVandermondeL2_coeFn hn (inverseVandermondeL2 n hn v),
    (complexGaussianMeasure_absolutelyContinuous_ginibreMeasure h).ae_eq
      (inverseVandermondeL2_coeFn hn v), normalized_inverse_cancel_ae h v] with z hF hI hc
  rw [hF, hI]
  exact hc

theorem inverseVandermondeL2_normalizedVandermondeL2 {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (ginibreMeasure n)) :
    inverseVandermondeL2 n hn (normalizedVandermondeL2 n hn u) = u := by
  apply (normalizedVandermondeL2 n hn).injective
  rw [normalizedVandermondeL2_inverseVandermondeL2]

/-- The inverse transform sends alternating Gaussian functions to symmetric
Ginibre functions. -/
theorem inverseVandermondeL2_mem_ginibreSymmetric {n : ℕ} (hn : 0 < n)
    (v : gaussianAlternatingL2 n) :
    inverseVandermondeL2 n hn v.1 ∈ ginibreSymmetricL2 n := by
  intro σ
  apply (normalizedVandermondeL2 n hn).injective
  rw [normalizedVandermondeL2_inverseVandermondeL2]
  have ht := normalizedVandermondeL2_intertwines hn σ
    (inverseVandermondeL2 n hn v.1)
  rw [normalizedVandermondeL2_inverseVandermondeL2] at ht
  have hv := v.2 σ
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
    simp [permutationSign, hs] at ht hv ⊢ <;> grind

/-- Unitary identification of symmetric Ginibre `L²` with alternating
Gaussian `L²`. -/
def vandermondeSymmetricAlternatingEquiv (n : ℕ) (hn : 0 < n) :
    ginibreSymmetricL2 n ≃ₗᵢ[ℂ] gaussianAlternatingL2 n where
  toFun := normalizedVandermondeSymmetricL2 n hn
  invFun v := ⟨inverseVandermondeL2 n hn v.1,
    inverseVandermondeL2_mem_ginibreSymmetric hn v⟩
  left_inv u := by
    apply Subtype.ext
    exact inverseVandermondeL2_normalizedVandermondeL2 hn u.1
  right_inv v := by
    apply Subtype.ext
    exact normalizedVandermondeL2_inverseVandermondeL2 hn v.1
  map_add' := map_add (normalizedVandermondeSymmetricL2 n hn)
  map_smul' := map_smul (normalizedVandermondeSymmetricL2 n hn)
  norm_map' := (normalizedVandermondeSymmetricL2 n hn).norm_map

end

end GinibrePoincare
