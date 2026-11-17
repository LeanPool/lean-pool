/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/VandermondeL2.lean.
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

public import LeanPool.GinibrePoincare.Analysis.CollisionNull
public import LeanPool.GinibrePoincare.Analysis.GinibreMassFiniteness
public import LeanPool.GinibrePoincare.Concrete.NormalizedGroundState

/-! # The normalized Vandermonde isometry on `L²` -/


@[expose] public section


open MeasureTheory
open scoped ENNReal

namespace GinibrePoincare

noncomputable section

/-- Pointwise multiplier used by the normalized ground-state transform. -/
def normalizedVandermondeMultiplier (n : ℕ) (z : Configuration n) : ℂ :=
  ((groundStateNormalization n : ℂ)⁻¹) * vandermonde z

private theorem groundStateNormalization_pos {n : ℕ}
    (h : GinibreMassIsValid n) : 0 < groundStateNormalization n := by
  unfold groundStateNormalization
  apply Real.sqrt_pos.2
  exact ENNReal.toReal_pos h.1.ne' h.2.ne

private theorem enorm_normalizedVandermondeMultiplier_sq {n : ℕ}
    (h : GinibreMassIsValid n) (z : Configuration n) :
    ‖normalizedVandermondeMultiplier n z‖ₑ ^ (2 : ℝ) =
      (ginibreNormalizingMass n)⁻¹ * vandermondeDensity z := by
  have hMtop : ginibreNormalizingMass n ≠ ⊤ := h.2.ne
  have hM0 : ginibreNormalizingMass n ≠ 0 := h.1.ne'
  have hnorm : 0 < groundStateNormalization n := groundStateNormalization_pos h
  unfold normalizedVandermondeMultiplier vandermondeDensity vandermondeWeight
  have hsquare (x : ℂ) : ‖x‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal (Complex.normSq x) := by
    rw [ENNReal.rpow_two, ← Complex.sq_norm]
    simp [enorm]
  rw [hsquare]
  rw [Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_ofReal]
  rw [ENNReal.ofReal_mul (by positivity :
    0 ≤ ((groundStateNormalization n) * groundStateNormalization n)⁻¹)]
  congr 1
  have hsqrt : groundStateNormalization n ^ 2 =
      (ginibreNormalizingMass n).toReal := by
    unfold groundStateNormalization
    exact Real.sq_sqrt ENNReal.toReal_nonneg
  have hinv : ((groundStateNormalization n) * groundStateNormalization n)⁻¹ =
      (ginibreNormalizingMass n).toReal⁻¹ := by
    rw [← pow_two, hsqrt]
  rw [hinv, ← ENNReal.toReal_inv]
  exact ENNReal.ofReal_toReal (ENNReal.inv_ne_top.mpr hM0)

private theorem normalizedMultiplier_withDensity {n : ℕ}
    (h : GinibreMassIsValid n) :
    (complexGaussianMeasure n).withDensity
        (fun z ↦ ‖normalizedVandermondeMultiplier n z‖ₑ ^ (2 : ℝ)) =
      ginibreMeasure n := by
  simp_rw [enorm_normalizedVandermondeMultiplier_sq h]
  unfold ginibreMeasure rawGinibreMeasure
  exact withDensity_smul _ measurable_vandermondeDensity

private theorem normalizedVandermonde_lintegral {n : ℕ}
    (h : GinibreMassIsValid n) (u : Lp ℂ 2 (ginibreMeasure n)) :
    (∫⁻ z, ‖normalizedVandermondeMultiplier n z * u z‖ₑ ^ (2 : ℝ)
      ∂complexGaussianMeasure n) =
      ∫⁻ z, ‖u z‖ₑ ^ (2 : ℝ) ∂ginibreMeasure n := by
  let d := fun z : Configuration n ↦
    ‖normalizedVandermondeMultiplier n z‖ₑ ^ (2 : ℝ)
  have hd : Measurable d := by
    unfold d normalizedVandermondeMultiplier
    exact (ENNReal.continuous_rpow_const.comp
      (continuous_vandermonde.const_mul _).enorm).measurable
  have hdtop : ∀ᵐ z ∂complexGaussianMeasure n, d z < ⊤ :=
    Filter.Eventually.of_forall fun z ↦ by
      unfold d
      rw [enorm_normalizedVandermondeMultiplier_sq h]
      exact ENNReal.mul_lt_top (ENNReal.inv_ne_top.mpr h.1.ne').lt_top
        (by unfold vandermondeDensity; exact ENNReal.ofReal_ne_top.lt_top)
  calc
    _ = ∫⁻ z, d z * ‖u z‖ₑ ^ (2 : ℝ) ∂complexGaussianMeasure n := by
      apply lintegral_congr
      intro z
      unfold d
      rw [enorm_mul, ENNReal.mul_rpow_of_nonneg]
      positivity
    _ = ∫⁻ z, ‖u z‖ₑ ^ (2 : ℝ)
        ∂(complexGaussianMeasure n).withDensity d := by
      exact (lintegral_withDensity_eq_lintegral_mul_non_measurable
        _ hd hdtop _).symm
    _ = _ := by
      have hm := normalizedMultiplier_withDensity h
      change (∫⁻ z, ‖u z‖ₑ ^ (2 : ℝ)
        ∂(complexGaussianMeasure n).withDensity d) = _
      rw [hm]

theorem normalizedVandermonde_memLp {n : ℕ}
    (h : GinibreMassIsValid n) (u : Lp ℂ 2 (ginibreMeasure n)) :
    MemLp (fun z ↦ normalizedVandermondeMultiplier n z * u z) 2
      (complexGaussianMeasure n) := by
  have hac := complexGaussianMeasure_absolutelyContinuous_ginibreMeasure h
  have hf : AEStronglyMeasurable
      (fun z ↦ normalizedVandermondeMultiplier n z * u z)
      (complexGaussianMeasure n) :=
    ((continuous_vandermonde.const_mul _).aestronglyMeasurable).mul
      ((Lp.aestronglyMeasurable u).mono_ac hac)
  rw [memLp_iff]
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hf,
    eLpNorm'_eq_lintegral_enorm]
  norm_num only [ENNReal.toReal_ofNat]
  rw [normalizedVandermonde_lintegral h u]
  have hu := (Lp.memLp u).eLpNorm_lt_top
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) (Lp.aestronglyMeasurable u),
    eLpNorm'_eq_lintegral_enorm] at hu
  exact hu

theorem normalizedVandermonde_norm {n : ℕ}
    (h : GinibreMassIsValid n) (u : Lp ℂ 2 (ginibreMeasure n)) :
    ‖(normalizedVandermonde_memLp h u).toLp
        (fun z ↦ normalizedVandermondeMultiplier n z * u z)‖ = ‖u‖ := by
  simp only [Lp.norm_def]
  congr 1
  rw [eLpNorm_congr_ae (normalizedVandermonde_memLp h u).coeFn_toLp]
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) (normalizedVandermonde_memLp h
    u).aestronglyMeasurable,
    eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) (Lp.aestronglyMeasurable u),
    eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm]
  norm_num only [ENNReal.toReal_ofNat]
  rw [normalizedVandermonde_lintegral h u]

/-- Normalized multiplication by the Vandermonde as a genuine complex linear
isometry from Ginibre `L²` into Gaussian `L²`. -/
def normalizedVandermondeL2 (n : ℕ) (hn : 0 < n) :
    Lp ℂ 2 (ginibreMeasure n) →ₗᵢ[ℂ]
      Lp ℂ 2 (complexGaussianMeasure n) := by
  let h := ginibreMassEvaluation n hn
  exact
    { toFun := fun u ↦ (normalizedVandermonde_memLp h u).toLp
          (fun z ↦ normalizedVandermondeMultiplier n z * u z)
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [(normalizedVandermonde_memLp h (u + v)).coeFn_toLp,
          (normalizedVandermonde_memLp h u).coeFn_toLp,
          (normalizedVandermonde_memLp h v).coeFn_toLp,
          (complexGaussianMeasure_absolutelyContinuous_ginibreMeasure h).ae_eq
            (Lp.coeFn_add u v),
          Lp.coeFn_add
            ((normalizedVandermonde_memLp h u).toLp _)
            ((normalizedVandermonde_memLp h v).toLp _)] with z huv hu hv hadd hout
        rw [huv, hout]
        simp only [Pi.add_apply] at hadd ⊢
        rw [hadd, hu, hv, mul_add]
      map_smul' := by
        intro c u
        apply Lp.ext
        filter_upwards [(normalizedVandermonde_memLp h (c • u)).coeFn_toLp,
          (normalizedVandermonde_memLp h u).coeFn_toLp,
          (complexGaussianMeasure_absolutelyContinuous_ginibreMeasure h).ae_eq
            (Lp.coeFn_smul c u),
          Lp.coeFn_smul c ((normalizedVandermonde_memLp h u).toLp _)] with z hcu hu hin hout
        rw [hcu]
        simp only [RingHom.id_apply]
        rw [hout]
        simp only [Pi.smul_apply] at hin ⊢
        rw [hin, hu]
        simp only [smul_eq_mul]
        ring
      norm_map' := normalizedVandermonde_norm h }

/-- Almost-everywhere representative of the actual normalized Vandermonde isometry. -/
theorem normalizedVandermondeL2_coeFn_public (n : ℕ) (hn : 0 < n)
    (u : Lp ℂ 2 (ginibreMeasure n)) :
    (normalizedVandermondeL2 n hn u : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n]
      fun z => normalizedVandermondeMultiplier n z * u z :=
  (normalizedVandermonde_memLp (ginibreMassEvaluation n hn) u).coeFn_toLp

/-- The normalized Vandermonde transform is an isometric equivalence onto its
range. -/
def normalizedVandermondeL2EquivRange (n : ℕ) (hn : 0 < n) :=
  (normalizedVandermondeL2 n hn).equivRange

end

end GinibrePoincare
