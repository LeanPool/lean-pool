/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Defs
import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Torus.Cube

/-!
# Trigonometric polynomials and Fourier multipliers on the torus

On the torus `𝕋^ι = (ℝ / ℤ)^ι`, with Mathlib's measure (of total mass one) and the monomials
`e_n = UnitAddTorus.mFourier n`, `n ∈ ℤ^ι`:

* `HarmonicAnalysis.trigPoly c = Σ_n c_n e_n`, for finitely supported coefficients `c`;
* `HarmonicAnalysis.torusMultiplier m c = Σ_n m (n) c_n e_n`, the Fourier multiplier with symbol
  `m : ℤ^ι → ℂ` applied to `trigPoly c`;
* `HarmonicAnalysis.torusMultiplierNorm m p`, the norm of this multiplier on the mean-zero
  subspace `L^p_0 (𝕋^ι)`, computed on the dense subspace of mean-zero trigonometric polynomials
  (`c₀ = 0`): `⨆ ‖T_m (trigPoly c)‖_p / ‖trigPoly c‖_p` in `ℝ≥0∞`.

## Main results

* `HarmonicAnalysis.eLpNorm_torusMultiplier_le`: `‖T_m P‖_p ≤ ‖T_m‖_{L^p_0} ‖P‖_p` for every
  mean-zero trigonometric polynomial `P`; `HarmonicAnalysis.enorm_le_torusMultiplierNorm`:
  `|m (n)| ≤ ‖T_m‖_{L^p_0}` for `n ≠ 0`.
* `HarmonicAnalysis.integral_mFourier_mul_mFourier` (orthogonality): `∫ e_k e_ℓ` is `1` if `ℓ = −k`
  and `0` otherwise; `HarmonicAnalysis.integral_torusMultiplier_mul_trigPoly`: hence
  `∫ T_m (Σ_k c_k e_k) (Σ_ℓ d_ℓ e_ℓ) = Σ_k m (k) c_k d_{−k}`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HarmonicAnalysis

open UnitAddTorus

variable {ι : Type*} [Fintype ι]

theorem continuous_trigPoly (c : (ι → ℤ) →₀ ℂ) : Continuous (trigPoly c) :=
  continuous_finsetSum _ fun n _ => continuous_const.mul (mFourier n).continuous

theorem continuous_torusMultiplier (m : (ι → ℤ) → ℂ) (c : (ι → ℤ) →₀ ℂ) :
    Continuous (torusMultiplier m c) :=
  continuous_finsetSum _ fun n _ => continuous_const.mul (mFourier n).continuous

/-! ### Orthogonality -/

/-- Orthogonality: `∫ e_k e_ℓ = 1` if `ℓ = −k`, and `0` otherwise. -/
theorem integral_mFourier_mul_mFourier (k l : ι → ℤ) :
    ∫ x : UnitAddTorus ι, mFourier k x * mFourier l x = if l = -k then 1 else 0 := by
  have h := orthonormal_iff_ite.mp (orthonormal_mFourier (d := ι)) (-k) l
  rw [ContinuousMap.inner_toLp] at h
  simp only [← mFourier_neg, neg_neg] at h
  rw [volume_eq_pi_haarAddCircle]
  simp_rw [mul_comm (mFourier k _), eq_comm (a := l)]
  exact h

/-- The pairing of two trigonometric polynomials, by orthogonality:
`∫ T_m (Σ_k c_k e_k) (Σ_ℓ d_ℓ e_ℓ) = Σ_k m (k) c_k d_{−k}`. -/
theorem integral_torusMultiplier_mul_trigPoly (m : (ι → ℤ) → ℂ) (c d : (ι → ℤ) →₀ ℂ) :
    ∫ x, torusMultiplier m c x * trigPoly d x = c.sum fun n a => m n * a * d (-n) := by
  classical
  have hint : ∀ k l : ι → ℤ, Integrable (fun x : UnitAddTorus ι =>
      m k * c k * d l * (mFourier k x * mFourier l x)) := fun k l =>
    (Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (HasCompactSupport.of_compactSpace _)).const_mul _
  have hprod : ∀ x, torusMultiplier m c x * trigPoly d x =
      ∑ k ∈ c.support, ∑ l ∈ d.support, m k * c k * d l * (mFourier k x * mFourier l x) := by
    intro x
    simp only [torusMultiplier, trigPoly, Finsupp.sum, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  simp_rw [hprod]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l, Finsupp.sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => hint k l]
  simp_rw [integral_const_mul, integral_mFourier_mul_mFourier, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Finsupp.notMem_support_iff.1 h, mul_zero]

/-- A trigonometric polynomial determines its coefficients: if `Σ_n c_n e_n` vanishes almost
everywhere, then `c = 0`, by `c_k = ∫ (Σ_n c_n e_n) e_{−k}`. -/
private lemma eq_zero_of_trigPoly_ae_eq_zero {c : (ι → ℤ) →₀ ℂ} (h : trigPoly c =ᵐ[volume] 0) :
    c = 0 := by
  classical
  ext k
  have h1 := integral_torusMultiplier_mul_trigPoly (fun _ => 1) c (Finsupp.single (-k) 1)
  have h2 : torusMultiplier (fun _ => 1) c = trigPoly c := by
    funext x
    simp [torusMultiplier, trigPoly]
  have h3 : ∫ x, trigPoly c x * trigPoly (Finsupp.single (-k) 1) x = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [h] with x hx
    simp [hx]
  rw [h2, h3, Finsupp.sum, Finset.sum_eq_single k] at h1
  · simpa using h1.symm
  · intro n _ hn
    simp [hn]
  · intro hk
    simp [Finsupp.notMem_support_iff.1 hk]

/-! ### The multiplier norm -/

/-- The bound defining `torusMultiplierNorm`, for one mean-zero trigonometric polynomial. -/
theorem eLpNorm_torusMultiplier_le (m : (ι → ℤ) → ℂ) {p : ℝ} (hp : 0 < p)
    (c : (ι → ℤ) →₀ ℂ) (hc0 : c 0 = 0) :
    eLpNorm (torusMultiplier m c) (ENNReal.ofReal p) volume ≤
      torusMultiplierNorm m p * eLpNorm (trigPoly c) (ENNReal.ofReal p) volume := by
  by_cases hy : eLpNorm (trigPoly c) (ENNReal.ofReal p) volume = 0
  · obtain rfl := eq_zero_of_trigPoly_ae_eq_zero
      ((eLpNorm_eq_zero_iff (ENNReal.ofReal_pos.2 hp).ne').1 hy)
    have : torusMultiplier m (0 : (ι → ℤ) →₀ ℂ) = 0 := funext fun x => by simp [torusMultiplier]
    simp [this]
  have hy' : eLpNorm (trigPoly c) (ENNReal.ofReal p) volume ≠ ⊤ :=
    ((continuous_trigPoly c).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).eLpNorm_lt_top.ne
  calc eLpNorm (torusMultiplier m c) (ENNReal.ofReal p) volume
      = eLpNorm (torusMultiplier m c) (ENNReal.ofReal p) volume /
          eLpNorm (trigPoly c) (ENNReal.ofReal p) volume *
          eLpNorm (trigPoly c) (ENNReal.ofReal p) volume := (ENNReal.div_mul_cancel hy hy').symm
    _ ≤ _ := by
      gcongr
      exact le_iSup₂ (f := fun (c : (ι → ℤ) →₀ ℂ) (_ : c 0 = 0) =>
        eLpNorm (torusMultiplier m c) (ENNReal.ofReal p) volume /
          eLpNorm (trigPoly c) (ENNReal.ofReal p) volume) c hc0

/-- `‖e_n‖_p = 1` on the torus, of total mass one. -/
private lemma eLpNorm_mFourier (n : ι → ℤ) {p : ℝ} (hp : 0 < p) :
    eLpNorm (mFourier n) (ENNReal.ofReal p) (volume : Measure (UnitAddTorus ι)) = 1 := by
  have hμ : (volume : Measure (UnitAddTorus ι)) ≠ 0 := by
    rw [volume_eq_pi_haarAddCircle]
    exact IsProbabilityMeasure.ne_zero _
  rw [eLpNorm_congr_norm_ae (g := fun _ => (1 : ℂ)) (mFourier n).continuous.aestronglyMeasurable
      aestronglyMeasurable_const (ae_of_all _ fun x => by simp [norm_mFourier_apply_eq_one]),
    eLpNorm_const _ (by simpa using hp) hμ, volume_eq_pi_haarAddCircle, measure_univ]
  simp

/-- The values of the symbol off `0` are at most the multiplier norm: `|m (n)| ≤ ‖T_m‖_{L^p_0}` for
`n ≠ 0`, by `T_m e_n = m (n) e_n`. -/
theorem enorm_le_torusMultiplierNorm (m : (ι → ℤ) → ℂ) {p : ℝ} (hp : 0 < p) {n : ι → ℤ}
    (hn : n ≠ 0) : ‖m n‖ₑ ≤ torusMultiplierNorm m p := by
  classical
  have h := eLpNorm_torusMultiplier_le m hp (Finsupp.single n 1) (by simp [hn])
  have h1 : trigPoly (Finsupp.single n 1) = mFourier n := by
    funext x
    simp [trigPoly]
  have h2 : torusMultiplier m (Finsupp.single n 1) = m n • ⇑(mFourier n) := by
    funext x
    simp [torusMultiplier]
  rwa [h1, h2, eLpNorm_const_smul, eLpNorm_mFourier n hp, mul_one, mul_one] at h

end HarmonicAnalysis
