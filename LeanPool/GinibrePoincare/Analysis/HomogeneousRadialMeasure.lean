/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/HomogeneousRadialMeasure.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MeasureTransport
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import LeanPool.GinibrePoincare.Analysis.GaussianDensity

/-! # Radial laws of homogeneous measures

A homogeneous measure of degree `2*k` and a nonnegative quadratic homogeneous
radius have a radial pushforward proportional to `r^(k-1) dr` on `(0,∞)`.
This formulation uses sublevel-set scaling and does not require spherical
coordinates or a particular choice of norm.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Pointwise

namespace GinibrePoincare
noncomputable section

/-- Multiplying Haar measure by a homogeneous density adds its degree to the
scaling dimension. -/
theorem homogeneous_withDensity_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (f : E → ℝ≥0∞) (hf : Measurable f) (d : ℕ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ z, f (t • z) = ENNReal.ofReal (t ^ d) * f z)
    (t : ℝ) (ht : 0 < t) (s : Set E) :
    (μ.withDensity f) (t • s) =
      ENNReal.ofReal (t ^ (Module.finrank ℝ E + d)) * (μ.withDensity f) s := by
  let e : E ≃ᵐ E :=
    { toFun := fun z => t⁻¹ • z
      invFun := fun z => t • z
      left_inv := by intro z; simp [smul_smul, ht.ne']
      right_inv := by intro z; simp [smul_smul, ht.ne']
      measurable_toFun := measurable_const_smul _
      measurable_invFun := measurable_const_smul _ }
  have hmap : (μ.withDensity f).map e =
      ENNReal.ofReal (t ^ (Module.finrank ℝ E + d)) • μ.withDensity f := by
    have he : MeasurePreserving e μ (μ.map e) := ⟨e.measurable, rfl⟩
    have hden : f = (f ∘ e.symm) ∘ e := by funext z; simp
    conv_lhs => rw [hden]
    rw [he.map_withDensity_comp e (hf.comp e.symm.measurable)]
    have hhaar : μ.map e = ENNReal.ofReal (t ^ Module.finrank ℝ E) • μ := by
      change μ.map (fun z => t⁻¹ • z) = _
      rw [Measure.map_addHaar_smul μ (inv_ne_zero ht.ne'), inv_pow, inv_inv,
        abs_of_nonneg (pow_nonneg ht.le _)]
    rw [hhaar, withDensity_smul_measure]
    have hfd : f ∘ e.symm = ENNReal.ofReal (t ^ d) • f := by
      funext z
      exact hhom t ht z
    rw [hfd, withDensity_smul _ hf, smul_smul,
      ← ENNReal.ofReal_mul (pow_nonneg ht.le _), ← pow_add]
  have hpre : e ⁻¹' s = t • s := by
    ext z
    constructor
    · intro hz
      exact ⟨t⁻¹ • z, hz, by simp [smul_smul, ht.ne']⟩
    · rintro ⟨w, hw, rfl⟩
      change t⁻¹ • (t • w) ∈ s
      simpa [smul_smul, ht.ne'] using hw
  have hm := congrArg (fun ν : Measure E => ν s) hmap
  rw [e.map_apply s, hpre, smul_apply, smul_eq_mul] at hm
  exact hm

/-- Transporting a density which depends only on the mapped random variable. -/
theorem map_withDensity_comp_measurable
    {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (q : E → F) (hq : Measurable q)
    (f : F → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity (f ∘ q)).map q = (μ.map q).withDensity f := by
  ext s hs
  rw [Measure.map_apply hq hs, withDensity_apply _ (hq hs), withDensity_apply _ hs]
  exact (setLIntegral_map hs hf hq).symm

/-- The unnormalized power-law measure on the positive half-line. -/
def radialPowerMeasure (k : ℕ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun r => ENNReal.ofReal (r ^ (k - 1)))

instance (k : ℕ) : SigmaFinite (radialPowerMeasure k) := by
  unfold radialPowerMeasure
  infer_instance

/-- Cumulative mass of the power-law measure. -/
theorem radialPowerMeasure_Iic (k : ℕ) (hk : 0 < k) (x : ℝ) :
    radialPowerMeasure k (Iic x) =
      if 0 ≤ x then ENNReal.ofReal (x ^ k / (k : ℝ)) else 0 := by
  unfold radialPowerMeasure
  rw [withDensity_apply _ measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  by_cases hx : 0 ≤ x
  · rw [ite_eq_left hx]
    have hset : Iic x ∩ Ioi (0 : ℝ) = Ioc 0 x := by ext y; simp; tauto
    rw [hset]
    rw [← ofReal_integral_eq_lintegral_ofReal ((continuous_pow (k - 1)).intervalIntegrable (μ :=
        volume) 0 x).1]
    · rw [← intervalIntegral.integral_of_le hx, integral_pow]
      have hkcast : ((k - 1 : ℕ) : ℝ) + 1 = k := by
        exact_mod_cast (Nat.sub_add_cancel hk)
      simp only [Nat.sub_add_cancel hk, zero_pow hk.ne', sub_zero, hkcast]
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      exact pow_nonneg hy.1.le _
  · rw [ite_eq_right hx]
    have hset : Iic x ∩ Ioi (0 : ℝ) = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false, not_and]
      intro hy
      exact not_lt_of_ge (hy.trans (le_of_not_ge hx))
    rw [hset, Measure.restrict_empty, lintegral_zero_measure]

/-- A radial pushforward is determined by homogeneity, its unit sublevel mass,
and the absence of mass at radius zero. -/
theorem map_quadratic_homogeneous_measure
    {E : Type*} [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
    (μ : Measure E) (q : E → ℝ) (hq : Measurable q)
    (hq_nonneg : ∀ z, 0 ≤ q z) (k : ℕ) (hk : 0 < k)
    (hq_smul : ∀ t : ℝ, 0 < t → ∀ z, q (t • z) = t ^ 2 * q z)
    (hμ_smul : ∀ t : ℝ, 0 < t → ∀ s : Set E,
      μ (t • s) = ENNReal.ofReal (t ^ (2 * k)) * μ s)
    (hzero : μ (q ⁻¹' {0}) = 0)
    (hfinite : μ (q ⁻¹' Iic 1) < ⊤) :
    μ.map q = ((k : ℝ≥0∞) * μ (q ⁻¹' Iic 1)) • radialPowerMeasure k := by
  let K := μ (q ⁻¹' Iic 1)
  have hcdf : ∀ x : ℝ, (μ.map q) (Iic x) =
      if 0 ≤ x then ENNReal.ofReal (x ^ k) * K else 0 := by
    intro x
    rw [Measure.map_apply hq measurableSet_Iic]
    by_cases hx : 0 < x
    · have ht : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
      have ht2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
      have hset : q ⁻¹' Iic x = Real.sqrt x • (q ⁻¹' Iic 1) := by
        ext z
        constructor
        · intro hz
          refine ⟨(Real.sqrt x)⁻¹ • z, ?_, ?_⟩
          · change q ((Real.sqrt x)⁻¹ • z) ≤ 1
            rw [hq_smul _ (inv_pos.mpr ht), inv_pow, ht2]
            have hz' : q z ≤ x := hz
            exact (inv_mul_le_iff₀ hx).mpr (by simpa using hz')
          · simp [smul_smul, ht.ne']
        · rintro ⟨w, hw, rfl⟩
          change q (Real.sqrt x • w) ≤ x
          rw [hq_smul _ ht, ht2]
          exact mul_le_of_le_one_right hx.le hw
      rw [hset, hμ_smul _ ht, ite_eq_left hx.le]
      congr 2
      rw [show 2 * k = 2 * k by rfl, pow_mul, ht2]
    · by_cases hx0 : x = 0
      · subst x
        have hset : q ⁻¹' Iic (0 : ℝ) = q ⁻¹' {0} := by
          ext z
          simp only [mem_preimage, mem_Iic, mem_singleton_iff]
          exact ⟨fun h => le_antisymm h (hq_nonneg z), fun h => h.le⟩
        rw [hset, hzero]
        simp [hk.ne']
      · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hx0
        have hset : q ⁻¹' Iic x = ∅ := by
          ext z
          simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
          exact not_le_of_gt (hxneg.trans_le (hq_nonneg z))
        rw [hset, measure_empty, ite_eq_right (not_le.mpr hxneg)]
  have hmass : ∀ x : ℝ, (μ.map q) (Iic x) < ⊤ := by
    intro x
    rw [hcdf]
    split_ifs
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinite
    · exact ENNReal.zero_lt_top
  let ν := ((k : ℝ≥0∞) * K) • radialPowerMeasure k
  have hcdfν : ∀ x : ℝ, ν (Iic x) = (μ.map q) (Iic x) := by
    intro x
    rw [smul_apply, radialPowerMeasure_Iic k hk, hcdf]
    by_cases hx : 0 ≤ x
    · rw [ite_eq_left hx, ite_eq_left hx, smul_eq_mul]
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      rw [ENNReal.ofReal_div_of_pos hkR, ENNReal.ofReal_natCast]
      have hkE : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk.ne'
      rw [div_eq_mul_inv]
      calc
        _ = ((k : ℝ≥0∞) * (k : ℝ≥0∞)⁻¹) * (ENNReal.ofReal (x ^ k) * K) := by ac_rfl
        _ = _ := by rw [ENNReal.mul_inv_cancel hkE (ENNReal.natCast_ne_top k), one_mul]
    · simp [hx]
  apply Measure.ext_of_Ioc' _ ν
  · intro a b hab
    exact (measure_mono Ioc_subset_Iic_self).trans_lt (hmass b) |>.ne
  · intro a b hab
    rw [← Iic_sdiff_Iic, measure_sdiff (Iic_subset_Iic.mpr hab.le)
        measurableSet_Iic.nullMeasurableSet,
      measure_sdiff (Iic_subset_Iic.mpr hab.le) measurableSet_Iic.nullMeasurableSet,
      hcdfν a, hcdfν b]
    · rw [hcdfν a]
      exact (hmass a).ne
    · exact (hmass a).ne

/-- The Gaussian tilt of an integer power-law radial measure is proportional
to the Gamma law with rate one. -/
theorem radialPowerMeasure_gaussian_tilt (k : ℕ) (hk : 0 < k) :
    (radialPowerMeasure k).withDensity (fun x => ENNReal.ofReal (Real.exp (-x))) =
      ENNReal.ofReal (Real.Gamma (k : ℝ)) • ProbabilityTheory.gammaMeasure (k : ℝ) 1 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hgR : 0 < Real.Gamma (k : ℝ) := Real.Gamma_pos_of_pos hkR
  unfold radialPowerMeasure ProbabilityTheory.gammaMeasure
  rw [← withDensity_mul _ (by fun_prop) (by fun_prop),
    ← withDensity_indicator measurableSet_Ioi,
    ← withDensity_smul _ (by unfold ProbabilityTheory.gammaPDF; fun_prop)]
  apply withDensity_congr_ae
  filter_upwards [(volume : Measure ℝ).ae_ne (0 : ℝ)] with x hx0
  by_cases hx : 0 < x
  · simp only [mem_Ioi, hx, indicator_of_mem, Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
    rw [ProbabilityTheory.gammaPDF_of_nonneg hx.le]
    rw [← ENNReal.ofReal_mul hgR.le, ← ENNReal.ofReal_mul (pow_nonneg hx.le _)]
    congr 1
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      simp only [Nat.cast_sub hk, Nat.cast_one]
    rw [Real.one_rpow, one_mul, ← hcast, Real.rpow_natCast]
    field_simp
  · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hx0
    simp [hx, ProbabilityTheory.gammaPDF_of_neg hxneg]

/-- Once a Gaussian-tilted homogeneous radial law is normalized, its
proportionality constant cancels and its distribution is exactly Gamma. -/
theorem normalized_gaussian_tilt_gamma
    (k : ℕ) (hk : 0 < k) (b : ℝ≥0∞)
    (hprob : IsProbabilityMeasure
      (b • (radialPowerMeasure k).withDensity (fun x => ENNReal.ofReal (Real.exp (-x))))) :
    b • (radialPowerMeasure k).withDensity (fun x => ENNReal.ofReal (Real.exp (-x))) =
      ProbabilityTheory.gammaMeasure (k : ℝ) 1 := by
  have : IsProbabilityMeasure (ProbabilityTheory.gammaMeasure (k : ℝ) 1) :=
    ProbabilityTheory.isProbabilityMeasure_gammaMeasure (by exact_mod_cast hk) (by norm_num)
  rw [radialPowerMeasure_gaussian_tilt k hk, smul_smul] at hprob ⊢
  have htotal := hprob.measure_univ
  rw [smul_apply, measure_univ, smul_eq_mul, mul_one] at htotal
  rw [htotal, one_smul]

end
end GinibrePoincare
