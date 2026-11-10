/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.EhrhardType.ConvexSublevels
public import LeanPool.EhrhardGaussian.Provider.EhrhardInequality
import Mathlib.Analysis.Convex.Continuous

/-! # Convex Gaussian images are of Ehrhard type

Ehrhard’s inequality applied to strict convex sublevels gives concavity of the Gaussian quantile.
The canonical affine realization handles constants on the Gaussian support,
including singular covariance and dimension zero. Possible lower-endpoint atoms
are retained throughout the strict-CDF argument.
-/

@[expose] public noncomputable section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open EhrhardGaussian.Gaussian
open scoped Pointwise

namespace EhrhardGaussian.EhrhardType

/-- The positive strict-CDF quantile is concave when no strict sublevel has full mass. -/
theorem concaveOn_gaussian_sublevel_quantile {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsGaussian μ]
    {F : EuclideanSpace ℝ (Fin n) → ℝ} (hF : ConvexOn ℝ univ F)
    (hupper : ∀ a, μ.map F (Iio a) < 1) :
    ConcaveOn ℝ {a | 0 < μ.map F (Iio a)}
      (fun a => Ehrhard.gaussianCDFChart.symm ((μ.map F (Iio a)).toReal)) := by
  have hcont : Continuous F := continuousOn_univ.mp (hF.continuousOn isOpen_univ)
  have hmap (a : ℝ) : μ.map F (Iio a) = μ {x | F x < a} :=
    Measure.map_apply hcont.measurable measurableSet_Iio
  have hbox (a : ℝ) (ha : 0 < μ.map F (Iio a)) :
      (μ.map F (Iio a)).toReal ∈ Ioo (0 : ℝ) 1 := by
    exact ⟨ENNReal.toReal_pos ha.ne' (measure_ne_top _ _),
      by simpa only [ENNReal.toReal_one] using
        (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2 (hupper a)⟩
  let g := fun a => Ehrhard.gaussianCDFChart.symm ((μ.map F (Iio a)).toReal)
  have hg (a : ℝ) (ha : 0 < μ.map F (Iio a)) :
      Ehrhard.gaussianCDF (g a) = (μ.map F (Iio a)).toReal :=
    Ehrhard.gaussianCDF_chart_symm (hbox a ha)
  have hconv (a : ℝ) : Convex ℝ {x | F x < a} := by
    simpa only [mem_univ, true_and] using hF.convex_lt a
  refine ⟨convex_positive_strictCDF _, ?_⟩
  intro a ha b hb p q hp hq hsum
  change p * g a + q * g b ≤ g (p * a + q * b)
  have hsub : p • {x | F x < a} + q • {x | F x < b} ⊆ {x | F x < p * a + q * b} := by
    rintro z ⟨u, hu, v, hv, rfl⟩
    obtain ⟨x, hx, rfl⟩ := Set.mem_smul_set.mp hu
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hv
    change F x < a at hx
    change F y < b at hy
    have hbound := hF.2 (mem_univ x) (mem_univ y) hp hq hsum
    have hstrict : p * F x + q * F y < p * a + q * b := by
      by_cases hp0 : p = 0
      · have hq1 : q = 1 := by linarith only [hsum, hp0]
        simpa only [hp0, hq1, zero_mul, zero_add, one_mul] using hy
      · exact add_lt_add_of_lt_of_le
          (mul_lt_mul_of_pos_left hx (lt_of_le_of_ne hp (Ne.symm hp0)))
          (mul_le_mul_of_nonneg_left hy.le hq)
    exact hbound.trans_lt hstrict
  have hpq : 1 - q = p := by linarith only [hsum]
  have hE := Provider.ehrhard_inequality μ _ _ (hconv a) (hconv b) q hq
    (by linarith only [hp, hsum]) (g a) (g b)
    (by change Ehrhard.gaussianCDF (g a) ≤ _; rw [hg a ha, hmap])
    (by change Ehrhard.gaussianCDF (g b) ≤ _; rw [hg b hb, hmap])
  rw [hpq] at hE
  apply Ehrhard.strictMono_gaussianCDF.le_iff_le.mp
  have hcpos : 0 < μ.map F (Iio (p * a + q * b)) := by
    simpa only [smul_eq_mul, mem_ofPred_eq] using (convex_positive_strictCDF (μ.map F)) ha hb hp hq
      hsum
  rw [hg _ hcpos, hmap]
  exact hE.trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub))

/-- The convex Gaussian image property, including constants on a singular Gaussian support and
lower-endpoint atoms. -/
theorem isEhrhardType_map_of_convex {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsGaussian μ]
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ConvexOn ℝ univ F) :
    IsEhrhardType (μ.map F) := by
  have hcont : Continuous F := continuousOn_univ.mp (hF.continuousOn isOpen_univ)
  let H : (Fin n → ℝ) → ℝ := F ∘ gaussianAffineMap μ
  have hH : ConvexOn ℝ univ H := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ p q hp hq hsum
    change F (gaussianAffineMap μ (p • x + q • y)) ≤ _
    rw [Ehrhard.gaussian_affine_combination μ hsum]
    exact hF.2 (mem_univ _) (mem_univ _) hp hq hsum
  have hHcont : Continuous H := continuousOn_univ.mp (hH.continuousOn isOpen_univ)
  have hlaw : (standardGaussianMeasure n).map H = μ.map F := by
    change (standardGaussianMeasure n).map (F ∘ gaussianAffineMap μ) = _
    rw [← Measure.map_map hcont.measurable (measurable_gaussianAffineMap μ),
      (hasLaw_gaussianAffineMap μ).map_eq]
  by_cases hn : ∀ x, H x = H 0
  · rw [← hlaw, show H = fun _ => H 0 from funext hn,
      Measure.map_const, measure_univ, one_smul]
    exact isEhrhardType_dirac _
  have hnormal : IsOpenPosMeasure (gaussianReal 0 1) :=
    isOpenPosMeasure_gaussianReal 0 (v := 1) one_ne_zero
  have : IsOpenPosMeasure (standardGaussianMeasure n) := by
    unfold standardGaussianMeasure
    infer_instance
  have hupper (a : ℝ) : μ.map F (Iio a) < 1 := by
    rw [← hlaw, Measure.map_apply hHcont.measurable measurableSet_Iio]
    exact strict_sublevel_measure_lt_one (standardGaussianMeasure n) hH hHcont hn a
  refine ⟨inferInstance,
    Or.inr ⟨hupper, fun a => Ehrhard.gaussianCDFChart.symm ((μ.map F (Iio a)).toReal),
      concaveOn_gaussian_sublevel_quantile μ hF hupper, ?_⟩⟩
  intro a ha
  have hbox : (μ.map F (Iio a)).toReal ∈ Ioo (0 : ℝ) 1 :=
    ⟨ENNReal.toReal_pos ha.ne' (measure_ne_top _ _),
      by simpa only [ENNReal.toReal_one] using
        (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2 (hupper a)⟩
  exact (Ehrhard.gaussianCDF_chart_symm hbox).symm

end EhrhardGaussian.EhrhardType

end
