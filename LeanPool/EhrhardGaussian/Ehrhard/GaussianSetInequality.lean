/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.AffineGaussianSets

/-! # Ehrhard's inequality for convex sets and arbitrary Gaussian laws -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open EhrhardGaussian.Gaussian
open scoped Pointwise

namespace EhrhardGaussian.Ehrhard

/-- The affine Gaussian map preserves affine combinations whose coefficients sum to one. -/
theorem gaussian_affine_combination {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    {p q : ℝ} (hsum : p + q = 1) (x y : Fin n → ℝ) :
    gaussianAffineMap μ (p • x + q • y) = p • gaussianAffineMap μ x + q • gaussianAffineMap μ y :=
      by
  rw [gaussianAffineMap_eq]
  simp only [map_add, map_smul, smul_add]
  rw [add_add_add_comm, ← add_smul, hsum, one_smul]

/-- Ehrhard's inequality holds for convex sets under Gaussian measure with positive combination
coefficients. -/
theorem gaussian_set_ehrhard_pos {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsGaussian μ] {A B : Set (EuclideanSpace ℝ (Fin n))}
    (hA : Convex ℝ A) (hB : Convex ℝ B)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hsum : p + q = 1) {a b : ℝ}
    (ha : gaussianCDF a ≤ (μ A).toReal) (hb : gaussianCDF b ≤ (μ B).toReal) :
    gaussianCDF (p * a + q * b) ≤ (μ (p • A + q • B)).toReal := by
  let f := gaussianAffineMap μ
  have hAc : Convex ℝ (f ⁻¹' A) := by
    change Convex ℝ ((fun x => (∫ y, y ∂μ) + gaussianLinearMap μ x) ⁻¹' A)
    exact (hA.translate_preimage_right _).linear_preimage (gaussianLinearMap μ).toLinearMap
  have hBc : Convex ℝ (f ⁻¹' B) := by
    change Convex ℝ ((fun x => (∫ y, y ∂μ) + gaussianLinearMap μ x) ⁻¹' B)
    exact (hB.translate_preimage_right _).linear_preimage (gaussianLinearMap μ).toLinearMap
  have hcomp := standard_convex_set_ehrhard hAc hBc hp hq hsum
    (by simpa only [gaussian_convex_preimage_measure μ hA] using ha)
    (by simpa only [gaussian_convex_preimage_measure μ hB] using hb)
  have hsub : p • (f ⁻¹' A) + q • (f ⁻¹' B) ⊆ f ⁻¹' (p • A + q • B) := by
    rintro z ⟨u, hu, v, hv, rfl⟩
    obtain ⟨x, hx, rfl⟩ := Set.mem_smul_set.mp hu
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hv
    change gaussianAffineMap μ (p • x + q • y) ∈ p • A + q • B
    rw [gaussian_affine_combination μ hsum]
    exact Set.add_mem_add (Set.smul_mem_smul_set hx) (Set.smul_mem_smul_set hy)
  have houter : standardGaussianMeasure n (f ⁻¹' (p • A + q • B)) ≤ μ (p • A + q • B) := by
    exact (Measure.le_map_apply (measurable_gaussianAffineMap μ).aemeasurable _).trans_eq
      (congrArg (fun ν : Measure (EuclideanSpace ℝ (Fin n)) => ν (p • A + q • B))
        (hasLaw_gaussianAffineMap μ).map_eq)
  exact hcomp.trans (ENNReal.toReal_mono (measure_ne_top _ _) ((measure_mono hsub).trans houter))

/-- Ehrhard's inequality holds for convex sets under Gaussian measure for every convex combination.
-/
theorem gaussian_set_ehrhard {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsGaussian μ] {A B : Set (EuclideanSpace ℝ (Fin n))}
    (hA : Convex ℝ A) (hB : Convex ℝ B) (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (a b : ℝ) (ha : gaussianCDF a ≤ (μ A).toReal) (hb : gaussianCDF b ≤ (μ B).toReal) :
    gaussianCDF ((1 - t) * a + t * b) ≤ (μ ((1 - t) • A + t • B)).toReal := by
  have hAne : A.Nonempty := by
    by_contra hn
    have hzero : μ A = 0 := by rw [Set.not_nonempty_iff_eq_empty.mp hn, measure_empty]
    rw [hzero, ENNReal.toReal_zero] at ha
    exact (not_le_of_gt (gaussianCDF_pos a)) ha
  have hBne : B.Nonempty := by
    by_contra hn
    have hzero : μ B = 0 := by rw [Set.not_nonempty_iff_eq_empty.mp hn, measure_empty]
    rw [hzero, ENNReal.toReal_zero] at hb
    exact (not_le_of_gt (gaussianCDF_pos b)) hb
  by_cases ht0 : t = 0
  · subst t
    obtain ⟨y, hy⟩ := hBne
    have hsub : A ⊆ (1 - (0 : ℝ)) • A + (0 : ℝ) • B := by
      intro x hx
      have h := Set.add_mem_add (Set.smul_mem_smul_set (a := (1 : ℝ)) hx)
        (Set.smul_mem_smul_set (a := (0 : ℝ)) hy)
      simpa using h
    simpa only [sub_zero, one_mul, zero_mul, add_zero] using
      ha.trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub))
  by_cases ht1 : t = 1
  · subst t
    obtain ⟨x, hx⟩ := hAne
    have hsub : B ⊆ (1 - (1 : ℝ)) • A + (1 : ℝ) • B := by
      intro y hy
      have h := Set.add_mem_add (Set.smul_mem_smul_set (a := (0 : ℝ)) hx)
        (Set.smul_mem_smul_set (a := (1 : ℝ)) hy)
      simpa using h
    simpa only [sub_self, zero_mul, one_mul, zero_add] using
      hb.trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub))
  exact gaussian_set_ehrhard_pos μ hA hB (sub_pos.mpr (lt_of_le_of_ne ht₁ ht1)) (lt_of_le_of_ne ht₀
    (Ne.symm ht0))
    (by ring) ha hb

end EhrhardGaussian.Ehrhard

end
