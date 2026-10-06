/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatNorms

/-!
# Weak formulation of the smooth forced heat response

For a smooth compactly supported tensor supported in positive times, the forced
heat response satisfies, against every smooth compactly supported test
function, the weak gradient identity and the weak form of the heat equation
`∫∫ -Z_i ∂_t φ + ∑_j ∂_j Z_i ∂_j φ + ∑_j G_ij ∂_j φ = 0` used in
`lem:pv-stokes`.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

local instance : Measure.IsAddHaarMeasure (volume : Measure (Vec3 × ℝ)) := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- Integration by parts on `Vec3 × ℝ` against a smooth compactly supported test
function. -/
theorem integral_mul_fderiv_test {f ψ : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (v : Vec3 × ℝ) :
    ∫ p, f p * fderiv ℝ ψ p v = -∫ p, fderiv ℝ f p v * ψ p := by
  have hDf : Continuous (fun p => fderiv ℝ f p v) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDψ : Continuous (fun p => fderiv ℝ ψ p v) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDψc : HasCompactSupport (fun p => fderiv ℝ ψ p v) := hψc.fderiv_apply (𝕜 := ℝ) v
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hDf.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left)
    ((hf.continuous.mul hDψ).integrable_of_hasCompactSupport hDψc.mul_left)
    ((hf.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left)
    (fun p _ => hf.differentiable one_ne_zero p) (fun p _ => hψ.differentiable one_ne_zero p)

/-- The weak form of the forced heat equation for smooth compactly supported
tensors, on `Vec3 × ℝ`: for every smooth compactly supported test function,
`∫∫ -Z_i ∂_t ψ + ∑_j ∂_j Z_i ∂_j ψ + ∑_j g_ij ∂_j ψ = 0`. -/
theorem response_weak_equation {g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hg : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (g i j)) (hgc : ∀ i j, HasCompactSupport (g i j))
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (i : Fin 3) :
    ∫ p, (-(causalHeatConv (vecTimeDiv g i) p * fderiv ℝ ψ p (0, 1)) +
      ∑ j : Fin 3, fderiv ℝ (causalHeatConv (vecTimeDiv g i)) p (CKN.basisVec j, 0) *
        fderiv ℝ ψ p (CKN.basisVec j, 0) +
      ∑ j : Fin 3, g i j p * fderiv ℝ ψ p (CKN.basisVec j, 0)) = 0 := by
  set U : Vec3 × ℝ → ℝ := causalHeatConv (vecTimeDiv g i)
  have hU : ContDiff ℝ (⊤ : ℕ∞) U :=
    causalHeatConv_contDiff (vecTimeDiv_contDiff hg i) (vecTimeDiv_hasCompactSupport hgc i)
  have hDU (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ U p (CKN.basisVec j, 0)) :=
    contDiff_fderiv_apply_const hU _
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hcs {f : Vec3 × ℝ → ℝ} (hf : Continuous f) : Integrable (fun p => f p * ψ p) :=
    (hf.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left
  have hcs' {f : Vec3 × ℝ → ℝ} (hf : Continuous f) (v : Vec3 × ℝ) :
      Integrable (fun p => f p * fderiv ℝ ψ p v) :=
    (hf.mul ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hψc.fderiv_apply (𝕜 := ℝ) v).mul_left
  have hDc (F : Vec3 × ℝ → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (v : Vec3 × ℝ) :
      Continuous (fun p => fderiv ℝ F p v) :=
    (hF.continuous_fderiv (by simp)).clm_apply continuous_const
  have h1 := integral_mul_fderiv_test (hU.of_le (by simp)) hψ1 hψc (0, 1)
  have h2 (j : Fin 3) := integral_mul_fderiv_test ((hDU j).of_le (by simp)) hψ1 hψc
    (CKN.basisVec j, 0)
  have h3 (j : Fin 3) := integral_mul_fderiv_test ((hg i j).of_le (by simp)) hψ1 hψc
    (CKN.basisVec j, 0)
  have hpde (p : Vec3 × ℝ) : fderiv ℝ U p (0, 1) =
      ∑ j : Fin 3, fderiv ℝ (fun q => fderiv ℝ U q (CKN.basisVec j, 0)) p (CKN.basisVec j, 0) +
        ∑ j : Fin 3, fderiv ℝ (g i j) p (CKN.basisVec j, 0) := by
    have h := causalHeatConv_heat_equation (vecTimeDiv_contDiff hg i)
      (vecTimeDiv_hasCompactSupport hgc i) p
    simp only [vecTimeDiv] at h
    linarith only [h]
  -- name the second-order terms
  set DDU : Fin 3 → Vec3 × ℝ → ℝ := fun j p =>
    fderiv ℝ (fun q => fderiv ℝ U q (CKN.basisVec j, 0)) p (CKN.basisVec j, 0) with hDDU
  set Dg : Fin 3 → Vec3 × ℝ → ℝ := fun j p => fderiv ℝ (g i j) p (CKN.basisVec j, 0) with hDg
  have hDDUc (j : Fin 3) : Continuous (DDU j) := hDc _ (hDU j) _
  have hDgc (j : Fin 3) : Continuous (Dg j) := hDc _ (hg i j) _
  -- split the integral
  have hA : Integrable (fun p => -(U p * fderiv ℝ ψ p (0, 1))) := (hcs' hU.continuous _).neg
  have hB : Integrable (fun p => ∑ j : Fin 3, fderiv ℝ U p (CKN.basisVec j, 0) *
      fderiv ℝ ψ p (CKN.basisVec j, 0)) :=
    integrable_finsetSum _ fun j _ => hcs' (hDc U hU _) _
  have hC : Integrable (fun p => ∑ j : Fin 3, g i j p * fderiv ℝ ψ p (CKN.basisVec j, 0)) :=
    integrable_finsetSum _ fun j _ => hcs' (hg i j).continuous _
  have hAB : Integrable (fun p => -(U p * fderiv ℝ ψ p (0, 1)) +
      ∑ j : Fin 3, fderiv ℝ U p (CKN.basisVec j, 0) * fderiv ℝ ψ p (CKN.basisVec j, 0)) :=
    hA.add hB
  have hsum1 : (∫ p, ∑ j : Fin 3, fderiv ℝ U p (CKN.basisVec j, 0) *
      fderiv ℝ ψ p (CKN.basisVec j, 0)) = ∑ j : Fin 3, -∫ p, DDU j p * ψ p := by
    rw [integral_finsetSum _ fun j _ => hcs' (hDc U hU _) _]
    exact Finset.sum_congr rfl fun j _ => h2 j
  have hsum2 : (∫ p, ∑ j : Fin 3, g i j p * fderiv ℝ ψ p (CKN.basisVec j, 0)) =
      ∑ j : Fin 3, -∫ p, Dg j p * ψ p := by
    rw [integral_finsetSum _ fun j _ => hcs' (hg i j).continuous _]
    exact Finset.sum_congr rfl fun j _ => h3 j
  have hsplit : ∫ p, fderiv ℝ U p (0, 1) * ψ p =
      (∑ j : Fin 3, ∫ p, DDU j p * ψ p) + ∑ j : Fin 3, ∫ p, Dg j p * ψ p := by
    have hF : Integrable (fun p => ∑ j : Fin 3, DDU j p * ψ p) :=
      integrable_finsetSum _ fun j _ => hcs (hDDUc j)
    have hG : Integrable (fun p => ∑ j : Fin 3, Dg j p * ψ p) :=
      integrable_finsetSum _ fun j _ => hcs (hDgc j)
    have hpt : (fun p => fderiv ℝ U p (0, 1) * ψ p) =
        fun p => (∑ j : Fin 3, DDU j p * ψ p) + ∑ j : Fin 3, Dg j p * ψ p := by
      funext p
      rw [hpde, add_mul, Finset.sum_mul, Finset.sum_mul]
    rw [hpt, integral_add hF hG, integral_finsetSum _ fun j _ => hcs (hDDUc j),
      integral_finsetSum _ fun j _ => hcs (hDgc j)]
  calc
    _ = (-(∫ p, U p * fderiv ℝ ψ p (0, 1)) +
          (∫ p, ∑ j : Fin 3, fderiv ℝ U p (CKN.basisVec j, 0) *
            fderiv ℝ ψ p (CKN.basisVec j, 0))) +
        ∫ p, ∑ j : Fin 3, g i j p * fderiv ℝ ψ p (CKN.basisVec j, 0) := by
      rw [integral_add hAB hC, integral_add hA hB, integral_neg]
    _ = ((∫ p, fderiv ℝ U p (0, 1) * ψ p) + ∑ j : Fin 3, -∫ p, DDU j p * ψ p) +
        ∑ j : Fin 3, -∫ p, Dg j p * ψ p := by
      rw [h1, neg_neg, hsum1, hsum2]
    _ = (∫ p, fderiv ℝ U p (0, 1) * ψ p) -
        ((∑ j : Fin 3, ∫ p, DDU j p * ψ p) + ∑ j : Fin 3, ∫ p, Dg j p * ψ p) := by
      rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib]
      ring
    _ = 0 := by rw [hsplit, sub_self]

end ESS

end
