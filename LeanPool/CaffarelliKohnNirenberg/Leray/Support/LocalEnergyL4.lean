/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.VelocityTenThirds
public import LeanPool.CaffarelliKohnNirenberg.Setting.ExtSobolevBallSupported
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.H1.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Local Energy L4

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CKN

/-- The spatial interpolation step used for manuscript label `lem:lei-L4` of the
Escauriaza–Seregin–Šverák manuscript:
an `H¹` slice in `L³` belongs to `L⁴`, with a bound that retains the `L³`
factor and the Sobolev `L⁶` factor for later time integration. -/
theorem scalarH1L4_bound {x₀ : Vec3} {r : ℝ} (hr : 0 < r)
    (v : H1Function (euclideanBall x₀ r))
    (h3 : MemLp v.toFun 3 (volume.restrict (euclideanBall x₀ r))) :
    MemLp v.toFun 4 (volume.restrict (euclideanBall x₀ r)) ∧
      eLpNorm v.toFun 4 (volume.restrict (euclideanBall x₀ r)) ^ (4 : ℝ) ≤
        eLpNorm v.toFun 3 (volume.restrict (euclideanBall x₀ r)) ^ (2 : ℝ) *
          (ENNReal.ofReal sobolevPoincareFaithfulC5 *
            (eLpNorm v.grad 2 (volume.restrict (euclideanBall x₀ r)) +
              (ENNReal.ofReal r)⁻¹ * eLpNorm v.toFun 2
                (volume.restrict (euclideanBall x₀ r)))) ^ (2 : ℝ) := by
  let μ := volume.restrict (euclideanBall x₀ r)
  have hfun2 : MemLp v.toFun 2 μ := by simpa [μ, MemL2On, MemLpOn] using v.memL2
  have hgrad2 : MemLp v.grad 2 μ := (memLp_pi_iff).2 v.gradMemL2
  have hsob := extSobolevBall_everyBall hr v
  have hsobRhs : ENNReal.ofReal sobolevPoincareFaithfulC5 *
        (weakGradientLpNormOn 2 (euclideanBall x₀ r) v.grad +
          (ENNReal.ofReal r)⁻¹ * lpNormOn 2 (euclideanBall x₀ r) v.toFun) < ⊤ := by
    rw [ENNReal.mul_lt_top_iff]
    left
    constructor
    · exact ENNReal.ofReal_lt_top
    · rw [ENNReal.add_lt_top]
      refine ⟨hgrad2.eLpNorm_lt_top, ?_⟩
      rw [ENNReal.mul_lt_top_iff]
      exact Or.inl ⟨ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hr), hfun2.eLpNorm_lt_top⟩
  have h6top : lpNormOn 6 (euclideanBall x₀ r) v.toFun < ⊤ := lt_of_le_of_lt hsob hsobRhs
  have h6 : MemLp v.toFun 6 μ := by
    rw [memLp_iff]
    exact h6top
  have hpow3 : MemLp (fun x => ‖v.toFun x‖ ^ (2 : ℝ)) (3/2 : ℝ≥0∞) μ := by
    have h := h3.norm_rpow_div (2 : ℝ≥0∞)
    simpa [ENNReal.toReal_ofNat, div_eq_mul_inv] using h
  have hpow6 : MemLp (fun x => ‖v.toFun x‖ ^ (2 : ℝ)) 3 μ := by
    have h := h6.norm_rpow_div (2 : ℝ≥0∞)
    have heq : (6 : ℝ≥0∞) / 2 = 3 := by
      symm
      apply (ENNReal.eq_div_iff (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)).2
      norm_num
    rw [heq] at h
    exact h
  have hprod : MemLp (fun x => (‖v.toFun x‖ ^ (2 : ℝ)) * (‖v.toFun x‖ ^ (2 : ℝ))) 1 μ :=
    MeasureTheory.MemLp.mul (p := (3/2 : ℝ≥0∞)) (q := (3 : ℝ≥0∞)) (r := (1 : ℝ≥0∞))
      (φ := fun x => ‖v.toFun x‖ ^ (2 : ℝ))
      (f := fun x => ‖v.toFun x‖ ^ (2 : ℝ)) hpow3 hpow6
  have hprodTop : eLpNorm (fun x => ‖v.toFun x‖ ^ (4 : ℝ)) 1 μ < ⊤ := by
    have hEq : (fun x => (‖v.toFun x‖ ^ (2 : ℝ)) * (‖v.toFun x‖ ^ (2 : ℝ))) =
        (fun x => ‖v.toFun x‖ ^ (4 : ℝ)) := by
      funext x
      by_cases hx : ‖v.toFun x‖ = 0
      · simp [hx]
      · have hxpos : 0 < ‖v.toFun x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
        rw [← Real.rpow_add hxpos]
        norm_num
    rw [← hEq]
    exact hprod.eLpNorm_lt_top
  have hpowEq := eLpNorm_norm_rpow v.toFun hfun2.aestronglyMeasurable
    (p := (1:ℝ≥0∞)) (q := (4:ℝ)) (by norm_num)
  have hpowEq' : eLpNorm (fun x => ‖v.toFun x‖ ^ (4 : ℝ)) 1 μ =
      eLpNorm v.toFun 4 μ ^ (4 : ℝ) := by
    rw [hpowEq]
    norm_num
  have hfourTop : eLpNorm v.toFun 4 μ < ⊤ := by
    rw [hpowEq'] at hprodTop
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mp hprodTop
  have hpow3Eq : eLpNorm (fun x => ‖v.toFun x‖ ^ (2 : ℝ)) (3/2 : ℝ≥0∞) μ =
      eLpNorm v.toFun 3 μ ^ (2 : ℝ) := by
    rw [eLpNorm_norm_rpow v.toFun h3.aestronglyMeasurable (p := (3/2 : ℝ≥0∞))
      (q := (2 : ℝ)) (by norm_num)]
    have heq : (3/2 : ℝ≥0∞) * ENNReal.ofReal (2 : ℝ) = 3 := by
      have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
      rw [h2]
      exact ENNReal.div_mul_cancel (a := (2 : ℝ≥0∞)) (b := (3 : ℝ≥0∞))
        (by norm_num) (by norm_num)
    rw [heq]
  have hpow6Eq : eLpNorm (fun x => ‖v.toFun x‖ ^ (2 : ℝ)) 3 μ =
      eLpNorm v.toFun 6 μ ^ (2 : ℝ) := by
    rw [eLpNorm_norm_rpow v.toFun h6.aestronglyMeasurable (p := (3 : ℝ≥0∞))
      (q := (2 : ℝ)) (by norm_num)]
    norm_num
  have hholder := eLpNorm_smul_le_mul_eLpNorm
    (p := (3/2 : ℝ≥0∞)) (q := (3 : ℝ≥0∞)) (r := (1 : ℝ≥0∞))
    hpow3.aestronglyMeasurable hpow6.aestronglyMeasurable
  have hsobNorm : eLpNorm v.toFun 6 μ ≤
      ENNReal.ofReal sobolevPoincareFaithfulC5 *
        (eLpNorm v.grad 2 μ + (ENNReal.ofReal r)⁻¹ * eLpNorm v.toFun 2 μ) := by
    simpa [lpNormOn, weakGradientLpNormOn, μ] using hsob
  have hholder' : eLpNorm (fun x => ‖v.toFun x‖ ^ (2 : ℝ) *
      ‖v.toFun x‖ ^ (2 : ℝ)) 1 μ ≤
      eLpNorm (fun x => ‖v.toFun x‖ ^ (2 : ℝ)) (3/2 : ℝ≥0∞) μ *
        eLpNorm (fun x => ‖v.toFun x‖ ^ (2 : ℝ)) 3 μ := by
    calc
      _ = eLpNorm ((fun x => ‖v.toFun x‖ ^ (2 : ℝ)) •
          (fun x => ‖v.toFun x‖ ^ (2 : ℝ))) 1 μ := by
            apply eLpNorm_congr_ae
            filter_upwards with x
            simp [smul_eq_mul]
      _ ≤ _ := hholder
  have hpowEq4 : eLpNorm (fun x => ‖v.toFun x‖ ^ (4 : ℝ)) 1 μ =
      eLpNorm v.toFun 4 μ ^ (4 : ℝ) := by
    rw [eLpNorm_norm_rpow v.toFun hfun2.aestronglyMeasurable (p := (1:ℝ≥0∞))
      (q := (4:ℝ)) (by norm_num)]
    norm_num
  have hEq2 : (fun x => (‖v.toFun x‖ ^ (2 : ℝ)) * (‖v.toFun x‖ ^ (2 : ℝ))) =
      (fun x => ‖v.toFun x‖ ^ (4 : ℝ)) := by
    funext x
    by_cases hx : ‖v.toFun x‖ = 0
    · simp [hx]
    · have hxpos : 0 < ‖v.toFun x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
      rw [← Real.rpow_add hxpos]
      norm_num
  have hbound : eLpNorm v.toFun 4 μ ^ (4 : ℝ) ≤
      eLpNorm v.toFun 3 μ ^ (2 : ℝ) *
        (ENNReal.ofReal sobolevPoincareFaithfulC5 *
          (eLpNorm v.grad 2 μ + (ENNReal.ofReal r)⁻¹ * eLpNorm v.toFun 2 μ)) ^ (2 : ℝ) := by
    calc
      eLpNorm v.toFun 4 μ ^ (4 : ℝ) = eLpNorm (fun x => ‖v.toFun x‖ ^ (4 : ℝ)) 1 μ :=
        hpowEq4.symm
      _ = eLpNorm (fun x => (‖v.toFun x‖ ^ (2 : ℝ)) * (‖v.toFun x‖ ^ (2 : ℝ))) 1 μ := by
        rw [← hEq2]
      _ ≤ eLpNorm (fun x => ‖v.toFun x‖ ^ (2 : ℝ)) (3/2 : ℝ≥0∞) μ *
            eLpNorm (fun x => ‖v.toFun x‖ ^ (2 : ℝ)) 3 μ := hholder'
      _ = eLpNorm v.toFun 3 μ ^ (2 : ℝ) * eLpNorm v.toFun 6 μ ^ (2 : ℝ) := by
            rw [hpow3Eq, hpow6Eq]
      _ ≤ eLpNorm v.toFun 3 μ ^ (2 : ℝ) *
            (ENNReal.ofReal sobolevPoincareFaithfulC5 *
              (eLpNorm v.grad 2 μ + (ENNReal.ofReal r)⁻¹ * eLpNorm v.toFun 2 μ)) ^ (2 : ℝ) := by
            gcongr
  rw [memLp_iff]
  exact ⟨hfourTop, hbound⟩

end CKN
