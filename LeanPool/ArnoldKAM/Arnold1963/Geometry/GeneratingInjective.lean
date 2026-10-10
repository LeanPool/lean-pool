/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.GlobalInverse
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
The generating-function smallness bound gives injectivity of both mixed-coordinate maps
on the same buffered source domain.
-/

@[expose] public section
noncomputable section
open Set Metric
open scoped NNReal
namespace KamProject.Arnold1963

theorem generating_small_sixteenth {n : ℕ} (hn : 0 < n) {r : ℝ≥0} (hr : 0 < r)
    {M : ℝ} (hM : M < (r : ℝ) ^ 2 / (16 * n)) : M / r / r < 1 / 16 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : (16 : ℝ) ≤ 16 * n := by linarith
  have hb := hM.trans_le (div_le_div_of_nonneg_left (sq_nonneg (r : ℝ)) (by norm_num) hd)
  apply (div_lt_iff₀ (show (0 : ℝ) < r from hr)).2
  apply (div_lt_iff₀ (show (0 : ℝ) < r from hr)).2
  nlinarith

variable {n : ℕ} {S : ComplexPhaseSpace n → ℂ} {V : Set (ComplexPhaseSpace n)}
  {r : ℝ≥0} {M : ℝ}

theorem generating_injOn (hr : 0 < r) (hS : AnalyticOnNhd ℂ S V)
    (hM : NormBoundOn S V M) (hsmall : M / r / r < 1 / 16) :
    InjOn (generatingInput S) (erosion V r) ∧
      InjOn (generatingOutput S) (erosion V r) := by
  have hquarter : (0 : ℝ≥0) < r / 4 := by positivity
  have hhalf : r / 4 + r / 4 = r / 2 := by ring
  have hsum : r / 2 + r / 2 = r := by ring
  have hR : (0 : ℝ) < r := hr
  have hnum : M / (r / 4 : ℝ≥0) / (r / 4 : ℝ≥0) = 16 * (M / r / r) := by
    simp only [NNReal.coe_div, NNReal.coe_ofNat]
    field_simp
    ring
  let κ : ℝ≥0 := ⟨M / (r / 4 : ℝ≥0) / (r / 4 : ℝ≥0),
    div_nonneg (div_nonneg hM.nonneg (by positivity)) (by positivity)⟩
  have hk : κ < 1 := by change M / _ / _ < 1; rw [hnum]; linarith
  have hε : 2 * (M / r) ≤ (r / 2 : ℝ≥0) := by
    have hh := (div_lt_iff₀ hR).mp hsmall
    norm_num only [NNReal.coe_div, NNReal.coe_ofNat]
    linarith
  have hbuffer {x z : ComplexPhaseSpace n} (hx : x ∈ erosion V r)
      (hz : z ∈ closedBall x (r / 2 : ℝ≥0)) : z ∈ erosion V (r / 4 + r / 4) := by
    rw [hhalf]
    apply mem_erosion_of_dist_le (s := r / 2) (by simpa only [hsum] using hx) hz
  have hproof (b : Bool) :
      InjOn (fun x => x + if b then (0, pGradient S x) else (qGradient S x, 0))
        (erosion V r) := by
    apply injOn_add_of_local_lipschitz (ε := M / r) (κ := κ) (r := (r / 2 : ℝ≥0))
    · intro x hx
      cases b
      · simpa using norm_qGradient_le_div hr hS hM hx
      · simpa using norm_pGradient_le_div hr hS hM hx
    · exact hε
    · exact hk
    · intro x hx
      apply (convex_closedBall x (r / 2 : ℝ≥0)).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℂ)
      · intro z hz
        have ha := hS z (erosion_subset _ _ (hbuffer hx hz))
        cases b
        · exact ((analyticAt_qGradient ha).prod analyticAt_const).differentiableAt
        · exact (analyticAt_const.prod (analyticAt_pGradient ha)).differentiableAt
      · intro z hz
        have ha := hS z (erosion_subset _ _ (hbuffer hx hz))
        change ‖fderiv ℂ (fun x => if b then (0, pGradient S x)
          else (qGradient S x, 0)) z‖ ≤ (κ : ℝ)
        cases b
        · have hd := (analyticAt_qGradient ha).differentiableAt.hasFDerivAt.prodMk
            (hasFDerivAt_const (0 : ComplexSpace n) z)
          change ‖fderiv ℂ (fun x => (qGradient S x, 0)) z‖ ≤ _
          rw [hd.fderiv, ContinuousLinearMap.opNorm_prod]
          simp only [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
          convert norm_fderiv_qGradient_le hquarter hS hM (hbuffer hx hz) using 1
          simp [κ]
          rfl
        · have hd := (hasFDerivAt_const (0 : ComplexSpace n) z).prodMk
            (analyticAt_pGradient ha).differentiableAt.hasFDerivAt
          change ‖fderiv ℂ (fun x => (0, pGradient S x)) z‖ ≤ _
          rw [hd.fderiv, ContinuousLinearMap.opNorm_prod]
          simp only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
          convert norm_fderiv_pGradient_le hquarter hS hM (hbuffer hx hz) using 1
          simp [κ]
          rfl
  constructor
  · intro x hx y hy he
    apply hproof true hx hy
    simpa [Prod.add_def, generatingInput] using he
  · intro x hx y hy he
    apply hproof false hx hy
    simpa [Prod.add_def, generatingOutput] using he

end KamProject.Arnold1963
