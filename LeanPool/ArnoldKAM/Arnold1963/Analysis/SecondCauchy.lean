/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Analysis.Cauchy
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
Second Frechet derivative bounds from one-variable Cauchy estimates. Symmetric bilinear
polarization improves the mixed-coordinate constant when both sum and difference directions
lie in the unit ball.
-/

@[expose] public section

noncomputable section
open scoped NNReal Topology
namespace KamProject.Arnold1963

section Lines
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem deriv_line_eq_fderiv {f : E → F} {x v : E} {z : ℂ}
    (hf : DifferentiableAt ℂ f (x + z • v)) :
    deriv (fun w : ℂ => f (x + w • v)) z = fderiv ℂ f (x + z • v) v := by
  have hline : HasDerivAt (fun w : ℂ => x + w • v) v z := by
    simpa using ((hasDerivAt_id z).smul_const v).const_add x
  simpa [Function.comp_def] using (hf.hasFDerivAt.comp_hasDerivAt z hline).deriv

variable [CompleteSpace F]

theorem iteratedDeriv_two_line_eq {f : E → F} {U : Set E} {r : ℝ≥0}
    {x v : E} (hr : 0 < r) (hf : AnalyticOnNhd ℂ f U)
    (hx : x ∈ erosion U r) (hv : ‖v‖ ≤ 1) :
    iteratedDeriv 2 (fun z : ℂ => f (x + z • v)) 0 =
      fderiv ℂ (fderiv ℂ f) x v v := by
  have heq : (fun z => deriv (fun w : ℂ => f (x + w • v)) z) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => fderiv ℂ f (x + z • v) v) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with z hz
    apply deriv_line_eq_fderiv
    have hz' : ‖z‖ < (r : ℝ) := by simpa using hz
    exact (hf _ (line_mem_of_mem_erosion hx hv hz'.le)).differentiableAt
  have hline : HasDerivAt (fun z : ℂ => x + z • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
  have hdf : HasFDerivAt (fderiv ℂ f) (fderiv ℂ (fderiv ℂ f) x) (x + (0 : ℂ) • v) := by
    simpa using (hf x (erosion_subset U r hx)).fderiv.differentiableAt.hasFDerivAt
  have hdfLine : HasDerivAt (fun z : ℂ => fderiv ℂ f (x + z • v))
      (fderiv ℂ (fderiv ℂ f) x v) 0 := hdf.comp_hasDerivAt 0 hline
  have hd : HasDerivAt (fun z : ℂ => fderiv ℂ f (x + z • v) v)
      (fderiv ℂ (fderiv ℂ f) x v v) 0 := by
    simpa using hdfLine.clm_apply (hasDerivAt_const (0 : ℂ) v)
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, heq.deriv_eq]
  simpa [Function.comp_def] using hd.deriv

theorem norm_second_fderiv_diag_le {f : E → F} {U : Set E} {r : ℝ≥0}
    {M : ℝ} {x v : E} (hr : 0 < r) (hf : AnalyticOnNhd ℂ f U)
    (hM : NormBoundOn f U M) (hx : x ∈ erosion U r) (hv : ‖v‖ ≤ 1) :
    ‖fderiv ℂ (fderiv ℂ f) x v v‖ ≤ 2 * M / (r : ℝ) ^ 2 := by
  have hg : DifferentiableOn ℂ (fun z : ℂ => f (x + z • v))
      (Metric.closedBall 0 (r : ℝ)) := by
    intro z hz
    exact ((hf _ (line_mem_of_mem_erosion hx hv (by simpa using hz))).differentiableAt.comp z
      ((differentiableAt_id.smul_const v).const_add x)).differentiableWithinAt
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hr
    (hg.diffContOnCl_ball (Set.Subset.refl _))
    (fun z hz => hM.norm_le (line_mem_of_mem_erosion hx hv (by simpa using le_of_eq hz)))
  simpa [iteratedDeriv_two_line_eq hr hf hx hv] using h

end Lines

theorem norm_second_fderiv_mixed_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {U : Set E} {r : ℝ≥0} {M : ℝ} {x v w : E}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f U) (hM : NormBoundOn f U M)
    (hx : x ∈ erosion U r) (hplus : ‖v + w‖ ≤ 1) (hminus : ‖v - w‖ ≤ 1) :
    ‖fderiv ℂ (fderiv ℂ f) x v w‖ ≤ M / (r : ℝ) ^ 2 := by
  let B := fderiv ℂ (fderiv ℂ f) x
  have hsym : B w v = B v w :=
    (hf x (erosion_subset U r hx)).contDiffAt.isSymmSndFDerivAt_of_omega w v
  have hid : (4 : ℂ) * B v w = B (v + w) (v + w) - B (v - w) (v - w) := by
    simp only [map_add, map_sub, add_apply, sub_apply]
    rw [hsym]
    ring
  have hp := norm_second_fderiv_diag_le hr hf hM hx hplus
  have hm := norm_second_fderiv_diag_le hr hf hM hx hminus
  have hb := (norm_sub_le (B (v + w) (v + w)) (B (v - w) (v - w))).trans (add_le_add hp hm)
  rw [← hid, norm_mul] at hb
  norm_num at hb
  simp only [mul_div_assoc] at hb
  dsimp [B] at hb
  linarith only [hb]

theorem norm_second_coordinate_le {n : ℕ} {f : ComplexSpace n → ℂ}
    {U : Set (ComplexSpace n)} {r : ℝ≥0} {M : ℝ} {x : ComplexSpace n}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f U) (hM : NormBoundOn f U M)
    (hx : x ∈ erosion U r) (i j : Fin n) :
    ‖fderiv ℂ (fderiv ℂ f) x (Pi.single i 1) (Pi.single j 1)‖ ≤
      2 * M / (r : ℝ) ^ 2 := by
  by_cases hij : i = j
  · subst j
    exact norm_second_fderiv_diag_le hr hf hM hx (by simp [Pi.norm_single])
  · have hp : ‖(Pi.single i 1 : ComplexSpace n) + Pi.single j 1‖ ≤ 1 := by
      apply (complex_norm_le_iff _ zero_le_one).2
      intro k
      by_cases hi : k = i <;> by_cases hj : k = j
      · exact False.elim (hij (hi.symm.trans hj))
      · simp [hi, hij]
      · simp [hj, Ne.symm hij]
      · simp [hi, hj]
    have hm : ‖(Pi.single i 1 : ComplexSpace n) - Pi.single j 1‖ ≤ 1 := by
      apply (complex_norm_le_iff _ zero_le_one).2
      intro k
      by_cases hi : k = i <;> by_cases hj : k = j
      · exact False.elim (hij (hi.symm.trans hj))
      · simp [hi, hij]
      · simp [hj, Ne.symm hij]
      · simp [hi, hj]
    refine (norm_second_fderiv_mixed_le hr hf hM hx hp hm).trans ?_
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    linarith [hM.nonneg]

end KamProject.Arnold1963
