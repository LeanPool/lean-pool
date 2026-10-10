/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Basic.Hamiltonian
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
First derivative bounds from one-variable Cauchy estimates along complex lines. All ambient
operator estimates use the specified maximum norm.
-/

@[expose] public section

noncomputable section
open scoped NNReal

namespace KamProject.Arnold1963

section Cauchy
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem line_mem_of_mem_erosion {U : Set E} {r : ℝ≥0} {x v : E}
    (hx : x ∈ erosion U r) (hv : ‖v‖ ≤ 1) {z : ℂ} (hz : ‖z‖ ≤ r) :
    x + z • v ∈ U := by
  apply hx
  rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
  exact (mul_le_mul_of_nonneg_left hv (norm_nonneg z)).trans (by simpa using hz)

theorem norm_fderiv_apply_le_div_of_mem_erosion {f : E → F} {U : Set E}
    {r : ℝ≥0} {M : ℝ} {x v : E} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f U) (hM : NormBoundOn f U M)
    (hx : x ∈ erosion U r) (hv : ‖v‖ ≤ 1) :
    ‖fderiv ℂ f x v‖ ≤ M / r := by
  let g : ℂ → F := fun z => f (x + z • v)
  have hg : DifferentiableOn ℂ g (Metric.closedBall 0 (r : ℝ)) := by
    intro z hz
    have hz' : ‖z‖ ≤ (r : ℝ) := by simpa using hz
    exact ((hf _ (line_mem_of_mem_erosion hx hv hz')).differentiableAt.comp z
      ((differentiableAt_id.smul_const v).const_add x)).differentiableWithinAt
  have hb : ∀ z ∈ Metric.sphere (0 : ℂ) (r : ℝ), ‖g z‖ ≤ M := by
    intro z hz
    exact hM.norm_le (line_mem_of_mem_erosion hx hv (by simpa using le_of_eq hz))
  have hg0 : HasDerivAt g (fderiv ℂ f x v) 0 := by
    have hline : HasDerivAt (fun z : ℂ => x + z • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
    have hf0 : HasFDerivAt f (fderiv ℂ f x) (x + (0 : ℂ) • v) := by
      simpa using (hf x (erosion_subset U r hx)).differentiableAt.hasFDerivAt
    simpa [g, Function.comp_def] using hf0.comp_hasDerivAt 0 hline
  rw [← hg0.deriv]
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
    (hg.diffContOnCl_ball (Set.Subset.refl _)) hb

theorem norm_fderiv_le_div_of_mem_erosion {f : E → F} {U : Set E}
    {r : ℝ≥0} {M : ℝ} {x : E} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f U) (hM : NormBoundOn f U M)
    (hx : x ∈ erosion U r) : ‖fderiv ℂ f x‖ ≤ M / r := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hM.nonneg r.coe_nonneg)
  intro v hv
  exact norm_fderiv_apply_le_div_of_mem_erosion hr hf hM hx hv.le

end Cauchy

theorem norm_pGradient_le_div {n : ℕ} {H : ComplexPhaseSpace n → ℂ}
    {U : Set (ComplexPhaseSpace n)} {r : ℝ≥0} {M : ℝ} {x : ComplexPhaseSpace n}
    (hr : 0 < r) (hH : AnalyticOnNhd ℂ H U) (hM : NormBoundOn H U M)
    (hx : x ∈ erosion U r) : ‖pGradient H x‖ ≤ M / r := by
  apply (complex_norm_le_iff _ (div_nonneg hM.nonneg r.coe_nonneg)).2
  intro j
  exact norm_fderiv_apply_le_div_of_mem_erosion hr hH hM hx (by simp)

theorem norm_qGradient_le_div {n : ℕ} {H : ComplexPhaseSpace n → ℂ}
    {U : Set (ComplexPhaseSpace n)} {r : ℝ≥0} {M : ℝ} {x : ComplexPhaseSpace n}
    (hr : 0 < r) (hH : AnalyticOnNhd ℂ H U) (hM : NormBoundOn H U M)
    (hx : x ∈ erosion U r) : ‖qGradient H x‖ ≤ M / r := by
  apply (complex_norm_le_iff _ (div_nonneg hM.nonneg r.coe_nonneg)).2
  intro j
  exact norm_fderiv_apply_le_div_of_mem_erosion hr hH hM hx (by simp)

theorem norm_hamiltonianVectorField_le_div {n : ℕ} {H : ComplexPhaseSpace n → ℂ}
    {U : Set (ComplexPhaseSpace n)} {r : ℝ≥0} {M : ℝ} {x : ComplexPhaseSpace n}
    (hr : 0 < r) (hH : AnalyticOnNhd ℂ H U) (hM : NormBoundOn H U M)
    (hx : x ∈ erosion U r) : ‖hamiltonianVectorField H x‖ ≤ M / r :=
  (norm_hamiltonianVectorField_le H x).trans
    (norm_fderiv_le_div_of_mem_erosion hr hH hM hx)

theorem AnalyticPhaseFunction.norm_vectorField_le_div {n : ℕ}
    {G : Set (ComplexSpace n)} {ρ r : ℝ≥0} (f : AnalyticPhaseFunction n G ρ)
    (hr : 0 < r) {x : ComplexPhaseSpace n} (hx : x ∈ erosion (phaseDomain G ρ) r) :
    ‖hamiltonianVectorField f.toFun x‖ ≤ f.uniformNorm / r :=
  norm_hamiltonianVectorField_le_div hr f.analytic (f.norm_le_iff.mp le_rfl) hx

end KamProject.Arnold1963
