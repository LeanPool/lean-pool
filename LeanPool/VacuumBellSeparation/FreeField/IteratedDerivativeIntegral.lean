/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Iterated differentiation under an integral with global derivative bounds

This is a reusable dominated-differentiation lemma. Every derivative has an
actual integrable majorant, uniform in the differentiated variable. The
hypotheses are proved for the polynomially bounded Fourier cutoff kernel in
`FreeField/CutoffFourierIntegral.lean` (`iteratedFDeriv_cutoffFourier_integral`);
they are not assumptions about the physical field or a distribution model.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace VacuumBellSeparation

theorem iteratedFDeriv_integral_of_global_bounds
    {P E F : Type*} [MeasurableSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure P) (f : P → E → F)
    (hf : ∀ p, ContDiff ℝ (⊤ : ℕ∞) (f p))
    (hmeas : ∀ j x, AEStronglyMeasurable (fun p => iteratedFDeriv ℝ j (f p) x) μ)
    (b : ℕ → P → ℝ) (hb : ∀ j p x, ‖iteratedFDeriv ℝ j (f p) x‖ ≤ b j p)
    (hbint : ∀ j, Integrable (b j) μ) (j : ℕ) (x : E) :
    iteratedFDeriv ℝ j (fun y => ∫ p, f p y ∂μ) x =
      ∫ p, iteratedFDeriv ℝ j (f p) x ∂μ := by
  have hint (j : ℕ) (x : E) : Integrable (fun p => iteratedFDeriv ℝ j (f p) x) μ :=
    (hbint j).mono' (hmeas j x) (Eventually.of_forall fun p => hb j p x)
  induction j generalizing x with
  | zero =>
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def]
    exact ((continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.integral_comp_comm _).symm
  | succ j ih =>
    let C := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F
    have hderivmeas (x : E) :
        AEStronglyMeasurable (fun p => fderiv ℝ (iteratedFDeriv ℝ j (f p)) x) μ := by
      simpa only [fderiv_iteratedFDeriv, Function.comp_def] using
        C.continuous.comp_aestronglyMeasurable (hmeas (j + 1) x)
    have hd : HasFDerivAt
        (fun y => ∫ p, iteratedFDeriv ℝ j (f p) y ∂μ)
        (∫ p, fderiv ℝ (iteratedFDeriv ℝ j (f p)) x ∂μ) x := by
      apply hasFDerivAt_integral_of_dominated_of_fderiv_le
        (𝕜 := ℝ) (μ := μ) (x₀ := x)
        (F := fun y p => iteratedFDeriv ℝ j (f p) y)
        (F' := fun y p => fderiv ℝ (iteratedFDeriv ℝ j (f p)) y)
        (s := univ) (bound := b (j + 1)) Filter.univ_mem
      · exact Eventually.of_forall (hmeas j)
      · exact hint j x
      · exact hderivmeas x
      · exact Eventually.of_forall fun p y hy => by
          rw [norm_fderiv_iteratedFDeriv]
          exact hb (j + 1) p y
      · exact hbint (j + 1)
      · exact Eventually.of_forall fun p y hy =>
          ((hf p).differentiable_iteratedFDeriv (m := j)
            (by exact_mod_cast ENat.natCast_lt_top j) y).hasFDerivAt
    have heq : iteratedFDeriv ℝ j (fun y => ∫ p, f p y ∂μ) =
        (fun y => ∫ p, iteratedFDeriv ℝ j (f p) y ∂μ) := funext ih
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, heq, hd.fderiv]
    change C.symm (∫ p, fderiv ℝ (iteratedFDeriv ℝ j (f p)) x ∂μ) = _
    calc
      _ = ∫ p, C.symm (fderiv ℝ (iteratedFDeriv ℝ j (f p)) x) ∂μ := by
        exact (LinearIsometry.integral_comp_comm (𝕜 := ℝ)
          (E := E →L[ℝ] E [×j]→L[ℝ] F) (F := E [×(j + 1)]→L[ℝ] F)
          C.symm.toLinearIsometry
          (fun p => fderiv ℝ (iteratedFDeriv ℝ j (f p)) x)).symm
      _ = _ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun p => by
          change C.symm (fderiv ℝ (iteratedFDeriv ℝ j (f p)) x) = _
          simp only [fderiv_iteratedFDeriv, Function.comp_apply, C,
            LinearIsometryEquiv.symm_apply_apply]

end VacuumBellSeparation
