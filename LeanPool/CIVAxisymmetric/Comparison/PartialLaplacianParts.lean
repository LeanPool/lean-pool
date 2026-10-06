/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.PartialLaplacian
public import LeanPool.CIVAxisymmetric.Statements.GradPair
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Green's identity for the truncated spatial Laplacian

This file proves the integration-by-parts identity needed for the comparison energy
inequality: moving one derivative from the truncated Laplacian `partialLaplacian` onto a
second compactly supported test function.  This is the missing ingredient for integrating
the mollified equation against a Kato test function in the mollified comparison equation.
-/

public section

open MeasureTheory
open CKN


noncomputable section

namespace CIV



/-- The spatial gradient paired with a basis vector is smooth when the test function
is smooth on each time slice. -/
theorem contDiff_gradPair_of_contDiff {m : ℕ} {φ : Vec m × ℝ → ℝ} {τ : ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m => φ (x, τ))) (i : Fin m) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m => gradPair m φ (x, τ) (basisVec i)) := by
  have h_fderiv : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (fun x : Vec m => φ (x, τ))) :=
    hφ.fderiv_right (by simp)
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m =>
      (fderiv ℝ (fun y : Vec m => φ (y, τ))) x (basisVec i)) :=
    h_fderiv.clm_apply contDiff_const
  simpa [gradPair] using h

/-- The spatial gradient paired with a basis vector has compact support when the test
function does. -/
theorem hasCompactSupport_gradPair_of_hasCompactSupport {m : ℕ} {φ : Vec m × ℝ → ℝ} {τ : ℝ}
    (hsupp : HasCompactSupport (fun x : Vec m => φ (x, τ))) (i : Fin m) :
    HasCompactSupport (fun x : Vec m => gradPair m φ (x, τ) (basisVec i)) := by
  simpa [gradPair] using hsupp.fderiv_apply (𝕜 := ℝ) (basisVec i)

/-- Integration by parts: one derivative of `gradPair` can be moved onto a second
compactly supported test function. -/
theorem integral_gradPair_deriv_mul_eq_neg_integral_gradPair_mul
    {m : ℕ} {φ ψ : Vec m × ℝ → ℝ} {τ : ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m => φ (x, τ)))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m => ψ (x, τ)))
    (hφsupp : HasCompactSupport (fun x : Vec m => φ (x, τ))) (i : Fin m) :
    ∫ x : Vec m,
        fderiv ℝ (fun y : Vec m => gradPair m φ (y, τ) (basisVec i)) x (basisVec i) * ψ (x, τ)
      = - ∫ x : Vec m, gradPair m φ (x, τ) (basisVec i) * gradPair m ψ (x, τ) (basisVec i) := by
  let f : Vec m → ℝ := fun x => ψ (x, τ)
  let g : Vec m → ℝ := fun x => gradPair m φ (x, τ) (basisVec i)
  have hf_cont : Continuous f := hψ.continuous
  have hg_cont : Continuous g :=
    (contDiff_gradPair_of_contDiff hφ i).continuous
  have hg_supp : HasCompactSupport g :=
    hasCompactSupport_gradPair_of_hasCompactSupport hφsupp i
  have h_fderiv_g_cont : Continuous (fun x : Vec m =>
      fderiv ℝ (fun y : Vec m => gradPair m φ (y, τ) (basisVec i)) x (basisVec i)) := by
    have h_cdiff : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m => gradPair m φ (x, τ) (basisVec i)) :=
      contDiff_gradPair_of_contDiff hφ i
    have h_cont : Continuous (fun p : Vec m × Vec m =>
        (fderiv ℝ (fun y : Vec m => gradPair m φ (y, τ) (basisVec i)) p.1) p.2) :=
      h_cdiff.continuous_fderiv_apply (by simp)
    exact h_cont.comp (continuous_id.prodMk continuous_const)
  have h_fderiv_g_supp : HasCompactSupport (fun x : Vec m =>
      fderiv ℝ (fun y : Vec m => gradPair m φ (y, τ) (basisVec i)) x (basisVec i)) :=
    hg_supp.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have h_fderiv_f_cont : Continuous (fun x : Vec m =>
      fderiv ℝ (fun y : Vec m => ψ (y, τ)) x (basisVec i)) := by
    have h_cont : Continuous (fun p : Vec m × Vec m =>
        (fderiv ℝ (fun y : Vec m => ψ (y, τ)) p.1) p.2) :=
      hψ.continuous_fderiv_apply (by simp)
    exact h_cont.comp (continuous_id.prodMk continuous_const)
  -- Integrability hypotheses for the integration-by-parts theorem.
  have hf'g : Integrable (fun x => fderiv ℝ f x (basisVec i) * g x) (μ := volume) := by
    have h := (hg_cont.mul h_fderiv_f_cont).integrable_of_hasCompactSupport
      (hg_supp.mul_right (f' := fun x => fderiv ℝ (fun y => ψ (y, τ)) x (basisVec i)))
      (μ := volume)
    have : (fun x => fderiv ℝ f x (basisVec i) * g x) =
        (fun x => g x * fderiv ℝ (fun y => ψ (y, τ)) x (basisVec i)) := by
      ext x; simp [f, g, mul_comm]
    rw [this]
    exact h
  have hfg' : Integrable (fun x => f x * fderiv ℝ g x (basisVec i)) (μ := volume) := by
    have h := (h_fderiv_g_cont.mul hf_cont).integrable_of_hasCompactSupport
      (h_fderiv_g_supp.mul_right (f' := f)) (μ := volume)
    have : (fun x => f x * fderiv ℝ g x (basisVec i)) =
        ((fun x => fderiv ℝ g x (basisVec i)) * f) := by
      ext x; exact mul_comm _ _
    rw [this]
    exact h
  have hfg : Integrable (fun x => f x * g x) (μ := volume) := by
    have h := (hg_cont.mul hf_cont).integrable_of_hasCompactSupport
      (hg_supp.mul_right (f' := f)) (μ := volume)
    have : (fun x => f x * g x) = (g * f) := by
      ext x; exact mul_comm _ _
    rw [this]
    exact h
  have hf_diff : ∀ x ∈ tsupport g, DifferentiableAt ℝ f x := by
    intro x _hx
    exact hψ.differentiable (by simp) x
  have hg_diff : ∀ x ∈ tsupport f, DifferentiableAt ℝ g x := by
    intro x _hx
    have h_cdiff : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_gradPair_of_contDiff hφ i
    exact h_cdiff.differentiable (by simp) x
  have h_ibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    hf'g hfg' hfg hf_diff hg_diff
  -- h_ibp : ∫ x, f x * fderiv ℝ g x (basisVec i) = - ∫ x, fderiv ℝ f x (basisVec i) * g x
  calc
    ∫ x : Vec m, fderiv ℝ (fun y : Vec m => gradPair m φ (y, τ) (basisVec i)) x (basisVec i) * ψ
      (x, τ)
        = ∫ x : Vec m, (fderiv ℝ g x (basisVec i)) * f x := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
          simp [g, f, mul_comm]
    _ = ∫ x : Vec m, f x * fderiv ℝ g x (basisVec i) := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun x => mul_comm _ _))
    _ = - ∫ x : Vec m, fderiv ℝ f x (basisVec i) * g x := h_ibp
    _ = - ∫ x : Vec m, g x * fderiv ℝ f x (basisVec i) := by
          refine congrArg (fun t => -t) (integral_congr_ae (Filter.Eventually.of_forall (fun x
            => ?_)))
          exact mul_comm _ _
    _ = - ∫ x : Vec m, gradPair m φ (x, τ) (basisVec i) * gradPair m ψ (x, τ) (basisVec i) := by
          simp [g, f, gradPair]

/-- Integration by parts for the full truncated Laplacian: moving one derivative from
`partialLaplacian` onto a compactly supported test function. -/
theorem integral_partialLaplacian_mul_eq_neg_integral_gradPair_mul
    {m d : ℕ} {φ ψ : Vec m × ℝ → ℝ} {τ : ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m => φ (x, τ)))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m => ψ (x, τ)))
    (hφsupp : HasCompactSupport (fun x : Vec m => φ (x, τ))) :
    ∫ x : Vec m, partialLaplacian m d φ (x, τ) * ψ (x, τ)
      = - ∫ x : Vec m, ∑ i : Fin m, if (i : ℕ) < d then
            gradPair m φ (x, τ) (basisVec i) * gradPair m ψ (x, τ) (basisVec i) else 0 := by
  set A := fun (i : Fin m) (x : Vec m) =>
    (if (i : ℕ) < d then
      fderiv ℝ (fun y : Vec m => fderiv ℝ (fun z : Vec m => φ (z, τ)) y (basisVec i))
        x (basisVec i) else 0) * ψ (x, τ) with hA
  have h_integrand : (fun x : Vec m => partialLaplacian m d φ (x, τ) * ψ (x, τ)) =
      (fun x : Vec m => ∑ i : Fin m, A i x) := by
    ext x
    simp [partialLaplacian, Finset.sum_mul, hA]
  rw [h_integrand]
  have hint : ∀ i : Fin m, Integrable (A i) (μ := volume) := by
    intro i
    dsimp [A]
    by_cases hi : (i : ℕ) < d
    · simp [hi]
      have h_cdiff : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m =>
          fderiv ℝ (fun y : Vec m => φ (y, τ)) x (basisVec i)) :=
        contDiff_gradPair_of_contDiff hφ i
      have h_cont : Continuous (fun x : Vec m =>
          fderiv ℝ (fun y : Vec m => fderiv ℝ (fun z : Vec m => φ (z, τ)) y (basisVec i))
            x (basisVec i)) := by
        have : (fun x : Vec m =>
            fderiv ℝ (fun y : Vec m => fderiv ℝ (fun z : Vec m => φ (z, τ)) y (basisVec i))
              x (basisVec i)) =
            (fun x : Vec m => fderiv ℝ (fun y : Vec m => gradPair m φ (y, τ) (basisVec i)) x
              (basisVec i)) := by
          ext x; simp [gradPair]
        rw [this]
        have h_cdiff_gp : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m => gradPair m φ (x, τ) (basisVec i)) :=
          contDiff_gradPair_of_contDiff hφ i
        have h_cont' : Continuous (fun p : Vec m × Vec m =>
            (fderiv ℝ (fun y : Vec m => gradPair m φ (y, τ) (basisVec i)) p.1) p.2) :=
          h_cdiff_gp.continuous_fderiv_apply (by simp)
        exact h_cont'.comp (continuous_id.prodMk continuous_const)
      have h_supp : HasCompactSupport (fun x : Vec m =>
          fderiv ℝ (fun y : Vec m => fderiv ℝ (fun z : Vec m => φ (z, τ)) y (basisVec i))
            x (basisVec i)) := by
        have : (fun x : Vec m =>
            fderiv ℝ (fun y : Vec m => fderiv ℝ (fun z : Vec m => φ (z, τ)) y (basisVec i))
              x (basisVec i)) =
            (fun x : Vec m => fderiv ℝ (fun y : Vec m => gradPair m φ (y, τ) (basisVec i)) x
              (basisVec i)) := by
          ext x; simp [gradPair]
        rw [this]
        exact (hasCompactSupport_gradPair_of_hasCompactSupport hφsupp i).fderiv_apply (𝕜 := ℝ)
          (basisVec i)
      have h_cont_ψ : Continuous (fun x : Vec m => ψ (x, τ)) := hψ.continuous
      exact (h_cont.mul h_cont_ψ).integrable_of_hasCompactSupport
        (h_supp.mul_right (f' := fun x => ψ (x, τ))) (μ := volume)
    · simp [hi]
  have h_term (i : Fin m) : ∫ x : Vec m, A i x
      = - ∫ x : Vec m, if (i : ℕ) < d then
          gradPair m φ (x, τ) (basisVec i) * gradPair m ψ (x, τ) (basisVec i) else 0 := by
    dsimp [A]
    by_cases hi : (i : ℕ) < d
    · simp [hi]
      simpa [gradPair] using integral_gradPair_deriv_mul_eq_neg_integral_gradPair_mul hφ hψ hφsupp i
    · simp [hi]
  have h_int_gradPair_prod (i : Fin m) : Integrable (fun x : Vec m =>
      if (i : ℕ) < d then gradPair m φ (x, τ) (basisVec i) * gradPair m ψ (x, τ) (basisVec i)
        else 0)
      (μ := volume) := by
    by_cases hi : (i : ℕ) < d
    · simp [hi]
      have h_cont : Continuous (fun x : Vec m =>
          gradPair m φ (x, τ) (basisVec i) * gradPair m ψ (x, τ) (basisVec i)) :=
        ((contDiff_gradPair_of_contDiff hφ i).continuous.mul
          (contDiff_gradPair_of_contDiff hψ i).continuous)
      have h_supp : HasCompactSupport (fun x : Vec m =>
          gradPair m φ (x, τ) (basisVec i) * gradPair m ψ (x, τ) (basisVec i)) :=
        (hasCompactSupport_gradPair_of_hasCompactSupport hφsupp i).mul_right
          (f' := fun x => gradPair m ψ (x, τ) (basisVec i))
      exact h_cont.integrable_of_hasCompactSupport h_supp
    · simp [hi]
  calc
    ∫ x : Vec m, ∑ i : Fin m, A i x
        = ∑ i : Fin m, ∫ x : Vec m, A i x := by
          rw [integral_finsetSum Finset.univ (fun i _ => hint i)]
    _ = ∑ i : Fin m, (- ∫ x : Vec m, if (i : ℕ) < d then
          gradPair m φ (x, τ) (basisVec i) * gradPair m ψ (x, τ) (basisVec i) else 0) :=
          Finset.sum_congr rfl (fun i _ => by rw [h_term i])
    _ = - ∑ i : Fin m, ∫ x : Vec m, if (i : ℕ) < d then
          gradPair m φ (x, τ) (basisVec i) * gradPair m ψ (x, τ) (basisVec i) else 0 := by
          simp [Finset.sum_neg_distrib]
    _ = - ∫ x : Vec m, ∑ i : Fin m, if (i : ℕ) < d then
          gradPair m φ (x, τ) (basisVec i) * gradPair m ψ (x, τ) (basisVec i) else 0 := by
          rw [← integral_finsetSum Finset.univ (fun i _ => h_int_gradPair_prod i)]

/-- Symmetry of the truncated-Laplacian pairing: the bilinear form induced by
`partialLaplacian` is symmetric on smooth compactly supported test functions. -/
theorem integral_partialLaplacian_mul_symm
    {m d : ℕ} {φ ψ : Vec m × ℝ → ℝ} {τ : ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m => φ (x, τ)))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m => ψ (x, τ)))
    (hφsupp : HasCompactSupport (fun x : Vec m => φ (x, τ)))
    (hψsupp : HasCompactSupport (fun x : Vec m => ψ (x, τ))) :
    ∫ x : Vec m, partialLaplacian m d φ (x, τ) * ψ (x, τ)
      = ∫ x : Vec m, φ (x, τ) * partialLaplacian m d ψ (x, τ) := by
  have h1 := integral_partialLaplacian_mul_eq_neg_integral_gradPair_mul
    (d := d) hφ hψ hφsupp
  have h2 := integral_partialLaplacian_mul_eq_neg_integral_gradPair_mul
    (d := d) hψ hφ hψsupp
  -- The two right-hand sides are equal because multiplication commutes pointwise.
  have h_rhs_eq : (∫ x : Vec m, ∑ i : Fin m, if (i : ℕ) < d then
      gradPair m φ (x, τ) (basisVec i) * gradPair m ψ (x, τ) (basisVec i) else 0)
      = (∫ x : Vec m, ∑ i : Fin m, if (i : ℕ) < d then
          gradPair m ψ (x, τ) (basisVec i) * gradPair m φ (x, τ) (basisVec i) else 0) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    refine Finset.sum_congr rfl (fun i hi => ?_)
    by_cases hi_d : (i : ℕ) < d
    · simp [hi_d, mul_comm]
    · simp [hi_d]
  calc
    ∫ x : Vec m, partialLaplacian m d φ (x, τ) * ψ (x, τ)
        = - ∫ x : Vec m, ∑ i : Fin m, if (i : ℕ) < d then
            gradPair m φ (x, τ) (basisVec i) * gradPair m ψ (x, τ) (basisVec i) else 0 := h1
    _ = - ∫ x : Vec m, ∑ i : Fin m, if (i : ℕ) < d then
            gradPair m ψ (x, τ) (basisVec i) * gradPair m φ (x, τ) (basisVec i) else 0 := by
          rw [h_rhs_eq]
    _ = ∫ x : Vec m, φ (x, τ) * partialLaplacian m d ψ (x, τ) := by
      rw [← h2]
      simp [mul_comm]


end CIV
