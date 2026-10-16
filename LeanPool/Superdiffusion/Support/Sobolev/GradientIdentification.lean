/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.EuclideanL2CZ

/-!
# Gradient identification for a smooth representative

Extracted from scottnarmstrong/Superdiffusion at
7f20476385d4af418f110303085ad0740c9eba46, with shared dependency placement.
-/

@[expose] public section

namespace Algsuperdiff

open HCPolySupport MeasureTheory

noncomputable section

variable {d : ℕ}

/-- A `C¹` representative has the weak gradient of the a.e.-equal `H¹` function
on an arbitrary open subdomain. -/
theorem ae_eq_euclideanGradient_of_ae_eq_of_contDiff {U V : Set (Vec d)}
    (hV : IsOpen V) (hVU : V ⊆ U) [IsFiniteMeasure (volumeMeasureOn V)]
    (h : H1Function U) {v : Vec d → ℝ} (hv : ContDiff ℝ 1 v)
    (hae : v =ᵐ[volume.restrict V] h.toFun) :
    euclideanGradient v =ᵐ[volume.restrict V] h.grad := by
  have hgv : HasWeakGradientOn V v (euclideanGradient v) :=
    HasWeakGradientOn.of_contDiff hv
  have hcoord : ∀ i : Fin d,
      (fun x => euclideanGradient v x i) =ᵐ[volume.restrict V]
        fun x => h.grad x i := by
    intro i
    apply HCPolySupport.HasWeakPartialDerivOn.ae_eq hV
    · have hcont : Continuous (fun x => euclideanGradient v x i) := by
        simpa [euclideanGradient, euclideanCoordDeriv] using
          (hv.continuous_fderiv (by simp)).clm_apply
            (continuous_const (y := basisVec i))
      exact hcont.locallyIntegrable.locallyIntegrableOn V
    · have hL2 : MemL2On V (fun x => h.grad x i) :=
        memL2On_mono hVU (h.grad_memL2 i)
      have hint : IntegrableOn (fun x => h.grad x i) V volume :=
        hL2.integrable (by norm_num)
      exact hint.locallyIntegrableOn
    · exact hgv i
    · intro φ hφ hφc hsupp
      have hcongr : ∫ x in V, v x * (fderiv ℝ φ x) (basisVec i) =
          ∫ x in V, h.toFun x * (fderiv ℝ φ x) (basisVec i) :=
        integral_congr_ae (hae.mono fun x hx =>
          congrArg (fun c : ℝ => c * (fderiv ℝ φ x) (basisVec i)) hx)
      rw [hcongr]
      exact (HasWeakPartialDerivOn.restrict hV hVU (h.hasWeakGradient i)) φ hφ hφc hsupp
  have hall : ∀ᵐ x ∂(volume.restrict V), ∀ i : Fin d,
      euclideanGradient v x i = h.grad x i := ae_all_iff.2 hcoord
  filter_upwards [hall] with x hx
  funext i
  exact hx i

end

end Algsuperdiff
