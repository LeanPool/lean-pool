/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.CausalDistribution
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.BackwardPotentialIdentity
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average

/-!
# Heat Kernel Fundamental Solution

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open scoped BigOperators Distributions

noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Parabolic

private lemma backwardTestPotential_zero_eq_integral_product
    (f : Vec3 × ℝ → ℝ) :
    backwardTestPotential f (0, 0) =
      ∫ z : Vec3 × ℝ, heatKernelPlus z * f z := by
  rw [backwardTestPotential_eq_backwardHeatPotential]
  unfold backwardHeatPotential backwardHeatKernel
  simp only [sub_zero]
  rw [Integration.volume_parabolicPoint_eq_prod]
  change (∫ z : Vec3 × ℝ, heatKernelPlus z * f z
      ∂((volume : Measure Vec3).prod (volume : Measure ℝ))) = _
  rw [show (volume : Measure (Vec3 × ℝ)) =
      (volume : Measure Vec3).prod (volume : Measure ℝ) from
        MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]

private lemma test_timePartial_eq
    (ψ : 𝓓((⊤ : TopologicalSpace.Opens (Vec3 × ℝ)), ℝ)) (z : Vec3 × ℝ) :
    (TestFunction.lineDerivCLM (𝕜 := ℝ) (n := ⊤) (k := ⊤)
      ((0 : Vec3), (1 : ℝ)) ψ) z =
      CKN.timePartial (show ParabolicPoint → ℝ from ψ) z := by
  rw [TestFunction.lineDerivCLM_apply_of_le (k := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞))
    (by simp)]
  obtain ⟨fderiv, hfderiv⟩ := ψ.contDiff.differentiable (by simp) z
  have hdiff : DifferentiableAt ℝ (ψ : Vec3 × ℝ → ℝ) z := hfderiv.differentiableAt
  rw [hdiff.lineDeriv_eq_fderiv,
    timePartial_eq_fderiv_apply ψ.contDiff z.1 z.2]

private lemma test_spatialPartial_eq
    (ψ : 𝓓((⊤ : TopologicalSpace.Opens (Vec3 × ℝ)), ℝ))
    (i : Fin 3) (z : Vec3 × ℝ) :
    (TestFunction.lineDerivCLM (𝕜 := ℝ) (n := ⊤) (k := ⊤)
      (basisVec i, (0 : ℝ)) ψ) z =
      CKN.spatialPartial (show ParabolicPoint → ℝ from ψ) i z := by
  rw [TestFunction.lineDerivCLM_apply_of_le (k := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞))
    (by simp)]
  obtain ⟨fderiv, hfderiv⟩ := ψ.contDiff.differentiable (by simp) z
  have hdiff : DifferentiableAt ℝ (ψ : Vec3 × ℝ → ℝ) z := hfderiv.differentiableAt
  rw [hdiff.lineDeriv_eq_fderiv,
    spatialPartial_eq_fderiv_apply ψ.contDiff i z.1 z.2]

private lemma test_spatialSecondPartial_eq
    (ψ : 𝓓((⊤ : TopologicalSpace.Opens (Vec3 × ℝ)), ℝ))
    (i : Fin 3) (z : Vec3 × ℝ) :
    (TestFunction.lineDerivCLM (𝕜 := ℝ) (n := ⊤) (k := ⊤)
      (basisVec i, (0 : ℝ))
      (TestFunction.lineDerivCLM (𝕜 := ℝ) (n := ⊤) (k := ⊤)
        (basisVec i, (0 : ℝ)) ψ)) z =
      CKN.spatialSecondPartial (fun w : ParabolicPoint => ψ w) i i z := by
  let ψ₁ : 𝓓((⊤ : TopologicalSpace.Opens (Vec3 × ℝ)), ℝ) :=
    TestFunction.lineDerivCLM (𝕜 := ℝ) (n := ⊤) (k := ⊤)
      (basisVec i, (0 : ℝ)) ψ
  rw [test_spatialPartial_eq
    (ψ := ψ₁) i z]
  change CKN.spatialPartial
      (fun w : ParabolicPoint => ψ₁ (show Vec3 × ℝ from w)) i z =
    CKN.spatialSecondPartial (fun w : ParabolicPoint => ψ w) i i z
  have hfirst :
      (fun w : ParabolicPoint => ψ₁ (show Vec3 × ℝ from w)) =
        fun w => CKN.spatialPartial (show ParabolicPoint → ℝ from ψ) i w := by
    funext w
    exact test_spatialPartial_eq ψ i (show Vec3 × ℝ from w)
  rw [hfirst]
  rfl

private lemma heatKernelPlusDistribution_timePartial_apply
    (ψ : 𝓓((⊤ : TopologicalSpace.Opens (Vec3 × ℝ)), ℝ)) :
      Distribution.lineDerivCLM (n := ⊤) (k := ⊤) ((0 : Vec3), (1 : ℝ))
        heatKernelPlusDistribution ψ =
      -backwardTestPotential
        (fun z : Vec3 × ℝ => CKN.timePartial
          (show ParabolicPoint → ℝ from ψ) z) (0, 0) := by
  rw [Distribution.lineDerivCLM_apply, heatKernelPlusDistribution_apply,
    backwardTestPotential_zero_eq_integral_product]
  simp only [smul_eq_mul]
  rw [neg_inj]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [test_timePartial_eq]
  ring

private lemma heatKernelPlusDistribution_spatialSecondPartial_apply
    (ψ : 𝓓((⊤ : TopologicalSpace.Opens (Vec3 × ℝ)), ℝ)) (i : Fin 3) :
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (basisVec i, (0 : ℝ))
      (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (basisVec i, (0 : ℝ))
        heatKernelPlusDistribution) ψ =
      backwardTestPotential
        (fun z : Vec3 × ℝ => CKN.spatialSecondPartial
          (show ParabolicPoint → ℝ from ψ) i i z)
        (0, 0) := by
  simp only [Distribution.lineDerivCLM_apply, neg_neg]
  rw [heatKernelPlusDistribution_apply,
    backwardTestPotential_zero_eq_integral_product]
  simp only [smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [test_spatialSecondPartial_eq]
  ring

/-- The causal heat kernel is a fundamental solution of the heat operator, as a
distribution on the ordinary product space `ℝ³ × ℝ` (paper label `ext:heat-kernel`). -/
theorem heatKernelPlusDistribution_fundamentalSolution :
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) ((0 : Vec3), (1 : ℝ))
        heatKernelPlusDistribution -
      ∑ i : Fin 3,
        Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (basisVec i, (0 : ℝ))
          (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (basisVec i, (0 : ℝ))
            heatKernelPlusDistribution) =
      Distribution.delta (0 : Vec3 × ℝ) := by
  ext ψ
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (ψ : Vec3 × ℝ → ℝ) := ψ.contDiff
  have hψc : HasCompactSupport (ψ : Vec3 × ℝ → ℝ) := ψ.hasCompactSupport
  have hback := backwardTestPotential_heat_equation
    (ζ := fun z : Vec3 × ℝ => ψ z) hψ hψc (0 : Vec3) (0 : ℝ)
  rw [backwardTestPotential_timePartial (ζ := fun z : Vec3 × ℝ => ψ z)
      hψ hψc (0 : Vec3) (0 : ℝ)] at hback
  simp_rw [backwardTestPotential_spatialSecondPartial
    (ζ := fun z : Vec3 × ℝ => ψ z) hψ hψc] at hback
  calc
    (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) ((0 : Vec3), (1 : ℝ))
        heatKernelPlusDistribution -
      ∑ i : Fin 3,
        Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (basisVec i, (0 : ℝ))
          (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (basisVec i, (0 : ℝ))
            heatKernelPlusDistribution)) ψ =
      -backwardTestPotential
          (fun z => CKN.timePartial (show ParabolicPoint → ℝ from ψ) z) (0, 0) -
        ∑ i : Fin 3, backwardTestPotential
          (fun z => CKN.spatialSecondPartial (show ParabolicPoint → ℝ from ψ) i i z)
          (0, 0) := by
      simp only [sub_apply, sum_apply,
        heatKernelPlusDistribution_timePartial_apply,
        heatKernelPlusDistribution_spatialSecondPartial_apply]
    _ = ψ (0, 0) := hback
    _ = Distribution.delta (0 : Vec3 × ℝ) ψ := rfl

end CKN.Foundation.Heat

end
