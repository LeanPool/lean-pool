/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Convergence.Composition
public import LeanPool.ArnoldKAM.Arnold1963.Geometry.RealCover
public import LeanPool.ArnoldKAM.Arnold1963.Geometry.RealJacobian

/-!
Derivative bounds for finite cumulative transformations on the real cover. Restricting
to real coordinates and taking real parts does not increase the operator norm.
-/

@[expose] public section
noncomputable section
open Set
open scoped NNReal
namespace KamProject.Arnold1963

/-- Complexification of action and angle coordinates as a real continuous linear map. -/
def complexifyPhaseCLM (n : ℕ) : RealPhaseCover n →L[ℝ] ComplexPhaseSpace n :=
  (complexifyCLM n).prodMap (complexifyCLM n)

/-- Real-part projection of phase coordinates as a real continuous linear map. -/
def realPartPhaseCLM (n : ℕ) : ComplexPhaseSpace n →L[ℝ] RealPhaseCover n :=
  (realPartCLM n).prodMap (realPartCLM n)

@[simp] theorem complexifyPhaseCLM_apply {n} (x : RealPhaseCover n) :
    complexifyPhaseCLM n x = complexifyPhase x := rfl

@[simp] theorem realPartPhaseCLM_apply {n} (z : ComplexPhaseSpace n) :
    realPartPhaseCLM n z = realPartPhase z := rfl

@[simp] theorem norm_complexifyPhase {n} (x : RealPhaseCover n) :
    ‖complexifyPhase x‖ = ‖x‖ := by
  simp [complexifyPhase, Prod.norm_def]

theorem norm_realPartPhase_le {n} (z : ComplexPhaseSpace n) :
    ‖realPartPhase z‖ ≤ ‖z‖ :=
  max_le_max (norm_realPart_le z.1) (norm_realPart_le z.2)

/-- Restriction of a complex phase map to real input and real output coordinates. -/
def realPhaseRestriction {n} (f : ComplexPhaseSpace n → ComplexPhaseSpace n) :
    RealPhaseCover n → RealPhaseCover n := realPartPhase ∘ f ∘ complexifyPhase

/-- The real continuous linear derivative induced by a complex phase derivative. -/
def realPhaseDerivative {n} (L : ComplexPhaseSpace n →L[ℂ] ComplexPhaseSpace n) :
    RealPhaseCover n →L[ℝ] RealPhaseCover n :=
  (realPartPhaseCLM n).comp ((L.restrictScalars ℝ).comp (complexifyPhaseCLM n))

theorem hasFDerivAt_realPhaseRestriction {n}
    {f : ComplexPhaseSpace n → ComplexPhaseSpace n} {x : RealPhaseCover n}
    (hf : DifferentiableAt ℂ f (complexifyPhase x)) :
    HasFDerivAt (realPhaseRestriction f)
      (realPhaseDerivative (fderiv ℂ f (complexifyPhase x))) x :=
  (realPartPhaseCLM n).hasFDerivAt.comp x
    ((hf.hasFDerivAt.restrictScalars ℝ).comp x (complexifyPhaseCLM n).hasFDerivAt)

theorem norm_realPhaseDerivative_le {n}
    (L : ComplexPhaseSpace n →L[ℂ] ComplexPhaseSpace n) :
    ‖realPhaseDerivative L‖ ≤ ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
  intro x
  exact (norm_realPartPhase_le _).trans (by simpa using L.le_opNorm (complexifyPhase x))

namespace Iteration.InitialData
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
  (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D)

theorem cumulative_realPhase_value (s : ℕ) {x : RealPhaseCover n}
    (hx : complexifyPhase x ∈ h.phase b s) :
    complexifyPhase (realPhaseRestriction (h.cumulative b s) x) =
      h.cumulative b s (complexifyPhase x) := by
  apply complexifyPhase_realPartPhase_of_conj
  have hr := h.cumulative_real b s _ hx
  rw [conjPhase_complexifyPhase] at hr
  exact hr.symm

theorem cumulative_real_derivative (s : ℕ) {x : RealPhaseCover n}
    (hx : complexifyPhase x ∈ h.phase b s) :
    ‖fderiv ℝ (realPhaseRestriction (h.cumulative b s)) x‖ ≤ (2 : ℝ) ^ s := by
  rw [(hasFDerivAt_realPhaseRestriction
    (h.cumulative_analytic b s _ hx).differentiableAt).fderiv]
  exact (norm_realPhaseDerivative_le _).trans (h.cumulative_derivative b s _ hx)

end Iteration.InitialData
end KamProject.Arnold1963
