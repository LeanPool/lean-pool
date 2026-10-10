/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Step.Integrable

/-!
Supporting results for the analytic Hamiltonian KAM construction.
-/

@[expose] public section
noncomputable section
open Set
namespace KamProject.Arnold1963

/-- Evaluation of an action covector on the coordinate basis as a continuous linear map. -/
def actionFrequencyCLM (n : ℕ) :
    (ComplexSpace n →L[ℂ] ℂ) →L[ℂ] ComplexSpace n :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.apply ℂ ℂ (Pi.single j 1))

theorem fderiv_actionFrequency_apply {n : ℕ} {h : ComplexSpace n → ℂ}
    {p : ComplexSpace n} (ha : AnalyticAt ℂ h p) (v : ComplexSpace n) (j : Fin n) :
    fderiv ℂ (actionFrequency h) p v j =
      fderiv ℂ (fderiv ℂ h) p v (Pi.single j 1) := by
  exact congrArg (fun L : ComplexSpace n →L[ℂ] ComplexSpace n => L v j)
    (((actionFrequencyCLM n).hasFDerivAt.comp p ha.fderiv.differentiableAt.hasFDerivAt).fderiv)

theorem IntegrableData.of_frequency_bound {n : ℕ} {G : Set (ComplexSpace n)}
    {h : ComplexSpace n → ℂ} {Θ : ℝ} (ha : AnalyticOnNhd ℂ h G)
    (hc : ∀ p ∈ G, h (conjVec p) = star (h p))
    (hωc : ∀ p ∈ G, actionFrequency h (conjVec p) = conjVec (actionFrequency h p))
    (hbound : ∀ p ∈ G, ‖fderiv ℂ (actionFrequency h) p‖ ≤ Θ) : IntegrableData h G Θ where
  analytic := ha
  conj_compatible := hc
  frequency_conj := hωc
  hessian_bound := by
    intro p hp i j
    rw [← fderiv_actionFrequency_apply (ha p hp)]
    calc
      _ ≤ ‖fderiv ℂ (actionFrequency h) p (Pi.single i 1)‖ := norm_le_pi_norm _ j
      _ ≤ ‖fderiv ℂ (actionFrequency h) p‖ * ‖(Pi.single i 1 : ComplexSpace n)‖ :=
        (fderiv ℂ (actionFrequency h) p).le_opNorm (Pi.single i 1)
      _ ≤ Θ := by simpa only [Pi.norm_single, norm_one, mul_one] using hbound p hp

end KamProject.Arnold1963
