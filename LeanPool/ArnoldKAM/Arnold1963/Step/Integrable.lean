/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Step.GeneratingFunction
public import LeanPool.ArnoldKAM.Arnold1963.Analysis.Taylor

/-!
Supporting results for the analytic Hamiltonian KAM construction.
-/

@[expose] public section
noncomputable section
open Set
open Filter
open scoped Topology
namespace KamProject.Arnold1963

/-- The coordinate gradient of an action-dependent Hamiltonian, giving its frequency map. -/
def actionFrequency {n : ℕ} (h : ComplexSpace n → ℂ) (p : ComplexSpace n) :
    ComplexSpace n := fun j => fderiv ℂ h p (Pi.single j 1)

theorem fderiv_eq_actionFrequency {n : ℕ} (h : ComplexSpace n → ℂ)
    (p v : ComplexSpace n) :
    fderiv ℂ h p v = ∑ j, actionFrequency h p j * v j := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp [actionFrequency, mul_comm]

theorem analyticOnNhd_actionFrequency {n : ℕ} {G : Set (ComplexSpace n)}
    {h : ComplexSpace n → ℂ} (hh : AnalyticOnNhd ℂ h G) :
    AnalyticOnNhd ℂ (actionFrequency h) G := by
  intro p hp
  apply AnalyticAt.pi
  intro j
  exact ((ContinuousLinearMap.apply ℂ ℂ (Pi.single j 1)).analyticAt _).comp (hh.fderiv p hp)

theorem actionFrequency_conj_of_mem_nhds {n : ℕ} {h : ComplexSpace n → ℂ}
    {V : Set (ComplexSpace n)} {p : ComplexSpace n}
    (ha : AnalyticAt ℂ h p) (hc : ∀ x ∈ V, h (conjVec x) = star (h x))
    (hp : V ∈ 𝓝 (conjVec p)) :
    actionFrequency h (conjVec p) = conjVec (actionFrequency h p) := by
  have he : h =ᶠ[𝓝 (star p)] (star ∘ h ∘ star) := by
    filter_upwards [hp] with z hz
    simpa [Function.comp_def, ← hc z hz] using (star_star (h z)).symm
  have hd := ha.differentiableAt.hasFDerivAt.star_star
  ext j
  dsimp [actionFrequency, conjVec]
  rw [he.fderiv_eq, hd.fderiv]
  simp

/-- Analyticity, real compatibility and frequency bounds for an integrable Hamiltonian. -/
structure IntegrableData {n : ℕ} (h : ComplexSpace n → ℂ)
    (G : Set (ComplexSpace n)) (Θ : ℝ) : Prop where
  analytic : AnalyticOnNhd ℂ h G
  conj_compatible : ∀ p ∈ G, h (conjVec p) = star (h p)
  frequency_conj : ∀ p ∈ G,
    actionFrequency h (conjVec p) = conjVec (actionFrequency h p)
  hessian_bound : ∀ p ∈ G, ∀ i j,
    ‖fderiv ℂ (fderiv ℂ h) p (Pi.single i 1) (Pi.single j 1)‖ ≤ Θ

end KamProject.Arnold1963
