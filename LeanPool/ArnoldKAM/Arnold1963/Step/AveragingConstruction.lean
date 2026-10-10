/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Step.Averaging
public import LeanPool.ArnoldKAM.Arnold1963.Step.IterationParameters
public import LeanPool.ArnoldKAM.Arnold1963.Step.FrequencyPreparation

/-!
Supporting results for the analytic Hamiltonian KAM construction.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped NNReal Topology
namespace KamProject.Arnold1963

/-- The analytic chart and quantitative hypotheses required for one inductive KAM step. -/
structure IterationInput {n : ℕ} {G Ω : Set (ComplexSpace n)}
    {ρ : ℝ≥0} (a : ComplexSpace n → ℂ) (f : AnalyticPhaseFunction n G ρ)
    (g : ComplexSpace n → ComplexSpace n) (β δ γ θ Θ : ℝ≥0) (K M : ℝ) : Prop where
  chart : AnalyticFrequencyChart (actionFrequency a) g G Ω
  analytic : AnalyticOnNhd ℂ a G
  conj : ∀ p ∈ G, a (conjVec p) = star (a p)
  lower : ∀ p ∈ G, ∀ v, (θ : ℝ) * ‖v‖ ≤ ‖fderiv ℂ (actionFrequency a) p v‖
  upper : ∀ p ∈ G, ‖fderiv ℂ (actionFrequency a) p‖ ≤ Θ
  perturbation : f.uniformNorm ≤ M
  budget : IterationParameters n ρ β δ γ θ Θ K M

namespace IterationInput
variable {n : ℕ} {G Ω : Set (ComplexSpace n)} {ρ β δ γ θ Θ : ℝ≥0} {K M : ℝ}
  {a : ComplexSpace n → ℂ} {f : AnalyticPhaseFunction n G ρ}
  {g : ComplexSpace n → ComplexSpace n} (i : IterationInput (Ω := Ω) a f g β δ γ θ Θ K M)
include i

theorem frequencyChange : FrequencyChangeInput (actionFrequency a) g f.frequencyShift
    G Ω β δ θ Θ where
  chart := i.chart
  radius_pos := i.budget.beta_pos
  contraction := i.budget.delta_lt_one
  lower_pos := i.budget.lower_pos
  lower_le_upper := i.budget.lower_le_upper
  lower := i.lower
  upper := i.upper
  analytic := f.frequencyShift_analytic.mono (erosion_subset _ _)
  bounded := ⟨β.coe_nonneg, fun _ hp =>
    ((f.frequencyShift_bound i.budget.beta_pos i.perturbation).norm_le hp).trans
      (i.budget.mean_gradient_small.le.trans
        (by
          have hd : (δ : ℝ) ≤ 1 := i.budget.delta_lt_one.le
          simpa using mul_le_mul_of_nonneg_left hd β.coe_nonneg))⟩
  derivative := fun _ hp => (f.frequencyShift_derivative_bound i.budget.beta_pos
    i.perturbation hp).trans i.budget.mean_hessian_small.le
  conj := fun _ hp => f.frequencyShift_conj i.budget.beta_pos hp

/-- The updated integrable Hamiltonian after absorbing the angle average. -/
def newIntegrable (_ : IterationInput (Ω := Ω) a f g β δ γ θ Θ K M) :
    ComplexSpace n → ℂ := f.averagedHamiltonian a

/-- The centered perturbation restricted to the once-eroded action domain. -/
def centeredPerturbation (_ : IterationInput (Ω := Ω) a f g β δ γ θ Θ K M) :
    AnalyticPhaseFunction n (erosion G β) ρ :=
  f.centered.restrict (erosion_subset _ _) le_rfl
    (fun _ hp => star_mem_erosion f.domain_conj hp)

theorem frequency_eventually {p} (hp : p ∈ G) :
    actionFrequency i.newIntegrable =ᶠ[𝓝 p]
      (fun p => actionFrequency a p + f.frequencyShift p) :=
  actionFrequency_add_eventually (i.analytic p hp) (f.analyticOnNhd_angleAverage p hp)

theorem newIntegrable_data : IntegrableData i.newIntegrable (erosion G β) (2 * Θ) := by
  apply IntegrableData.of_frequency_bound (h := i.newIntegrable)
    ((i.analytic.add f.analyticOnNhd_angleAverage).mono (erosion_subset _ _))
  · intro p hp
    change a (conjVec p) + f.angleAverage (conjVec p) = star (a p + f.angleAverage p)
    rw [i.conj _ (erosion_subset _ _ hp), f.angleAverage_conj (erosion_subset _ _ hp), star_add]
  · intro p hp
    rw [(i.frequency_eventually (p := conjVec p)
        (erosion_subset _ _ (star_mem_erosion f.domain_conj hp))).self_of_nhds,
      (i.frequency_eventually (erosion_subset _ _ hp)).self_of_nhds]
    dsimp only
    rw [i.chart.map_conj _ (erosion_subset _ _ hp), f.frequencyShift_conj i.budget.beta_pos hp]
    simp
  · intro p hp
    have hd : fderiv ℂ (fun p => actionFrequency a p + f.frequencyShift p) p =
        fderiv ℂ (actionFrequency a) p + fderiv ℂ f.frequencyShift p :=
      ((i.chart.analytic p (erosion_subset _ _ hp)).differentiableAt.hasFDerivAt.add
        (f.frequencyShift_analytic p (erosion_subset _ _ hp)).differentiableAt.hasFDerivAt).fderiv
    rw [(i.frequency_eventually (erosion_subset _ _ hp)).fderiv_eq, hd]
    calc
      _ ≤ ‖fderiv ℂ (actionFrequency a) p‖ + ‖fderiv ℂ f.frequencyShift p‖ := norm_add_le _ _
      _ ≤ (Θ : ℝ) + (δ : ℝ) * θ := add_le_add (i.upper _ (erosion_subset _ _ hp))
        (i.frequencyChange.derivative p hp)
      _ ≤ 2 * Θ := by
        have hle := mul_le_mul (show (δ : ℝ) ≤ 1 from i.budget.delta_lt_one.le)
          (show (θ : ℝ) ≤ Θ from i.budget.lower_le_upper)
          θ.coe_nonneg (show (0 : ℝ) ≤ 1 by norm_num)
        nlinarith

theorem fundamental : FundamentalInput
    (E := i.frequencyChange.iterationE K (fundamentalCutoff γ (2 * M)))
    (β := β) (δ := δ) (γ := γ) (K := K) (M := 2 * M) (Θ := 2 * Θ)
    i.newIntegrable i.centeredPerturbation := by
  apply i.frequencyChange.fundamentalInput i.newIntegrable_data
    (fun p hp => (i.frequency_eventually (erosion_subset _ _ hp)).self_of_nhds)
    i.budget.fundamental
  · exact (f.centered.uniformNorm_restrict_le _ _ _).trans
      (f.uniformNorm_centered_le.trans (mul_le_mul_of_nonneg_left i.perturbation (by norm_num)))
  · intro p hp
    exact f.angleAverage_centered_eq_zero (erosion_subset _ _ hp)

end IterationInput
end KamProject.Arnold1963
