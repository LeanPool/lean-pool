/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Step.InductiveDomains
public import LeanPool.ArnoldKAM.Arnold1963.Step.MeasureBudget

/-!
Supporting results for the analytic Hamiltonian KAM construction.
-/

@[expose] public section
noncomputable section
open Set
open scoped NNReal ENNReal
namespace KamProject.Arnold1963

/-- The quadratic perturbation bound supplied by one inductive KAM step. -/
def iterationRemainderBound (n : ℕ) (M δ β : ℝ) : ℝ :=
  M ^ 2 / (δ ^ (2 * stepExponent n) * β ^ 2)

theorem fundamentalRemainderBound_eq_iterationRemainderBound (n : ℕ) (M δ β : ℝ) :
    fundamentalRemainderBound n (2 * M) δ β = iterationRemainderBound n M δ β :=
  fundamentalRemainderBound_twice n M δ β

namespace IterationInput
variable {n : ℕ} {G Ω : Set (ComplexSpace n)} {ρ β δ γ θ Θ : ℝ≥0} {K M : ℝ}
  {a : ComplexSpace n → ℂ} {f : AnalyticPhaseFunction n G ρ}
  {g : ComplexSpace n → ComplexSpace n} (i : IterationInput (Ω := Ω) a f g β δ γ θ Θ K M)

/-- The fundamental result before restricting to the narrower inductive phase domain. -/
def wideResult := i.fundamental.result

theorem newDomain_subset_wide : i.newDomain ⊆ i.wideDomain :=
  (subset_closedBallNeighborhood _ β).trans (i.frequencyChange.iteration_target_buffer _ _)

/-- The next perturbation restricted to the inductive action domain and angle strip. -/
def newPerturbation : AnalyticPhaseFunction n i.newDomain (ρ - 3 * γ) :=
  i.wideResult.perturbation.restrict i.newDomain_subset_wide
    (tsub_le_tsub_left (by nlinarith : γ + γ ≤ 3 * γ) ρ) i.newChart.domain_conj

theorem newPerturbation_bound : i.newPerturbation.uniformNorm < iterationRemainderBound n M δ β :=
  (i.wideResult.perturbation.uniformNorm_restrict_le _ _ _).trans_lt (by
    simpa only [fundamentalRemainderBound_twice, iterationRemainderBound] using i.wideResult.bound)

/-- The inductive canonical transformation restricted to its retained phase domain. -/
def transformation : AnalyticCanonicalTransformation
    (phaseDomain i.newDomain (ρ - 3 * γ)) (phaseDomain G ρ) β :=
  let B := i.wideResult.transformation.restrict i.phase_subset_wide
  { B with
    mapsTo := fun _ hx =>
      ⟨erosion_subset _ _ (B.mapsTo hx).1, (B.mapsTo hx).2⟩
    displacement := ⟨β.coe_nonneg, fun z hz =>
      (i.wideResult.displacement_lt z (i.phase_subset_wide hz)).le⟩ }

theorem transformed_hamiltonian (z : ComplexPhaseSpace n) :
    a (i.transformation.toFun z).1 + f.toFun (i.transformation.toFun z) =
      i.newIntegrable z.1 + i.newPerturbation.toFun z := by
  have hh := i.wideResult.identity z
  change (a (i.transformation.toFun z).1 + f.angleAverage (i.transformation.toFun z).1) +
    (f.toFun (i.transformation.toFun z) - f.angleAverage (i.transformation.toFun z).1) =
      i.newIntegrable z.1 + i.newPerturbation.toFun z at hh
  linear_combination hh

theorem displacement_lt {z} (hz : z ∈ phaseDomain i.newDomain (ρ - 3 * γ)) :
    ‖i.transformation.toFun z - z‖ < β :=
  i.wideResult.displacement_lt z (i.phase_subset_wide hz)

theorem remainder_derivative_bound {z} (hz : z ∈ phaseDomain i.newDomain (ρ - 3 * γ)) :
    ‖fderiv ℂ i.newPerturbation.toFun z‖ < iterationRemainderBound n M δ β / β := by
  apply (norm_fderiv_le_div_of_mem_erosion i.budget.beta_pos i.wideResult.perturbation.analytic
    (i.wideResult.perturbation.norm_le_iff.mp le_rfl) (i.phase_buffer hz)).trans_lt
  apply div_lt_div_of_pos_right _ (show (0 : ℝ) < β from i.budget.beta_pos)
  simpa only [fundamentalRemainderBound_twice, iterationRemainderBound] using i.wideResult.bound

theorem remainder_second_derivative_bound {z}
    (hz : z ∈ phaseDomain i.newDomain (ρ - 3 * γ)) (j k : Fin n ⊕ Fin n) :
    ‖fderiv ℂ (fderiv ℂ i.newPerturbation.toFun) z (phaseBasis j) (phaseBasis k)‖ <
      2 * iterationRemainderBound n M δ β / (β : ℝ) ^ 2 := by
  apply (norm_second_phaseCoordinate_le i.budget.beta_pos i.wideResult.perturbation.analytic
    (i.wideResult.perturbation.norm_le_iff.mp le_rfl) (i.phase_buffer hz) j k).trans_lt
  apply div_lt_div_of_pos_right _ (sq_pos_of_pos (show (0 : ℝ) < β from i.budget.beta_pos))
  apply mul_lt_mul_of_pos_left _ (by norm_num)
  simpa only [fundamentalRemainderBound_twice, iterationRemainderBound] using i.wideResult.bound

end IterationInput

/-- The updated frequency chart, canonical transformation and remainder of an inductive step. -/
structure InductiveResult {n : ℕ} {G : Set (ComplexSpace n)} {ρ : ℝ≥0}
    (a : ComplexSpace n → ℂ) (f : AnalyticPhaseFunction n G ρ)
    (Ω : Set (ComplexSpace n)) (β δ γ θ Θ : ℝ≥0) (K M : ℝ) where
  /-- The retained action domain of the inductive step. -/
  domain : Set (ComplexSpace n)
  /-- The inverse of the updated action-frequency chart. -/
  inverseFrequency : ComplexSpace n → ComplexSpace n
  chart : AnalyticFrequencyChart (actionFrequency (f.averagedHamiltonian a)) inverseFrequency domain
    (erosion (nonresonantDomain Ω id K (fundamentalCutoff γ (2 * M))) ((5 + 7 * Θ) * β))
  domain_subset : domain ⊆ erosion G β
  width_pos : 0 < ρ - 3 * γ
  analytic : AnalyticOnNhd ℂ (f.averagedHamiltonian a) domain
  conj : ∀ p ∈ domain, f.averagedHamiltonian a (conjVec p) = star (f.averagedHamiltonian a p)
  lower_pos : 0 < (θ : ℝ) * (1 - (δ : ℝ))
  derivative_bounds : ∀ p ∈ domain, ∀ v,
    ((θ : ℝ) * (1 - (δ : ℝ))) * ‖v‖ ≤
      ‖fderiv ℂ (actionFrequency (f.averagedHamiltonian a)) p v‖ ∧
    ‖fderiv ℂ (actionFrequency (f.averagedHamiltonian a)) p v‖ ≤
      ((Θ : ℝ) * (1 + (δ : ℝ))) * ‖v‖
  frequency_displacement : ∀ p ∈ domain,
    ‖actionFrequency (f.averagedHamiltonian a) p - actionFrequency a p‖ < (β : ℝ) * δ
  /-- The canonical transformation carrying the retained phase domain into the previous one. -/
  transformation : AnalyticCanonicalTransformation
    (phaseDomain domain (ρ - 3 * γ)) (phaseDomain G ρ) β
  /-- The analytic perturbation remainder after updating the integrable Hamiltonian. -/
  perturbation : AnalyticPhaseFunction n domain (ρ - 3 * γ)
  identity : ∀ z, a (transformation.toFun z).1 + f.toFun (transformation.toFun z) =
    f.averagedHamiltonian a z.1 + perturbation.toFun z
  bound : perturbation.uniformNorm < iterationRemainderBound n M δ β
  displacement_lt : ∀ z ∈ phaseDomain domain (ρ - 3 * γ), ‖transformation.toFun z - z‖ < β
  periodic : ∀ z ∈ phaseDomain domain (ρ - 3 * γ), ∀ k,
    transformation.toFun (phaseShift k z) = phaseShift k (transformation.toFun z)
  conj_compatible : ∀ z ∈ phaseDomain domain (ρ - 3 * γ),
    transformation.toFun (conjPhase z) = conjPhase (transformation.toFun z)
  phase_buffer : phaseDomain domain (ρ - 3 * γ) ⊆ erosion (phaseDomain G ρ) β
  derivative : ∀ z ∈ phaseDomain domain (ρ - 3 * γ),
    ‖fderiv ℂ perturbation.toFun z‖ < iterationRemainderBound n M δ β / β
  second_derivative : ∀ z ∈ phaseDomain domain (ρ - 3 * γ), ∀ j k : Fin n ⊕ Fin n,
    ‖fderiv ℂ (fderiv ℂ perturbation.toFun) z (phaseBasis j) (phaseBasis k)‖ <
      2 * iterationRemainderBound n M δ β / (β : ℝ) ^ 2
  measure : realVolume (G \ domain) ≤ ENNReal.ofReal ((θ : ℝ)⁻¹ ^ n) *
    realVolume (Ω \ erosion (nonresonantDomain Ω id K (fundamentalCutoff γ (2 * M)))
      ((6 + 7 * Θ) * β))

/-- The inductive-step result assembled from its verified input data. -/
def IterationInput.result {n : ℕ} {G Ω : Set (ComplexSpace n)} {ρ β δ γ θ Θ : ℝ≥0}
    {K M : ℝ} {a : ComplexSpace n → ℂ} {f : AnalyticPhaseFunction n G ρ}
    {g : ComplexSpace n → ComplexSpace n} (i : IterationInput (Ω := Ω) a f g β δ γ θ Θ K M) :
    InductiveResult a f Ω β δ γ θ Θ K M where
  domain := i.newDomain
  inverseFrequency := i.frequencyChange.newInverse
  chart := i.newChart
  domain_subset := i.newDomain_subset
  width_pos := i.new_width_pos
  analytic := i.newIntegrable_data.analytic.mono i.newDomain_subset
  conj := fun _ hp => i.newIntegrable_data.conj_compatible _ (i.newDomain_subset hp)
  lower_pos := mul_pos i.budget.lower_pos (sub_pos.mpr i.budget.delta_lt_one)
  derivative_bounds := fun _ hp v => i.new_derivative_bounds hp v
  frequency_displacement := fun _ hp => i.frequency_displacement hp
  transformation := i.transformation
  perturbation := i.newPerturbation
  identity := i.transformed_hamiltonian
  bound := i.newPerturbation_bound
  displacement_lt := fun _ hz => i.displacement_lt hz
  periodic := fun _ hz k => i.wideResult.periodic _ (i.phase_subset_wide hz) k
  conj_compatible := fun _ hz => i.wideResult.conj_compatible _ (i.phase_subset_wide hz)
  phase_buffer := i.phase_subset_old_erosion
  derivative := fun _ hz => i.remainder_derivative_bound hz
  second_derivative := fun _ hz j k => i.remainder_second_derivative_bound hz j k
  measure := i.frequencyChange.iteration_measure _ _

theorem inductive_lemma {n : ℕ} {G Ω : Set (ComplexSpace n)} {ρ β δ γ θ Θ : ℝ≥0}
    {K M : ℝ} {a : ComplexSpace n → ℂ} {f : AnalyticPhaseFunction n G ρ}
    {g : ComplexSpace n → ComplexSpace n} (i : IterationInput (Ω := Ω) a f g β δ γ θ Θ K M) :
    Nonempty (InductiveResult a f Ω β δ γ θ Θ K M) := ⟨i.result⟩

end KamProject.Arnold1963
