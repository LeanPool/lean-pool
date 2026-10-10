/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Step.DomainGeometry
public import LeanPool.ArnoldKAM.Arnold1963.Step.Integrable

/-!
Supporting results for the analytic Hamiltonian KAM construction.
-/

@[expose] public section
noncomputable section
open Set
open scoped NNReal
namespace KamProject.Arnold1963

/-- The analytic, nonresonance and numerical hypotheses for the fundamental KAM construction. -/
structure FundamentalInput {n : ℕ} {G E : Set (ComplexSpace n)}
    {ρ β δ γ : ℝ≥0} {K M Θ : ℝ}
    (h : ComplexSpace n → ℂ) (f : AnalyticPhaseFunction n G ρ) : Prop where
  integrable : IntegrableData h G Θ
  domain_subset : E ⊆ G
  domain_conj : ConjInvariant E
  perturbation_bound : f.uniformNorm ≤ M
  mean_zero : ∀ p ∈ E, f.angleAverage p = 0
  nonresonant : ∀ p ∈ E,
    FiniteNonresonant (actionFrequency h p) K (fundamentalCutoff γ M)
  budget : FundamentalParameters n ρ β δ γ K M Θ

namespace FundamentalInput
variable {n : ℕ} {G E : Set (ComplexSpace n)} {ρ β δ γ : ℝ≥0} {K M Θ : ℝ}
  {h : ComplexSpace n → ℂ} {f : AnalyticPhaseFunction n G ρ}
  (i : FundamentalInput (E := E) (β := β) (δ := δ) (γ := γ) (K := K) (M := M) (Θ := Θ) h f)

/-- The bounded analytic generating function solving the finite homological equation. -/
def generator : AnalyticPhaseFunction n E (ρ - (δ + δ)) :=
  homologicalFunction f (actionFrequency h) i.domain_subset i.domain_conj
    ((analyticOnNhd_actionFrequency i.integrable.analytic).mono i.domain_subset)
    (fun p hp => i.integrable.frequency_conj p (i.domain_subset hp)) i.nonresonant
    i.budget.K_pos i.perturbation_bound i.budget.delta_pos
    (by exact_mod_cast (show (δ : ℝ) ≤ 1 by linarith [i.budget.delta_lt])) i.budget.double_delta_le

theorem generator_bound : i.generator.uniformNorm ≤ homologicalBound n M K δ :=
  norm_homologicalFunction_le f (actionFrequency h) _ _ _ _ _ _ _ _ _ _

theorem generatingData : GeneratingData i.generator.toFun E
    (angleStrip n (ρ - (δ + δ))) β (homologicalBound n M K δ) :=
  GeneratingData.of_arnold i.budget.dimension_pos i.budget.beta_pos i.generator.analytic
    (i.generator.norm_le_iff.mp i.generator_bound) i.budget.generating_small

/-- The phase transformation obtained from the fundamental step's generating function. -/
def transform : ComplexPhaseSpace n → ComplexPhaseSpace n :=
  generatingTransform i.generator.toFun E (angleStrip n (ρ - (δ + δ))) β

/-- The fundamental canonical transformation on its retained phase domain. -/
def transformation : AnalyticCanonicalTransformation
    (phaseDomain (erosion E (β + β)) (ρ - (γ + γ))) (phaseDomain G ρ)
    (homologicalBound n M K δ / β) :=
  let B := i.generatingData.transformation.restrict (i.budget.target_subset E)
  { B with mapsTo := fun _ hz =>
      ⟨i.domain_subset (B.mapsTo hz).1,
        angleStrip_mono (tsub_le_self : ρ - (δ + δ) ≤ ρ) (B.mapsTo hz).2⟩ }

include i

theorem displacement {z : ComplexPhaseSpace n}
    (hz : z ∈ phaseDomain (erosion E (β + β)) (ρ - (γ + γ))) :
    ‖i.transform z - z‖ ≤ homologicalBound n M K δ / β :=
  i.transformation.displacement.norm_le hz

theorem action_displacement {z : ComplexPhaseSpace n}
    (hz : z ∈ phaseDomain (erosion E (β + β)) (ρ - (γ + γ))) :
    ‖(i.transform z).1 - z.1‖ ≤ homologicalBound n M K δ / δ :=
  i.generatingData.action_displacement i.budget.delta_pos hz.1 (i.budget.target_angle_buffer hz.2)

theorem action_displacement_beta {z : ComplexPhaseSpace n}
    (hz : z ∈ phaseDomain (erosion E (β + β)) (ρ - (γ + γ))) :
    ‖(i.transform z).1 - z.1‖ ≤ β :=
  (norm_fst_le (i.transform z - z)).trans
    ((i.displacement hz).trans i.budget.displacement_lt_beta.le)

theorem angle_displacement_beta {z : ComplexPhaseSpace n}
    (hz : z ∈ phaseDomain (erosion E (β + β)) (ρ - (γ + γ))) :
    dist (i.transform z).2 z.2 ≤ β := by
  rw [dist_eq_norm]
  exact (norm_snd_le (i.transform z - z)).trans
    ((i.displacement hz).trans i.budget.displacement_lt_beta.le)

theorem action_segment {z : ComplexPhaseSpace n}
    (hz : z ∈ phaseDomain (erosion E (β + β)) (ρ - (γ + γ))) :
    segment ℝ z.1 (i.transform z).1 ⊆ erosion G β :=
  (segment_subset_erosion_of_displacement hz.1 (i.action_displacement_beta hz)).trans
    (erosion_mono i.domain_subset β)

theorem transformed_angle {z : ComplexPhaseSpace n}
    (hz : z ∈ phaseDomain (erosion E (β + β)) (ρ - (γ + γ))) :
    (i.transform z).2 ∈ angleStrip n (ρ - (δ + γ)) :=
  i.budget.shifted_angle_tail hz.2 (i.angle_displacement_beta hz)

end FundamentalInput
end KamProject.Arnold1963
