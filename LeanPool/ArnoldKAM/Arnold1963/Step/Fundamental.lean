/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Step.Remainder

/-!
Supporting results for the analytic Hamiltonian KAM construction.
-/

@[expose] public section
noncomputable section
open Set
open scoped NNReal
namespace KamProject.Arnold1963

namespace FundamentalInput
variable {n : ℕ} {G E : Set (ComplexSpace n)} {ρ β δ γ : ℝ≥0} {K M Θ : ℝ}
  {h : ComplexSpace n → ℂ} {f : AnalyticPhaseFunction n G ρ}
  (i : FundamentalInput (E := E) (β := β) (δ := δ) (γ := γ) (K := K) (M := M) (Θ := Θ) h f)

/-- The transformed Hamiltonian remainder packaged as an analytic perturbation. -/
def newPerturbation : AnalyticPhaseFunction n (erosion E (β + β)) (ρ - (γ + γ)) where
  toFun := i.remainder
  domain_conj := fun _ hp => star_mem_erosion i.domain_conj hp
  analytic := by
    intro z hz
    have hB : AnalyticAt ℂ i.transform z := i.transformation.analytic z hz
    have hm : i.transform z ∈ phaseDomain G ρ := i.transformation.mapsTo hz
    have hpB : AnalyticAt ℂ (fun x => (i.transform x).1) z :=
      analyticAt_fst.comp (f := i.transform) hB
    exact (((i.integrable.analytic _ hm.1).comp
      (f := fun x => (i.transform x).1) hpB).add
      ((f.analytic _ hm).comp (f := i.transform) hB)).sub
      ((i.integrable.analytic _ (i.domain_subset (erosion_subset _ _ hz.1))).comp
        (f := Prod.fst) analyticAt_fst)
  periodic := by
    intro p hp q hq k
    have hz : (p, q) ∈ phaseDomain (erosion E (β + β)) (ρ - (γ + γ)) := ⟨hp, hq⟩
    have he := i.generator.generatingTransform_shift i.generatingData
      (i.budget.target_subset E hz) k
    change i.transform (phaseShift k (p, q)) = phaseShift k (i.transform (p, q)) at he
    change i.remainder (phaseShift k (p, q)) = i.remainder (p, q)
    unfold remainder
    rw [he]
    have hm : i.transform (p, q) ∈ phaseDomain G ρ := i.transformation.mapsTo hz
    change h (i.transform (p, q)).1 +
      f.toFun ((i.transform (p, q)).1, (i.transform (p, q)).2 + angleShift k) - h p = _
    rw [f.periodic _ hm.1 _ hm.2 k]
  conj_compatible := by
    intro z hz
    have he := i.generator.generatingTransform_conj i.generatingData (i.budget.target_subset E hz)
    change i.transform (conjPhase z) = conjPhase (i.transform z) at he
    change i.remainder (conjPhase z) = star (i.remainder z)
    unfold remainder
    rw [he]
    have hm : i.transform z ∈ phaseDomain G ρ := i.transformation.mapsTo hz
    change h (conjVec (i.transform z).1) + f.toFun (conjPhase (i.transform z)) -
      h (conjVec z.1) = _
    rw [i.integrable.conj_compatible _ hm.1, f.conj_compatible _ hm,
      i.integrable.conj_compatible _ (i.domain_subset (erosion_subset _ _ hz.1))]
    simp only [star_sub, star_add]
  bounded := ⟨fundamentalRawBound n M K Θ δ β, i.remainder_norm_bound⟩

theorem newPerturbation_bound : i.newPerturbation.uniformNorm <
    fundamentalRemainderBound n M δ β :=
  ((i.newPerturbation.norm_le_iff).mpr i.remainder_norm_bound).trans_lt i.budget.remainder_budget

theorem transformed_hamiltonian (z : ComplexPhaseSpace n) :
    h (i.transform z).1 + f.toFun (i.transform z) = h z.1 + i.newPerturbation.toFun z := by
  change _ = h z.1 + (h (i.transform z).1 + f.toFun (i.transform z) - h z.1)
  ring

end FundamentalInput

/-- The fundamental canonical transformation and its quantitative perturbation remainder. -/
structure FundamentalResult {n : ℕ} {G : Set (ComplexSpace n)}
    (h : ComplexSpace n → ℂ) (f : AnalyticPhaseFunction n G ρ)
    (E : Set (ComplexSpace n)) (β δ γ : ℝ≥0) (K M : ℝ) where
  /-- The canonical transformation constructed by the fundamental step. -/
  transformation : AnalyticCanonicalTransformation
    (phaseDomain (erosion E (β + β)) (ρ - (γ + γ))) (phaseDomain G ρ)
    (homologicalBound n M K δ / β)
  /-- The analytic remainder of the transformed Hamiltonian on the retained phase domain. -/
  perturbation : AnalyticPhaseFunction n (erosion E (β + β)) (ρ - (γ + γ))
  identity : ∀ z, h (transformation.toFun z).1 + f.toFun (transformation.toFun z) =
    h z.1 + perturbation.toFun z
  bound : perturbation.uniformNorm < fundamentalRemainderBound n M δ β
  displacement_lt : ∀ z ∈ phaseDomain (erosion E (β + β)) (ρ - (γ + γ)),
    ‖transformation.toFun z - z‖ < β
  action_bound : ∀ z ∈ phaseDomain (erosion E (β + β)) (ρ - (γ + γ)),
    ‖(transformation.toFun z).1 - z.1‖ ≤ homologicalBound n M K δ / δ
  periodic : ∀ z ∈ phaseDomain (erosion E (β + β)) (ρ - (γ + γ)), ∀ k,
    transformation.toFun (phaseShift k z) = phaseShift k (transformation.toFun z)
  conj_compatible : ∀ z ∈ phaseDomain (erosion E (β + β)) (ρ - (γ + γ)),
    transformation.toFun (conjPhase z) = conjPhase (transformation.toFun z)

/-- The fundamental-step result assembled from its verified analytic and numerical inputs. -/
def FundamentalInput.result {n : ℕ} {G E : Set (ComplexSpace n)} {ρ β δ γ : ℝ≥0}
    {K M Θ : ℝ} {h : ComplexSpace n → ℂ} {f : AnalyticPhaseFunction n G ρ}
    (i : FundamentalInput (E := E) (β := β) (δ := δ) (γ := γ) (K := K) (M := M) (Θ := Θ) h f) :
    FundamentalResult h f E β δ γ K M where
  transformation := i.transformation
  perturbation := i.newPerturbation
  identity := i.transformed_hamiltonian
  bound := i.newPerturbation_bound
  displacement_lt := fun _ hz => (i.displacement hz).trans_lt i.budget.displacement_lt_beta
  action_bound := fun _ hz => i.action_displacement hz
  periodic := fun _ hz k => i.generator.generatingTransform_shift i.generatingData
    (i.budget.target_subset E hz) k
  conj_compatible := fun _ hz => i.generator.generatingTransform_conj i.generatingData
    (i.budget.target_subset E hz)

theorem fundamental_lemma {n : ℕ} {G E : Set (ComplexSpace n)} {ρ β δ γ : ℝ≥0}
    {K M Θ : ℝ} {h : ComplexSpace n → ℂ} {f : AnalyticPhaseFunction n G ρ}
    (i : FundamentalInput (E := E) (β := β) (δ := δ) (γ := γ) (K := K) (M := M) (Θ := Θ) h f) :
    Nonempty (FundamentalResult h f E β δ γ K M) := ⟨i.result⟩

theorem FundamentalInput.onNonresonantDomain {n : ℕ} {G : Set (ComplexSpace n)}
    {ρ β δ γ : ℝ≥0} {K M Θ : ℝ} {h : ComplexSpace n → ℂ}
    {f : AnalyticPhaseFunction n G ρ} (hi : IntegrableData h G Θ)
    (hb : FundamentalParameters n ρ β δ γ K M Θ) (hf : f.uniformNorm ≤ M)
    (hzero : ∀ p ∈ G, f.angleAverage p = 0) :
    FundamentalInput (E := nonresonantDomain G (actionFrequency h) K (fundamentalCutoff γ M))
      (β := β) (δ := δ) (γ := γ) (K := K) (M := M) (Θ := Θ) h f where
  integrable := hi
  domain_subset := fun _ hp => hp.1
  domain_conj := nonresonantDomain_conj f.domain_conj hi.frequency_conj
  perturbation_bound := hf
  mean_zero := fun _ hp => hzero _ hp.1
  nonresonant := fun _ hp => hp.2
  budget := hb

end KamProject.Arnold1963
