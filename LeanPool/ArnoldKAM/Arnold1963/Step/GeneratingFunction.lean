/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Step.HomologicalBound

/-!
Supporting results for the analytic Hamiltonian KAM construction.
-/

@[expose] public section
noncomputable section
open Set
open scoped NNReal
namespace KamProject.Arnold1963

/-- The finite homological generator packaged with analytic phase-function structure and bounds. -/
def homologicalFunction {n : ℕ} {G E : Set (ComplexSpace n)} {ρ δ : ℝ≥0}
    (f : AnalyticPhaseFunction n G ρ) (ω : ComplexSpace n → ComplexSpace n)
    {K N M : ℝ} (hE : E ⊆ G) (hc : ConjInvariant E)
    (hω : AnalyticOnNhd ℂ ω E) (hωc : ∀ p ∈ E, ω (conjVec p) = conjVec (ω p))
    (hnr : ∀ p ∈ E, FiniteNonresonant (ω p) K N) (hK : 0 < K)
    (hM : f.uniformNorm ≤ M) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδρ : δ + δ ≤ ρ) :
    AnalyticPhaseFunction n E (ρ - (δ + δ)) where
  toFun := homologicalGenerator f ω N
  domain_conj := hc
  analytic := fun z hz => analyticAt_homologicalGenerator f (hE hz.1)
    (hω z.1 hz.1) hK (hnr z.1 hz.1)
  periodic := by intro p hp q hq m; exact homologicalGenerator_periodic f p q m
  conj_compatible := fun z hz => homologicalGenerator_conj f (hE hz.1) (hωc z.1 hz.1)
  bounded := by
    refine ⟨homologicalBound n M K δ, ?_, fun z hz => ?_⟩
    · have hm := (f.norm_le_iff.mp le_rfl).nonneg.trans hM
      have hL := constantL5_pos n
      unfold homologicalBound
      positivity
    · apply norm_homologicalGenerator_le f (hE hz.1) hM hK hδ
        (show (δ : ℝ) ≤ 1 from hδ1) (hnr z.1 hz.1)
      have hq := hz.2
      change ‖imagPart z.2‖ ≤ (↑(ρ - (δ + δ)) : ℝ) at hq
      rw [NNReal.coe_sub hδρ, NNReal.coe_add] at hq
      convert hq using 1
      rfl

theorem norm_homologicalFunction_le {n : ℕ} {G E : Set (ComplexSpace n)} {ρ δ : ℝ≥0}
    (f : AnalyticPhaseFunction n G ρ) (ω : ComplexSpace n → ComplexSpace n)
    {K N M : ℝ} (hE : E ⊆ G) (hc : ConjInvariant E)
    (hω : AnalyticOnNhd ℂ ω E) (hωc : ∀ p ∈ E, ω (conjVec p) = conjVec (ω p))
    (hnr : ∀ p ∈ E, FiniteNonresonant (ω p) K N) (hK : 0 < K)
    (hM : f.uniformNorm ≤ M) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδρ : δ + δ ≤ ρ) :
    (homologicalFunction f ω hE hc hω hωc hnr hK hM hδ hδ1 hδρ).uniformNorm ≤
      homologicalBound n M K δ := by
  apply (AnalyticPhaseFunction.norm_le_iff _).mpr
  refine ⟨?_, fun z hz => ?_⟩
  · have hm := (f.norm_le_iff.mp le_rfl).nonneg.trans hM
    have hL := constantL5_pos n
    unfold homologicalBound
    positivity
  · exact norm_homologicalGenerator_le f (hE hz.1) hM hK hδ (show (δ : ℝ) ≤ 1 from hδ1)
      (hnr z.1 hz.1) (by
        have hq := hz.2
        change ‖imagPart z.2‖ ≤ (↑(ρ - (δ + δ)) : ℝ) at hq
        rw [NNReal.coe_sub hδρ, NNReal.coe_add] at hq
        convert hq using 1)

end KamProject.Arnold1963
