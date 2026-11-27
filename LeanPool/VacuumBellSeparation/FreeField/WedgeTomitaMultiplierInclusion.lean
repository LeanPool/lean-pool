/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WedgeWaveMultiplierDomain
public import LeanPool.VacuumBellSeparation.FreeField.WedgeReflection
public import LeanPool.VacuumBellSeparation.FreeField.WedgeSpacetimeTomitaCore

/-!
# One full graph inclusion for the actual wedge Tomita operator

The literal spacetime test graph is contained in J times the maximal positive
rapidity half-power. Closedness and the actual test-core theorem extend this
inclusion to the whole original source graph. The reverse inclusion, by Gaussian
regularization, is proved in another module (`wedgeRapidityTomitaGraph_subset_sourceTomitaGraph`
in `FreeField/WedgeTomitaMultiplierEquality.lean`).
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped ComplexConjugate

/-- Set of points satisfying the wedge rapidity Tomita graph condition. -/
def wedgeRapidityTomitaGraph {m : ℝ} (hm : 0 < m) :
    Set (Lp ℂ 2 (oneParticleMeasure m) × Lp ℂ 2 (oneParticleMeasure m)) :=
  {p | (p.1, physicalWedgeReflection hm p.2) ∈ (physicalRapidityExponential hm (1 / 2)).graph}

theorem wedgeRapidityTomitaGraph_isClosed {m : ℝ} (hm : 0 < m) :
    IsClosed (wedgeRapidityTomitaGraph hm) :=
  (physicalRapidityExponential_isSelfAdjoint hm (1 / 2)).isClosed.preimage
    (continuous_fst.prodMk ((physicalWedgeReflection hm).continuous.comp continuous_snd))

private theorem conjugate_submodule_add_I_mem {E : Type*}
    [AddCommGroup E] [Module ℂ E] (P : Submodule ℂ (E × E))
    (J : E → E) {x y : E}
    (hJ : J (x - Complex.I • y) = J x + Complex.I • J y)
    (hx : (x, J x) ∈ P) (hy : (y, J y) ∈ P) :
    (x + Complex.I • y, J (x - Complex.I • y)) ∈ P := by
  rw [hJ]
  exact P.add_mem hx (P.smul_mem Complex.I hy)

private theorem physicalWedgeReflection_sub_I {m : ℝ} (hm : 0 < m)
    (ψ χ : Lp ℂ 2 (oneParticleMeasure m)) :
    physicalWedgeReflection hm (ψ - Complex.I • χ) =
      physicalWedgeReflection hm ψ + Complex.I • physicalWedgeReflection hm χ := by
  rw [map_sub, physicalWedgeReflection_smul, Complex.conj_I, neg_smul, sub_neg_eq_add]

private theorem wedgeWave_reflection_mem_physicalRapidityHalf_graph
    {m : ℝ} (hm : 0 < m) (F : RealTestFunction)
    (hF : tsupport F.1 ⊆ leftWedge 0) :
    (oneParticleL2 hm F, physicalWedgeReflection hm (oneParticleL2 hm F)) ∈
      (physicalRapidityExponential hm (1 / 2)).graph :=
  Eq.mp (congrArg (fun ψ => (oneParticleL2 hm F, ψ) ∈
      (physicalRapidityExponential hm (1 / 2)).graph)
    (wedgeWaveL2_upper_eq_reflection hm F hF))
    (wedgeWave_upper_mem_physicalRapidityHalf_graph hm F hF)

private theorem conjugate_submodule_testGraph_subset {α E : Type*}
    [AddCommGroup E] [Module ℂ E] (P : Submodule ℂ (E × E))
    (J : E → E) (f : α → E) (Q : α → Prop)
    (hJ : ∀ x y, J (x - Complex.I • y) = J x + Complex.I • J y)
    (hf : ∀ a, Q a → (f a, J (f a)) ∈ P) :
    {p | ∃ a b, Q a ∧ Q b ∧ p = (f a + Complex.I • f b, f a - Complex.I • f b)} ⊆
      {p | (p.1, J p.2) ∈ P} := by
  rintro _ ⟨a, b, ha, hb, rfl⟩
  exact conjugate_submodule_add_I_mem P J (hJ (f a) (f b)) (hf a ha) (hf b hb)

theorem wedgeSpacetimeTomitaTestGraph_subset_rapidityGraph {m : ℝ} (hm : 0 < m) :
    wedgeSpacetimeTomitaTestGraph hm 0 ⊆ wedgeRapidityTomitaGraph hm :=
  conjugate_submodule_testGraph_subset
    (α := RealTestFunction) (E := Lp ℂ 2 (oneParticleMeasure m))
    (physicalRapidityExponential hm (1 / 2)).graph
    (physicalWedgeReflection hm) (oneParticleL2 hm)
    (fun F => tsupport F.1 ⊆ leftWedge 0)
    (physicalWedgeReflection_sub_I hm)
    (wedgeWave_reflection_mem_physicalRapidityHalf_graph hm)

/-- This is a full graph inclusion for the actual original halfspace source;
no modular formula or multiplier-domain premise occurs in the hypotheses. -/
theorem sourceTomitaGraph_subset_wedgeRapidityTomitaGraph {m : ℝ} (hm : 0 < m) :
    sourceTomitaGraph hm (leftWedgeTimeZero 0) ⊆ wedgeRapidityTomitaGraph hm := by
  rw [← closure_wedgeSpacetimeTomitaTestGraph hm 0]
  exact closure_minimal (wedgeSpacetimeTomitaTestGraph_subset_rapidityGraph hm)
    (wedgeRapidityTomitaGraph_isClosed hm)

end VacuumBellSeparation
