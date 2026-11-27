/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SourceModularHalfPower

/-!
# Modular operators and whole-source powers in the physical one-particle space

The transported exponent-one operator has exactly the universal physical
Tomita adjoint-product graph. Every source vector lies in the transported
power domain for 0≤c≤1/2 and satisfies the literal bounded-weight formula.
These powers are the established regularizable continuous construction;
no additional unbounded Borel calculus is assumed.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory ContinuousLinearMap

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))
variable (hU : Bornology.IsBounded U) (hopen : IsOpen U) (hne : U.Nonempty)

/-- Linear map for the physical modular operator, of type `Lp ℂ 2 (oneParticleMeasure m) →ₗ.[ℂ] Lp
ℂ 2 (oneParticleMeasure m)`. -/
noncomputable def physicalModularOperator :
    Lp ℂ 2 (oneParticleMeasure m) →ₗ.[ℂ] Lp ℂ 2 (oneParticleMeasure m) :=
  unitaryPartialTransport (sourcePolarUnitary hm U hU hopen hne) (sourceModularOperator hm U hU)

/-- Linear map for the physical modular power, of type `Lp ℂ 2 (oneParticleMeasure m) →ₗ.[ℂ] Lp ℂ 2
(oneParticleMeasure m)`. -/
noncomputable def physicalModularPower (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    Lp ℂ 2 (oneParticleMeasure m) →ₗ.[ℂ] Lp ℂ 2 (oneParticleMeasure m) :=
  unitaryPartialTransport (sourcePolarUnitary hm U hU hopen hne)
    (sourceModularPower hm U hU c hc hc1)

/-- Full graph equality with the literal maximal S*S relation. -/
theorem physicalModularOperator_graph :
    ((physicalModularOperator hm U hU hopen hne).graph :
      Set (Lp ℂ 2 (oneParticleMeasure m) × Lp ℂ 2 (oneParticleMeasure m))) =
        sourceTomitaModularGraph hm U hU := by
  ext p
  rcases p with ⟨x, y⟩
  change (x, y) ∈ (unitaryPartialTransport (sourcePolarUnitary hm U hU hopen hne)
    (sourceModularOperator hm U hU)).graph ↔ (x, y) ∈ sourceTomitaModularGraph hm U hU
  rw [unitaryPartialTransport_mem_graph, sourceModularOperator, boundedRatio_mem_graph]
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    (sourceTomitaModularGraph_polar_iff hm U hU hopen hne
      ((sourcePolarUnitary hm U hU hopen hne).symm x)
      ((sourcePolarUnitary hm U hU hopen hne).symm y)).symm

theorem physicalModularPower_one :
    physicalModularPower hm U hU hopen hne 1 (by norm_num) (by norm_num) =
      physicalModularOperator hm U hU hopen hne := by
  rw [physicalModularPower, sourceModularPower_one, physicalModularOperator]

/-- The source's entire completed complex space is in the composed domain. -/
theorem physicalModularPower_apply_source (c : ℝ) (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2)
    (z : ComplexSourceHilbert hm U) :
    ∃ hx : complexSourceMap hm U z ∈
        (physicalModularPower hm U hU hopen hne c hc (by linarith)).domain,
      physicalModularPower hm U hU hopen hne c hc (by linarith)
        ⟨complexSourceMap hm U z, hx⟩ =
          sourcePolarUnitary hm U hU hopen hne (sourceModularWeight hm U c z) := by
  let V := sourcePolarUnitary hm U hU hopen hne
  obtain ⟨hz, hval⟩ := sourceModularPower_apply_sqrt hm U hU c hc hc2 z
  have hpre : sourceGramRoot hm U z = V.symm (complexSourceMap hm U z) := by
    simpa only [V, sourceGramRoot, LinearIsometryEquiv.symm_apply_apply] using
      congrArg V.symm (sourcePolarUnitary_sqrt_gram hm U hU hopen hne z)
  have hx : complexSourceMap hm U z ∈
      (physicalModularPower hm U hU hopen hne c hc (by linarith)).domain := by
    change V.symm (complexSourceMap hm U z) ∈ (sourceModularPower hm U hU c hc (by linarith)).domain
    rw [← hpre]
    exact hz
  refine ⟨hx, ?_⟩
  change V (sourceModularPower hm U hU c hc (by linarith)
    ⟨V.symm (complexSourceMap hm U z), hx⟩) = V (sourceModularWeight hm U c z)
  have he : (⟨V.symm (complexSourceMap hm U z), hx⟩ :
      (sourceModularPower hm U hU c hc (by linarith)).domain) =
        ⟨sourceGramRoot hm U z, hz⟩ := Subtype.ext hpre.symm
  rw [he, hval]

end VacuumBellSeparation
