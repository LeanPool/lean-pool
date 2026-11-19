/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralTiltKilledOriginalLaw.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralTiltCanonicalPathMeasure
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianOUActionLocality
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianKilledOUPathMeasure

/-!
# Ginibre Brownian integral tilt killed original law

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `ginibreBrownian_original_killed_compact_path_law`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths over the horizon `[0, T]`. -/
local instance killedOriginalPathMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance killedOriginalPathBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩

/-- The actual original Ginibre Brownian path law killed on a Hamiltonian
sublevel is precisely the actual OU reference law with its literal killed
Hamiltonian interaction action. All integral and Girsanov witnesses are
constructed internally. -/
theorem ginibreBrownian_original_killed_compact_path_law {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z) (R : ℝ)
    (hR : ginibreHamiltonian n z < R) (T : ℝ≥0) (hT : 0 < T) :
    (P.map (ginibreCanonicalCompactPath n α z T (fun ω =>
      (ginibreBrownianFullContinuousNoise n B α ω).val))).restrict
        (ginibreHamiltonianCompactSurvival n T R)=
    (P.withDensity (fun ω => ENNReal.ofReal (Real.exp (ginibreInteractionPotential n z)*
      ginibreHamiltonianKilledOUActionWeight n α T R T.property
        (ginibreHamiltonianOUReferenceHorizon n α z B T ω)))).map
          (ginibreHamiltonianOUReferenceHorizon n α z B T) := by
  classical
  obtain ⟨Y, M, hM, hDi, hD1, hPath, hCouple⟩ :=
    ginibreActualOU_sublevel_canonical_compact_path_law_exists hn B P hB hind α z hz R hR T hT
  let F := fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i
  let D := brownianVectorExponentialIntegralDensity F T (fun i => M i T)
  let d := fun ω => ENNReal.ofReal (D ω)
  let Q := P.withDensity d
  let N := fun ω => ginibreConfigurationBrownianNoise n (ginibreInteractionCorrectedBrownian n α B
      Y) α ω
  let C := ginibreCanonicalCompactPath n α z T N
  let O := ginibreHamiltonianOUReferenceHorizon n α z B T
  let G := ginibreHamiltonianCompactSurvival n (T : ℝ) R
  let S := O ⁻¹' G
  let e := fun ω => ENNReal.ofReal (Real.exp (ginibreInteractionPotential n z)*
    ginibreHamiltonianOUActionWeight n α T T.property (O ω))
  have hOm : Measurable O := ginibreHamiltonianOUReferenceHorizon_measurable n α z B P hB T
  have hG : MeasurableSet G := ginibreHamiltonianCompactSurvival_measurableSet n T R
  have hS : MeasurableSet S := hG.preimage hOm
  have hPQ : P ≪ Q := withDensity_absolutelyContinuous'
    (ENNReal.measurable_ofReal.comp_aemeasurable hDi.aemeasurable)
    (ae_of_all P (fun ω => ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))))
  have hOStay (ω : Ω) : ω∈S ↔ ∀ t≤T,
      ginibreHamiltonianOUReferenceProcess n α z B t ω ∈ ginibreHamiltonianOUSublevelDomain n R :=
          by
    constructor
    · intro h t ht
      have hh := h (⟨t, ⟨t.property, by exact_mod_cast ht⟩⟩ : Icc (0 : ℝ) (T : ℝ))
      change ginibreHamiltonianOUReferenceProcess n α z B (t : ℝ).toNNReal ω∈_ at hh
      simpa only [Real.toNNReal_coe] using hh
    · intro h t
      exact h t.val.toNNReal (Real.toNNReal_le_iff_le_coe.mpr t.property.2)
  have hSetEq : C ⁻¹' G=ᵐ[Q] S := by
    filter_upwards [hPath.1, hCouple] with ω hAlive hω
    apply propext
    exact (ginibreCanonicalCompactPath_forall_iff_of_alive n α z T N ω hAlive
      (ginibreHamiltonianOUSublevelDomain n R)).trans (hω.1.trans (hOStay ω).symm)
  have hCO : ∀ᵐ ω ∂Q, ω∈S → C ω=O ω := by
    filter_upwards [hPath.1, hCouple] with ω hAlive hω
    intro hSω
    have hCan := (hω.2 ((hOStay ω).mp hSω)).1
    apply ContinuousMap.ext
    intro t
    rw [ginibreCanonicalCompactPath_apply_of_alive n α z T N ω hAlive]
    have he := hCan t.val.toNNReal (Real.toNNReal_le_iff_le_coe.mpr t.property.2)
    change ginibreDrivenMaximalValue n α (N ω) z t.val.toNNReal=
      ginibreHamiltonianOUReferenceProcess n α z B t.val.toNNReal ω
    exact he
  have hdeQ : ∀ᵐ ω ∂Q, ω∈S → d ω=e ω := by
    filter_upwards [hCouple] with ω hω
    intro hSω
    have hh := hω.2 ((hOStay ω).mp hSω)
    have hLocal := ginibreHamiltonianOUReference_action_of_prefix n α z B T ω Y hh.2.1
    change ENNReal.ofReal (brownianVectorExponentialIntegralDensity
      (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) T (fun i => M i T) ω)=
      ENNReal.ofReal (Real.exp (ginibreInteractionPotential n z)*
        ginibreHamiltonianOUActionWeight n α T T.property (O ω))
    rw [hh.2.2, hLocal]
  have hdeP : ∀ᵐ ω ∂P, ω∈S → d ω=e ω := hPQ.ae_le hdeQ
  have hIndicator : S.indicator e=fun ω => ENNReal.ofReal (Real.exp (ginibreInteractionPotential n
      z)*
      ginibreHamiltonianKilledOUActionWeight n α T R T.property (O ω)) := by
    funext ω
    by_cases hmem : ω∈S
    · have hm : O ω∈ginibreHamiltonianCompactSurvival n T R := hmem
      simp only [indicator_of_mem hmem, e, ginibreHamiltonianKilledOUActionWeight, indicator_of_mem
          hm]
    · have hm : O ω∉ginibreHamiltonianCompactSurvival n T R := hmem
      simp only [indicator_of_notMem hmem, ginibreHamiltonianKilledOUActionWeight,
          indicator_of_notMem hm, mul_zero, ENNReal.ofReal_zero]
  rw [← hPath.2.2.2, Measure.restrict_map hPath.2.1 hG, Measure.restrict_congr_set hSetEq]
  have hMap := actualTiltedKilledPath_map P d e S hS C O hCO hdeP
  rw [hIndicator] at hMap
  exact hMap

end
end GinibrePoincare
