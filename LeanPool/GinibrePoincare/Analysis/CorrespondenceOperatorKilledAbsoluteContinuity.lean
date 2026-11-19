/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorKilledAbsoluteContinuity.lean.
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
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralTiltKilledOriginalLaw
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralTiltJointCanonicalPath
/-!
# Correspondence operator killed absolute continuity

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperator_killed_path_absolutelyContinuous_OU`,
`correspondenceOperator_endpoint_absolutelyContinuous_OU`.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous paths `Icc 0 T → Configuration n`. -/
local instance correspondenceOperatorPathMeasurableSpace (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance correspondenceOperatorPathBorelSpace (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩

/-- The actual killed original Ginibre path law is absolutely continuous with
respect to the genuine OU path law. Its density is not an assumed Girsanov
certificate: the concrete interaction-action likelihood is proved internally. -/
theorem correspondenceOperator_killed_path_absolutelyContinuous_OU {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z) (R : ℝ)
    (hR : ginibreHamiltonian n z < R) (T : ℝ≥0) (hT : 0 < T) :
    (P.map (ginibreCanonicalCompactPath n α z T (fun ω =>
      (ginibreBrownianFullContinuousNoise n B α ω).val))).restrict
        (ginibreHamiltonianCompactSurvival n T R) ≪
      P.map (ginibreHamiltonianOUReferenceHorizon n α z B T) := by
  rw [ginibreBrownian_original_killed_compact_path_law hn B P hB hind α z hz R hR T hT]
  have hm := ginibreHamiltonianOUReferenceHorizon_measurable n α z B P hB T
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hs0
  rw [Measure.map_apply hm hs] at hs0 ⊢
  exact (withDensity_absolutelyContinuous _ _) hs0

/-- Removing Hamiltonian killing by the actual compact-path exhaustion proves
absolute continuity of the entire original path law, for every collision-free
deterministic initial configuration. -/
theorem correspondenceOperator_path_absolutelyContinuous_OU {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z) (T : ℝ≥0) (hT : 0 < T) :
    P.map (fun ω => ginibreCanonicalJointHorizonPath α T
      (⟨z, hz⟩, ginibreBrownianFullContinuousNoise n B α ω)) ≪
      P.map (ginibreHamiltonianOUReferenceHorizon n α z B T) := by
  let X := fun ω => ginibreCanonicalJointHorizonPath α T
    (⟨z, hz⟩, ginibreBrownianFullContinuousNoise n B α ω)
  let μ := P.map X
  have hX : Measurable X := (ginibreCanonicalJointHorizonPath_measurable hn α T).comp
    (measurable_const.prodMk (ginibreBrownianFullContinuousNoise_measurable n B P hB α))
  have hEx : ∀ᵐ x ∂μ, ∃ k : ℕ, x∈ginibreHamiltonianCompactSurvival n T k := by
    apply (ae_map_iff hX.aemeasurable ?_).mpr
    · exact Filter.Eventually.of_forall (fun ω =>
        ginibreHamiltonian_compact_path_natural_sublevel_exhaustion T (X ω)
          (ginibreCanonicalJointHorizonPath_collisionFree α T _))
    · have he : {x | ∃ k : ℕ, x∈ginibreHamiltonianCompactSurvival n T k} =
          ⋃ k : ℕ, ginibreHamiltonianCompactSurvival n T k := by ext x; simp
      rw [he]
      exact MeasurableSet.iUnion (fun k : ℕ => ginibreHamiltonianCompactSurvival_measurableSet n T
          k)
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hs0
  have hk : ∀ k : ℕ, μ (s∩ginibreHamiltonianCompactSurvival n T k)=0 := by
    intro k
    have hac : μ.restrict (ginibreHamiltonianCompactSurvival n T k) ≪
        P.map (ginibreHamiltonianOUReferenceHorizon n α z B T) := by
      change (P.map X).restrict _ ≪ _
      rw [ginibreBrownian_original_joint_killed_compact_path_law_all_initial
        hn B P hB hind α z hz k T hT]
      have hm := ginibreHamiltonianOUReferenceHorizon_measurable n α z B P hB T
      apply Measure.AbsolutelyContinuous.mk
      intro a ha ha0
      rw [Measure.map_apply hm ha] at ha0 ⊢
      exact (withDensity_absolutelyContinuous _ _) ha0
    simpa only [Measure.restrict_apply hs] using hac hs0
  apply measure_eq_zero_iff_ae_notMem.mpr
  have hAll : ∀ᵐ x ∂μ, ∀ k : ℕ, x∉s∩ginibreHamiltonianCompactSurvival n T k :=
    ae_all_iff.mpr (fun k => measure_eq_zero_iff_ae_notMem.mp (hk k))
  filter_upwards [hEx, hAll] with x hx hnot
  obtain ⟨k, hk⟩ := hx
  exact fun hsx => hnot k ⟨hsx, hk⟩

/-- Every positive-time original transition law is absolutely continuous with
respect to its deterministic-initial OU endpoint law. -/
theorem correspondenceOperator_endpoint_absolutelyContinuous_OU {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z) (T : ℝ≥0) (hT : 0 < T) :
    P.map (fun ω => ginibreCanonicalJointHorizonPath α T
      (⟨z, hz⟩, ginibreBrownianFullContinuousNoise n B α ω) ⟨T, ⟨T.property, le_rfl⟩⟩) ≪
      P.map (fun ω => ginibreHamiltonianOUReferenceHorizon n α z B T ω
        ⟨T, ⟨T.property, le_rfl⟩⟩) := by
  let e : C(Icc (0 : ℝ) (T : ℝ), Configuration n) → Configuration n :=
    fun x => x ⟨T, ⟨T.property, le_rfl⟩⟩
  have he : Measurable e := (continuous_eval_const _).measurable
  have hX : Measurable (fun ω => ginibreCanonicalJointHorizonPath α T
      (⟨z, hz⟩, ginibreBrownianFullContinuousNoise n B α ω)) :=
    (ginibreCanonicalJointHorizonPath_measurable hn α T).comp
    (measurable_const.prodMk (ginibreBrownianFullContinuousNoise_measurable n B P hB α))
  have hY := ginibreHamiltonianOUReferenceHorizon_measurable n α z B P hB T
  have hac := correspondenceOperator_path_absolutelyContinuous_OU hn B P hB hind α z hz T hT
  apply Measure.AbsolutelyContinuous.mk
  intro a ha ha0
  change (P.map (e ∘ ginibreHamiltonianOUReferenceHorizon n α z B T)) a=0 at ha0
  change (P.map (e ∘ (fun ω => ginibreCanonicalJointHorizonPath α T
    (⟨z, hz⟩, ginibreBrownianFullContinuousNoise n B α ω)))) a=0
  rw [Measure.map_apply (he.comp hY) ha] at ha0
  rw [Measure.map_apply (he.comp hX) ha]
  have hy0 : (P.map (ginibreHamiltonianOUReferenceHorizon n α z B T)) (e ⁻¹' a)=0 := by
    rw [Measure.map_apply hY (he ha)]
    exact ha0
  have hx0 := hac hy0
  rw [Measure.map_apply hX (he ha)] at hx0
  exact hx0

end
end GinibrePoincare
